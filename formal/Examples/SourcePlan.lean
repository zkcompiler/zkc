import Zkc.Compiler.ArtifactFormat
import Zkc.Source.InputBinding
import Mathlib.Data.ZMod.Basic

/-! A maintained client with two real fields and a stateful call that can stop.
Its finite vocabulary is an example interpretation, not the compiler's registry.
-/

set_option autoImplicit false

namespace SourcePlanExample

open Zkc.Source Zkc.Compiler

inductive FieldDomain where
  | five
  | seven
  deriving DecidableEq, Repr

inductive Ty where
  | boolean
  | natural
  | field (domain : FieldDomain)
  | summary
  deriving DecidableEq, Repr

abbrev Value : Ty → Type
  | .boolean => Bool
  | .natural => Nat
  | .field .five => ZMod 5
  | .field .seven => ZMod 7
  | .summary => ZMod 5 × ZMod 7 × Nat

inductive Op where
  | subtract (domain : FieldDomain)
  | negate (domain : FieldDomain)
  | increment
  | record
  | pack
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .subtract domain => [.field domain, .field domain]
  | .negate domain => [.field domain]
  | .increment | .record => [.natural]
  | .pack => [.field .five, .field .seven, .natural]

def result : Op → Ty
  | .subtract domain | .negate domain => .field domain
  | .increment | .record => .natural
  | .pack => .summary

abbrev language : Language := ⟨Ty, Op, arguments, result, .boolean⟩

abbrev interface : PIR.Signature := ⟨Nat, fun _ => Nat⟩

abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation
    | .subtract .five, .cons a (.cons b .nil) => .done (a - b)
    | .subtract .seven, .cons a (.cons b .nil) => .done (a - b)
    | .negate .five, .cons a .nil => .done (-a)
    | .negate .seven, .cons a .nil => .done (-a)
    | .increment, .cons n .nil => .done (n + 1)
    | .record, .cons n .nil => .call n .done
    | .pack, .cons a (.cons b (.cons n .nil)) => .done (a, b, n)

/-- A failed call still increments the state and emits the attempted value. -/
def handler : PIR.Handler interface Nat Nat := fun value state =>
  ⟨if value == 0 then .stopped .abort else .returned value, state + 1, [value]⟩

def declarations : List (InputDeclaration Ty) := [
  ⟨"enabled", .boolean, .shared, .argument⟩,
  ⟨"counter", .natural, .privateTo "prover", .argument⟩,
  ⟨"left", .field .five, .privateTo "prover", .capture⟩,
  ⟨"right", .field .five, .privateTo "prover", .capture⟩,
  ⟨"offset", .field .seven, .privateTo "prover", .capture⟩]

abbrev context : List Ty := [.boolean, .natural, .field .five, .field .five, .field .seven]

def raw : RawProgram Ty Op :=
  .letOp (.subtract .five) [2, 3]
    (.letOp (.negate .seven) [5]
      (.branch 2
        (.iterate 3 .natural 3
          (.letOp .record [0] (.letOp .increment [0] (.ret 0)))
          (.letOp .pack [2, 1, 0] (.ret 0)))
        (.stop .reject)))

def source : Program language context .summary :=
  (raw.elaborate context .summary (language := language)).toOption.get (by decide)

def supplied (enabled : Bool) (counter : Nat) : List (SuppliedInput Value) := [
  ⟨"enabled", .boolean, enabled⟩,
  ⟨"counter", .natural, counter⟩,
  ⟨"left", .field .five, 4⟩,
  ⟨"right", .field .five, 2⟩,
  ⟨"offset", .field .seven, 3⟩]

def values (enabled : Bool) (counter : Nat) : Values Value context :=
  .cons enabled (.cons counter (.cons 4 (.cons 2 (.cons 3 .nil))))

def run (enabled : Bool) (counter : Nat) : PIR.Execution Nat Nat (ZMod 5 × ZMod 7 × Nat) :=
  (lower source).run meaning handler (values enabled counter).get 0

def typeCodec : Format.Codec Ty where
  encode
    | .boolean => .str "bool"
    | .natural => .str "nat"
    | .field .five => .str "field/5"
    | .field .seven => .str "field/7"
    | .summary => .str "summary"
  decode
    | .str "bool" => .ok .boolean
    | .str "nat" => .ok .natural
    | .str "field/5" => .ok (.field .five)
    | .str "field/7" => .ok (.field .seven)
    | .str "summary" => .ok .summary
    | _ => .error .unknownType

def operationCodec : Format.Codec Op where
  encode
    | .subtract .five => .str "subtract/5"
    | .subtract .seven => .str "subtract/7"
    | .negate .five => .str "negate/5"
    | .negate .seven => .str "negate/7"
    | .increment => .str "increment"
    | .record => .str "record"
    | .pack => .str "pack"
  decode
    | .str "subtract/5" => .ok (.subtract .five)
    | .str "subtract/7" => .ok (.subtract .seven)
    | .str "negate/5" => .ok (.negate .five)
    | .str "negate/7" => .ok (.negate .seven)
    | .str "increment" => .ok .increment
    | .str "record" => .ok .record
    | .str "pack" => .ok .pack
    | _ => .error .unknownOperation

/-- Example registry resolution is an exact, versioned vocabulary selection. -/
def dependencies : List DefinitionRef := [⟨"source-plan-example", "1"⟩]

def request : Request Ty Op :=
  ⟨⟨"prover", declarations, .summary, dependencies⟩, [], raw⟩

def candidate : Candidate Ty Op :=
  ⟨formatVersion, semanticsVersion, [], "direct-logical-plan", "direct-lowering",
    completeExecution, request.context, [], raw⟩

def requestCodec : Format.Codec (Request Ty Op) :=
  ArtifactFormat.request typeCodec operationCodec 256

def candidateCodec : Format.Codec (Candidate Ty Op) :=
  ArtifactFormat.candidate typeCodec operationCodec 256

end SourcePlanExample
