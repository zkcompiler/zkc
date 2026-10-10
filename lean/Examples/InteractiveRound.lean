import Zkc.Compiler.Admission
import Zkc.Compiler.ArtifactFormat
import Zkc.Source.PhaseAdmissionFormat

/-! A local endpoint with commit, receive-challenge and respond operations.

This interaction skeleton exercises admission, not cryptographic commitments,
challenge distributions or a security reduction. All replies have type Nat;
the summary laws cover every such reply, independently of the example handler.
-/

set_option autoImplicit false

namespace InteractiveRound

open Zkc.Source Zkc.Compiler PhaseAdmission

inductive Ty where
  | boolean
  | natural
  deriving DecidableEq, Repr

abbrev Value : Ty → Type
  | .boolean => Bool
  | .natural => Nat

inductive Op where
  | commit
  | challenge
  | respond
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .commit | .respond => [.natural]
  | .challenge => []

abbrev language : Language := ⟨Ty, Op, arguments, fun _ => .natural, .boolean⟩

inductive Call where
  | commit (value : Nat)
  | challenge
  | respond (value : Nat)
  deriving DecidableEq, Repr

abbrev interface : PIR.Signature := ⟨Call, fun _ => Nat⟩

abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation
    | .commit, .cons value .nil => .call (.commit value) .done
    | .challenge, .nil => .call .challenge .done
    | .respond, .cons value .nil => .call (.respond value) .done

inductive Phase where
  | ready
  | committed
  | challenged
  deriving DecidableEq, Repr

/-- Owners identify the local endpoint actions, including receiving a challenge. -/
def interaction : PIR.Interaction interface where
  Role := Unit
  Phase := Phase
  owner := fun _ => ()
  enabled
    | .ready, .commit _ => True
    | .committed, .challenge => True
    | .challenged, .respond _ => True
    | _, _ => False
  advance := fun _ op _ => match op with
    | .commit _ => .committed
    | .challenge => .challenged
    | .respond _ => .ready

def policy : Policy language Phase where
  step
    | .commit, .ready => some [.committed]
    | .challenge, .committed => some [.challenged]
    | .respond, .challenged => some [.ready]
    | _, _ => none

def summaryLaws : Realizes policy meaning interaction where
  relates := Eq
  operation := by
    intro op before exits accepted args phase relates
    cases relates
    cases op with
    | commit =>
      cases before <;> simp [policy] at accepted
      subst exits
      cases args with
      | cons value tail =>
        cases tail
        exact ⟨⟨trivial, fun _ => trivial⟩, fun _ => ⟨.committed, by simp, rfl⟩⟩
    | challenge =>
      cases before <;> simp [policy] at accepted
      subst exits
      cases args
      exact ⟨⟨trivial, fun _ => trivial⟩, fun _ => ⟨.challenged, by simp, rfl⟩⟩
    | respond =>
      cases before <;> simp [policy] at accepted
      subst exits
      cases args with
      | cons value tail =>
        cases tail
        exact ⟨⟨trivial, fun _ => trivial⟩, fun _ => ⟨.ready, by simp, rfl⟩⟩

/-- Failure records the attempted call and residual provider state. -/
def handler : PIR.Handler interface Nat Call := fun op state =>
  let outcome := match op with
    | .commit value => if value == 0 then .stopped .abort else .returned value
    | .challenge => .returned (state + 10)
    | .respond value => .returned value
  ⟨outcome, state + 1, [op]⟩

def declarations : List (InputDeclaration Ty) := [
  ⟨"enabled", .boolean, .shared, .argument⟩,
  ⟨"value", .natural, .privateTo "prover", .argument⟩]

abbrev context : List Ty := [.boolean, .natural]

def roundBody : RawProgram Ty Op :=
  .letOp .commit [0] (.letOp .challenge [] (.letOp .respond [0] (.ret 0)))

def raw : RawProgram Ty Op :=
  .branch 0 (.iterate 3 .natural 1 roundBody (.ret 0)) (.stop .reject)

def source : Program language context .natural :=
  (raw.elaborate context .natural (language := language)).toOption.get (by decide)

def certificate : Certificate Phase :=
  .branch (.loop [.ready] (.next (.next (.next .terminal))) .terminal) .terminal

def admitted : Admitted policy source [.ready] [.ready] :=
  (admit policy source certificate [.ready] [.ready]).get (by decide)

def supplied (enabled : Bool) (value : Nat) : List (SuppliedInput Value) := [
  ⟨"enabled", .boolean, enabled⟩, ⟨"value", .natural, value⟩]

def values (enabled : Bool) (value : Nat) : Values Value context :=
  .cons enabled (.cons value .nil)

def run (enabled : Bool) (value : Nat) :=
  (lower source).run meaning (PIR.ExecutionPath.handler interaction handler)
    (values enabled value).get (.ready, 0)

def typeCodec : Format.Codec Ty where
  encode
    | .boolean => .str "bool"
    | .natural => .str "nat"
  decode
    | .str "bool" => .ok .boolean
    | .str "nat" => .ok .natural
    | _ => .error .unknownType

def operationCodec : Format.Codec Op where
  encode
    | .commit => .str "commit"
    | .challenge => .str "challenge"
    | .respond => .str "respond"
  decode
    | .str "commit" => .ok .commit
    | .str "challenge" => .ok .challenge
    | .str "respond" => .ok .respond
    | _ => .error .unknownOperation

def phaseCodec : Format.Codec Phase where
  encode
    | .ready => .str "ready"
    | .committed => .str "committed"
    | .challenged => .str "challenged"
  decode
    | .str "ready" => .ok .ready
    | .str "committed" => .ok .committed
    | .str "challenged" => .ok .challenged
    | _ => .error .shape

def dependencies : List DefinitionRef := [⟨"interactive-round", "1"⟩]

def request : Request Ty Op := ⟨⟨"prover", declarations, .natural, dependencies⟩, [], raw⟩

def candidate : Candidate Ty Op :=
  ⟨formatVersion, semanticsVersion, [], "direct-logical-plan", "direct-lowering",
    completeExecution, request.context, [], raw⟩

def requestCodec : Format.Codec (Request Ty Op) :=
  ArtifactFormat.request typeCodec operationCodec 256

def candidateCodec : Format.Codec (Candidate Ty Op) :=
  ArtifactFormat.candidate typeCodec operationCodec 256

end InteractiveRound
