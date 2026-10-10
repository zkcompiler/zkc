import Zkc.Polynomial.Table
import Zkc.Compiler.Checking
import Zkc.Source.InputBinding
import Mathlib.Data.ZMod.Basic

/-! Two-domain table and protocol-operation interpretation for native correspondence.
This finite example profile is not the common protocol language or a security theorem. -/

set_option autoImplicit false
namespace TableProtocol
open Zkc.Source Zkc.Compiler Zkc.Polynomial Zkc.Polynomial.Table

inductive Domain where | two | seven deriving DecidableEq, Repr
abbrev Field : Domain → Type | .two => ZMod 2 | .seven => ZMod 7
instance (d : Domain) : CommRing (Field d) := by cases d <;> infer_instance
instance (d : Domain) : DecidableEq (Field d) := by cases d <;> infer_instance

inductive Ty where
  | boolean | digest | summary
  | scalar (d : Domain)
  | table (d : Domain) (originalRank : Nat)
  | residual (d : Domain) (originalRank : Nat)
  | point (d : Domain)
  deriving DecidableEq, Repr

abbrev Value : Ty → Type
  | .boolean => Bool
  | .digest => Nat
  | .summary => Field .two × Field .seven × Nat
  | .scalar d => Field d
  | .table d n => Table (Field d) n
  | .residual d n => Residual (Field d) n
  | .point d => List (Field d)

inductive Op where
  | view (d : Domain) (n : Nat)
  | restrict (d : Domain) (n : Nat)
  | evaluate (d : Domain) (n : Nat)
  | add (d : Domain)
  | record (d : Domain)
  | abortWrite (d : Domain)
  | orderedPair | pack
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .view d n => [.table d n]
  | .restrict d n => [.residual d n, .scalar d]
  | .evaluate d n => [.residual d n, .point d]
  | .add d => [.scalar d, .scalar d]
  | .record d | .abortWrite d => [.scalar d]
  | .orderedPair => [.digest, .digest]
  | .pack => [.scalar .two, .scalar .seven, .digest]

def result : Op → Ty
  | .view d n | .restrict d n => .residual d n
  | .evaluate d _ | .add d => .scalar d
  | .record _ | .abortWrite _ => .boolean
  | .orderedPair => .digest
  | .pack => .summary

abbrev language : Language := ⟨Ty, Op, arguments, result, .boolean⟩
structure Request where
  domain : Domain
  value : Field domain
  abort : Bool
abbrev interface : PIR.Signature := ⟨Request, fun _ => Bool⟩

def checked {A : Type} (value : Option A) : PIR.Proc interface A :=
  match value with | some x => .done x | none => .halt .refused

abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation
    | .view _ _, .cons t .nil => .done (view t)
    | .restrict _ _, .cons v (.cons r .nil) => checked (restrict v r)
    | .evaluate d _, .cons v (.cons p .nil) => checked (evaluate (F := Field d) v p)
    | .add _, .cons a (.cons b .nil) => .done (a + b)
    | .record d, .cons x .nil => .call ⟨d, x, false⟩ .done
    | .abortWrite d, .cons x .nil => .call ⟨d, x, true⟩ .done
    | .orderedPair, .cons a (.cons b .nil) => .done (Nat.pair a b)
    | .pack, .cons a (.cons b (.cons c .nil)) => .done (a, b, c)

structure World where
  two : Field .two := 0
  seven : Field .seven := 0
  writes : Nat := 0

structure Event where
  domain : Domain
  value : Nat
  deriving DecidableEq, Repr

def write (request : Request) (world : World) : World :=
  match request with
  | ⟨.two, x, _⟩ => { world with two := x, writes := world.writes + 1 }
  | ⟨.seven, x, _⟩ => { world with seven := x, writes := world.writes + 1 }

def event (request : Request) : Event :=
  match request with
  | ⟨.two, x, _⟩ => ⟨.two, x.val⟩
  | ⟨.seven, x, _⟩ => ⟨.seven, x.val⟩

def handler : PIR.Handler interface World Event := fun request world =>
  ⟨if request.abort then .stopped .abort else .returned (decide (request.value ≠ 0)),
    write request world, [event request]⟩

theorem failed_write_retained (d : Domain) (x : Field d) (world : World) :
    handler ⟨d, x, true⟩ world =
      ⟨.stopped .abort, write ⟨d, x, true⟩ world, [event ⟨d, x, true⟩]⟩ := rfl

theorem false_reply_retained (d : Domain) (world : World) :
    handler ⟨d, 0, false⟩ world =
      ⟨.returned false, write ⟨d, 0, false⟩ world, [event ⟨d, 0, false⟩]⟩ := by
  simp [handler]

theorem direct_preserves {Γ : List Ty} {ty : Ty}
    (source : Program language Γ ty) (values : Values Value Γ) (world : World) :
    (lower source).run meaning handler values.get world =
      (source.denote meaning values.get).run handler world :=
  lower_correct meaning handler source values.get world

namespace Protocol
inductive Call where
  | base (request : Request)
  | send (atZero atOne : Field .seven)
  | draw
abbrev Reply : Call → Type
  | .base _ | .send _ _ => Bool
  | .draw => Field .seven
abbrev protocolInterface : PIR.Signature := ⟨Call, Reply⟩

def lift {A : Type} : PIR.Proc interface A → PIR.Proc protocolInterface A
  | .done x => .done x
  | .halt why => .halt why
  | .call request next => .call (.base request) (fun reply => lift (next reply))

inductive Operation where
  | base (op : Op)
  | send | draw | linear | point | equal
  | endpointPoint (atOne : Bool)
  | parent (siblingOnLeft : Bool)
  | digestEqual
  deriving DecidableEq, Repr

def arguments : Operation → List Ty
  | .base op => TableProtocol.arguments op
  | .send | .equal => [.scalar .seven, .scalar .seven]
  | .draw | .endpointPoint _ => []
  | .linear => [.scalar .seven, .scalar .seven, .scalar .seven]
  | .point => [.scalar .seven]
  | .parent _ | .digestEqual => [.digest, .digest]
def result : Operation → Ty
  | .base op => TableProtocol.result op
  | .send | .equal | .digestEqual => .boolean
  | .draw | .linear => .scalar .seven
  | .point | .endpointPoint _ => .point .seven
  | .parent _ => .digest
abbrev language : Language := ⟨Ty, Operation, arguments, result, .boolean⟩
abbrev meaning : Interpretation language protocolInterface where
  Value := Value
  condition := id
  operation
    | .base op, args => lift (TableProtocol.meaning.operation op args)
    | .send, .cons a (.cons b .nil) => .call (.send a b) .done
    | .draw, .nil => .call .draw .done
    | .linear, .cons a (.cons b (.cons r .nil)) => .done ((1-r)*a+r*b)
    | .point, .cons r .nil => .done [r]
    | .endpointPoint atOne, .nil => .done [if atOne then 1 else 0]
    | .equal, .cons a (.cons b .nil) => .done (decide (a=b))
    | .parent left, .cons value (.cons sibling .nil) =>
        .done (if left then Nat.pair sibling value else Nat.pair value sibling)
    | .digestEqual, .cons a (.cons b .nil) => .done (decide (a=b))

structure State where
  base : World := {}
  sent : List (Field .seven × Field .seven) := []
  tape : List (Field .seven) := []
inductive Trace where
  | base (event : Event)
  | sent (atZero atOne : Nat)
  | drawn (value : Nat)
  deriving DecidableEq, Repr

def handler : PIR.Handler protocolInterface State Trace
  | .base request, state =>
      let out := TableProtocol.handler request state.base
      ⟨out.outcome, { state with base := out.state }, out.events.map Trace.base⟩
  | .send a b, state =>
      ⟨.returned true, { state with sent := state.sent ++ [(a,b)] }, [.sent a.val b.val]⟩
  | .draw, state =>
      match state.tape with
      | [] => ⟨.stopped .exhausted, state, []⟩
      | r :: rest => ⟨.returned r, { state with tape := rest }, [.drawn r.val]⟩


end Protocol
end TableProtocol
