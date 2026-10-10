import Zkc.Protocols.AlgebraicRounds.EarlySource
import Zkc.Source.Composition
import Zkc.Transformations.Memoization.Execution
import Zkc.Protocols.CapturedPrograms.Execution

set_option autoImplicit false
namespace Tests.SourceComposition
open PIR
open Zkc.Protocols.CapturedPrograms PIR.SourceView Zkc.Protocols.CapturedPrograms.Inputs
open Zkc.Source.Availability

variable {Role F H : Type} [DecidableEq Role] [CommRing F] [DecidableEq F]

/-- Actual role-qualified admission establishes equality of the entire client
    process, uniformly over public session bounds and every supplied history. -/
theorem client_same_view (actor : Role) (bindings : List (Slot Role))
    (w v : World Role F H) (tree : Tree) (x y : Issued F)
    (hx : admit actor bindings w tree = some x) (hy : admit actor bindings v tree = some y)
    (agree : SameView actor w v) (a b : Zkc.Protocols.CorrelatedSetup.Witness F) (p : Zkc.Protocols.CorrelatedSetup.Triple F)
    (n : Nat) (history : Zkc.Protocols.CorrelatedSetup.Service.History F) :
    Zkc.Protocols.CorrelatedSetup.Execution.source (controller x a) p n history =
      Zkc.Protocols.CorrelatedSetup.Execution.source (controller y b) p n history := by
  rw [admitted_controller actor bindings w v tree x y hx hy agree a b]

/-- S1 establishes the actual same-context premise consumed by S2's existing
    handler simulation. Backend laws remain stated assumptions, not re-proved. -/
theorem admitted_refinement {S T E G O : Type}
    (actor : Role) (bindings : List (Slot Role)) (w v : World Role F H)
    (tree : Tree) (x y : Issued F)
    (hx : admit actor bindings w tree = some x) (hy : admit actor bindings v tree = some y)
    (agree : SameView actor w v) (a b : Zkc.Protocols.CorrelatedSetup.Witness F) (p : Zkc.Protocols.CorrelatedSetup.Triple F)
    (n : Nat) (history : Zkc.Protocols.CorrelatedSetup.Service.History F)
    (R : S → T → Prop) (observeL : E → List O) (observeR : G → List O)
    (h : Handler (Zkc.Protocols.CorrelatedSetup.Execution.sig F) S E) (g : Handler (Zkc.Protocols.CorrelatedSetup.Execution.sig F) T G)
    (law : HandlerRelated R observeL observeR h g) (s : S) (t : T) (related : R s t) :
    Related R observeL observeR
      ((Zkc.Protocols.CorrelatedSetup.Execution.source (controller x a) p n history).run h s)
      ((Zkc.Protocols.CorrelatedSetup.Execution.source (controller y b) p n history).run g t) := by
  rw [client_same_view actor bindings w v tree x y hx hy agree a b p n history]
  exact run_related R observeL observeR h g law _ s t related

end Tests.SourceComposition

namespace Tests.SourceComposition.Controls
open PIR
open Zkc.Protocols.CapturedPrograms PIR.SourceView Zkc.Protocols.CapturedPrograms.Inputs
open Zkc.Source.Availability

def literal : Literal := ⟨Zkc.Protocols.CorrelatedSetup.Source.specialized 1,
  .commit (.var (.inl 0)) (.var (.inl 1)) (.var (.inl 2)) (.var (.inl 3))⟩
def tree : Tree := .leaf literal [.var 0,.var 1,.var 2,.var 3,.var 4]
def bindings : List (Slot Bool) := [.shared 0,.shared 1,.shared 2,.shared 3,.shared 4]
def world (hidden : Nat) : World Bool Int Nat :=
  ⟨fun _ => some 0,fun _ _ => some 7,hidden⟩

theorem present_zero_admitted :
    admit true bindings (world 11) tree = some ⟨literal,[0,0,0,0,0]⟩ := by decide +kernel

theorem missing_input_refused :
    admit true bindings {world 11 with publicInputs := fun _ => none} tree = none := by decide +kernel

theorem foreign_input_refused :
    admit true [.owned false 0,.shared 1,.shared 2,.shared 3,.shared 4]
      (world 11) tree = none := by decide +kernel

theorem own_input_admitted :
    admit true [.owned true 0,.shared 1,.shared 2,.shared 3,.shared 4]
      (world 11) tree = some ⟨literal,[7,0,0,0,0]⟩ := by decide +kernel

theorem forbidden_guard_refused :
    admit true (bindings ++ [.owned false 0]) (world 11)
      (.ifz (.var 5) tree tree) = none := by decide +kernel

theorem dormant_capture_refused :
    admit true (bindings ++ [.owned false 0]) (world 11)
      (.ifz (.lit 0) tree (.leaf literal [.var 5,.lit 0,.lit 0,.lit 0,.lit 0])) = none := by
  decide +kernel

theorem hidden_state_does_not_select_code (h k : Nat) :
    admit true bindings (world h) tree = admit true bindings (world k) tree :=
  admission_same_view true bindings _ _ tree ⟨rfl,rfl⟩

def setup : Zkc.Protocols.CorrelatedSetup.Setup Int := ⟨3,5,1,6,2⟩
def witness : Zkc.Protocols.CorrelatedSetup.Witness Int := ⟨1,1,by decide⟩
def publication : Zkc.Protocols.CorrelatedSetup.Triple Int := (6,4,5)
def req : Zkc.Protocols.CorrelatedSetup.Service.Request Int := ⟨2,3,true⟩
def controller : Zkc.Protocols.CorrelatedSetup.Service.Controller Int := fun _ _ => some req

def exhaustedRun :=
  (Zkc.Protocols.CorrelatedSetup.Execution.source controller publication 2 Zkc.Protocols.CorrelatedSetup.Service.empty).run
    (Zkc.Protocols.CorrelatedSetup.Execution.handler setup witness publication) (Zkc.Protocols.CorrelatedSetup.Service.empty,[9])

/-- One partial response is retained when the second request exhausts. -/
theorem exhaustion_retains_response :
    exhaustedRun.outcome = .stopped .exhausted ∧
    exhaustedRun.state.2 = [] ∧
    exhaustedRun.events.length = 1 ∧
    exhaustedRun.state.1.events = exhaustedRun.events ∧
    exhaustedRun.state.1.halted = false := by decide +kernel

theorem stopped_client_preserves_tape :
    (Zkc.Protocols.CorrelatedSetup.Execution.source (fun _ _ => none) publication 2 Zkc.Protocols.CorrelatedSetup.Service.empty).run
      (Zkc.Protocols.CorrelatedSetup.Execution.handler setup witness publication) (Zkc.Protocols.CorrelatedSetup.Service.empty,[9,10]) =
      ⟨.returned ⟨[.stopped],true⟩,(⟨[.stopped],true⟩,[9,10]),[.stopped]⟩ := rfl

theorem partial_delivery_has_no_v_or_tag :
    ∃ u, exhaustedRun.events = [.response req u none none] := by
  exact ⟨_,rfl⟩

theorem challenge_before_message_forbidden :
    ¬(Zkc.Protocols.AlgebraicRounds.EarlySource.interaction Zkc.Protocols.AlgebraicRounds.Scalar.value (F := Int)).enabled
      (Zkc.Protocols.AlgebraicRounds.EarlySource.start 1 1) .challenge := fun h => h

end Tests.SourceComposition.Controls

/-! These independently authored regions exercise syntax-level composition.
A fixed five-iteration loop carries a residual natural: zero is inactive and
produces no more requests. The continuation uses both the returned residual
and original inputs, across the first region's operation and loop binders.
This is a bounded recurrence client, not a recurrence-security theorem.
-/

namespace Tests.SourceComposition.Regions

open PIR Zkc.Source

inductive Ty where
  | natural | boolean

inductive Op where
  | begin | positive | decrement | add | finish

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .add | .finish => [.natural, .natural]
    | _ => [.natural]
  result
    | .positive => .boolean
    | _ => .natural
  condition := .boolean

abbrev Value : Ty → Type
  | .natural => Nat
  | .boolean => Bool

inductive Request where
  | begin (seed : Nat)
  | decrement (remaining : Nat)
  | finish (value offset : Nat)
  deriving DecidableEq, Repr

abbrev interface : Signature := ⟨Request, fun _ => Nat⟩

def provider : Request → Nat
  | .begin seed => seed
  | .decrement remaining => remaining - 1
  | .finish value offset => value + offset

abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation
    | .begin, .cons seed .nil => .call (.begin seed) .done
    | .positive, .cons remaining .nil => .done (remaining != 0)
    | .decrement, .cons remaining .nil => .call (.decrement remaining) .done
    | .add, .cons left (.cons right .nil) => .done (left + right)
    | .finish, .cons value (.cons offset .nil) => .call (.finish value offset) .done

/-- Inputs are permission, initial residual, and the continuation's offset. -/
abbrev context : List Ty := [.boolean, .natural, .natural]

def environment (enabled : Bool) (seed offset : Nat) : Environment Value context :=
  (Values.cons enabled (.cons seed (.cons offset .nil))).get

/-- The extra loop iterations only test the inactive accumulator. -/
def recurrence : Program language context .natural :=
  .branch .here
    (.letOp .begin (.cons (.there .here) .nil)
      (.iterate 5 .here
        (.letOp .positive (.cons .here .nil)
          (.branch .here
            (.letOp .decrement (.cons (.there .here) .nil) (.ret .here))
            (.ret (.there .here))))
        (.ret .here)))
    (.stop .reject)

/-- Original seed and offset remain captures, distinct from all new temporaries. -/
def finish : Program language (.natural :: context) .natural :=
  .letOp .add (.cons .here (.cons (.there (.there .here)) .nil))
    (.letOp .finish
      (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))
      (.ret .here))

def composed : Program language context .natural := recurrence.seq finish

/-- Even a failing request first updates state and emits its attempted operation. -/
def handler (failAt : Option Nat) : Handler interface Nat Request := fun request state =>
  ⟨if failAt = some state then .stopped .abort else .returned (provider request),
    state + 1, [request]⟩

def execute (enabled : Bool) (seed offset : Nat) (failAt : Option Nat := none) :=
  (composed.denote meaning (environment enabled seed offset)).run (handler failAt) 0

/-- Only two decrement requests occur in the fixed five-iteration source. -/
example : execute true 2 10 =
    ⟨.returned 12, 4, [.begin 2, .decrement 2, .decrement 1, .finish 2 10]⟩ := rfl

example : execute true 0 10 = ⟨.returned 10, 2, [.begin 0, .finish 0 10]⟩ := rfl

/-- A larger residual remains nonzero when the public iteration budget runs out. -/
example : execute true 7 10 =
    ⟨.returned 19, 7, [.begin 7, .decrement 7, .decrement 6, .decrement 5,
      .decrement 4, .decrement 3, .finish 9 10]⟩ := rfl

example : execute false 2 10 = ⟨.stopped .reject, 0, []⟩ := rfl

/-- A failing loop operation retains its write and prevents the second region. -/
example : execute true 2 10 (some 1) =
    ⟨.stopped .abort, 2, [.begin 2, .decrement 2]⟩ := rfl

/-- Failure in the second region also retains the first region's entire prefix. -/
example : execute true 2 10 (some 3) =
    ⟨.stopped .abort, 4, [.begin 2, .decrement 2, .decrement 1, .finish 2 10]⟩ := rfl

/-- Substitution can alias the return with an original capture of the same type. -/
example :
    (((Program.ret (.there .here) : Program language context .natural).seq finish).denote
      meaning (environment true 2 10)).run (handler none) 0 =
      ⟨.returned 14, 1, [.finish 4 10]⟩ := rfl

/-- A syntactic stop after the composed result still preserves all earlier effects. -/
example : ((composed.seq (.stop .refused : Program language (.natural :: context) .natural)).denote
    meaning (environment true 2 10)).run (handler none) 0 =
      ⟨.stopped .refused, 4, [.begin 2, .decrement 2, .decrement 1, .finish 2 10]⟩ := rfl

open Zkc.Modules.ImmutableCache Zkc.Transformations.Memoization

/-- Two equal pure requests surround an explicit event. The result determines
which remaining source loop iterations become active. -/
def preparedRequest (request : Request) : Client Request Nat Request Nat :=
  .call request fun first => .emit request
    (.call request fun second => .done (if first = second then second else 100))

def prepared : Proc (Preparation.signature Request Nat (Preparation.Emission.signature Request)) Nat :=
  (composed.denote meaning (environment true 2 10)).interpret
    (fun request => (preparedRequest request).toProc)

def cached : Execution (Cache Request Nat) Request Nat :=
  prepared.run (memoHandler provider (fun _ _ => true)) empty

example : prepared.run (directHandler provider) () =
    ⟨.returned 12, (), [.begin 2, .decrement 2, .decrement 1, .finish 2 10]⟩ := rfl

example : cached.outcome = .returned 12 ∧
    cached.events = [.begin 2, .decrement 2, .decrement 1, .finish 2 10] ∧
    cached.state (.decrement 2) = some 1 ∧ cached.state (.finish 2 10) = some 12 :=
  ⟨rfl, rfl, rfl, rfl⟩

def stale : Cache Request Nat := insert empty (.decrement 2) 0

example : ¬Valid provider stale := by
  intro valid
  have wrong : (0 : Nat) = 1 := valid (.decrement 2) 0 rfl
  contradiction

/-- An invalid cache changes active iterations even though the final value agrees. -/
example :
    let bad := prepared.run (memoHandler provider (fun _ _ => true)) stale
    bad.outcome = cached.outcome ∧ bad.events = [.begin 2, .decrement 2, .finish 2 10] ∧
      bad.events ≠ cached.events := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The common process may stop after an embedded client, retaining cache and events. -/
example :
    let stopped := ((preparedRequest (.begin 2)).toProc.bind
      (fun _ => .halt .refused :
        Nat → Proc (Preparation.signature Request Nat (Preparation.Emission.signature Request)) Nat)).run
        (memoHandler provider (fun _ _ => true)) empty
    stopped.outcome = .stopped .refused ∧ stopped.state (.begin 2) = some 2 ∧
      stopped.events = [.begin 2] := ⟨rfl, rfl, rfl⟩

end Tests.SourceComposition.Regions
