import Zkc.Source.LocatedExecution
import Zkc.Source.ControlAgreement
import Zkc.Semantics.Locality

set_option autoImplicit false

namespace Tests.LocatedCalls

open Zkc.Source
open Zkc.Source.LocatedExecution

inductive Role where
  | prover | verifier | observer
  deriving DecidableEq, Repr

abbrev State : Role → Type
  | .prover => Nat
  | .verifier => List Nat
  | .observer => Bool

abbrev Event (_ : Role) := Nat

def initial : States State
  | .prover => 0
  | .verifier => []
  | .observer => true

abbrev language : Language where
  Ty := Unit
  Op := Unit
  arguments _ := [()]
  result _ := ()
  condition := ()

abbrev interface : PIR.Signature := ⟨Nat, fun _ => Nat⟩

abbrev meaning : Interpretation language interface where
  Value _ := Nat
  condition value := value != 0
  operation
    | (), .cons value .nil => .call value .done

abbrev signature : DefinitionSignature Unit := ⟨[()], ()⟩

def body : Region (language.withDefinitions []) signature.arguments signature.result :=
  .letOp (.primitive ()) (.cons .here .nil) (.ret .here)

def definitions : Definitions language [signature] :=
  Definitions.snoc (language := language) .nil signature body

def origin (role : Role) (site : Nat) : Origin Role String Nat :=
  ⟨role, "interactive", 5, [.invocation 7, .iteration 9 2], site⟩

/-- Failed draws and duplicate-use attempts retain their actual changed state. -/
def handler (role : Role) : PIR.Handler interface (State role) (Event role) :=
  match role with
  | .prover => fun request cursor =>
      ⟨if request == 0 then .stopped .exhausted else .returned (request + cursor),
        cursor + 1, [cursor]⟩
  | .verifier => fun ticket used =>
      ⟨if ticket ∈ used then .stopped .refused else .returned ticket, ticket :: used, [ticket]⟩
  | .observer => fun request enabled => ⟨.returned request, enabled, [request]⟩

def call (role : Role) (site request : Nat) (states : States State) :=
  LocatedExecution.run (origin role site) meaning definitions .here
    (.cons request .nil) (handler role) states

/-- The same stored body runs under different roles' local service bindings. -/
def sequence :=
  (call .prover 0 3 initial).follow fun _ first =>
    (call .verifier 1 7 first.locals).follow fun _ second =>
      (call .verifier 2 7 second.locals).follow fun _ third =>
        call .prover 3 11 third.locals

def summary {A : Type}
    (result : PIR.Execution (StateWithOrigin Role String Nat State)
      (LocatedEvent Role String Nat Event) A) :=
  (result.outcome, result.state.locals .prover, result.state.locals .verifier,
    result.state.locals .observer, result.state.stoppedAt,
    result.events.map fun event => (event.origin, event.value))

example : summary sequence =
    (.stopped .refused, 1, [7, 7], true, some (origin .verifier 2),
      [(origin .prover 0, 0), (origin .verifier 1, 7), (origin .verifier 2, 7)]) := rfl

example : summary (call .prover 4 0 initial) =
    (.stopped .exhausted, 1, [], true, some (origin .prover 4), [(origin .prover 4, 0)]) := rfl

/-- A source-level stop needs an origin even when no primitive emitted an event. -/
def stoppedDefinitions : Definitions language [signature, signature] :=
  definitions.snoc signature (.stop .reject)

example : summary (LocatedExecution.run (origin .verifier 8) meaning stoppedDefinitions .here
    (.cons 1 .nil) (handler .verifier) initial) =
    (.stopped .reject, 0, [], true, some (origin .verifier 8), []) := rfl

example (peer : List Nat) (observer : Bool) :
    localView .prover (call .prover 0 3 (fun role => match role with
      | .prover => 0 | .verifier => peer | .observer => observer)) =
      localView .prover (call .prover 0 3 initial) :=
  run_local (origin .prover 0) meaning definitions .here (.cons 3 .nil)
    (handler .prover) _ initial rfl

/-- Disjoint participant state is insufficient for reordering stopped effects. -/
def stopFirst :=
  (call .prover 0 0 initial).follow fun _ state => call .verifier 1 7 state.locals

def stopLast :=
  (call .verifier 1 7 initial).follow fun _ state => call .prover 0 0 state.locals

example : stopFirst.outcome = stopLast.outcome := rfl
example : stopFirst.state.locals .verifier ≠ stopLast.state.locals .verifier := by decide
example : stopFirst.events.length = 1 ∧ stopLast.events.length = 2 := by decide

/-- Runtime paths retain loop indices and selected instances, independently of callee type. -/
example :
    ({ origin .prover 0 with path := [.invocation 7, .iteration 9 3] } :
      Origin Role String Nat) ≠ origin .prover 0 := by decide
example : ({ origin .prover 0 with instanceId := 6 } : Origin Role String Nat) ≠
    origin .prover 0 := by decide

open ControlAgreement

def participants : List Role := [.prover, .verifier, .observer]

example : check participants (fun _ => some false) = .ok false := rfl
example : check participants (fun _ => some (0 : Nat)) = .ok 0 := rfl
example : check participants (fun _ => some (4 : Nat)) = .ok 4 := rfl
example : check ([] : List Role) (fun _ => some true) = .error .noParticipants := rfl
example : check participants (fun role => if role = .verifier then none else some false) =
    .error (.unavailable .verifier) := rfl
example : check participants (fun role => if role = .verifier then some false else some true) =
    .error (.disagreement .verifier) := rfl
example : check participants (fun role => if role = .observer then some 3 else some (4 : Nat)) =
    .error (.disagreement .observer) := rfl

/-- Accepted agreement rewrites an actual local Region, including its stopped branch. -/
example (input : Nat) (yes no : Region language [()] ())
    (values : Role → Option Bool) (choice : Bool)
    (accepted : check participants values = .ok choice)
    (binding : values .verifier = some (input != 0)) :
    (Region.branch .here yes no).denote meaning (Values.cons input .nil).get =
      if choice then yes.denote meaning (Values.cons input .nil).get
        else no.denote meaning (Values.cons input .nil).get :=
  branch_denote meaning .here yes no
    (Values.cons (Value := meaning.Value) (ty := ()) input .nil).get participants values choice
    accepted .verifier (by decide) binding

/-- Admission classifies the actual interpreted body, including its stored callee. -/
example (request : Nat) : LocallyAdmitted (fun _ => some Role.prover) .prover
    (definitions.operation meaning (.call .here) (.cons request .nil)) := by
  exact ⟨rfl, fun _ => True.intro⟩

example : ¬ LocallyAdmitted (fun _ => some Role.verifier) .prover
    (definitions.operation meaning (.call .here) (.cons 3 .nil)) := by
  intro admitted
  have impossible : some Role.verifier = some Role.prover := admitted.1
  cases impossible

example : ¬ LocallyAdmitted (fun _ => (none : Option Role)) .prover
    (definitions.operation meaning (.call .here) (.cons 3 .nil)) := by
  intro admitted
  have impossible : (none : Option Role) = some Role.prover := admitted.1
  cases impossible

/-- Matching local Bool types do not make a privately chosen global branch implementable. -/
example : ¬ ∃ choose : Unit → Bool, ∀ hidden : Bool, choose () = hidden := by
  exact Zkc.Semantics.Locality.no_local_adapter (fun _ : Bool => ()) id
    false true rfl (by decide)

end Tests.LocatedCalls
