import Examples.TableProtocol.Admission
import Examples.TableProtocol.Invocation

/-! Stateful application of the table interaction. The local actor owns writes,
sends and challenge-receive requests; this is not multi-party projection or a
claim that the actor chooses challenge values. Entry state is host-supplied. -/
set_option autoImplicit false
namespace TableProtocol.Endpoint
open Lean Zkc.Source Zkc.Compiler PhaseAdmission Protocol

abbrev Phase := Admission.Phase
def profile : String := "table-endpoint/1"
def role : String := "prover"
def primitiveOwner (_ : Call) : String := role
structure Entry where
  actor : String
  phase : Phase
  deriving DecidableEq, Repr
structure State where
  entry : Entry
  data : Protocol.State

def entryJson (entry : Entry) : Json := .arr #[.str entry.actor, Admission.phases.encode entry.phase]
def decodeEntry (json : Json) : Except String Entry := do
  match ← json.getArr?.mapError (fun _ => "invalid-endpoint-entry") with
  | #[actor, phase] => return ⟨← actor.getStr?.mapError (fun _ => "invalid-entry-role"),
      ← Admission.phases.decode phase |>.mapError (fun _ => "invalid-endpoint-phase")⟩
  | _ => throw "invalid-endpoint-entry"
def decodeState (json : Json) : Except String State := do
  match ← json.getArr?.mapError (fun _ => "invalid-endpoint-state") with
  | #[actor, phase, data] => return ⟨← decodeEntry (.arr #[actor, phase]), ← TableProtocol.decodeState data⟩
  | _ => throw "invalid-endpoint-state"
def stateJson (state : State) : Json := .arr #[.str state.entry.actor,
  Admission.phases.encode state.entry.phase, TableProtocol.stateJson state.data]
def validateEntry (expected : Entry) (state : State) : Except String Unit := do
  if state.entry.actor != role then throw "endpoint-role-mismatch"
  if state.entry != expected then throw "endpoint-entry-mismatch"

def run {A : Type} (body : PIR.Proc protocolInterface A) (state : State) :
    PIR.Execution State Trace A :=
  let out := body.run (PIR.ExecutionPath.handler Admission.interaction Protocol.handler)
    (state.entry.phase, state.data)
  ⟨out.outcome, ⟨⟨state.entry.actor, out.state.1⟩, out.state.2⟩,
    out.events.filterMap (fun | .inl _ => none | .inr event => some event)⟩

/-- Entry equality provides the actual initial phase, not a fresh ready trace. -/
theorem entry_coverage (expected : Entry) (state : State) (same : state.entry = expected) :
    Covered Admission.summaryLaws [expected.phase] state.entry.phase := by
  exact ⟨expected.phase, by simp, by rw [same]; rfl⟩

theorem validated_entry (expected : Entry) (state : State)
    (accepted : validateEntry expected state = .ok ()) :
    state.entry.actor = role ∧ state.entry = expected := by
  by_cases actor : state.entry.actor = role
  · by_cases same : state.entry = expected
    · exact ⟨actor, same⟩
    · simp [validateEntry, actor, same] at accepted
  · simp [validateEntry, actor, Bind.bind, Except.bind] at accepted

theorem actual_primitive_owner (state : State) (actor : state.entry.actor = role) (call : Call) :
    primitiveOwner call = state.entry.actor := actor.symm

/-- Erasing the phase wrapper preserves stopped outcomes and original effects. -/
theorem erasure {A : Type} (body : PIR.Proc protocolInterface A) (state : State) :
    (⟨(run body state).outcome, (run body state).state.data, (run body state).events⟩ :
      PIR.Execution Protocol.State Trace A) = body.run Protocol.handler state.data := by
  refine Eq.trans ?_ (PIR.ExecutionPath.erasure Admission.interaction Protocol.handler
    body state.entry.phase state.data)
  dsimp only [run]
  congr 2
  funext event
  cases event <;> rfl

/-- Re-entry checks cannot interpret a retained sent endpoint as ready. -/
example (data : Protocol.State) :
    validateEntry ⟨role, .ready⟩ ⟨⟨role, .sent⟩, data⟩ = .error "endpoint-entry-mismatch" := by
  rfl

example (data : Protocol.State) :
    (run (.call .draw .done) ⟨⟨role, .sent⟩, {data with tape := []}⟩).state.entry.phase = .sent := rfl

end TableProtocol.Endpoint
