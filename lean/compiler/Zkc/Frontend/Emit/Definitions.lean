module

public import Zkc.Frontend.Emit.NamedProtocol
public import Zkc.Frontend.Emit.Dependencies

@[expose] public section
set_option autoImplicit false
namespace Zkc.Frontend.Emit

open Zkc.Vocabulary.Project
open Static
open Typing (EmitM EmitFailure)

/-- Register the project rows reached by these concrete calls, before emitting any
term indexed by the resulting vocabulary. -/
def bindCalls (start : Bindings) (calls : Array InstanceId) : EmitM Bindings := do
  let results := (← read).results
  calls.foldlM (init := start) fun b id => do
    let some (.row row) := results.body? id | return b
    let some entry := results.rows[row]? | Typing.defect s!"missing primitive row {row}"
    Typing.linkRow b entry

def bodyContext (b : Bindings) : EmitM (Named.Context b) := do
  let results := (← read).results
  let stops (inst : InstanceId) : Bool := match results.body? inst with
    | some (.done code) => code.canStop
    | _ => false
  let restricted (inst : InstanceId) : Bool := match results.body? inst with
    | some (.row id) => (results.rows[id]?).any fun row => (row.kind matches .restricted _)
    | _ => false
  let apply (inst : InstanceId) (inputs : Array ClosedType) (result : ClosedType) : EmitM (Core.LocalRaw b.vocabulary) := do
    match results.body? inst with
    | some (.row id) =>
      let some row := results.rows[id]? | Typing.defect s!"missing primitive row {id}"
      unless sameRowSignature row {row with inputs, outputs := #[result]} do
        Typing.defect s!"callee {inst} disagrees with its registered primitive"
      return .row (← Typing.rowKey b row)
    | some (.done _) => return .call ⟨inst⟩
    | some (.waiting reason) => throw (.waiting reason)
    | _ => throw (.waiting s!"function {inst} has no checked body")
  return {callees := {stops, restricted}, apply}

def functionHeader (b : Bindings) (inst : InstanceId) (code : Typing.FunctionCode) : EmitM (Core.FnHeader b.vocabulary) := do
  return ⟨⟨inst⟩, ← code.inputs.toList.mapM (Typing.toTy ·), ← code.outputs.toList.mapM (Typing.toTy ·),
    code.canStop, none, ⟨[],[]⟩⟩

/-- Open checking uses the declared headers of the concrete callees. Primitive calls
resolve in the linked vocabulary and have no function-table header. -/
def calleeHeaders (b : Bindings) (calls : Array InstanceId) : EmitM (Core.Headers b.vocabulary) := do
  let results := (← read).results
  let mut fns := []
  for inst in calls do
    match results.body? inst with
    | some (.row _) => pure ()
    | some (.done code) => fns := (← functionHeader b inst code) :: fns
    | some (.waiting reason) => throw (.waiting reason)
    | _ => throw (.waiting s!"function {inst} has no checked body")
  return ⟨fns,[]⟩

end Zkc.Frontend.Emit
