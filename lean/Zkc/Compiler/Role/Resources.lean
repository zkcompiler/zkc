import Zkc.Semantics.ResourceView
import Zkc.Compiler.Role.Execution

/-! Restricted resource views for the actual typed role runtime.
Local bodies still resolve the supplied stored definitions. Primitive services,
send and completed receive see only the admitted heterogeneous cells. This
module proves confinement for that adapter, not resource-handle admission or
correspondence with a native backend or joint controller. -/
set_option autoImplicit false
namespace Zkc.Compiler.Role.Resources

open Zkc.Source Zkc.Source.Protocol
open Zkc.Semantics.ResourceView

variable {Slot : Type} {Cell : Slot → Type} {Party Entry Binding Schema : Type}
  {language : Language} {Value : language.Ty → Type} {E A : Type}
  {locals : List (DefinitionSignature language.Ty)}

/-- The stored body's meaning is unchanged; only its primitive state boundary
is lifted. Every returned or stopped primitive result installs its actual view. -/
def scopeRuntime (admitted : Slot → Prop) [DecidablePred admitted]
    (runtime : Protocol.Role.Runtime Party Entry Binding Schema language Value
      (Selected Cell admitted) E) :
    Protocol.Role.Runtime Party Entry Binding Schema language Value (Store Cell) E where
  implementations binding :=
    { effects := (runtime.implementations binding).effects
      condition := (runtime.implementations binding).condition
      operation := (runtime.implementations binding).operation
      handler := scopeHandler admitted (runtime.implementations binding).handler }
  send location schema receiver value store :=
    lift admitted store (runtime.send location schema receiver value (restrict admitted store))
  receive ty location schema sender store :=
    lift admitted store (runtime.receive ty location schema sender (restrict admitted store))

def StateFrame (admitted : Slot → Prop) (initial : Store Cell)
    (selected : Protocol.Role.State Entry Binding (Selected Cell admitted))
    (whole : Protocol.Role.State Entry Binding (Store Cell)) : Prop :=
  Frame admitted initial selected.localState whole.localState ∧
    selected.stoppedAt = whole.stoppedAt

/-- Equal full primitive outcomes determine equal local stop locations. -/
theorem located_related (admitted : Slot → Prop) (initial : Store Cell)
    (location : Protocol.Role.Location Entry Binding)
    (left : PIR.Execution (Selected Cell admitted) E A)
    (right : PIR.Execution (Store Cell) E A)
    (related : PIR.Related (Frame admitted initial) (fun e => [e]) (fun e => [e]) left right) :
    PIR.Related (StateFrame admitted initial) (fun e => [e]) (fun e => [e])
      (Protocol.Role.lift location left) (Protocol.Role.lift location right) := by
  obtain ⟨outcome, state, events⟩ := related
  have sameEvents : left.events = right.events := by simpa [PIR.observeEvents] using events
  refine ⟨outcome, ⟨state, ?_⟩, ?_⟩
  · simp only [Protocol.Role.lift, outcome]
  · simp only [Protocol.Role.lift, sameEvents]

/-- Primitive confinement composes through the actual stored local body, and
then through location tagging. No whole-program simulation premise is assumed. -/
theorem handler_related (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell)
    (runtime : Protocol.Role.Runtime Party Entry Binding Schema language Value
      (Selected Cell admitted) E)
    (definitions : Source.Definitions language locals) :
    PIR.HandlerRelated (StateFrame admitted initial) (fun e => [e]) (fun e => [e])
      (runtime.handler definitions) ((scopeRuntime admitted runtime).handler definitions) := by
  intro op selected whole related
  obtain ⟨frame, _⟩ := related
  cases op with
  | «local» location callee args =>
      apply located_related
      exact PIR.run_related _ _ _ _ _
        (Zkc.Semantics.ResourceView.handler_related admitted initial
          (runtime.implementations location.binding).handler) _ _ _ frame
  | send location schema receiver value =>
      apply located_related
      change PIR.Related (Frame admitted initial) _ _
        (runtime.send location schema receiver value selected.localState)
        (lift admitted whole.localState
          (runtime.send location schema receiver value (restrict admitted whole.localState)))
      rw [frame.1]
      refine ⟨rfl, ⟨restrict_install admitted _ _, ?_⟩, rfl⟩
      intro slot outside
      exact (install_outside admitted _ _ slot outside).trans (frame.2 slot outside)
  | receive ty location schema sender =>
      apply located_related
      change PIR.Related (Frame admitted initial) _ _
        (runtime.receive ty location schema sender selected.localState)
        (lift admitted whole.localState
          (runtime.receive ty location schema sender (restrict admitted whole.localState)))
      rw [frame.1]
      refine ⟨rfl, ⟨restrict_install admitted _ _, ?_⟩, rfl⟩
      intro slot outside
      exact (install_outside admitted _ _ slot outside).trans (frame.2 slot outside)
  | stop location reason => exact ⟨rfl, ⟨frame, rfl⟩, rfl⟩

/-- Actual source-role execution and its projected stored role run agree with
the restricted resource frame, complete outcome, local stop origin and events.
This is a scoped endpoint law; it is not the joint/open controller theorem. -/
theorem run_project_scoped [DecidableEq Party]
    (admitted : Slot → Prop) [DecidablePred admitted] (initial : Store Cell)
    (runtime : Protocol.Role.Runtime Party Entry Binding Schema language Value
      (Selected Cell admitted) E)
    (localDefinitions : Source.Definitions language locals)
    {scope : List (Signature Party language.Ty)}
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (self : Party)
    (selected : Instance Party Binding language.Ty scope signature) (entry : Entry)
    (inputs : Protocol.Role.Environment Value self signature.arguments) :
    PIR.Related (StateFrame admitted initial) (fun e => [e]) (fun e => [e])
      ((Protocol.Role.denoteDefinitions self definitions selected.callee entry selected.binding []
        inputs).run (runtime.handler localDefinitions) ⟨restrict admitted initial, none⟩)
      (Role.run (scopeRuntime admitted runtime) localDefinitions
        (projectDefinitions self definitions) selected entry inputs initial) := by
  rw [run_project_runtime]
  exact PIR.run_related _ _ _ _ _ (handler_related admitted initial runtime localDefinitions)
    _ _ _ ⟨⟨rfl, fun _ _ => rfl⟩, rfl⟩

end Zkc.Compiler.Role.Resources
