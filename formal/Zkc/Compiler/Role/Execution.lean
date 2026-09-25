import Zkc.Compiler.Role.Projection
import Zkc.Compiler.Role.Runner

/-! Entry execution of actual role tables and source-role correspondence.
The role entry receives one local state and focused inputs. Neither execution
path receives a joint environment or an honest sender's packet.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Role

open Zkc.Source Zkc.Source.Protocol
open Zkc.Source.Protocol.Role (Environment Runtime State Event Ingress interface)

variable {Party Entry Binding Schema : Type} {self : Party} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {scope : List (Signature Party language.Ty)}
  {Value : language.Ty → Type} {S E : Type}

def start (definitions : Definitions Nat self Binding Schema language locals scope)
    {signature : Signature Party language.Ty}
    (selected : Instance Party Binding language.Ty scope signature) (entry : Entry)
    (inputs : Environment Value self signature.arguments) (state : S) :
    Cursor (Protocol.Role.interface Party Entry Binding Schema language locals Value)
      (State Entry Binding S) (Event Entry Binding E) (Environment Value self signature.results) :=
  ⟨definitions.denote selected.callee entry selected.binding [] inputs, ⟨state, none⟩, []⟩

def run (runtime : Runtime Party Entry Binding Schema language Value S E)
    (localDefinitions : Source.Definitions language locals)
    (definitions : Definitions Nat self Binding Schema language locals scope)
    {signature : Signature Party language.Ty}
    (selected : Instance Party Binding language.Ty scope signature) (entry : Entry)
    (inputs : Environment Value self signature.arguments) (state : S) :=
  ((start (E := E) definitions selected entry inputs state).program).run
    (runtime.handler localDefinitions) ⟨state, none⟩

def drive (runtime : Runtime Party Entry Binding Schema language Value S E)
    (localDefinitions : Source.Definitions language locals)
    (definitions : Definitions Nat self Binding Schema language locals scope)
    {signature : Signature Party language.Ty}
    (selected : Instance Party Binding language.Ty scope signature) (entry : Entry)
    (inputs : Environment Value self signature.arguments) (state : S)
    (ingress : Ingress Party Entry Binding Schema language Value S E) (fuel : Nat) :=
  advance (runtime.poll localDefinitions ingress) fuel (start definitions selected entry inputs state)

/-- The same arbitrary polling policy sees equal source-role and projected cursors,
including suspension, budget yield and every retained continuation.
-/
theorem advance_project [DecidableEq Party]
    (poll : Poll (Protocol.Role.interface Party Entry Binding Schema language locals Value) S E)
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List LocatedExecution.Frame)
    (inputs : Environment Value self signature.arguments) (state : S) (events : List E)
    (fuel : Nat) :
    advance poll fuel
      ⟨(projectDefinitions self definitions).denote ref entry binding path inputs, state, events⟩ =
    advance poll fuel
      ⟨Protocol.Role.denoteDefinitions self definitions ref entry binding path inputs, state, events⟩ := by
  rw [denote_projectDefinitions]

/-- Actual local and protocol tables, arbitrary binding-selected primitive implementations,
and arbitrary completed ingress retain the whole direct source-role execution. -/
theorem run_project_runtime [DecidableEq Party]
    (runtime : Runtime Party Entry Binding Schema language Value S E)
    (localDefinitions : Source.Definitions language locals)
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty}
    (selected : Instance Party Binding language.Ty scope signature) (entry : Entry)
    (inputs : Environment Value self signature.arguments) (state : S) :
    run runtime localDefinitions (projectDefinitions self definitions) selected entry inputs state =
      (Protocol.Role.denoteDefinitions self definitions selected.callee entry selected.binding [] inputs
        ).run (runtime.handler localDefinitions) ⟨state, none⟩ := by
  unfold run start
  rw [denote_projectDefinitions]

/-- Finite denotation is recovered when ingress is complete and the call budget suffices. -/
theorem drive_complete
    (runtime : Runtime Party Entry Binding Schema language Value S E)
    (localDefinitions : Source.Definitions language locals)
    (definitions : Definitions Nat self Binding Schema language locals scope)
    {signature : Signature Party language.Ty}
    (selected : Instance Party Binding language.Ty scope signature) (entry : Entry)
    (inputs : Environment Value self signature.arguments) (state : S) (fuel : Nat)
    (bounded : PIR.Within fuel
      (definitions.denote selected.callee entry selected.binding [] inputs)) :
    drive runtime localDefinitions definitions selected entry inputs state
      (fun ty location schema sender state => some (runtime.receive ty location schema sender state))
      fuel = .finished (run runtime localDefinitions definitions selected entry inputs state) := by
  unfold drive run start
  have same : runtime.poll localDefinitions
      (fun ty location schema sender state => some (runtime.receive ty location schema sender state)) =
      (fun op state => some (runtime.handler localDefinitions op state)) := by
    funext op state
    exact runtime.poll_complete localDefinitions op state
  rw [same, advance_complete _ _ _ bounded]
  rfl

end Zkc.Compiler.Role
