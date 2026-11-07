module

public import Zkc.Construction.OriginalSimulation
public import Zkc.Construction.ConnectionTargetPrefix
public import Zkc.Construction.DomainCorrespondence

@[expose] public section

/-! Composition at a known closed return or stop. The structural target may
have checkpoints; their obligations survive composition. These rules avoid
asking a caller to justify continuations at values the prefix cannot return. -/
set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source

namespace ConnectionTargetPrefix

theorem correspondence_append (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) {first rest : List Instruction} {firstSpine suffix : Prefix}
    (head : Domain.Correspondence.Block (model := model) (program := program) (context := context)
      first (firstSpine.block model))
    (tail : Domain.Correspondence.Block (model := model) (program := program) (context := context)
      rest (suffix.block model)) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (first ++ rest) ((firstSpine.append suffix).block model) := by
  intro environment
  rw [Domain.evaluate_append, head]
  rw [funext tail]
  change _ = (firstSpine.append suffix).plug (fun _ ↦ Domain.View.empty) model environment
  rw [Prefix.append_plug, Prefix.plug_eq_bind]
  rfl

end ConnectionTargetPrefix

namespace Original
variable {carriers : Structured.Carriers} {A B C : Type}

noncomputable def Simulation.continueDone
    {value : A} {target : PIR.Process (Domain.effects carriers) A}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {nextLive : PIR.Process (Domain.effects carriers) B → Domain.Environment carriers → Prop}
    {returns : B → C → Prop} {sourceNext : PIR.Process (Domain.effects carriers) B}
    {targetNext : A → PIR.Process (Domain.effects carriers) C}
    (head : Simulation Eq live (.done value) target)
    (frames : ∀ frame, live (.done value) frame → nextLive sourceNext frame)
    (tail : Simulation returns nextLive sourceNext (targetNext value)) :
    Simulation returns nextLive sourceNext (target.bind targetNext) := by
  generalize sourceEq : PIR.Process.done value = source at head
  induction head with
  | done related => cases sourceEq; cases related; exact tail
  | halt reason => cases sourceEq
  | call operation next ih => cases sourceEq
  | checkpoint frame retained next ih =>
      cases sourceEq
      exact .checkpoint frame (frames frame retained) (ih rfl)

noncomputable def Simulation.continueHalt
    {reason : PIR.Stop} {target : PIR.Process (Domain.effects carriers) A}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {nextLive : PIR.Process (Domain.effects carriers) B → Domain.Environment carriers → Prop}
    {returns : B → C → Prop} (targetNext : A → PIR.Process (Domain.effects carriers) C)
    (head : Simulation Eq live (.halt reason) target)
    (frames : ∀ frame, live (.halt reason) frame → nextLive (.halt reason) frame) :
    Simulation returns nextLive (.halt reason) (target.bind targetNext) := by
  generalize sourceEq :
    (PIR.Process.halt reason : PIR.Process (Domain.effects carriers) A) = source at head
  induction head with
  | done related => cases sourceEq
  | halt reason => cases sourceEq; exact .halt reason
  | call operation next ih => cases sourceEq
  | checkpoint frame retained next ih =>
      cases sourceEq
      exact .checkpoint frame (frames frame retained) (ih rfl)

end Original
end Zkc.Construction
