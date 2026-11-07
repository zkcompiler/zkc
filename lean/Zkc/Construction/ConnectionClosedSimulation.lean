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

/-- Compose a complete closed computation, including its stopping outcome.
The continuation sees the mathematical result, while the target receives its
derived frame. Only frames the closed computation can return need a suffix law. -/
noncomputable def Simulation.continueClosed {D : Type}
    (process : Structured.Closed A) (encode : A → B)
    {target : PIR.Process (Domain.effects carriers) B}
    {live : PIR.Process (Domain.effects carriers) B → Domain.Environment carriers → Prop}
    {nextLive : PIR.Process (Domain.effects carriers) C → Domain.Environment carriers → Prop}
    {returns : C → D → Prop}
    {sourceNext : A → PIR.Process (Domain.effects carriers) C}
    {targetNext : B → PIR.Process (Domain.effects carriers) D}
    (head : Simulation Eq live
      ((process.interpret (Structured.closedLift (I := Domain.effects carriers))).bind
        fun value ↦ .done (encode value)) target)
    (frames : ∀ first next frame, live first frame → nextLive next frame)
    (tail : ∀ value, Simulation returns nextLive (sourceNext value) (targetNext (encode value))) :
    Simulation returns nextLive
      ((process.interpret (Structured.closedLift (I := Domain.effects carriers))).bind sourceNext)
      (target.bind targetNext) := by
  cases process with
  | done value => exact head.continueDone (fun frame held ↦ frames _ _ frame held) (tail value)
  | halt reason => exact head.continueHalt _ (fun frame held ↦ frames _ _ frame held)
  | call operation _ => exact nomatch operation

end Original
end Zkc.Construction
