module

public import Zkc.Construction.OriginalProjection
public import Zkc.Construction.DomainRuntimeProjection

@[expose] public section

/-! Execution of the actual original construction and its certified paired
view. The named runtime interaction projection removes only physical SSA
frames; proof buffers, service/oracle state, full source returns and ordered
stopped prefixes remain exact. Complete constructed frames remain in the paired
execution and carry the simulation's independent live-value obligations. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A B : Type}

/-- The paired source view runs the original interaction, for every lawful
monad and every public/private provider, even when an operation stops. -/
theorem Simulation.source_run_interaction
    {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live source target)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (mode : Domain.Mode) (oracle : Domain.Oracle m carriers S)
    (services : Domain.LocalServices m carriers S) (state : Domain.RuntimeState carriers S) :
    source.runM (Domain.interactionHandler mode oracle services) state.interaction =
      (do let execution ← Domain.run mode oracle derivation.paired state services
          PIR.Execution.expand (fun (final : Domain.RuntimeState carriers S) => pure final.interaction) (mapExecution Prod.fst execution)) := by
  have erased := congrArg (fun process =>
    process.runM (Domain.interactionHandler mode oracle services) state.interaction) derivation.source
  rw [Domain.interaction_forgetCheckpoints, Domain.interaction_forgetCheckpoints] at erased
  calc
    _ = (derivation.paired.bind (fun pair => .done pair.1)).runM
        (Domain.interactionHandler mode oracle services) state.interaction := erased.symm
    _ = _ := by
      rw [Domain.run_interaction]
      simp only [Domain.run, runM_map, bind_assoc, pure_bind]

/-- This version runs both processes in the existing full runtime handler.
The explicitly named projection relates their interaction state; the paired
execution simultaneously retains every actual constructed physical frame. -/
theorem Simulation.source_run
    {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live source target)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (mode : Domain.Mode) (oracle : Domain.Oracle m carriers S)
    (services : Domain.LocalServices m carriers S) (state : Domain.RuntimeState carriers S) :
    (do let execution ← Domain.run mode oracle source state services
        PIR.Execution.expand (fun (final : Domain.RuntimeState carriers S) => pure final.interaction) execution) =
      (do let execution ← Domain.run mode oracle derivation.paired state services
          PIR.Execution.expand (fun (final : Domain.RuntimeState carriers S) => pure final.interaction) (mapExecution Prod.fst execution)) :=
  (Domain.run_interaction mode oracle services source state).symm.trans
    (derivation.source_run_interaction mode oracle services state)

end Zkc.Construction.Original
