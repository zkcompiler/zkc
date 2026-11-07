module

public import Zkc.Realization.QueryPhaseYield

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryPhaseYield
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization.QueryPhaseYield

def state {carriers : Carriers} (phase : Nat) : Domain.Environment carriers :=
  [0, 1, 2, 3, 4, 5, phase].map (fun value ↦ .data (.index value))

/-- Both controller thresholds use the same certificate. The flag, seventh
state field and complete output layout are connected at any caller suffix. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (phase threshold : Nat) (phaseBound : phase < indexLimit) (thresholdBound : threshold < indexLimit)
    (suffix : Domain.Environment model.toCarriers) :
    let environment := state phase ++ suffix
    Nonempty (Original.Simulation
      (ConnectionLocalRange.Yield (fun value carried ↦ carried = state value) true
        (List.replicate 7 (.data .index)) ((environment.length + 1) :: List.range 7))
      (fun (_ : PIR.Process (Domain.effects model.toCarriers) (Bool × Nat)) live ↦ environment <+: live)
      (.done (decide (phase < threshold), phase))
      (Domain.evaluate model program context
        (instructions environment.length 6 threshold) environment)) := by
  dsimp only
  let environment := state (carriers := model.toCarriers) phase ++ suffix
  let checked : Recognized (instructions environment.length 6 threshold)
      ((environment.length + 1) :: List.range 7) :=
    ⟨environment.length, 6, threshold, List.range 7, rfl, rfl, rfl⟩
  exact checked.yieldSimulation model program context environment environment (state phase)
    (List.prefix_refl _) rfl phase phaseBound thresholdBound rfl rfl
    (List.replicate 7 (.data .index)) rfl (fun value carried ↦ carried = state value) phase rfl

example : (recognize 7 (instructions 7 6 2) [8, 0, 1, 2, 3, 4, 5, 6]).isSome = true := by
  decide +kernel

-- Reading the kind field instead of the phase remains type-correct, but does
-- not establish the continuation condition for the returned controller state.
example : (recognize 7 (instructions 7 5 2) [8, 0, 1, 2, 3, 4, 5, 6]).isNone = true := by
  decide +kernel

example : (recognize 7 (instructions 7 6 2) [7, 0, 1, 2, 3, 4, 5, 6]).isNone = true := by
  decide +kernel

example : (recognize 7
    [⟨.execute (.indexConstant 2), [], [.data .index], []⟩,
     ⟨.execute .indexLess, [7, 6], [.data .boolean], []⟩]
    [8, 0, 1, 2, 3, 4, 5, 6]).isNone = true := by decide +kernel

#print axioms actual
#print axioms Recognized.yieldSimulation
end Tests.QueryPhaseYield
