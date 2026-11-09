module

public import Zkc.Tests.Protocol.Construction.Choices.Companions
public meta import Zkc.Tools.Program.Companions.Report

/-! The expected type is fixed before each selection. Registration is discovery only;
Lean checks the actual scale, interpretation, source body, event and request bound.
-/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source ProtocolProof Std.WP
open ProtocolProofExamples.AdaptiveChecks ProtocolProofExamples.AdaptiveSource

namespace ProtocolProofExamples.ConstructionChoices

attribute [local instance] upperLogic

def chosen (e : AdaptiveChecks.Environment) : Scale := zkc_companion ["adaptive.scale"[e]]

theorem chosen_law (e : AdaptiveChecks.Environment) : ScaleLaw e (chosen e) :=
  zkc_companion ["adaptive.scale-law"[e]]

theorem chosen_budget (e : AdaptiveChecks.Environment) (count : Nat) : Budget e count (chosen e) :=
  zkc_companion ["adaptive.budget"[e, count]]

theorem installed (e : AdaptiveChecks.Environment) (count : Nat)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (potential (factor e.residual ^ count * value) (env .here))⦄
      (AdaptiveSource.rounds count).denote (meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ :=
  fixed_rounds e count (chosen e) (chosen_law e) (chosen_budget e count) env value

-- Nonempty initialization prevents the zero invariant from proving the requested bound.
example (e : AdaptiveChecks.Environment) : ¬ ScaleLaw e (fun _ => 0) := by
  intro law
  have impossible : (0 : ENNReal) = 1 := law.1
  exact zero_ne_one impossible

-- A changed residual changes the mathematical law; a same-typed old scale is not evidence.
example : ¬ ScaleLaw ⟨true, fun _ => false⟩ (scale ⟨false, fun _ => false⟩) := by
  intro law
  have impossible := law.2 0
  norm_num [scale, AdaptiveChecks.factor, AdaptiveChecks.half] at impossible
  have halves := ENNReal.inv_two_add_inv_two
  rw [← impossible] at halves
  norm_num at halves

open Lean Elab Command Term Meta in
run_elab do
  let target ← elabTerm (← `(term| Scale)) none
  let absent ← ZkcTools.Companions.resolve #[⟨"adaptive.missing-scale", #[]⟩] target
  unless (match absent with | .missing => true | _ => false) do
    throwError "missing mathematical choice was not reported"
  let invalid ← ZkcTools.Companions.resolve
    #[⟨"adaptive.invalid-scale", #[]⟩, ⟨"adaptive.scale", #[← `(term| ⟨true, fun _ => false⟩)]⟩]
    target
  unless (match invalid with | .refused _ _ => true | _ => false) do
    throwError "ill-typed explicit choice fell back to a valid registration"
  let expected ← elabTerm (← `(term| ScaleLaw ⟨true, fun _ => false⟩ (scale ⟨true, fun _ => false⟩))) none
  let invalidLaw ← ZkcTools.Companions.assemble #[⟨"adaptive.invalid-law", #[]⟩] expected
    #[⟨"valid-default", ← `(term| scaleLaw ⟨true, fun _ => false⟩)⟩]
  unless (match invalidLaw with | .refused _ _ => true | _ => false) do
    throwError "invalid explicit proof fell back to a default theorem"
  let report ← ZkcTools.Companions.report
    { identity := "adaptive.scale-law", responsibility := "mathematical recurrence",
      expected := expected } (.openObligation "companion deliberately omitted" #[])
  unless (report.getObjValAs? String "status").toOption == some "open" do
    throwError "conditional authoring obligation was reported as established"

end ProtocolProofExamples.ConstructionChoices
