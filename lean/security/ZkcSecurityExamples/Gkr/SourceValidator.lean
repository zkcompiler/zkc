module

public import ZkcSecurityExamples.Gkr.CanonicalVerifier
public import ZkcSecurityExamples.Gkr.SourceAdmission
public import ZkcSecurityExamples.Gkr.SourceRoot
public import ZkcSecurityExamples.Gkr.Budget
public import ZkcSecurity.Bindings.Source.PropertyAssembly

@[expose] public section

/-! The actual occurrence validator on all typed public inputs, including malformed
lengths and counts. Admission is an internal case split in the safety proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.SourceValidator
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open ZkcSecurity.Source ZkcSecurity.FiatShamir ZkcExamples.Structured
variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def inputs (runtime : Source.Invocation F) :
    Values (Component (ringModel F G).Value) GkrSourceViews.program.payload.entry.inputs :=
  GkrSourceAdmission.inputs (G := G) runtime.inputs runtime.outputs runtime.add runtime.mul
    runtime.layers runtime.selector runtime.width runtime.handle

def output : Var GkrSourceViews.program.payload.entry.outputs .boolean := .here

def body (runtime : Source.Invocation F) :=
  Occurrence.participant (ringModel F G) GkrSourceViews.program 1 (inputs runtime)

theorem admitted_body (runtime : Source.Invocation F) (admitted : runtime.Admitted) :
    body (G := G) runtime =
      (HonestProducerObserved.validator {} runtime.handle HonestProducerSource.currentSites
        runtime.encoding runtime.outputs).bind (fun accepted => .done (SourceRows.Decision.pack (Value := Component (assignment F G)) ⟨accepted⟩)) :=
  CanonicalVerifier.reads runtime.encoding runtime.outputs admitted runtime.handle

theorem invalid_erasure (runtime : Source.Invocation F) (invalid : ¬ runtime.Admitted) :
    ∃ reason : PIR.Stop, (body (G := G) runtime).interpret Occurrence.erase = .halt reason := by
  obtain ⟨reason, stops⟩ := Source.invalid_stops (G := G) runtime invalid
  refine ⟨reason, ?_⟩
  unfold body
  rw [Occurrence.participant_erase]
  exact (Program.participant_eq_participantOn GkrSourceViews.program 1
    (inputs runtime)).symm.trans stops

variable [Fintype F] [SampleableType F]
attribute [local instance] OccurrenceReading.rawSampleable
attribute [local irreducible] body

def price : ENNReal := 4 / (Fintype.card F : ENNReal)

def rejected (runtime : Source.Invocation F) (wrong : ¬ runtime.Correct)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape (price (F := F)))
      (fun _ result => result.get output ≠ some true)
      history (body runtime) := by
  by_cases admitted : runtime.Admitted
  · rw [admitted_body runtime admitted]
    have noTable : runtime.outputTable ≠ runtime.encoding.circuit.wires runtime.layers 0 :=
      fun same => wrong ((Source.admitted_correct_iff runtime admitted).mpr same)
    exact PropertyAssembly.map (fun accepted : Option Bool => SourceRows.Decision.pack
      (Value := Component (ringModel F G).Value) ⟨accepted⟩)
      (SourceRoot.rejected {} HonestProducerSource.currentSites runtime.handle runtime.encoding runtime.outputs
        noTable (price (F := F))
        (ENNReal.div_le_div (by norm_num) le_rfl)
        (ENNReal.div_le_div (by norm_num) le_rfl)
        (ENNReal.div_le_div (by exact_mod_cast admitted.2.2.1) le_rfl) history)
      (fun _ _ failed => failed)
  · have stops := invalid_erasure (G := G) runtime admitted
    exact OccurrenceProperties.stopped _ (Classical.choose stops)
      (Classical.choose_spec stops) history

omit [SampleableType F] in
theorem costs (runtime : Source.Invocation F)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price (F := F))
      (body runtime) history (40 * price (F := F)) := by
  by_cases admitted : runtime.Admitted
  · rw [admitted_body runtime admitted]
    apply (CostComposition.map_iff _ _ _).mpr
    apply CostComposition.mono (Budget.validator {} HonestProducerSource.currentSites runtime.handle
      runtime.encoding runtime.outputs (price (F := F)) history)
    have countBound : runtime.width + runtime.layers * (2*runtime.width+1) ≤ 40 := by
      calc
        _ ≤ 4 + 4*(2*4+1) := Nat.add_le_add admitted.2.2.1
          (Nat.mul_le_mul admitted.2.2.2.1
            (Nat.add_le_add_right (Nat.mul_le_mul_left 2 admitted.2.2.1) 1))
        _ = 40 := rfl
    exact mul_le_mul' (by exact_mod_cast countBound) le_rfl
  · have stops := invalid_erasure (G := G) runtime admitted
    exact OccurrenceProperties.stopped_cost _ (Classical.choose stops)
      (Classical.choose_spec stops) _ _ history

#print axioms rejected
#print axioms costs
end ZkcSecurity.Realizations.Gkr.SourceValidator
