module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamilyProperties

@[expose] public section

/-! Honest producer/validator pairing at an arbitrary source occurrence of an
installed reduction. Both actual source bodies and full residuals are retained.
The message representation is the existing two-value degree-one family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceFamily
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Construction
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent
open ZkcSecurity.Source
variable {program : Zkc.Source.Structured.Program}
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

theorem pair (installation : Installation program) (site : String) (scope : PairScope)
    (roles : scope.producer = 0 ∧ scope.validator = 1)
    (delivery : (SumcheckRoundNormalForms.challengeSite (context site),
      SumcheckRoundNormalForms.deliverySite (context site)) ∈ scope.deliveries)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count)
    (bounded : count ≤ installation.maximum) (small : count < 64) (finite : original.length < indexLimit)
    (honest : scalar = original.sum) :
    Pair scope (fun _ v => v = some true)
      (producerOne installation model site original count)
      (one installation model {} site (some original) (some scalar)
        (some count) (some handle)) := by
  rw [one_reduction model installation site original count handle scalar callerFrame shape]
  have tableLaw := Multilinear.Admission.table_eq model program.payload.linked
    installation.admissionBodies original count 1 finite
    (lt_trans small (by decide +kernel)) (by decide +kernel)
  have valid : Multilinear.Admission.HasShape original count 1 :=
    Multilinear.Admission.hasShape_of_length _ _ _ (by decide) small (by simpa using shape)
  unfold producerOne
  change Pair scope _ ((Participant.owned 0 0
    (invoke (tables model program.payload.definitions).closed
      tableHelper)
    (Values.cons original (Values.cons count (Values.cons 1 Values.nil)) :
      Values model.Value [.vector field, .index, .index]).present).bind _) _
  rw [Participant.owned_present]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  change Pair scope _
    ((invoke (tables model program.payload.definitions).closed
      tableHelper
      (.cons original (.cons count (.cons 1 .nil)))).bind _) _
  rw [Evaluation.closed_invoke_componentTablesOn]
  change invoke (List.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []
    program.payload.definitions) tableHelper
    (.cons original (.cons count (.cons 1 .nil))) = _ at tableLaw
  rw [tableLaw]
  simp only [Multilinear.Admission.tableOutcome, valid, ↓reduceIte, primitiveOutcome,
    PIR.Process.interpret, PIR.Process.bind]
  unfold producerReduction SourceIteration.reduction
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  have distinctP : NormalForm.RosterDistinct (context site) 0 2 :=
    .ofSeparate (by change (1 : Nat) ≠ 0; decide) (by decide)
  have installed := (SourcePair.reduction model _ program.payload.linked installation.roundBodies
    (installation.producerBodies model)
    (installation.validatorBodies model)
    (Occurrence.table model program.payload) (context site) distinctP
    (context_distinct site) scope
    ⟨by change 0 = scope.producer; exact roles.1.symm,
      by change 1 = scope.validator; exact roles.2.symm⟩ delivery
    original scalar callerFrame (installation.maximum) count handle shape bounded small finite honest).bind
    (Final := fun _ v => v = some true) PIR.Process.done
    (terminalCheck model installation original) (by
    intro p v result
    obtain ⟨state, same, _, right, _, rfl⟩ := result
    have checked := terminal_check model installation state count
      (by simpa only [same] using shape) small (by simpa only [same] using finite)
    rw [same] at checked
    change terminalCheck model installation original
      (SumcheckVerifierBodies.reduceReturnValues (SourcePair.validatorSlots model state)) = _ at checked
    change Pair scope _ (.done p) (terminalCheck model installation original _)
    rw [checked]
    exact .done (by simp only [right, decide_true]))
  rw [PIR.Process.bind_done] at installed
  convert installed using 1 <;> rfl

#print axioms pair
end ZkcSecurity.Realizations.Sumcheck.SourceFamily
