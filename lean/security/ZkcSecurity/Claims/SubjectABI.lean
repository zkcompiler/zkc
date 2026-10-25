module

public import Zkc.Source.TypedABI
public import ZkcSecurity.Claims.SubjectInputs
public import ZkcSecurity.Claims.PairValidator

@[expose] public section

/-! Laws shared by generated source/public ABIs. The generated presentation
supplies checked preparation and selector equations, never formula mathematics. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair.Subject
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

abbrev domainModel (_subject : Subject model original imported selected) : DomainModel := model

/-- Resolve the source layout once before reasoning about optional input values.
This equation keeps source admission out of every data-presence case split. -/
theorem runtime_layout (subject : Subject model original imported selected)
    (inputs : subject.Inputs) (producerPositions : List Nat)
    (layout : (entryInterface original).map (fun (types, interface) =>
      dataInputs types interface.inputScopes selected.policy.producer) = some producerPositions) :
    subject.runtimeInputs inputs = (do
      let producer ← project (encodeInputs inputs) producerPositions
      let validator ← project (encodeInputs inputs) selected.policy.publicInputs
      let history ← Domain.PublicBinding.fromEnvironment subject.originalExport
        selected.policy.publicInputs subject.publicBindingArity validator
      pure (producer ++ [.transcript selected.policy.suite history],
        validator ++ [.transcript selected.policy.suite history])) := by
  cases entry : entryInterface original with
  | none => simp [entry] at layout
  | some actual =>
    rcases actual with ⟨types, interface⟩
    simp only [entry, Option.map_some, Option.some.injEq] at layout
    subst producerPositions
    simp only [runtimeInputs, entry]
    rfl

/-- Exact partial preparation uses the source role projection and the admitted
public ABI. The same typed history constructor is used by the verifier game. -/
theorem runtime_of_projections (subject : Subject model original imported selected)
    (inputs : subject.Inputs) {sourceTypes : List Ty} {interface : ProtocolInterface}
    (entry : entryInterface original = some (sourceTypes, interface))
    (producer validator : Domain.Environment model.toCarriers)
    (statement : Values model.Value subject.selection.publics)
    (producerProjection : project (encodeInputs inputs)
      (dataInputs sourceTypes interface.inputScopes selected.policy.producer) = some producer)
    (publicProjection : project (encodeInputs inputs) selected.policy.publicInputs = some validator)
    (encoding : Domain.encodeValues statement = some validator) :
    subject.runtimeInputs inputs = some
      (producer ++ [.transcript selected.policy.suite (Domain.PublicBinding.history
        subject.originalExport selected.policy.publicInputs statement subject.publicBindingArity)],
       validator ++ [.transcript selected.policy.suite (Domain.PublicBinding.history
        subject.originalExport selected.policy.publicInputs statement subject.publicBindingArity)]) := by
  simp [runtimeInputs, entry, producerProjection, publicProjection,
    Domain.PublicBinding.fromEnvironment_encodeValues statement subject.originalExport
      selected.policy.publicInputs subject.publicBindingArity encoding]

theorem no_input_clauses (subject : Subject model original imported selected)
    (empty : ∀ clause ∈ subject.target.owner.contract.clauses, clause.kind ≠ .input)
    (inputs : subject.Inputs) : ∀ index isInput, subject.inputClause inputs index isInput := by
  intro index isInput
  exact False.elim (empty _ (List.get_mem ..) isInput)

/-- A source ABI presentation separates optional source coordinates from the
data whose presence is necessary for preparing the selected actual pair. -/
structure ABI (subject : Subject model original imported selected) where
  Data : Type
  pack : Data → subject.Inputs
  complete : subject.Inputs → Option Data
  complete_iff : ∀ inputs data, complete inputs = some data ↔ inputs = pack data
  producer : Data → Domain.Environment model.toCarriers
  validator : Data → Domain.Environment model.toCarriers
  preparation : ∀ inputs, subject.runtimeInputs inputs =
    (complete inputs).map (fun data => (producer data, validator data))
  producerSorts : ∀ data, Domain.sortsMatch selected.artifacts.producer.inputs (producer data) = true
  validatorSorts : ∀ data, Domain.sortsMatch selected.artifacts.validator.inputs (validator data) = true

namespace ABI
variable {subject : Subject model original imported selected} (abi : ABI subject)

theorem runtime_pack (data : abi.Data) :
    subject.runtimeInputs (abi.pack data) = some (abi.producer data, abi.validator data) := by
  rw [abi.preparation, (abi.complete_iff _ _).mpr rfl]
  rfl

theorem honest_exists (inputs : subject.Inputs) (honest : subject.HonestInput inputs) :
    ∃ data, inputs = abi.pack data := by
  obtain ⟨_, _, producer, validator, prepared, _⟩ := honest
  rw [abi.preparation] at prepared
  cases found : abi.complete inputs with
  | none => simp [found] at prepared
  | some data => exact ⟨data, (abi.complete_iff _ _).mp found⟩

theorem honest_pack_iff (data : abi.Data) :
    subject.HonestInput (abi.pack data) ↔
      subject.inputPolicy.Holds (abi.pack data) ∧
        ∀ index isInput, subject.inputClause (abi.pack data) index isInput := by
  constructor
  · exact fun honest => ⟨honest.1, honest.2.1⟩
  · rintro ⟨policy, clauses⟩
    exact ⟨policy, clauses, _, _, abi.runtime_pack data,
      abi.producerSorts data, abi.validatorSorts data⟩

theorem honest_iff_exists (inputs : subject.Inputs) :
    subject.HonestInput inputs ↔ ∃ data, inputs = abi.pack data ∧
      subject.inputPolicy.Holds (abi.pack data) ∧
        ∀ index isInput, subject.inputClause (abi.pack data) index isInput := by
  constructor
  · intro honest
    obtain ⟨data, rfl⟩ := abi.honest_exists inputs honest
    exact ⟨data, rfl, (abi.honest_pack_iff data).mp honest⟩
  · rintro ⟨data, rfl, holds⟩
    exact (abi.honest_pack_iff data).mpr holds

end ABI
end ZkcSecurity.Claims.HonestPair.Subject

namespace ZkcSecurity.Claims.Domain.Subject
open Zkc.Source Zkc.Source.Structured
variable {model : DomainModel} {art : Endpoint.Domain.Artifacts}

theorem holds_iff_of_read (subject : Subject model art) (statement : art.Statement model)
    (witness : subject.Witness)
    (arguments : Values model.Value subject.target.application.relation.declaration.inputs)
    (read : subject.target.application.read {} (subject.boundary statement)
      (subject.assignments statement witness) = some arguments) :
    subject.Holds statement witness ↔ subject.target.formula.invokeRelationOn model arguments =
      .done (subject.target.booleanOutput.symm ▸ Values.cons true .nil) := by
  constructor
  · rintro ⟨actual, actualRead, truth⟩
    cases Option.some.inj (read.symm.trans actualRead)
    exact truth
  · exact fun truth => ⟨arguments, read, truth⟩

/-- Mathematical characterization is supplied after the exact retained read.
Witness-independent public targets can eliminate their existential uniformly. -/
theorem falseStatement_iff_of_holds (subject : Subject model art)
    (statement : art.Statement model) (proposition : Prop)
    (holds : ∀ witness, subject.Holds statement witness ↔ proposition) :
    subject.FalseStatement statement ↔ ¬ proposition := by
  constructor
  · intro rejected truth
    exact rejected ⟨fun _ _ => none, (holds _).mpr truth⟩
  · rintro incorrect ⟨witness, accepted⟩
    exact incorrect ((holds witness).mp accepted)

end ZkcSecurity.Claims.Domain.Subject
