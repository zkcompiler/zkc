module

public import ZkcSecurity.Examples.TableMembership.Subject
public import ZkcSecurity.Tools.SubjectABI
public import ZkcSecurity.Tools.SourceInputClauses

@[expose] public section
noncomputable section

/-! Generated from the actual admitted subject, source ABI, input clauses
and retained selectors. Regenerate; do not hand edit. Input formula semantics
are reduced in Lean. Target mathematics requires its own checked laws. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace ZkcSecurity.Examples.TableMembership.ABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.TableMembership.Subject

abbrev model := subject.domainModel
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.vector "koala-bear",  Zkc.Source.Structured.Ty.sequence    (Zkc.Source.Structured.Ty.product      "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"      "case00000000"      (Zkc.Source.Structured.ProductFields.cons        (Zkc.Source.Structured.Ty.boolean)        (Zkc.Source.Structured.ProductFields.cons          (Zkc.Source.Structured.Ty.field "koala-bear")          (Zkc.Source.Structured.ProductFields.nil))))]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.vector "koala-bear",  Zkc.Source.Structured.Ty.sequence    (Zkc.Source.Structured.Ty.product      "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"      "case00000000"      (Zkc.Source.Structured.ProductFields.cons        (Zkc.Source.Structured.Ty.boolean)        (Zkc.Source.Structured.ProductFields.cons          (Zkc.Source.Structured.Ty.field "koala-bear")          (Zkc.Source.Structured.ProductFields.nil))))]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:bffc188ca392be022ddf0fbef687ceb2404fdb5a9210a0aff8ce5c96c20cb921",  "sha256:5c9c7d62147e8e3357a2969255722853f887853d43dbbe09a60cdb7de309d1e4",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:bffc188ca392be022ddf0fbef687ceb2404fdb5a9210a0aff8ce5c96c20cb921",  "sha256:5c9c7d62147e8e3357a2969255722853f887853d43dbbe09a60cdb7de309d1e4",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) : subject.Inputs :=
  (.cons input0 (.cons input1 .nil))

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) : Data :=
  (.cons input0 (.cons input1 .nil))

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))), values = (sourceInputs input0 input1) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))), values = (data input0 input1) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) : validatorArtifacts.Statement model :=
  (.cons input0 (.cons input1 .nil))

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))), values = (statement input0 input1) := by subject_abi_surjective

abbrev StatementData := TypedABI.Fields model.Value validatorArtifacts.publics

def statementData (values : validatorArtifacts.Statement model) : StatementData := TypedABI.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := TypedABI.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := TypedABI.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := TypedABI.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1) subject.publicBindingArity subject.publicBindingData

def producerInputs : Domain.Environment model.toCarriers :=
  []

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.vector "koala-bear"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))), by decide, input1⟩]

theorem producer_sorts :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) :
    subject.runtimeInputs (inputs input0 input1) = some ((producerInputs), (validatorInputs input0 input1)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1) (by rfl)
    [] [.data ⟨(Zkc.Source.Structured.Ty.vector "koala-bear"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))), by decide, input1⟩] (statement input0 input1)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs), (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1))) := by
  rw [Subject.runtime_layout subject values ([]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun _data => (producerInputs)
  validator := fun data => (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1)
  preparation := preparation
  producerSorts := fun _data => producer_sorts
  validatorSorts := fun data => validator_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1

theorem source_clauses (values : subject.Inputs) :
    ∀ index isInput, subject.inputClause values index isInput :=
  Subject.no_input_clauses subject (by decide +kernel) values

set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) :
    inputsRepresentable (inputs input0 input1) ↔ (input0.length < indexLimit ∧ inputRepresentable (carriers := model.toCarriers) (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))) (some input1)) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1)) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) :
    subject.HonestInput (inputs input0 input1) ↔ (input0.length < indexLimit ∧ inputRepresentable (carriers := model.toCarriers) (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))) (some input1)) := by
  exact (abi.honest_pack_iff (data input0 input1)).trans
    ((and_iff_left (source_clauses _)).trans (representable_iff input0 input1))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))), values = (inputs input0 input1) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input1 .nil))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1))
      (subject.assignments (inputs input0 input1)) = some (arguments input0 input1) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) (_witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (some input1) .nil))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "koala-bear"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.sequence   (Zkc.Source.Structured.Ty.product     "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"     "case00000000"     (Zkc.Source.Structured.ProductFields.cons       (Zkc.Source.Structured.Ty.boolean)       (Zkc.Source.Structured.ProductFields.cons         (Zkc.Source.Structured.Ty.field "koala-bear")         (Zkc.Source.Structured.ProductFields.nil))))))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0 input1))
      (validatorSubject.assignments (statement input0 input1) witness) =
      some (.cons input0 (.cons input1 .nil)) := by
  rfl

theorem context_eq : subject.selection.context = (Context.plain ("zkl_a640d0482dc3e22330cd86a653acff52afd2c13a23627566f0df20496d35cc9e") (["role00000000", "role00000001"]) 0 1) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:4f999b8a75cff894105d7a535f7b16453d7635ddc3af3b73f49415833b295617") := rfl
theorem producer_export : subject.producerExport = ("sha256:e7d8db9a3a3140e28a5167809f95e3df45507cd76fa3080a3478366abea814cb") := rfl
theorem validator_export : subject.validatorExport = ("sha256:c93e2b6585b74d9eaee11131fb3a5676e56d9aab511dc1810bae4ce31d4616d6") := rfl

end ZkcSecurity.Examples.TableMembership.ABI
