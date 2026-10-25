module

public import ZkcSecurity.Examples.Generated.SmallSumcheck
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
namespace ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.Generated.SmallSumcheck

abbrev model := subject.domainModel
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1, 2]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.index]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:9f977589953d6500cb633d25dd19c104f1c6e44270a7f5ffe4e43b823f6de379",  "sha256:c7df7deed94bda74552694eff3b924f698f0b3fc08221c97824ac9f64a9dac46",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:9f977589953d6500cb633d25dd19c104f1c6e44270a7f5ffe4e43b823f6de379",  "sha256:c7df7deed94bda74552694eff3b924f698f0b3fc08221c97824ac9f64a9dac46",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil))))

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil))))

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) : validatorArtifacts.Statement model :=
  (.cons input0 (.cons input1 (.cons input2 .nil)))

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))), values = (statement input0 input1 input2) := by subject_abi_surjective

abbrev StatementData := TypedABI.Fields model.Value validatorArtifacts.publics

def statementData (values : validatorArtifacts.Statement model) : StatementData := TypedABI.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := TypedABI.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := TypedABI.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := TypedABI.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1 input2) subject.publicBindingArity

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data (.vector ("bls12-381.fr") input0), .data (.index input2), .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data (.vector ("bls12-381.fr") input0), .data (.field ("bls12-381.fr") input1), .data (.index input2), .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1 input2) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3) = some ((producerInputs input0 input1 input2), (validatorInputs input0 input1 input2)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3) (by rfl)
    [.data (.vector ("bls12-381.fr") input0), .data (.index input2)] [.data (.vector ("bls12-381.fr") input0), .data (.field ("bls12-381.fr") input1), .data (.index input2)] (statement input0 input1 input2)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1), (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1))) := by
  rw [Subject.runtime_layout subject values ([0, 2]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1)
  validator := fun data => (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1)
  preparation := preparation
  producerSorts := fun data => producer_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1
  validatorSorts := fun data => validator_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1

def inputCondition (values : subject.Inputs) : Prop :=
  source_input_condition subject on values

theorem source_clauses (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ inputCondition values :=
  by source_input_clauses

set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3) ↔ (input0.length < indexLimit ∧ input2 < indexLimit) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) (some input2) input3) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs, and_assoc]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3) ↔ ((input0.length < indexLimit ∧ input2 < indexLimit) ∧ (source_input_condition subject on (inputs input0 input1 input2 input3))) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3)).trans
    (and_congr (representable_iff input0 input1 input2 input3) (by source_input_clauses))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (inputs input0 input1 input2 input3) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input1 .nil))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1 input2 input3))
      (subject.assignments (inputs input0 input1 input2 input3)) = some (arguments input0 input1) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (_witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (some input1) .nil))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.index))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0 input1 input2))
      (validatorSubject.assignments (statement input0 input1 input2) witness) =
      some (.cons input0 (.cons input1 .nil)) := by
  rfl

theorem context_eq : subject.selection.context = ({ entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",   roles := ["role00000000", "role00000001"],   producer := 0,   validator := 1,   service := 3,   contract := "random.bls12-381.fr/0",   request := some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" },   suite := "merlin3.bls12-381.fr64be/0",   draws := [("apply_18_label_726564756365_label_6368616c6c656e6765",              "apply_18_label_726564756365_label_64656c6976657279_0")] }) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:c7bd8f9e5ecf095602373f1aea9324ff67dc00870477a4d72aafb35f4ff6fef1") := rfl
theorem producer_export : subject.producerExport = ("sha256:52fe282e78ac5b875db5c98b5780e0f4e57b00505ce6e99fdc2b24a75dc398f9") := rfl
theorem validator_export : subject.validatorExport = ("sha256:5a57b102cd46cb4fc6e5e9f1aa86f59c88e726a6df18b5d5405041a146f9f7e3") := rfl

end ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
