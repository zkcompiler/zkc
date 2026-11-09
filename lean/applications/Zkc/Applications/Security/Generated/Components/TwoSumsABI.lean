module

public import Zkc.Applications.Security.Generated.TwoSums
public import Zkc.Tools.Verification.SubjectABI
public import Zkc.Tools.Verification.SourceInputClauses
public import Zkc.Tools.IR.StructuredSource.NamedValues
public meta import Zkc.Tools.IR.StructuredSource.NamedValues

@[expose] public section
noncomputable section

/-! Generated from the actual admitted subject, source ABI, input clauses
and retained selectors. Regenerate; do not hand edit. Input formula semantics
are reduced in Lean. Target mathematics requires its own checked laws. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace ZkcSecurity.Examples.Generated.Components.TwoSumsABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.Generated.TwoSums

abbrev model := subject.domainModel
named_values SourceView [input0, input1, input2, input3, input4, input5] := subject.target.owner.protocol.inputs

named_values PublicView [input0, input1, input2, input3, input4] := validatorArtifacts.publics

abbrev RawInputs := SourceView.View (Component model.Value)
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs
abbrev DataFields := SourceView.View (TypedABI.Slot Domain.dataType model.Value)

def fields (values : Data) : DataFields := SourceView.unpack values
def fromFields (fields : DataFields) : Data := SourceView.pack fields

theorem fromFields_fields (values : Data) : fromFields (fields values) = values :=
  SourceView.pack_unpack values

theorem fields_fromFields (record : DataFields) : fields (fromFields record) = record :=
  SourceView.unpack_pack record

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1, 2, 3, 4]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.index]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1, 2, 3]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:c6412e9dbfd654c98cabfb516f7e747b44b370e14d618d122c483b0f60ee20d3",  "sha256:5fc944428aa724030441283efc76355b9a252e1813e06c1eae06db77b9101ab4",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:c6412e9dbfd654c98cabfb516f7e747b44b370e14d618d122c483b0f60ee20d3",  "sha256:5fc944428aa724030441283efc76355b9a252e1813e06c1eae06db77b9101ab4",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  SourceView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3, input4 := input4, input5 := input5 }

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  SourceView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3, input4 := input4, input5 := input5 }

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3 input4 input5)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3 input4 input5) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3 input4 input5) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : validatorArtifacts.Statement model :=
  PublicView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3, input4 := input4 }

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))), values = (statement input0 input1 input2 input3 input4) := by subject_abi_surjective

abbrev StatementData := PublicView.View model.Value

def statementData (values : validatorArtifacts.Statement model) : StatementData := PublicView.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := PublicView.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := PublicView.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := PublicView.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1 input2 input3 input4) subject.publicBindingArity subject.publicBindingData

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3 input4)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3 input4)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2 input3 input4) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1 input2 input3 input4) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3 input4 input5) = some ((producerInputs input0 input1 input2 input3 input4), (validatorInputs input0 input1 input2 input3 input4)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3 input4 input5) (by rfl)
    [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩] [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩] (statement input0 input1 input2 input3 input4)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4), (validatorInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4))) := by
  rw [Subject.runtime_layout subject values ([0, 1, 4]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4)
  validator := fun data => (validatorInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4)
  preparation := preparation
  producerSorts := fun data => producer_sorts (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4
  validatorSorts := fun data => validator_sorts (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4

def inputCondition (values : subject.Inputs) : Prop :=
  source_input_condition subject on values

theorem source_clauses (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ inputCondition values :=
  by source_input_clauses

set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3 input4 input5) ↔ (input0.length < indexLimit ∧ input1.length < indexLimit ∧ input4 < indexLimit) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) (some input2) (some input3) (some input4) input5) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs, SourceView.pack]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3 input4 input5) ↔ ((input0.length < indexLimit ∧ input1.length < indexLimit ∧ input4 < indexLimit) ∧ (source_input_condition subject on (inputs input0 input1 input2 input3 input4 input5))) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3 input4 input5)).trans
    (and_congr (representable_iff input0 input1 input2 input3 input4 input5) (by source_input_clauses))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (inputs input0 input1 input2 input3 input4 input5) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil))))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1 input2 input3 input4 input5))
      (subject.assignments (inputs input0 input1 input2 input3 input4 input5)) = some (arguments input0 input1 input2 input3) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (_witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) .nil))))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0 input1 input2 input3 input4))
      (validatorSubject.assignments (statement input0 input1 input2 input3 input4) witness) =
      some (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) := by
  rfl

theorem context_eq : subject.selection.context = (Context.fiatShamir ("zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d") (["role00000000", "role00000001"]) 0 1 5 ("random.bls12-381.fr/0") (some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" }) ("merlin3.bls12-381.fr64be/0") ([("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"),  ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0")])) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:2a0351c54dc5de3d1b3cebb46e0172df3fff348683601797ad7fe58e349a2a96") := rfl
theorem producer_export : subject.producerExport = ("sha256:2bcc01b85b6ea57e3b71fb6c4f4fa3b7797ee4d1b1d0e09bfd1cda8fea18883e") := rfl
theorem validator_export : subject.validatorExport = ("sha256:106ab6342905e53d8ecd73b1c1c87a5cd176a2019840a04ae705c7595c53bbf6") := rfl

end ZkcSecurity.Examples.Generated.Components.TwoSumsABI
