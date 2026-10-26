module

public import ZkcSecurity.Examples.Generated.SampledAbort
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
namespace ZkcSecurity.Examples.Generated.Components.SampledAbortABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.Generated.SampledAbort

abbrev model := subject.domainModel
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.field "bls12-381.fr"]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:05855e7869890c3ee385d1b9e161253355a6cbc2faf534b2fdd5b5eec24c4ddd",  "sha256:cbd19dc6b21e82d369016065000738a83387fed49c203546f32fa96be2782fa8",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:05855e7869890c3ee385d1b9e161253355a6cbc2faf534b2fdd5b5eec24c4ddd",  "sha256:cbd19dc6b21e82d369016065000738a83387fed49c203546f32fa96be2782fa8",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil))))

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil))))

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : validatorArtifacts.Statement model :=
  (.cons input0 .nil)

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))), values = (statement input0) := by subject_abi_surjective

abbrev StatementData := TypedABI.Fields model.Value validatorArtifacts.publics

def statementData (values : validatorArtifacts.Statement model) : StatementData := TypedABI.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := TypedABI.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := TypedABI.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := TypedABI.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0) subject.publicBindingArity subject.publicBindingData

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input1⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input0⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3) = some ((producerInputs input0 input1), (validatorInputs input0)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3) (by rfl)
    [.data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input1⟩] [.data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input0⟩] (statement input0)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1), (validatorInputs (TypedABI.unpack data).1))) := by
  rw [Subject.runtime_layout subject values ([0, 1]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1)
  validator := fun data => (validatorInputs (TypedABI.unpack data).1)
  preparation := preparation
  producerSorts := fun data => producer_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1
  validatorSorts := fun data => validator_sorts (TypedABI.unpack data).1

theorem source_clauses (values : subject.Inputs) :
    ∀ index isInput, subject.inputClause values index isInput :=
  Subject.no_input_clauses subject (by decide +kernel) values

set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3) ↔ (True) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) input2 input3) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3) ↔ (True) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3)).trans
    ((and_iff_left (source_clauses _)).trans (representable_iff input0 input1 input2 input3))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (inputs input0 input1 input2 input3) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input1 .nil))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1 input2 input3))
      (subject.assignments (inputs input0 input1 input2 input3)) = some (arguments input0 input1) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (witness _ (validatorSubject.target.application.selectors.get (.there .here))) .nil))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0))
      (validatorSubject.assignments (statement input0) witness) =
      (validatorArguments input0 witness) := by
  rfl

theorem context_eq : subject.selection.context = (Context.fiatShamir ("s7h6578616d706c6512h53616d706c656441626f7274") (["role00000000", "role00000001"]) 0 1 3 ("random.bls12-381.fr/0") (some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" }) ("merlin3.bls12-381.fr64be/0") ([("label_6368616c6c656e6765", "label_64656c6976657279_0")])) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:ef0af2b02f1269fc2cac4e9ef71209246df5ce9213ef8a8bb5e83b4f31681776") := rfl
theorem producer_export : subject.producerExport = ("sha256:4b8b55c2804fe3a02922becc37ca9f959b0793b85daaa460ee63e376ebeffa8c") := rfl
theorem validator_export : subject.validatorExport = ("sha256:b6a32e9bd8876adf9c01f2fecd67ea9ffe9c8b17664935d5d2562c5ee20f99a8") := rfl

end ZkcSecurity.Examples.Generated.Components.SampledAbortABI
