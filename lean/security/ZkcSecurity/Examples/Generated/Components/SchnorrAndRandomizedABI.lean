module

public import ZkcSecurity.Examples.Generated.SchnorrAndRandomized
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
namespace ZkcSecurity.Examples.Generated.Components.SchnorrAndRandomizedABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.Generated.SchnorrAndRandomized

abbrev model := subject.domainModel
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1, 2, 3]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1"]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1, 2, 3, 4, 5]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:c08aaf7d2661f2e11113084a922047cbf851a5595166b30ef36eaab0f6950e46",  "sha256:6cef1393239243a4c3646d6bd2bb34fc03826705bd8b67028ae9e2b2c393dd98",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:c08aaf7d2661f2e11113084a922047cbf851a5595166b30ef36eaab0f6950e46",  "sha256:6cef1393239243a4c3646d6bd2bb34fc03826705bd8b67028ae9e2b2c393dd98",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 (.cons input7 .nil))))))))

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 (.cons input7 .nil))))))))

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3 input4 input5 input6 input7)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3 input4 input5 input6 input7) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3 input4 input5 input6 input7) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : validatorArtifacts.Statement model :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil))))

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))), values = (statement input0 input1 input2 input3) := by subject_abi_surjective

abbrev StatementData := TypedABI.Fields model.Value validatorArtifacts.publics

def statementData (values : validatorArtifacts.Statement model) : StatementData := TypedABI.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := TypedABI.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := TypedABI.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := TypedABI.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1 input2 input3) subject.publicBindingArity subject.publicBindingData

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input4⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input5⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2 input3 input4 input5) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1 input2 input3) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3 input4 input5 input6 input7) = some ((producerInputs input0 input1 input2 input3 input4 input5), (validatorInputs input0 input1 input2 input3)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3 input4 input5 input6 input7) (by rfl)
    [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input4⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input5⟩] [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩] (statement input0 input1 input2 input3)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1), (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1))) := by
  rw [Subject.runtime_layout subject values ([0, 1, 2, 3, 4, 5]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1)
  validator := fun data => (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1)
  preparation := preparation
  producerSorts := fun data => producer_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1
  validatorSorts := fun data => validator_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1

theorem source_clauses (values : subject.Inputs) :
    ∀ index isInput, subject.inputClause values index isInput :=
  Subject.no_input_clauses subject (by decide +kernel) values

set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3 input4 input5 input6 input7) ↔ (True) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) (some input2) (some input3) (some input4) (some input5) input6 input7) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3 input4 input5 input6 input7) ↔ (True) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3 input4 input5 input6 input7)).trans
    ((and_iff_left (source_clauses _)).trans (representable_iff input0 input1 input2 input3 input4 input5 input6 input7))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (inputs input0 input1 input2 input3 input4 input5 input6 input7) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 .nil))))))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1 input2 input3 input4 input5 input6 input7))
      (subject.assignments (inputs input0 input1 input2 input3 input4 input5 input6 input7)) = some (arguments input0 input1 input2 input3 input4 input5) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) (.cons (witness _ (validatorSubject.target.application.selectors.get (.there (.there (.there (.there .here)))))) (.cons (witness _ (validatorSubject.target.application.selectors.get (.there (.there (.there (.there (.there .here))))))) .nil))))))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0 input1 input2 input3))
      (validatorSubject.assignments (statement input0 input1 input2 input3) witness) =
      (validatorArguments input0 input1 input2 input3 witness) := by
  rfl

theorem context_eq : subject.selection.context = (Context.fiatShamir ("zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c") (["role00000000", "role00000001"]) 0 1 7 ("random.bls12-381.fr/0") (some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" }) ("merlin3.bls12-381.fr64be/0") ([("label_6368616c6c656e6765", "label_64656c6976657279_0")])) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:caa1f6f2253041b1592fe89382e19e68e6da204292e0fbe054e00c110dcb41b8") := rfl
theorem producer_export : subject.producerExport = ("sha256:ffdcffa0e83aa57ad7d06ec223a1555405546b1fc1539fae607379f32230ebaa") := rfl
theorem validator_export : subject.validatorExport = ("sha256:8185aea422cbb3ab2047f8261841f020bd1a713c703061e702c5edcfb90f5994") := rfl

end ZkcSecurity.Examples.Generated.Components.SchnorrAndRandomizedABI
