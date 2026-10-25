module

public import ZkcSecurity.Examples.Generated.SequentialSigma
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
namespace ZkcSecurity.Examples.Generated.Components.SequentialSigmaABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.Generated.SequentialSigma

abbrev model := subject.domainModel
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1, 2, 3]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1"]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1, 2, 3, 4]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:ac9b68071c8be6a674a21a332c0b2ac222bc9387ca4d6c3002bd4d0633ab60b5",  "sha256:5e251f9e7573fcde1b91f0daaa0d5c061242fe4cfdea2b74baf16e187e0933cd",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:ac9b68071c8be6a674a21a332c0b2ac222bc9387ca4d6c3002bd4d0633ab60b5",  "sha256:5e251f9e7573fcde1b91f0daaa0d5c061242fe4cfdea2b74baf16e187e0933cd",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 .nil)))))))

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 .nil)))))))

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3 input4 input5 input6)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3 input4 input5 input6) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3 input4 input5 input6) := by subject_abi_surjective

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
    (statement input0 input1 input2 input3) subject.publicBindingArity

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Domain.Environment model.toCarriers :=
  [.data (.group ("bls12-381.g1") input0), .data (.group ("bls12-381.g1") input1), .data (.group ("bls12-381.g1") input2), .data (.group ("bls12-381.g1") input3), .data (.field ("bls12-381.fr") input4), .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : Domain.Environment model.toCarriers :=
  [.data (.group ("bls12-381.g1") input0), .data (.group ("bls12-381.g1") input1), .data (.group ("bls12-381.g1") input2), .data (.group ("bls12-381.g1") input3), .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2 input3 input4) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1 input2 input3) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3 input4 input5 input6) = some ((producerInputs input0 input1 input2 input3 input4), (validatorInputs input0 input1 input2 input3)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3 input4 input5 input6) (by rfl)
    [.data (.group ("bls12-381.g1") input0), .data (.group ("bls12-381.g1") input1), .data (.group ("bls12-381.g1") input2), .data (.group ("bls12-381.g1") input3), .data (.field ("bls12-381.fr") input4)] [.data (.group ("bls12-381.g1") input0), .data (.group ("bls12-381.g1") input1), .data (.group ("bls12-381.g1") input2), .data (.group ("bls12-381.g1") input3)] (statement input0 input1 input2 input3)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1), (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1))) := by
  rw [Subject.runtime_layout subject values ([0, 1, 2, 3, 4]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1)
  validator := fun data => (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1)
  preparation := preparation
  producerSorts := fun data => producer_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1
  validatorSorts := fun data => validator_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1

theorem source_clauses (values : subject.Inputs) :
    ∀ index isInput, subject.inputClause values index isInput :=
  Subject.no_input_clauses subject (by decide +kernel) values

set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3 input4 input5 input6) ↔ (True) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) (some input2) (some input3) (some input4) input5 input6) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs, and_assoc]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3 input4 input5 input6) ↔ (True) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3 input4 input5 input6)).trans
    ((and_iff_left (source_clauses _)).trans (representable_iff input0 input1 input2 input3 input4 input5 input6))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (inputs input0 input1 input2 input3 input4 input5 input6) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 .nil)))))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1 input2 input3 input4 input5 input6))
      (subject.assignments (inputs input0 input1 input2 input3 input4 input5 input6)) = some (arguments input0 input1 input2 input3 input4) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) (.cons (witness _ (validatorSubject.target.application.selectors.get (.there (.there (.there (.there .here)))))) .nil)))))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0 input1 input2 input3))
      (validatorSubject.assignments (statement input0 input1 input2 input3) witness) =
      (validatorArguments input0 input1 input2 input3 witness) := by
  rfl

theorem context_eq : subject.selection.context = ({ entry := "s7h6578616d706c6515h53657175656e7469616c5369676d61",   roles := ["role00000000", "role00000001"],   producer := 0,   validator := 1,   service := 6,   contract := "random.bls12-381.fr/0",   request := some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" },   suite := "merlin3.bls12-381.fr64be/0",   draws := [("apply_2_s0_label_6368616c6c656e6765", "apply_2_s0_label_64656c6976657279_0"),             ("apply_2_s2_label_6368616c6c656e6765", "apply_2_s2_label_64656c6976657279_0")] }) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:e9ff8c20566b330bb1b5df00ba30126efd31a093520c4cc720f1dc40ce5b0c9c") := rfl
theorem producer_export : subject.producerExport = ("sha256:e4e3beed98682a971c15f97407915cebf4d62767d16c23fd29e5d701437a5938") := rfl
theorem validator_export : subject.validatorExport = ("sha256:eb7eecc515344a520e0fca3ee28e0554145ddeb936ffe3edca5409c98eead3cf") := rfl

end ZkcSecurity.Examples.Generated.Components.SequentialSigmaABI
