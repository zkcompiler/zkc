module

public import ZkcSecurity.Examples.Generated.TwoSums
public import ZkcSecurity.Tools.SubjectABI

@[expose] public section
noncomputable section

/-! Generated from the actual admitted subject, source ABI, request policy
and retained selectors. Regenerate; do not hand edit. Formula mathematics
is deliberately absent. Every presentation equation is kernel checked. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace ZkcSecurity.Examples.Generated.Components.TwoSumsABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.Generated.TwoSums

abbrev model := subject.domainModel
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1, 2, 3, 4]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.index]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1, 2, 3]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:3b69a20a3bf1c12e4fcfe7cb521bde2f3bb57b6de6fa094caa966248e366553e",  "sha256:5dd732f36008ef6ee75ba430df404fd66d91abaf4de509052cef05cd05a5865c",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:3b69a20a3bf1c12e4fcfe7cb521bde2f3bb57b6de6fa094caa966248e366553e",  "sha256:5dd732f36008ef6ee75ba430df404fd66d91abaf4de509052cef05cd05a5865c",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 .nil))))))

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 .nil))))))

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3 input4 input5)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3 input4 input5) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3 input4 input5) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : validatorArtifacts.Statement model :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 .nil)))))

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))), values = (statement input0 input1 input2 input3 input4) := by subject_abi_surjective

abbrev StatementData := TypedABI.Fields model.Value validatorArtifacts.publics

def statementData (values : validatorArtifacts.Statement model) : StatementData := TypedABI.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := TypedABI.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := TypedABI.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := TypedABI.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1 input2 input3 input4) subject.publicBindingArity

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data (.vector ("bls12-381.fr") input0), .data (.vector ("bls12-381.fr") input1), .data (.index input4), .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3 input4)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data (.vector ("bls12-381.fr") input0), .data (.vector ("bls12-381.fr") input1), .data (.field ("bls12-381.fr") input2), .data (.field ("bls12-381.fr") input3), .data (.index input4), .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3 input4)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2 input3 input4) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1 input2 input3 input4) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3 input4 input5) = some ((producerInputs input0 input1 input2 input3 input4), (validatorInputs input0 input1 input2 input3 input4)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3 input4 input5) (by rfl)
    [.data (.vector ("bls12-381.fr") input0), .data (.vector ("bls12-381.fr") input1), .data (.index input4)] [.data (.vector ("bls12-381.fr") input0), .data (.vector ("bls12-381.fr") input1), .data (.field ("bls12-381.fr") input2), .data (.field ("bls12-381.fr") input3), .data (.index input4)] (statement input0 input1 input2 input3 input4)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1), (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1))) := by
  rw [Subject.runtime_layout subject values ([0, 1, 4]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1)
  validator := fun data => (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1)
  preparation := preparation
  producerSorts := fun data => producer_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1
  validatorSorts := fun data => validator_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1

theorem source_clauses (values : subject.Inputs) :
    ∀ index isInput, subject.inputClause values index isInput :=
  Subject.no_input_clauses subject (by decide +kernel) values

-- The shared policy normalization basis covers different input layouts.
set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency false in
theorem policy_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.inputPolicy.Holds (inputs input0 input1 input2 input3 input4 input5) ↔ (0 < (1 : Nat) ∧ 1 < indexLimit ∧ input4 < indexLimit ∧ input0.length < indexLimit ∧ input0.length = 1 * 2 ^ input4 ∧ 0 < (1 : Nat) ∧ 1 < indexLimit ∧ input4 < indexLimit ∧ input1.length < indexLimit ∧ input1.length = 1 * 2 ^ input4 ∧ input4 ≤ 4 ∧ input4 < indexLimit) := by
  change inputPolicy.Holds (sourceInputs (some input0) (some input1) (some input2) (some input3) (some input4) input5) ↔ _
  simp [inputPolicy, InputPolicy.Holds, InputRule.Holds, sourceInputs, TypedABI.get_cons_here, TypedABI.get_cons_there, and_assoc]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3 input4 input5) ↔ (0 < (1 : Nat) ∧ 1 < indexLimit ∧ input4 < indexLimit ∧ input0.length < indexLimit ∧ input0.length = 1 * 2 ^ input4 ∧ 0 < (1 : Nat) ∧ 1 < indexLimit ∧ input4 < indexLimit ∧ input1.length < indexLimit ∧ input1.length = 1 * 2 ^ input4 ∧ input4 ≤ 4 ∧ input4 < indexLimit) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3 input4 input5)).trans
    ((and_iff_left (source_clauses _)).trans (policy_iff input0 input1 input2 input3 input4 input5))

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

theorem context_eq : subject.selection.context = ({ entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",   roles := ["role00000000", "role00000001"],   producer := 0,   validator := 1,   service := 5,   contract := "random.bls12-381.fr/0",   request := some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" },   suite := "merlin3.bls12-381.fr64be/0",   draws := [("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"),             ("apply_16_label_7269676874_label_6368616c6c656e6765",              "apply_16_label_7269676874_label_64656c6976657279_0")] }) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:ff5b4060dd0ad94db9061d59d7560152b8db7dc820b1d25f3b358433a6e78732") := rfl
theorem producer_export : subject.producerExport = ("sha256:0bd526cfbc6d29aef756e4b0389d9fb6fe40d3ba76c557aab569266471957942") := rfl
theorem validator_export : subject.validatorExport = ("sha256:f1110f3e53e1ab652a83adb2c5e4311a42961b4c21b4ed6c9ed6cbda3efe9fe0") := rfl

end ZkcSecurity.Examples.Generated.Components.TwoSumsABI
