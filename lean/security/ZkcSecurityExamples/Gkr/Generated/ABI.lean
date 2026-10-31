module

public import ZkcSecurityExamples.Gkr.Generated.Subject
public import ZkcSecurityTools.SubjectABI
public import ZkcSecurityTools.SourceInputClauses

@[expose] public section
noncomputable section

/-! Generated from the actual admitted subject, source ABI, input clauses
and retained selectors. Regenerate; do not hand edit. Input formula semantics
are reduced in Lean. Target mathematics requires its own checked laws. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace ZkcSecurity.Realizations.Gkr.Generated.ABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Realizations.Gkr.Generated.Subject

abbrev model := subject.domainModel
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1, 2, 3, 4, 5, 6]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.vector "bls12-381.fr",  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.index,  Zkc.Source.Structured.Ty.index]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 2, 3, 4, 5, 6, 1]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:00b9fc5bd392761c5c112d93bda31a99ba543cf594184f80c741d5d79f926cf9",  "sha256:22cba88007705d703cf95d5ea3685b488fab9757414a91b98c61fe82ddfc6f6b",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:00b9fc5bd392761c5c112d93bda31a99ba543cf594184f80c741d5d79f926cf9",  "sha256:22cba88007705d703cf95d5ea3685b488fab9757414a91b98c61fe82ddfc6f6b",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 (.cons input7 .nil))))))))

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 (.cons input7 .nil))))))))

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3 input4 input5 input6 input7)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3 input4 input5 input6 input7) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3 input4 input5 input6 input7) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) : validatorArtifacts.Statement model :=
  (.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 .nil)))))))

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))), values = (statement input0 input1 input2 input3 input4 input5 input6) := by subject_abi_surjective

abbrev StatementData := TypedABI.Fields model.Value validatorArtifacts.publics

def statementData (values : validatorArtifacts.Statement model) : StatementData := TypedABI.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := TypedABI.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := TypedABI.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := TypedABI.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1 input2 input3 input4 input5 input6) subject.publicBindingArity subject.publicBindingData

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input5⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input6⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3 input4 input5 input6)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input5⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input6⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3 input4 input5 input6)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2 input3 input4 input5 input6) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1 input2 input3 input4 input5 input6) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3 input4 input5 input6 input7) = some ((producerInputs input0 input1 input2 input3 input4 input5 input6), (validatorInputs input0 input1 input2 input3 input4 input5 input6)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3 input4 input5 input6 input7) (by rfl)
    [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input5⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input6⟩] [.data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.vector "bls12-381.fr"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input4⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input5⟩, .data ⟨(Zkc.Source.Structured.Ty.index), by decide, input6⟩] (statement input0 input1 input2 input3 input4 input5 input6)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.2.1), (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.2.1))) := by
  rw [Subject.runtime_layout subject values ([0, 2, 3, 4, 5, 6]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.2.1)
  validator := fun data => (validatorInputs (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.2.1)
  preparation := preparation
  producerSorts := fun data => producer_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.2.1
  validatorSorts := fun data => validator_sorts (TypedABI.unpack data).1 (TypedABI.unpack data).2.1 (TypedABI.unpack data).2.2.1 (TypedABI.unpack data).2.2.2.1 (TypedABI.unpack data).2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.1 (TypedABI.unpack data).2.2.2.2.2.2.1

def inputCondition (values : subject.Inputs) : Prop :=
  source_input_condition subject on values

theorem source_clauses (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ inputCondition values :=
  by source_input_clauses

set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3 input4 input5 input6 input7) ↔ (input0.length < indexLimit ∧ input1.length < indexLimit ∧ input2.length < indexLimit ∧ input3.length < indexLimit ∧ input4 < indexLimit ∧ input5 < indexLimit ∧ input6 < indexLimit) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) (some input2) (some input3) (some input4) (some input5) (some input6) input7) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3 input4 input5 input6 input7) ↔ ((input0.length < indexLimit ∧ input1.length < indexLimit ∧ input2.length < indexLimit ∧ input3.length < indexLimit ∧ input4 < indexLimit ∧ input5 < indexLimit ∧ input6 < indexLimit) ∧ (source_input_condition subject on (inputs input0 input1 input2 input3 input4 input5 input6 input7))) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3 input4 input5 input6 input7)).trans
    (and_congr (representable_iff input0 input1 input2 input3 input4 input5 input6 input7) (by source_input_clauses))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (inputs input0 input1 input2 input3 input4 input5 input6 input7) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 (.cons input1 .nil)))))))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (input7 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1 input2 input3 input4 input5 input6 input7))
      (subject.assignments (inputs input0 input1 input2 input3 input4 input5 input6 input7)) = some (arguments input0 input1 input2 input3 input4 input5 input6) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (_witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (some input2) (.cons (some input3) (.cons (some input4) (.cons (some input5) (.cons (some input6) (.cons (some input1) .nil)))))))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.vector "bls12-381.fr"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.index))) (input5 : (model.Value (Zkc.Source.Structured.Ty.index))) (input6 : (model.Value (Zkc.Source.Structured.Ty.index))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0 input1 input2 input3 input4 input5 input6))
      (validatorSubject.assignments (statement input0 input1 input2 input3 input4 input5 input6) witness) =
      some (.cons input0 (.cons input2 (.cons input3 (.cons input4 (.cons input5 (.cons input6 (.cons input1 .nil))))))) := by
  rfl

theorem context_eq : subject.selection.context = (Context.fiatShamir ("zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2") (["role00000000", "role00000001"]) 0 1 7 ("random.bls12-381.fr/0") (some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" }) ("merlin3.bls12-381.fr64be/0") ([("label_6f7574707574", "label_6f75747075745f64656c6976657279_0"),  ("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"),  ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0"),  ("label_6c696e655f6368616c6c656e6765", "label_6c696e655f64656c6976657279_0")])) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:d73cb1755bed132e32367f16a789977f090079fef5c5649a8296cf8e74665133") := rfl
theorem producer_export : subject.producerExport = ("sha256:d68f53c1bfc1a84c277906ac327e7bdee395aedd469f0b776b5b06000112086e") := rfl
theorem validator_export : subject.validatorExport = ("sha256:edab1a2f1991db65a7b9a7560d5614113a4babb83df7307cee4f537f13fb2e7e") := rfl

end ZkcSecurity.Realizations.Gkr.Generated.ABI
