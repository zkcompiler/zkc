module

public import ZkcSecurityExamples.Generated.SequentialSigma
public import ZkcSecurityTools.SubjectABI
public import ZkcSecurityTools.SourceInputClauses
public import ZkcTools.StructuredSource.NamedValues
public meta import ZkcTools.StructuredSource.NamedValues

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
named_values SourceView [input0, input1, input2, input3, input4, input5, input6] := subject.target.owner.protocol.inputs

named_values PublicView [input0, input1, input2, input3] := validatorArtifacts.publics

abbrev RawInputs := SourceView.View (Component model.Value)
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs
abbrev DataFields := SourceView.View (TypedABI.Slot Domain.dataType model.Value)

def fields (values : Data) : DataFields := SourceView.unpack values
def fromFields (fields : DataFields) : Data := SourceView.pack fields

theorem fromFields_fields (values : Data) : fromFields (fields values) = values :=
  SourceView.pack_unpack values

theorem fields_fromFields (record : DataFields) : fields (fromFields record) = record :=
  SourceView.unpack_pack record

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1, 2, 3]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1"]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1, 2, 3, 4]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:6b6b8fdffdb9eb2c66464d0a2f4b0b496e11c955c3ff40cf9dca6834c82472e6",  "sha256:8f3ce95d10f0f04971f51c08588ddbdaa2701c7370b412d143a0679ebf8571c0",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:6b6b8fdffdb9eb2c66464d0a2f4b0b496e11c955c3ff40cf9dca6834c82472e6",  "sha256:8f3ce95d10f0f04971f51c08588ddbdaa2701c7370b412d143a0679ebf8571c0",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  SourceView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3, input4 := input4, input5 := input5, input6 := input6 }

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  SourceView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3, input4 := input4, input5 := input5, input6 := input6 }

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3 input4 input5 input6)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3 input4 input5 input6) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3 input4 input5 input6) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : validatorArtifacts.Statement model :=
  PublicView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3 }

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))), values = (statement input0 input1 input2 input3) := by subject_abi_surjective

abbrev StatementData := PublicView.View model.Value

def statementData (values : validatorArtifacts.Statement model) : StatementData := PublicView.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := PublicView.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := PublicView.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := PublicView.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1 input2 input3) subject.publicBindingArity subject.publicBindingData

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input4⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1 input2 input3)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2 input3 input4) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1 input2 input3) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3 input4 input5 input6) = some ((producerInputs input0 input1 input2 input3 input4), (validatorInputs input0 input1 input2 input3)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3 input4 input5 input6) (by rfl)
    [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input4⟩] [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input2⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input3⟩] (statement input0 input1 input2 input3)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4), (validatorInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3))) := by
  rw [Subject.runtime_layout subject values ([0, 1, 2, 3, 4]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4)
  validator := fun data => (validatorInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3)
  preparation := preparation
  producerSorts := fun data => producer_sorts (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3 (SourceView.unpack data).input4
  validatorSorts := fun data => validator_sorts (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2 (SourceView.unpack data).input3

theorem source_clauses (values : subject.Inputs) :
    ∀ index isInput, subject.inputClause values index isInput :=
  Subject.no_input_clauses subject (by decide +kernel) values

set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input3 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input4 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input5 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input6 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3 input4 input5 input6) ↔ (True) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) (some input2) (some input3) (some input4) input5 input6) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs, SourceView.pack]

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

theorem context_eq : subject.selection.context = (Context.fiatShamir ("s7h6578616d706c6515h53657175656e7469616c5369676d61") (["role00000000", "role00000001"]) 0 1 6 ("random.bls12-381.fr/0") (some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" }) ("merlin3.bls12-381.fr64be/0") ([("apply_2_s0_label_6368616c6c656e6765", "apply_2_s0_label_64656c6976657279_0"),  ("apply_2_s2_label_6368616c6c656e6765", "apply_2_s2_label_64656c6976657279_0")])) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:237ba35f3d71a8e9f6178f2935229003e7c88095d46bb8ae4e3048b1403cda24") := rfl
theorem producer_export : subject.producerExport = ("sha256:5c63a7f05f75933feea15973ca2dbd8f6c628cfca17d10f576aea3d815c56534") := rfl
theorem validator_export : subject.validatorExport = ("sha256:743b0334c6f98b2abd0cd04e0fa70d1c82847a662fa8f407cfef8421b0d70913") := rfl

end ZkcSecurity.Examples.Generated.Components.SequentialSigmaABI
