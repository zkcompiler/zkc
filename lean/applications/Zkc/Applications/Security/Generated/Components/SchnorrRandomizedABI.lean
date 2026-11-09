module

public import Zkc.Applications.Security.Generated.SchnorrRandomized
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
namespace ZkcSecurity.Examples.Generated.Components.SchnorrRandomizedABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI
open ZkcSecurity.Examples.Generated.SchnorrRandomized

abbrev model := subject.domainModel
named_values SourceView [input0, input1, input2, input3, input4] := subject.target.owner.protocol.inputs

named_values PublicView [input0, input1] := validatorArtifacts.publics

abbrev RawInputs := SourceView.View (Component model.Value)
abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs
abbrev DataFields := SourceView.View (TypedABI.Slot Domain.dataType model.Value)

def fields (values : Data) : DataFields := SourceView.unpack values
def fromFields (fields : DataFields) : Data := SourceView.pack fields

theorem fromFields_fields (values : Data) : fromFields (fields values) = values :=
  SourceView.pack_unpack values

theorem fields_fromFields (record : DataFields) : fields (fromFields record) = record :=
  SourceView.unpack_pack record

theorem source_types : subject.target.owner.protocol.inputs = ([Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.group "bls12-381.g1",  Zkc.Source.Structured.Ty.field "bls12-381.fr",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0",  Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"]) := rfl
theorem public_positions : selected.policy.publicInputs = ([0, 1]) := rfl
theorem public_types : validatorArtifacts.publics = ([Zkc.Source.Structured.Ty.group "bls12-381.g1", Zkc.Source.Structured.Ty.group "bls12-381.g1"]) := rfl
theorem target_positions : selectorPositions subject.target.application.selectors = .ok ([0, 1, 2]) := rfl
theorem artifact_identities :
    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = (("sha256:e0e6520563aadb939aaac48414f14606e424c87e3c4f63d287e31479eb6f4d13",  "sha256:541268dea4cc1b1af6210452e2da74d30a261e09fa9cc7df43b96ec372d36e6e",  "_math_0")) ∧
    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = (("sha256:e0e6520563aadb939aaac48414f14606e424c87e3c4f63d287e31479eb6f4d13",  "sha256:541268dea4cc1b1af6210452e2da74d30a261e09fa9cc7df43b96ec372d36e6e",  "_math_1")) := by decide +kernel

def sourceInputs (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  SourceView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3, input4 := input4 }

def data (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : Data :=
  SourceView.pack { input0 := input0, input1 := input1, input2 := input2, input3 := input3, input4 := input4 }

def inputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) : subject.Inputs :=
  TypedABI.optional Domain.dataType (data input0 input1 input2 input3 input4)

theorem sourceInputs_surjective (values : subject.Inputs) :
    ∃ (input0 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : Option (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : Option (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (sourceInputs input0 input1 input2 input3 input4) := by subject_abi_surjective

theorem data_surjective (values : Data) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (data input0 input1 input2 input3 input4) := by subject_abi_surjective

def statement (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : validatorArtifacts.Statement model :=
  PublicView.pack { input0 := input0, input1 := input1 }

theorem statement_surjective (values : validatorArtifacts.Statement model) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))), values = (statement input0 input1) := by subject_abi_surjective

abbrev StatementData := PublicView.View model.Value

def statementData (values : validatorArtifacts.Statement model) : StatementData := PublicView.unpack values
def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := PublicView.pack fields

theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :
    statementOfData (statementData values) = values := PublicView.pack_unpack values

theorem statementData_statementOfData (fields : StatementData) :
    statementData (statementOfData fields) = fields := PublicView.unpack_pack fields

def initialHistory (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (statement input0 input1) subject.publicBindingArity subject.publicBindingData

def producerInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input2⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1)]

def validatorInputs (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) : Domain.Environment model.toCarriers :=
  [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .transcript ("merlin3.bls12-381.fr64be/0") (initialHistory input0 input1)]

theorem producer_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) :
    Domain.sortsMatch selected.artifacts.producer.inputs (producerInputs input0 input1 input2) = true := rfl

theorem validator_sorts (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) :
    Domain.sortsMatch selected.artifacts.validator.inputs (validatorInputs input0 input1) = true := rfl

theorem runtimeInputs_eq (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.runtimeInputs (inputs input0 input1 input2 input3 input4) = some ((producerInputs input0 input1 input2), (validatorInputs input0 input1)) := by
  exact Subject.runtime_of_projections subject (inputs input0 input1 input2 input3 input4) (by rfl)
    [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩, .data ⟨(Zkc.Source.Structured.Ty.field "bls12-381.fr"), by decide, input2⟩] [.data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input0⟩, .data ⟨(Zkc.Source.Structured.Ty.group "bls12-381.g1"), by decide, input1⟩] (statement input0 input1)
    (by rfl) (by rfl) (by rfl)

theorem preparation (values : subject.Inputs) :
    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map
      (fun (data : Data) => ((producerInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2), (validatorInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1))) := by
  rw [Subject.runtime_layout subject values ([0, 1, 2]) (by rfl)]
  subject_abi_options

def abi : Subject.ABI subject where
  Data := Data
  pack := TypedABI.optional Domain.dataType
  complete := TypedABI.complete Domain.dataType
  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType
  producer := fun data => (producerInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2)
  validator := fun data => (validatorInputs (SourceView.unpack data).input0 (SourceView.unpack data).input1)
  preparation := preparation
  producerSorts := fun data => producer_sorts (SourceView.unpack data).input0 (SourceView.unpack data).input1 (SourceView.unpack data).input2
  validatorSorts := fun data => validator_sorts (SourceView.unpack data).input0 (SourceView.unpack data).input1

theorem source_clauses (values : subject.Inputs) :
    ∀ index isInput, subject.inputClause values index isInput :=
  Subject.no_input_clauses subject (by decide +kernel) values

set_option backward.isDefEq.respectTransparency false in
theorem representable_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    inputsRepresentable (inputs input0 input1 input2 input3 input4) ↔ (True) := by
  change inputsRepresentable (sourceInputs (some input0) (some input1) (some input2) input3 input4) ↔ _
  simp [inputsRepresentable, inputRepresentable, sourceInputs, SourceView.pack]

theorem honestInput_iff (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.HonestInput (inputs input0 input1 input2 input3 input4) ↔ (True) := by
  exact (abi.honest_pack_iff (data input0 input1 input2 input3 input4)).trans
    ((and_iff_left (source_clauses _)).trans (representable_iff input0 input1 input2 input3 input4))

theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :
    ∃ (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))), values = (inputs input0 input1 input2 input3 input4) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists values honest
  subject_abi_surjective

def arguments (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) : Values model.Value subject.target.application.relation.declaration.inputs :=
  (.cons input0 (.cons input1 (.cons input2 .nil)))

theorem application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input2 : (model.Value (Zkc.Source.Structured.Ty.field "bls12-381.fr"))) (input3 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) (input4 : Option (model.Value (Zkc.Source.Structured.Ty.service "random.bls12-381.fr/0"))) :
    subject.target.application.read {} (subject.boundary (inputs input0 input1 input2 input3 input4))
      (subject.assignments (inputs input0 input1 input2 input3 input4)) = some (arguments input0 input1 input2) := rfl

def validatorArguments (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (witness : validatorSubject.Witness) :
    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=
  RoleFamily.sequence (.cons (some input0) (.cons (some input1) (.cons (witness _ (validatorSubject.target.application.selectors.get (.there (.there .here)))) .nil)))

theorem validator_application_read (input0 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (input1 : (model.Value (Zkc.Source.Structured.Ty.group "bls12-381.g1"))) (witness : validatorSubject.Witness) :
    validatorSubject.target.application.read {} (validatorSubject.boundary (statement input0 input1))
      (validatorSubject.assignments (statement input0 input1) witness) =
      (validatorArguments input0 input1 witness) := by
  rfl

theorem context_eq : subject.selection.context = (Context.fiatShamir ("zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad") (["role00000000", "role00000001"]) 0 1 4 ("random.bls12-381.fr/0") (some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" }) ("merlin3.bls12-381.fr64be/0") ([("label_6368616c6c656e6765", "label_64656c6976657279_0")])) := rfl

theorem pair_eq : selected.artifacts = artifacts := rfl

theorem original_export : subject.originalExport = ("sha256:b1d9b0d6d172578cf23ab89ace9c0188e11d937ef8c332257abc922fefd828e1") := rfl
theorem producer_export : subject.producerExport = ("sha256:5b30d9853dbba84a9dad0cddda1afa54009f9a80782c01eb713682b1d2576d85") := rfl
theorem validator_export : subject.validatorExport = ("sha256:34e9fc6980bda7ed3ee198856f30e2ecbcfb3bd5b5c9863ab2c1b9997cec0c35") := rfl

end ZkcSecurity.Examples.Generated.Components.SchnorrRandomizedABI
