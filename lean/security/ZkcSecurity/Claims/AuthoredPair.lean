module

public import Zkc.Construction.DomainPublicBinding
public import Zkc.Construction.AuthoredPair
public import Zkc.Construction.RetainedTarget
public import Zkc.Source.Structured.DomainContract
public import Zkc.Construction.SourceOccurrences
public import Zkc.Construction.ConnectionAdmission
public import Zkc.Source.Structured.InputAdmission
public import ZkcSecurity.FiatShamir.HonestCompiled

@[expose] public section

/-! Source-owned honest inputs and request-fixed retained relation truth.
The registry, every input clause and the target are selected before evidence. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- All selections precede evidence. Exact artifacts, input clauses and target
come from core pair admission; the retained target supplies checked selectors
and the request fixes the relation meaning. The original export fixes the initial namespace. -/
structure Subject (model : DomainModel) (original : Snapshot) (imported : Imported original)
    (selected : Zkc.Construction.AuthoredPair.Selection original) where
  /-- Physical export identities selected by the request. Pipeline read-back
  checks these against bytes; source/candidate identities stay in the artifacts. -/
  originalExport : String
  producerExport : String
  validatorExport : String
  admitted : Zkc.Construction.AuthoredPair.Admitted imported selected selected.artifacts
  selection : Zkc.Construction.Selection imported.program.payload.entry.outputs
  selectionExact : select imported selected.artifacts.validator = some selection
  selectionChecked : selection.check imported selected.artifacts.validator = true
  producerOccurrences : SourceOccurrences.check original selection.context selected.artifacts.producer = .ok ()
  validatorOccurrences : SourceOccurrences.check original selection.context selected.artifacts.validator = .ok ()
  /-- Role connections share one fixed source; each missing proof is reported
  as an open required link, independently of mathematical property evidence. -/
  producerConnection : Option (PLift (ConnectionAdmission.Required imported.program
    selection.context .producer selected.artifacts.producer)) := none
  validatorConnection : Option (PLift (ConnectionAdmission.Required imported.program
    selection.context .validator selected.artifacts.validator)) := none
  target : RetainedTarget imported selected.policy selection.publics
  relations : RegisteredRelations model.Value original.relations
  meaning : RelationMeaning imported target.application.relation model.Value relations.registry
  targetExact : target.owner.clause target.clauseIndex = selected.target
  inputContractExact : Zkc.Construction.AuthoredPair.inputContract original = some selected.inputs
  inputClausesExact : selected.inputs.clauses = target.owner.contract.clauses.filter (·.kind == .input)
  /-- Protocol entries currently have no index-bound preconditions. Refuse a
  future unsupported contract rather than silently dropping it. -/
  preconditionsEmpty : selected.inputs.preconditions = []
  inputMeanings : (index : Fin target.owner.contract.clauses.length) →
    (target.owner.clause index).kind = .input →
      RetainedClause imported target.owner (target.owner.clause index).subject model.Value relations.registry

namespace Subject
variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : Zkc.Construction.AuthoredPair.Selection original}

/-- Public source-coordinate arity comes from the checked admitted selection. -/
theorem publicBindingArity (subject : Subject model original imported selected) :
    selected.policy.publicInputs.length = subject.selection.publics.length := by
  rw [← Zkc.Construction.AuthoredPair.admitted_validator_policy subject.admitted]
  exact Domain.PublicBinding.selectionArity imported selected.artifacts.validator
    subject.selection subject.selectionChecked

/-- Capabilities are excluded by the checked public schema, before values arrive. -/
theorem publicBindingData (subject : Subject model original imported selected) :
    Domain.PublicBinding.DataSchema subject.selection.publics :=
  Domain.PublicBinding.selectionData imported selected.artifacts.validator
    subject.selection subject.selectionChecked

abbrev Inputs (subject : Subject model original imported selected) :=
  Values (Component model.Value) subject.target.owner.protocol.inputs

def boundary (subject : Subject model original imported selected) (inputs : subject.Inputs) :
    BoundaryValuation model.Value subject.target.owner.protocol.inputs subject.target.owner.protocol.outputs :=
  ⟨fun self => maskValues self subject.target.owner.protocol.inputScopes inputs,
    fun _ => Values.absent model.Value _⟩

def assignments (subject : Subject model original imported selected) (inputs : subject.Inputs) :
    LogicalAssignments model.Value subject.target.owner ⟨subject.target.owner.protocolIndex.val, []⟩ :=
  ⟨fun _ selector => selector.read {} (subject.boundary inputs),
    fun _ selector => selector.read {} (subject.boundary inputs)⟩

/-- The selected meaning reads the same source inputs as both participants. -/
def Relation (subject : Subject model original imported selected) (inputs : subject.Inputs) : Prop :=
  (subject.target.clause subject.meaning).Holds {} (subject.boundary inputs) (subject.assignments inputs)

def inputClause (subject : Subject model original imported selected) (inputs : subject.Inputs)
    (index : Fin subject.target.owner.contract.clauses.length)
    (isInput : (subject.target.owner.clause index).kind = .input) : Prop :=
  (subject.inputMeanings index isInput).Holds {} (subject.boundary inputs) (subject.assignments inputs)

/-- Formula targets retain precisely their previous authored-pair meaning. -/
theorem relation_formula_iff (subject : Subject model original imported selected)
    (binding : FormulaBinding imported subject.target.application.relation) (inputs : subject.Inputs) :
    subject.Relation inputs ↔
      ∃ arguments, subject.target.application.read {} (subject.boundary inputs)
        (subject.assignments inputs) = some arguments ∧
        binding.invokeRelationOn model arguments =
          .done (subject.target.booleanOutput.symm ▸ Values.cons true .nil) :=
  exists_congr fun arguments => and_congr Iff.rfl
    (subject.meaning.formula_exact binding subject.target.booleanOutput arguments)

/-- Every original input formula keeps its actual selector read and invocation. -/
theorem inputClause_formula_iff (subject : Subject model original imported selected)
    (inputs : subject.Inputs) (index : Fin subject.target.owner.contract.clauses.length)
    (isInput : (subject.target.owner.clause index).kind = .input)
    (binding : FormulaBinding imported (subject.inputMeanings index isInput).binding.relation) :
    subject.inputClause inputs index isInput ↔
      ∃ arguments, (subject.inputMeanings index isInput).binding.read {} (subject.boundary inputs)
        (subject.assignments inputs) = some arguments ∧ binding.invokeRelationOn model arguments =
          .done ((subject.inputMeanings index isInput).booleanOutput.symm ▸ Values.cons true .nil) :=
  exists_congr fun arguments => and_congr Iff.rfl
    ((subject.inputMeanings index isInput).meaning.formula_exact binding _ arguments)

/-- Source positions are retained even for absent values and service handles.
Dropping an absent input must not shift later public or witness coordinates. -/
def encodeInputs {carriers : Carriers} : {types : List Ty} →
    Values (Component carriers.Value) types → List (Option (Domain.Value carriers))
  | [], .nil => []
  | type :: _, .cons value rest => (value >>= Domain.Value.encode type) :: encodeInputs rest

def project {carriers : Carriers} (encoded : List (Option (Domain.Value carriers)))
    (positions : List Nat) : Option (Domain.Environment carriers) :=
  positions.mapM fun index => encoded[index]? >>= id

/-- The source ABI fixes both projections. A public binding contains the
actual nominal payloads and source positions, before either phase queries. -/
def runtimeInputs (subject : Subject model original imported selected) (inputs : subject.Inputs) :
    Option (Domain.Environment model.toCarriers × Domain.Environment model.toCarriers) := do
  let (types, interface) ← entryInterface original
  let encoded := encodeInputs inputs
  let producer ← project encoded (dataInputs types interface.inputScopes selected.policy.producer)
  let validator ← project encoded selected.policy.publicInputs
  match subject.selection.context.profile with
  | .plain => return (producer, validator)
  | .fiatShamir _ =>
      let history ← Domain.PublicBinding.fromEnvironment subject.originalExport
        selected.policy.publicInputs subject.publicBindingArity subject.publicBindingData validator
      return (Domain.inputFrame subject.selection.context producer history,
        Domain.inputFrame subject.selection.context validator history)

/-- The source clauses and executable ABI admission facts fix honest inputs.
The selected relation is the separate `Relation` premise of completeness.
Both participants are prepared from this same ordered source tuple, so shared
role copies cannot disagree. Failure inside this domain remains failure. -/
def HonestInput (subject : Subject model original imported selected) (inputs : subject.Inputs) : Prop :=
  inputsRepresentable inputs ∧
    (∀ index isInput, subject.inputClause inputs index isInput) ∧
    ∃ producer validator, subject.runtimeInputs inputs = some (producer, validator) ∧
      Domain.sortsMatch selected.artifacts.producer.inputs producer = true ∧
      Domain.sortsMatch selected.artifacts.validator.inputs validator = true

/-- Exact preservation of the complete formula-only honest-input domain,
including all actual clauses, representability and both executable ABIs. -/
theorem honestInput_formula_iff (subject : Subject model original imported selected)
    (bindings : (index : Fin subject.target.owner.contract.clauses.length) →
      (isInput : (subject.target.owner.clause index).kind = .input) →
      FormulaBinding imported (subject.inputMeanings index isInput).binding.relation)
    (inputs : subject.Inputs) :
    subject.HonestInput inputs ↔
      inputsRepresentable inputs ∧
        (∀ index isInput, ∃ arguments,
          (subject.inputMeanings index isInput).binding.read {} (subject.boundary inputs)
            (subject.assignments inputs) = some arguments ∧
          (bindings index isInput).invokeRelationOn model arguments =
            .done ((subject.inputMeanings index isInput).booleanOutput.symm ▸ Values.cons true .nil)) ∧
        ∃ producer validator, subject.runtimeInputs inputs = some (producer, validator) ∧
          Domain.sortsMatch selected.artifacts.producer.inputs producer = true ∧
          Domain.sortsMatch selected.artifacts.validator.inputs validator = true :=
  and_congr Iff.rfl (and_congr (forall_congr' fun index => forall_congr' fun isInput =>
    subject.inputClause_formula_iff inputs index isInput (bindings index isInput)) Iff.rfl)

end Subject
end ZkcSecurity.Claims.HonestPair
