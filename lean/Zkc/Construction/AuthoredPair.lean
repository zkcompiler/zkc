module

public import Zkc.Construction.Compiled
public import Zkc.Construction.AuthoredPairProducer
public import Zkc.Construction.SourceOccurrences

@[expose] public section

/-! Request-owned selection of actual compiled artifacts. Association checks
complete instruction trees, not their digest strings. The original snapshot is
an index: helper interpretation cannot be replaced independently. Admission
includes the existing validator construction/projection theorem. It does not
assert the still separate producer compilation or domain transport theorem.
-/
set_option autoImplicit false
namespace Zkc.Construction.AuthoredPair
open Zkc.Source Zkc.Source.Structured

structure Artifacts where
  producer : Participant
  validator : Participant
  deriving DecidableEq, Repr

/-- The source part of the honest-input contract. Additional experiment shape
conditions must be fixed by the request before evidence, not selected by a
proof. This record does not invent a source precondition. -/
structure InputContract where
  preconditions : List Bound
  clauses : List ContractClause
  deriving DecidableEq, Repr

def inputContract (original : Snapshot) : Option InputContract := do
  let .function entry ← original.definitions.find? (·.name == original.entry) | none
  let contract ← original.contracts.find? (·.owner == original.entry)
  return ⟨entry.preconditions, contract.clauses.filter (·.kind == .input)⟩

/-- Fixed by the subject/request, before any proof method runs. Whole artifacts
pin the registered producer and validator bodies, signatures and returned
references. The snapshot index fixes every helper body and relation formula.
Symbols select entries; symbols and hashes alone do not provide correspondence.
-/
structure Selection (original : Snapshot) where
  artifacts : Artifacts
  policy : Policy
  producerSymbol : String
  validatorSymbol : String
  inputs : InputContract
  target : ContractClause
  deriving DecidableEq, Repr

def roleInputSorts (original : Snapshot) (role : String) : Option (List ValueSort) := do
  let (inputs, interface) ← entryInterface original
  (dataInputs inputs interface.inputScopes role).mapM fun index =>
    (inputs[index]? >>= dataSort?).map ValueSort.data

def roleOutputSorts (original : Snapshot) (role : String) : Option (List ValueSort) := do
  let (_, interface) ← entryInterface original
  let (outputs, _) ← entryOutputs original
  (roleOutputs interface.outputScopes role).mapM fun index =>
    (outputs[index]? >>= dataSort?).map ValueSort.data

/-- Deterministic association with the independently fixed request. It does
not treat a new self-consistent pair as the selected pair. -/
def associated {original : Snapshot} (selected : Selection original) (actual : Artifacts) : Bool :=
  actual == selected.artifacts

/-- Exact source/role/input/target association. Successful compilation is not
inferred from any of these metadata checks. -/
def selectionValid {original : Snapshot} (selected : Selection original) : Bool :=
  let p := selected.artifacts.producer
  let v := selected.artifacts.validator
  let policy := selected.policy
  p.source == original.source && v.source == original.source &&
  Format.digestValid p.candidate && p.candidate == v.candidate &&
  p.policy == policy && v.policy == policy && policy.entry == original.entry &&
  policy.producer != policy.validator &&
  p.symbol == selected.producerSymbol && v.symbol == selected.validatorSymbol &&
  p.symbol != v.symbol &&
  SourceOccurrences.servicePorts original policy policy.producer == some p.servicePorts &&
  SourceOccurrences.servicePorts original policy policy.validator == some v.servicePorts &&
  inputContract original == some selected.inputs &&
  original.contracts.any (fun contract => contract.owner == original.entry &&
    contract.clauses.contains selected.target) &&
  selected.target.kind == .target && selected.target.residual == none &&
  selected.target.decision == some ⟨.output, policy.acceptance, policy.validator⟩ &&
  roleInputSorts original policy.producer == some (policy.dataPorts p.inputs) &&
  roleOutputSorts original policy.producer == some (policy.dataPorts p.outputs) &&
  (if policy.suite = "" then true else
    p.inputs.getLast? == some (.transcript policy.suite) &&
    p.outputs.getLast? == some (.transcript policy.suite))

/-- Construct the selection before proof search from an explicit retained
target name. Ambiguous, missing or changed targets refuse. -/
def select (original : Snapshot) (actual : Artifacts) (targetName : String) :
    Except String (Selection original) := do
  let some inputs := inputContract original | throw "authored-pair-input-contract"
  let targets := original.contracts.flatMap fun contract =>
    if contract.owner == original.entry then
      contract.clauses.filter (fun clause => clause.kind == .target && clause.name == targetName)
    else []
  let [target] := targets | throw "authored-pair-target"
  let selected : Selection original := ⟨actual, actual.validator.policy,
    actual.producer.symbol, actual.validator.symbol, inputs, target⟩
  if selectionValid selected then return selected else throw "authored-pair-selection"

def check {original : Snapshot} (imported : Imported original)
    (selected : Selection original) (actual : Artifacts) : Except String Unit :=
  if associated selected actual then
    if selectionValid selected then
      match exportContext original actual.validator with
      | some context =>
          match checkProducer imported.program context actual.producer with
          | .ok () =>
              match SourceOccurrences.check original context actual.producer with
              | .ok () =>
                  match SourceOccurrences.check original context actual.validator with
                  | .ok () => checkCompiled imported actual.validator
                  | .error error => .error error
              | .error error => .error error
          | .error error => .error error
      | none => .error "authored-pair-context"
    else .error "authored-pair-selection"
  else .error "authored-pair-artifacts"

/-- Admission contains a checked association and the original validator rule;
it is deliberately not a completeness certificate. -/
structure Admitted {original : Snapshot} (imported : Imported original)
    (selected : Selection original) (actual : Artifacts) : Prop where
  checked : check imported selected actual = .ok ()

theorem associated_iff {original : Snapshot} (selected : Selection original) (actual : Artifacts) :
    associated selected actual = true ↔ actual = selected.artifacts := by
  simp [associated]

theorem admitted_artifacts {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) : actual = selected.artifacts := by
  have h := admitted.checked
  unfold check at h
  split at h
  · rename_i accepted
    exact (associated_iff selected actual).mp accepted
  · cases h

theorem admitted_selection {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) : selectionValid selected = true := by
  have checked := admitted.checked
  unfold check at checked
  split at checked
  · split at checked
    · assumption
    · cases checked
  · cases checked

theorem admitted_validator_policy {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) :
    selected.artifacts.validator.policy = selected.policy := by
  have valid := admitted_selection admitted
  simp only [selectionValid, Bool.and_eq_true, beq_iff_eq] at valid
  tauto

/-- Admission authenticates both complete interfaces, including unused ports.
The existing validator rule separately refuses local service operations. -/
theorem admitted_servicePorts {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) :
    SourceOccurrences.servicePorts original selected.policy selected.policy.producer =
        some actual.producer.servicePorts ∧
      SourceOccurrences.servicePorts original selected.policy selected.policy.validator =
        some actual.validator.servicePorts := by
  rw [admitted_artifacts admitted]
  have valid := admitted_selection admitted
  simp only [selectionValid, Bool.and_eq_true, beq_iff_eq] at valid
  tauto

theorem admitted_validator {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) :
    checkCompiled imported actual.validator = .ok () := by
  have h := admitted.checked
  unfold check at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · exact h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Expose the structural producer obligation and its exact selected context.
This is a checker result, not a source compilation equivalence. -/
theorem admitted_producer {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) :
    ∃ context, exportContext original actual.validator = some context ∧
      checkProducer imported.program context actual.producer = .ok () := by
  have h := admitted.checked
  unfold check at h
  split at h
  · split at h
    · split at h
      · rename_i context found
        split at h
        · rename_i checked
          exact ⟨context, found, checked⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem admitted_occurrences {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) :
    ∃ context, exportContext original actual.validator = some context ∧
      SourceOccurrences.check original context actual.producer = .ok () ∧
      SourceOccurrences.check original context actual.validator = .ok () := by
  have h := admitted.checked
  unfold check at h
  split at h
  · split at h
    · split at h
      · rename_i context found
        split at h
        · split at h
          · rename_i producerOccurrences
            split at h
            · rename_i validatorOccurrences
              exact ⟨context, found, producerOccurrences, validatorOccurrences⟩
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

end Zkc.Construction.AuthoredPair
