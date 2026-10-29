module

public import Zkc.Source.Structured.ContractBoundary
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Structural binding from retained references. These constructors recover
metadata only; formula adequacy and experiment choices remain separate goals.
Lookup rejects missing and ambiguous names before checking the complete ABI.
-/
namespace Zkc.Source.Structured

namespace ContractElaboration

/-- Resolve exactly one occurrence, including when duplicate rows are equal. -/
def uniqueIndex? {α : Type} (items : List α) (name : α → String) (reference : String) :
    Option (Fin items.length) :=
  match (List.finRange items.length).filter (fun i => name (items.get i) == reference) with
  | [index] => some index
  | _ => none

/-- A checked unique lookup; no default index is available on failure. -/
def uniqueIndex {α : Type} (items : List α) (name : α → String) (reference : String)
    (found : (uniqueIndex? items name reference).isSome) : Fin items.length :=
  (uniqueIndex? items name reference).get found

theorem uniqueIndex?_sound {α : Type} {items : List α} {name : α → String}
    {reference : String} {index : Fin items.length}
    (found : uniqueIndex? items name reference = some index) :
    name (items.get index) = reference ∧
      ∀ other, name (items.get other) = reference → other = index := by
  have filtered : (List.finRange items.length).filter
      (fun i => name (items.get i) == reference) = [index] := by
    unfold uniqueIndex? at found
    split at found <;> simp_all
  have member : index ∈ (List.finRange items.length).filter
      (fun i => name (items.get i) == reference) := by rw [filtered]; exact List.mem_cons_self
  constructor
  · simpa using (List.mem_filter.mp member).2
  · intro other same
    have member : other ∈ (List.finRange items.length).filter
        (fun i => name (items.get i) == reference) :=
      List.mem_filter.mpr ⟨by simp, by simpa only [beq_iff_eq] using same⟩
    rw [filtered] at member
    exact List.mem_singleton.mp member

def originalFunction? (snapshot : Snapshot) (reference : Option String) : Option Function := do
  let reference ← reference
  let index ← uniqueIndex? snapshot.definitions Definition.name reference
  match snapshot.definitions.get index with
  | .function original => some original
  | _ => none

/-- Recover the exact typed port and participant, including its declared scope. -/
def selector? (signature : ProtocolSignature) (type : Ty) (source : ContractSelector) :
    Option (BoundarySelector signature type) := do
  if source.anchor then none else pure ()
  let port ← match source.direction with
    | .input => (Var.decode signature.inputs type source.port).map BoundaryPort.input
    | .output => (Var.decode signature.outputs type source.port).map BoundaryPort.output
  let role ← uniqueIndex? signature.roles id source.role
  if scope : ((match port with
      | .input _ => signature.inputScopes
      | .output _ => signature.outputScopes)[port.index]?.getD []).contains role.val = true then
    some ⟨port, role, scope⟩
  else none

def selectors? (signature : ProtocolSignature) : (types : List Ty) →
    List ContractSelector → Option (Values (BoundarySelector signature) types)
  | [], [] => some .nil
  | type :: types, source :: sources => do
    let selector ← selector? signature type source
    let rest ← selectors? signature types sources
    some (.cons selector rest)
  | _, _ => none

end ContractElaboration

open ContractElaboration

/-- A component owner selected by its exact retained name. -/
def ContractBinding.ofName {snapshot : Snapshot} (imported : Imported snapshot) (name : String)
    (ownerFound : (uniqueIndex? snapshot.contracts ProtocolContract.owner name).isSome := by decide +kernel)
    (protocolFound : (uniqueIndex? imported.program.payload.protocols (fun p => p.name) name).isSome := by decide +kernel)
    (same : (snapshot.contracts.get (uniqueIndex _ _ _ ownerFound)).owner =
      (imported.program.payload.protocols.get (uniqueIndex _ _ _ protocolFound)).name := by rfl) :
    ContractBinding imported :=
  ⟨uniqueIndex _ _ _ ownerFound, uniqueIndex _ _ _ protocolFound, same⟩

/-- Recover the component at the admitted entry index. This does not select an
Entry proof target: a run Entry can have no statement selecting one. -/
def ContractBinding.ofEntry {snapshot : Snapshot} (imported : Imported snapshot)
    (found : (uniqueIndex? snapshot.contracts ProtocolContract.owner
      imported.program.payload.entry.name).isSome := by decide +kernel)
    (same : (snapshot.contracts.get (uniqueIndex _ _ _ found)).owner =
      imported.program.payload.entry.name := by rfl) : ContractBinding imported :=
  ⟨uniqueIndex _ _ _ found, imported.program.payload.entryIndex, same⟩

def ContractBinding.namedClause {snapshot : Snapshot} {imported : Imported snapshot}
    (owner : ContractBinding imported) (name : String)
    (found : (uniqueIndex? owner.contract.clauses ContractClause.name name).isSome := by decide +kernel) :
    Fin owner.contract.clauses.length := uniqueIndex _ _ _ found

def RelationBinding.ofSource {snapshot : Snapshot} (application : RelationApplication)
    (found : (uniqueIndex? snapshot.relations Relation.name application.relation).isSome := by decide +kernel)
    (same : (snapshot.relations.get (uniqueIndex _ _ _ found)).name = application.relation := by rfl) :
    RelationBinding snapshot application := ⟨uniqueIndex _ _ _ found, same⟩

/-- Resolve the application's retained relation and ordered selectors. The
original application remains an index of the result, so changes cannot be hidden. -/
def ApplicationBinding.ofSource {snapshot : Snapshot} {imported : Imported snapshot}
    (owner : ContractBinding imported) (application : RelationApplication)
    (relation : RelationBinding snapshot application := by exact RelationBinding.ofSource _)
    (found : (selectors? owner.protocol.signature relation.declaration.inputs application.selectors).isSome := by decide +kernel)
    (same : eraseSelectors ((selectors? owner.protocol.signature relation.declaration.inputs
      application.selectors).get found) = application.selectors := by rfl) :
    ApplicationBinding owner application :=
  ⟨relation, (selectors? _ _ _).get found, same⟩

/-- Follow the actual formula reference, then recover the original Function and
checked helper. Every kind and ABI equality remains an explicit checked field.
No operation tree is synthesized or copied, and no mathematical law is inferred. -/
def FormulaBinding.ofSource {snapshot : Snapshot} (imported : Imported snapshot)
    {application : RelationApplication} (relation : RelationBinding snapshot application)
    (found : (originalFunction? snapshot relation.declaration.formula).isSome := by decide +kernel)
    (member : Definition.function ((originalFunction? snapshot relation.declaration.formula).get found) ∈
      snapshot.definitions := by structured_mem)
    (formulaKind : relation.declaration.kind = "zkc.language.formula/0" := by rfl)
    (formulaName : relation.declaration.formula =
      some ((originalFunction? snapshot relation.declaration.formula).get found).name := by rfl)
    (mathKind : ((originalFunction? snapshot relation.declaration.formula).get found).kind = .math := by rfl)
    (inputs : ((originalFunction? snapshot relation.declaration.formula).get found).inputs =
      relation.declaration.inputs := by rfl)
    (outputs : ((originalFunction? snapshot relation.declaration.formula).get found).outputs =
      relation.declaration.outputs := by rfl)
    (helperFound : (uniqueIndex? imported.program.payload.definitions CheckedDefinition.name
      ((originalFunction? snapshot relation.declaration.formula).get found).name).isSome := by decide +kernel)
    (signature : (imported.program.payload.definitions.get (uniqueIndex _ _ _ helperFound)).helper =
      ⟨((originalFunction? snapshot relation.declaration.formula).get found).name, .math,
        relation.declaration.inputs, relation.declaration.outputs⟩ := by rfl) :
    FormulaBinding imported relation :=
  ⟨(originalFunction? _ _).get found, member, formulaKind, formulaName, mathKind,
    inputs, outputs, uniqueIndex _ _ _ helperFound, signature⟩

/-- Materialize only binding metadata constructors and finite indices. Retained
Functions and checked operation trees stay as projections from the source.
This avoids rerunning concrete table searches at every later selector read. -/
private meta partial def materializeBinding (source : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let source ← Lean.Meta.whnf source
  let mut args := source.getAppArgs
  let size := args.size
  let positions ← match source.getAppFn.constName? with
    | some ``Fin.mk =>
      let value ← Lean.Meta.whnf args[size - 2]!
      let some value := value.rawNatLit? | Lean.throwError "bind_contract: expected a concrete index"
      return Lean.mkAppN source.getAppFn (args.set! (size - 2) (Lean.mkNatLit value))
    | some ``ContractBinding.mk => pure [size - 3, size - 2]
    | some ``RelationBinding.mk => pure [size - 2]
    | some ``FormulaBinding.mk => pure [size - 2]
    | some ``ApplicationBinding.mk => pure [size - 3, size - 2]
    | some ``BoundarySelector.mk => pure [size - 3, size - 2]
    | some ``BoundaryPort.input | some ``BoundaryPort.output | some ``Var.there => pure [size - 1]
    | some ``Values.cons => pure [size - 2, size - 1]
    | some ``Values.nil | some ``Var.here => pure []
    | _ => Lean.throwError "bind_contract: unsupported metadata constructor {source}"
  for position in positions do
    args := args.set! position (← materializeBinding args[position]!)
  return Lean.mkAppN source.getAppFn args

/-- Construct only source-determined binding metadata. Semantic predicates and
adequacy laws are intentionally unsupported targets and remain ordinary goals. -/
elab "bind_contract" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← Lean.Elab.Tactic.getMainTarget
  let target ← Lean.Meta.whnf target
  let term ← match target.getAppFn.constName? with
  | some ``FormulaBinding =>
    `(FormulaBinding.ofSource _ _)
  | some ``ApplicationBinding =>
    `(ApplicationBinding.ofSource _ _)
  | some ``RelationBinding =>
    `(RelationBinding.ofSource _)
  | some ``ContractBinding =>
    `(ContractBinding.ofEntry _)
  | _ => Lean.throwError "bind_contract: expected FormulaBinding, ApplicationBinding, RelationBinding, or ContractBinding"
  let original ← Lean.Elab.Term.elabTermEnsuringType term target
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let generated ← materializeBinding original
  unless ← Lean.Meta.isDefEq original generated do
    Lean.throwError "bind_contract: materialized metadata differs from the source binding"
  (← Lean.Elab.Tactic.getMainGoal).assign generated
  Lean.Elab.Tactic.replaceMainGoal []

end Zkc.Source.Structured
