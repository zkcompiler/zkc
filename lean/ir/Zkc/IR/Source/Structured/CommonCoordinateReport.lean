module

public import Zkc.IR.Source.Structured.CommonCoordinateCheck

@[expose] public section

/-! The finite requirement inventory is extracted from the checked structural witness.
Every value requirement names an actual root definition and port. Counter requirements
are reached-context requirements, never assertions that peer repeat counts are equal. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

structure Selection where
  scope : Scope
  inputs : List Ty
  roles : Nat → Nat
  cursor : Cursor
  origins : Origins scope
  kind : OracleKind
  maximum : Nat
  selected : List Nat
  location : OracleLocation
  operands : Operands inputs [.oracleSequence kind maximum, .index]
  environment : Symbols scope inputs
  term : Expression scope .index
  read : environment.get (operands.get (.there .here)) = some term

/-- Binder identity is preserved separately from its host carrier or observation class. -/
def originList {scope : Scope} : Origins scope → List Binding
  | .nil => []
  | .cons origin rest => origin :: originList rest

theorem originList_lookup {scope : Scope} (origins : Origins scope)
    {slot : Slot} (position : Var scope slot) :
    (originList origins)[position.index]? = some (origins.get position) := by
  induction origins with
  | nil => cases position
  | cons origin rest ih => cases position with
    | here => rfl
    | there position => exact ih position

def Selection.requirements (selection : Selection) : List Binding :=
  (demanded selection.term).filterMap fun position ↦ (originList selection.origins)[position]?

/-- Inventory extraction cannot silently discard a demanded typed binder. -/
theorem Selection.demanded_requirement (selection : Selection)
    {slot : Slot} (position : Var selection.scope slot)
    (member : position.index ∈ demanded selection.term) :
    selection.origins.get position ∈ selection.requirements := by
  exact List.mem_filterMap.mpr ⟨position.index, member, originList_lookup _ position⟩

/-- Coordinate evidence only; no data/handle or provider relation is stored here. -/
def atSelection {scope : Scope} {inputs : List Ty} (pair : Pair) (roles : Nat → Nat)
    (cursor : Cursor) (origins : Origins scope) (kind : OracleKind) (maximum : Nat)
    (selected : List Nat) (location : OracleLocation)
    (operands : Operands inputs [.oracleSequence kind maximum, .index])
    (env : Symbols scope inputs)
    (checked : supported pair roles (.oracle (.sequenceAt kind maximum selected) location)
      (operands.eval env.get) = true) : List Selection :=
  if active : pair.selected roles selected = true then
    match known : env.get (operands.get (.there .here)) with
    | none => False.elim (by
        change (!(pair.selected roles selected) ||
          ((operands.eval env.get).get (.there .here)).isSome) = true at checked
        have absent : ((operands.eval env.get).get (.there .here)).isSome = false := by
          rw [Operands.get_eval, known]
          rfl
        simp only [active, absent, Bool.not_true, Bool.false_or, Bool.false_eq_true] at checked)
    | some term => [⟨scope, inputs, roles, cursor, origins, kind, maximum, selected,
        location, operands, env, term, known⟩]
  else []

def Plan.selections {snapshot : Snapshot} {definitions : List CheckedProtocol} {pair : Pair}
    {scope : Scope} {inputs outputs : List Ty} {roles : Nat → Nat} {cursor : Cursor}
    {origins : Origins scope} {body : Region protocolDialect inputs outputs}
    {env : Symbols scope inputs} (plan : Plan snapshot definitions pair roles cursor origins body env) :
    List Selection :=
  match plan with
  | .ret | .stop => []
  | @Plan.step _ _ _ _ _ _ roles cursor origins op args _ _ env _ _ checked tail =>
    (match op, args, checked with
    | .oracle (.sequenceAt kind maximum selected) location, args, checked =>
      atSelection pair roles cursor origins kind maximum selected location args env checked
    | _, _, _ => []) ++ tail.selections
  | .bind inside tail => inside.selections ++ tail.selections
  | .apply _ _ _ inside tail => inside.selections ++ tail.selections
  | .repeat inside tail => inside.selections ++ tail.selections
termination_by structural plan

def PlansFor.selections {snapshot : Snapshot} {definitions : List CheckedProtocol}
    {definition : CheckedProtocol} {pairs : List Pair}
    (plans : PlansFor snapshot definitions definition pairs) : List (Pair × Selection) :=
  match plans with
  | .nil => []
  | @PlansFor.cons _ _ _ pair _ head tail =>
    (head.selections.map (fun selection ↦ (pair, selection))) ++ tail.selections

def UnitCertificate.selections {snapshot : Snapshot} {definitions remaining : List CheckedProtocol}
    (certificate : UnitCertificate snapshot definitions remaining) : List (Pair × Selection) :=
  match certificate with
  | .nil => []
  | .cons head tail => head.selections ++ tail.selections

end Zkc.Source.Structured.CommonCoordinate
