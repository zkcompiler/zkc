module

public import Zkc.Construction.DomainExecutionLaws
public import Zkc.Construction.Compiled

@[expose] public section

/-! One canonical typed public binding for constructed nominal-domain games.
Coordinates are source positions, and applications are selected by the request.
Arity is checked before a runtime row is accepted and proved for typed rows.
No shape restriction or native byte correspondence is asserted here. -/
set_option autoImplicit false
namespace Zkc.Construction.Domain.PublicBinding
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

def publicValue : (ty : Ty) → carriers.Value ty → PublicValue (Payload carriers)
  | .boolean, value => .scalar (.boolean value)
  | .index, value => .count value
  | .field domain, value => .scalar (.field domain value)
  | .vector domain, values => .vector (values.map (.field domain))
  | .group domain, value => .scalar (.group domain value)
  | .service _, handle => .count handle

theorem publicValue_injective : ∀ ty : Ty,
    Function.Injective (publicValue (carriers := carriers) ty)
  | .boolean, _, _, same => by simpa [publicValue] using same
  | .index, _, _, same => by simpa [publicValue] using same
  | .field _, _, _, same => by simpa [publicValue] using same
  | .vector _, _, _, same => by
      simp only [publicValue, PublicValue.vector.injEq] at same
      exact (List.map_inj_right (fun _ _ equal => by cases equal; rfl)).mp same
  | .group _, _, _, same => by simpa [publicValue] using same
  | .service _, _, _, same => by simpa [publicValue] using same

/-- Mandatory arity prevents truncation, including when the last value is absent. -/
def row : (positions : List Nat) → {tys : List Ty} → (values : Values carriers.Value tys) →
    positions.length = tys.length → Row (Payload carriers)
  | [], [], .nil, _ => []
  | position :: positions, _ :: _, .cons value rest, arity =>
      (decimal position, publicValue _ value) :: row positions rest (by simpa using arity)

theorem row_injective : ∀ (positions : List Nat) {tys : List Ty}
    (arity : positions.length = tys.length),
    Function.Injective (fun values : Values carriers.Value tys => row positions values arity)
  | [], [], _, .nil, .nil, _ => rfl
  | position :: positions, ty :: _, arity, .cons value rest, .cons value' rest', same => by
      simp only [row, List.cons.injEq, Prod.mk.injEq, true_and] at same
      rw [publicValue_injective ty same.1,
        row_injective positions (by simpa using arity) same.2]

def history {tys : List Ty} (application : String) (positions : List Nat)
    (values : Values carriers.Value tys) (arity : positions.length = tys.length) : History carriers :=
  [.publicBinding ⟨application, row positions values arity⟩]

/-- Identity of applications is explicit, while typed determination is raw-all. -/
theorem history_eq_iff {tys : List Ty} (application other : String) (positions : List Nat)
    (arity : positions.length = tys.length) (values values' : Values carriers.Value tys) :
    history application positions values arity = history other positions values' arity ↔
      application = other ∧ values = values' := by
  constructor
  · intro same
    have fields : application = other ∧ row positions values arity = row positions values' arity := by
      simpa [history] using same
    exact ⟨fields.1, row_injective positions arity fields.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Decode at the admitted public ABI, then use the same typed constructor.
Exact decoding refuses missing/excess values and wrong nominal data types. -/
def fromEnvironment {tys : List Ty} (application : String) (positions : List Nat)
    (arity : positions.length = tys.length) (environment : Environment carriers) :
    Option (History carriers) := do
  let values ← decodeValues tys environment
  return history application positions values arity

theorem fromEnvironment_encodeValues {tys : List Ty} (values : Values carriers.Value tys)
    (application : String) (positions : List Nat) (arity : positions.length = tys.length)
    {encoded : Environment carriers} (encoding : encodeValues values = some encoded) :
    fromEnvironment application positions arity encoded =
      some (history application positions values arity) := by
  simp [fromEnvironment, decodeValues_encodeValues encoding]

/-- Preserve every original input coordinate, including absent private/service inputs. -/
def optionalInputs : {tys : List Ty} → Values (Component carriers.Value) tys →
    List (Option (Value carriers))
  | [], .nil => []
  | ty :: _, .cons value rest => (value >>= Value.encode ty) :: optionalInputs rest

def project (encoded : List (Option (Value carriers))) (positions : List Nat) :
    Option (Environment carriers) := positions.mapM fun index => encoded[index]? >>= id

theorem optionalInputs_at {tys : List Ty} (inputs : Values (Component carriers.Value) tys)
    (index : Nat) (ty : Ty) (value : Value carriers)
    (typed : tys[index]? = some ty)
    (present : (optionalInputs inputs)[index]? >>= id = some value) :
    ∃ input : carriers.Value ty, Value.encode ty input = some value := by
  induction inputs generalizing index ty with
  | nil => simp at typed
  | @cons headTy tys head rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at typed
          subst ty
          cases head with
          | none => simp [optionalInputs] at present
          | some input => exact ⟨input, by simpa [optionalInputs] using present⟩
      | succ index =>
          exact ih index ty (by simpa using typed) (by simpa [optionalInputs] using present)

/-- Source projection recovers the exact typed raw statement. The arity equation
rules out out-of-range metadata; no honest shape assumption is needed. -/
theorem project_statement {tys : List Ty} (inputs : Values (Component carriers.Value) tys)
    (positions : List Nat) (environment : Environment carriers)
    (arity : (positions.filterMap (tys[·]?)).length = positions.length)
    (projected : project (optionalInputs inputs) positions = some environment) :
    ∃ values : Values carriers.Value (positions.filterMap (tys[·]?)),
      encodeValues values = some environment := by
  induction positions generalizing environment with
  | nil =>
      have same : environment = [] := by simpa [project] using projected.symm
      subst environment
      exact ⟨.nil, rfl⟩
  | cons position positions ih =>
      cases typed : tys[position]? with
      | none =>
          have bound := List.length_filterMap_le (tys[·]?) positions
          simp [typed] at arity
          omega
      | some ty =>
          rw [project, List.mapM_cons] at projected
          change ((optionalInputs inputs)[position]? >>= id).bind (fun value =>
            (project (optionalInputs inputs) positions).bind (fun rest => some (value :: rest))) =
            some environment at projected
          simp only [Option.bind_eq_some_iff] at projected
          obtain ⟨value, present, tail⟩ := projected
          obtain ⟨rest, projected, same⟩ := tail
          have same' : value :: rest = environment := by simpa using same
          subst environment
          obtain ⟨head, encoded⟩ := optionalInputs_at inputs position ty value typed present
          obtain ⟨values, encoding⟩ := ih rest (by simpa [typed] using arity) projected
          have encoding' : encodeValues (.cons head values) = some (value :: rest) := by
            simp [encodeValues, encoded, encoding]
          simp only [List.filterMap_cons]
          rw [typed]
          exact ⟨.cons head values, encoding'⟩

/-- Arity follows from the actual admitted selection, rather than a caller's guess. -/
theorem selectionArity {original : Snapshot} (imported : Imported original)
    (participant : Participant) (selection : Selection imported.program.payload.entry.outputs)
    (checked : selection.check imported participant = true) :
    participant.policy.publicInputs.length = selection.publics.length := by
  simp only [Selection.check, Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.1.1.2.symm

end Zkc.Construction.Domain.PublicBinding
