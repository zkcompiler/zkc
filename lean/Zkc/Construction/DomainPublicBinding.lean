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

/-- Checked public schemas contain data only. This does not assert validity,
representability, canonical byte encoding or any relation. -/
def DataSchema (tys : List Ty) : Prop := tys.all dataType = true

/-- Mandatory arity prevents truncation, including when the last value is absent.
The fixed schema proof excludes capabilities without erasing raw invalid data. -/
def encodeRow : (positions : List Nat) → {tys : List Ty} → (values : Values carriers.Value tys) →
    positions.length = tys.length → DataSchema tys → List (Nat × Payload carriers)
  | [], [], .nil, _, _ => []
  | position :: positions, ty :: _, .cons value rest, arity, data =>
      (position, ⟨ty, by simpa [DataSchema, dataType] using (Bool.and_eq_true_iff.mp data).1, value⟩) ::
        encodeRow positions rest (by simpa using arity) (Bool.and_eq_true_iff.mp data).2

theorem encodeRow_injective : ∀ (positions : List Nat) {tys : List Ty}
    (arity : positions.length = tys.length) (data : DataSchema tys),
    Function.Injective (fun values : Values carriers.Value tys => encodeRow positions values arity data)
  | [], [], _, _, .nil, .nil, _ => rfl
  | position :: positions, ty :: _, arity, data, .cons value rest, .cons value' rest', same => by
      simp only [encodeRow, List.cons.injEq, Prod.mk.injEq, true_and, Payload.mk_inj] at same
      rw [same.1, encodeRow_injective positions (by simpa using arity)
        (Bool.and_eq_true_iff.mp data).2 same.2]

def history {tys : List Ty} (application : String) (positions : List Nat)
    (values : Values carriers.Value tys) (arity : positions.length = tys.length)
    (data : DataSchema tys) : History carriers :=
  [.publicBinding ⟨application, encodeRow positions values arity data⟩]

/-- Identity of applications is explicit, while typed determination is raw-all. -/
theorem history_eq_iff {tys : List Ty} (application other : String) (positions : List Nat)
    (arity : positions.length = tys.length) (data : DataSchema tys)
    (values values' : Values carriers.Value tys) :
    history application positions values arity data = history other positions values' arity data ↔
      application = other ∧ values = values' := by
  constructor
  · intro same
    have fields : application = other ∧ encodeRow positions values arity data = encodeRow positions values' arity data := by
      simpa [history] using same
    exact ⟨fields.1, encodeRow_injective positions arity data fields.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Decode at the admitted public ABI, then use the same typed constructor.
Exact decoding refuses missing/excess values and wrong nominal data types. -/
def fromEnvironment {tys : List Ty} (application : String) (positions : List Nat)
    (arity : positions.length = tys.length) (data : DataSchema tys)
    (environment : Environment carriers) : Option (History carriers) := do
  let values ← decodeValues tys environment
  return history application positions values arity data

theorem fromEnvironment_encodeValues {tys : List Ty} (values : Values carriers.Value tys)
    (application : String) (positions : List Nat) (arity : positions.length = tys.length)
    (data : DataSchema tys) {encoded : Environment carriers} (encoding : encodeValues values = some encoded) :
    fromEnvironment application positions arity data encoded =
      some (history application positions values arity data) := by
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
  exact checked.2.1.1.2.symm

/-- Public data eligibility is checked once at selection, independently of values. -/
theorem selectionData {original : Snapshot} (imported : Imported original)
    (participant : Participant) (selection : Selection imported.program.payload.entry.outputs)
    (checked : selection.check imported participant = true) : DataSchema selection.publics := by
  exact (Bool.and_eq_true_iff.mp checked).1

end Zkc.Construction.Domain.PublicBinding
