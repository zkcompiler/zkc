import Examples.TableProtocol.Language

/-! Immutable scalar storage for the physical-table reference. A deferred cell
retains its original residual and a checked point. Handles are interpreted in
the actual store, not identified with their logical scalar values.

This mathematical store has unbounded capacity and no native issuer identity.
It is a reference for realization, not a model of either Rust buffer allocator.
-/

set_option autoImplicit false
namespace TablePhysical
open TableProtocol Zkc.Polynomial

inductive Mode where | lazy | materialized deriving DecidableEq, Repr

inductive Cell (d : Domain) where
  | scalar (value : Field d)
  | deferred (rank : Nat) (view : Table.Residual (Field d) rank)
      (tail : List (Field d)) (shape : (view.coordinates ++ tail).length = rank)

def Cell.read {d : Domain} : Cell d → Field d
  | .scalar value => value
  | .deferred _ view tail shape => Table.atPoint view.root (view.coordinates ++ tail) shape

def Cell.cost {d : Domain} : Cell d → Nat
  | .scalar _ => 0
  | .deferred .. => 1

def cell (mode : Mode) {d : Domain} {n : Nat} (view : Table.Residual (Field d) n)
    (tail : List (Field d)) (shape : (view.coordinates ++ tail).length = n) : Cell d :=
  match mode with
  | .lazy => .deferred n view tail shape
  | .materialized => .scalar (Table.atPoint view.root (view.coordinates ++ tail) shape)

@[simp] theorem read_cell (mode : Mode) {d : Domain} {n : Nat}
    (view : Table.Residual (Field d) n) (tail : List (Field d))
    (shape : (view.coordinates ++ tail).length = n) :
    (cell mode view tail shape).read = Table.atPoint view.root (view.coordinates ++ tail) shape := by
  cases mode <;> rfl

abbrev Store := (d : Domain) → List (Cell d)
def empty : Store := fun _ => []
def read (store : Store) (d : Domain) (index : Nat) : Option (Field d) :=
  ((store d)[index]?).map Cell.read

def publish (store : Store) (d : Domain) (value : Cell d) : Store :=
  Function.update store d (store d ++ [value])

/-- Publication preserves every old successful read, in either domain. -/
theorem read_publish_old (store : Store) (d : Domain) (value : Cell d)
    (other : Domain) (index : Nat) (x : Field other) (old : read store other index = some x) :
    read (publish store d value) other index = some x := by
  by_cases same : other = d
  · subst other
    simp only [read, publish, Function.update_self] at *
    have within : index < (store d).length := by
      by_contra outside
      have absent : (store d)[index]? = none := List.getElem?_eq_none (by omega)
      simp [absent] at old
    simpa [List.getElem?_append, within] using old
  · simpa [read, publish, Function.update_of_ne same] using old

@[simp] theorem read_publish_new (store : Store) (d : Domain) (value : Cell d) :
    read (publish store d value) d (store d).length = some value.read := by
  simp [read, publish]

inductive Scalar (d : Domain) where
  | immediate (value : Field d)
  | reference (index : Nat)

abbrev Value : Ty → Type
  | .scalar d => Scalar d
  | ty => TableProtocol.Value ty

def embed : (ty : Ty) → TableProtocol.Value ty → Value ty
  | .scalar _, x => .immediate x
  | .boolean, x | .digest, x | .summary, x | .table _ _, x | .residual _ _, x | .point _, x => x

def decode (store : Store) : (ty : Ty) → Value ty → Option (TableProtocol.Value ty)
  | .scalar _, .immediate x => some x
  | .scalar d, .reference index => read store d index
  | .boolean, x | .digest, x | .summary, x | .table _ _, x | .residual _ _, x | .point _, x => some x

@[simp] theorem decode_embed (store : Store) (ty : Ty) (x : TableProtocol.Value ty) :
    decode store ty (embed ty x) = some x := by cases ty <;> rfl

theorem decode_publish_old (store : Store) (d : Domain) (value : Cell d)
    (ty : Ty) (x : TableProtocol.Value ty) (y : Value ty) (old : decode store ty y = some x) :
    decode (publish store d value) ty y = some x := by
  cases ty with
  | scalar other =>
    cases y with
    | immediate _ => exact old
    | reference index => exact read_publish_old store d value other index x old
  | _ => exact old

/-- Kernel-call accounting only; not time, bytes or native capacity. -/
def readCost (store : Store) : (ty : Ty) → Value ty → Nat
  | .scalar d, .reference index => (((store d)[index]?).map Cell.cost).getD 0
  | _, _ => 0

def preparationCost : Mode → Nat | .lazy => 0 | .materialized => 1

end TablePhysical
