import Zkc.Relation.RankOne
import Zkc.Relation.SparsePolynomial
import Zkc.Algebra.FiniteVectors

/-! Pure independent reference entry points for canonical sparse data.
Rows contain strictly increasing column indices and nonzero coefficients.
Raw scalars already belong to the caller's selected ring: field identifiers,
byte decoding, source import and relation identity remain outside this API.
The result strings are reference refusals, not native diagnostic allocations.
-/

set_option autoImplicit false

namespace Zkc.Relation.Reference

abbrev Result := Except String

variable {F : Type} [CommRing F] [DecidableEq F] {m n p : Nat}

/-- Linear adjacent-order check; canonical admission never compares all pairs. -/
def increasing : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => decide (a < b) && increasing (b :: rest)

private def rowEntries (columns : Nat) : List (Nat × F) → Result (Sparse.Row F columns)
  | [] => .ok []
  | (column, value) :: rest => do
      if h : column < columns then
        return (⟨column, h⟩, value) :: (← rowEntries columns rest)
      else .error "relation-column-index"

def admitRow (columns : Nat) (entries : Array (Nat × F)) : Result (Sparse.Row F columns) := do
  if columns > Zkc.Algebra.FiniteVectors.limit || entries.size > Zkc.Algebra.FiniteVectors.limit then
    throw "relation-limit"
  if !increasing (entries.toList.map Prod.fst) then throw "relation-column-order"
  if entries.any (fun entry => decide (entry.2 = 0)) then throw "relation-zero-coefficient"
  rowEntries columns entries.toList

/-- CSR-style grouped rows; empty rows are explicit. Admission checks shapes,
bounds, sorted unique columns and zero-free coefficients without normalizing
malformed input into a different accepted representation. -/
def admitMatrix (rows columns : Nat) (data : Array (Array (Nat × F))) :
    Result (Sparse.Matrix F rows columns) := do
  if rows > Zkc.Algebra.FiniteVectors.limit || columns > Zkc.Algebra.FiniteVectors.limit ||
      data.foldl (fun total row => total + row.size) 0 > Zkc.Algebra.FiniteVectors.limit then
    throw "relation-limit"
  if data.size ≠ rows then throw "relation-matrix-shape"
  let admitted ← data.toList.mapM (admitRow columns)
  if h : admitted.length = rows then
    return ⟨⟨admitted.toArray, by simpa using h⟩⟩
  else throw "relation-matrix-shape"

def admitSystem (rows columns : Nat) (a b c : Array (Array (Nat × F))) :
    Result (RankOne.System F rows columns) := do
  return ⟨← admitMatrix rows columns a, ← admitMatrix rows columns b, ← admitMatrix rows columns c⟩

def admitVector (length : Nat) (values : Array F) (shapeCode : String) : Result (Vector F length) :=
  if length > Zkc.Algebra.FiniteVectors.limit then .error "relation-limit"
  else if shape : values.size = length then .ok ⟨values, shape⟩ else .error shapeCode

/-- An executable bound layout only needs ONE and public slots. Private slots
remain arbitrary assignment cells. Admission forbids aliases between bound slots. -/
structure Binding (columns publicCount : Nat) where
  one : Fin columns
  publicSlots : Vector (Fin columns) publicCount

def admitBinding (columns publicCount one : Nat) (publicSlots : Array Nat) :
    Result (Binding columns publicCount) := do
  if columns > Zkc.Algebra.FiniteVectors.limit || publicCount > Zkc.Algebra.FiniteVectors.limit then
    throw "relation-limit"
  if publicSlots.size ≠ publicCount then throw "relation-public-shape"
  if !increasing ((one :: publicSlots.toList).mergeSort (· ≤ ·)) then
    throw "relation-binding-alias"
  if h : one < columns then
    let slots ← publicSlots.toList.mapM fun index =>
      if within : index < columns then Except.ok (⟨index, within⟩ : Fin columns)
      else Except.error "relation-public-index"
    if shape : slots.length = publicCount then
      return ⟨⟨one, h⟩, ⟨slots.toArray, by simpa using shape⟩⟩
    else throw "relation-public-shape"
  else throw "relation-one-index"

def Binding.Bound (binding : Binding n p) (statement : Vector F p) (z : Vector F n) : Prop :=
  z[binding.one] = 1 ∧ ∀ j : Fin p, z[binding.publicSlots[j]] = statement[j]

instance (binding : Binding n p) (statement : Vector F p) (z : Vector F n) :
    Decidable (binding.Bound statement z) := inferInstanceAs
  (Decidable (z[binding.one] = 1 ∧ ∀ j : Fin p, z[binding.publicSlots[j]] = statement[j]))

def Binding.check (binding : Binding n p) (statement : Vector F p) (z : Vector F n) : Bool :=
  decide (binding.Bound statement z)

theorem Binding.check_correct (binding : Binding n p) (statement : Vector F p) (z : Vector F n) :
    binding.check statement z = true ↔ binding.Bound statement z := by simp [Binding.check]

def Binding.ofLayout {w : Nat} (layout : RankOne.Layout p w n) : Binding n p :=
  ⟨layout .one, Vector.ofFn fun j => layout (.publicInput j)⟩

omit [DecidableEq F] in
theorem Binding.layout_bound {w : Nat} (layout : RankOne.Layout p w n)
    (statement : Vector F p) (z : Vector F n) :
    (Binding.ofLayout layout).Bound statement z ↔
      RankOne.Bound layout (fun j => statement[j]) (fun j => z[j]) := by
  simp [Binding.Bound, Binding.ofLayout, RankOne.Bound]

structure Products (F : Type) (rows : Nat) where
  a : Vector F rows
  b : Vector F rows
  c : Vector F rows

def products (system : RankOne.System F m n) (z : Vector F n) : Products F m :=
  ⟨system.A.mul (fun j => z[j]), system.B.mul (fun j => z[j]), system.C.mul (fun j => z[j])⟩

def Products.check (values : Products F m) : Bool :=
  decide (∀ i : Fin m, values.a[i] * values.b[i] = values.c[i])

theorem products_check (system : RankOne.System F m n) (z : Vector F n) :
    (products system z).check = true ↔ system.Satisfies (fun j => z[j]) := by
  simp [products, Products.check, RankOne.System.Satisfies, Sparse.Matrix.mul]

/-- Both row equations and independently supplied public/ONE values are checked. -/
def check (system : RankOne.System F m n) (binding : Binding n p)
    (statement : Vector F p) (z : Vector F n) : Bool :=
  (products system z).check && binding.check statement z

theorem check_correct (system : RankOne.System F m n) (binding : Binding n p)
    (statement : Vector F p) (z : Vector F n) :
    check system binding statement z = true ↔
      system.Satisfies (fun j => z[j]) ∧ binding.Bound statement z := by
  simp [check, products_check, Binding.check_correct]

def product (matrix : Sparse.Matrix F m n) (assignment : Array F) : Result (Array F) := do
  let z ← admitVector n assignment "relation-assignment-shape"
  return (matrix.mul (fun j => z[j])).toArray

def contraction (matrix : Sparse.Matrix F m n) (rowWeights : Array F) :
    Result (Array (Nat × F)) := do
  let weights ← admitVector m rowWeights "relation-row-weights-shape"
  return ((matrix.contract (fun i => weights[i])).map fun entry => (entry.1.val, entry.2)).toArray

def weightedValue (matrix : Sparse.Matrix F m n) (rowWeights columnWeights : Array F) : Result F := do
  let rows ← admitVector m rowWeights "relation-row-weights-shape"
  let columns ← admitVector n columnWeights "relation-column-weights-shape"
  return matrix.bilinear (fun i => rows[i]) (fun j => columns[j])

def pointValue {r c : Nat} (matrix : Sparse.Matrix F (2 ^ r) (2 ^ c))
    (rowPoint columnPoint : Array F) : Result F := do
  let rows ← admitVector r rowPoint "relation-row-point-shape"
  let columns ← admitVector c columnPoint "relation-column-point-shape"
  return matrix.atPoint (fun i => rows[i]) (fun j => columns[j])

def checkAssignment (system : RankOne.System F m n) (binding : Binding n p)
    (statement assignment : Array F) : Result Bool := do
  let x ← admitVector p statement "relation-public-shape"
  let z ← admitVector n assignment "relation-assignment-shape"
  return check system binding x z

end Zkc.Relation.Reference
