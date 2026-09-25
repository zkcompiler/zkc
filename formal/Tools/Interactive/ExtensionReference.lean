import Tools.Interactive.ScalarReference

/-! Independent executable coordinate arithmetic for the nominal KoalaBear octic
extension. Multiplication is convolution reduced by X^8 = 3. No Field or ring-law
instance is asserted for this executable carrier; generic PIR meaning remains
parameterized by mathematical fields. Inversion checks its exponentiation result.
-/
set_option autoImplicit false

namespace Tools.Interactive.ExtensionReference
open Zkc.Algebra

abbrev Base := ScalarReference.Scalar .koalaBear
structure Scalar where
  coordinates : Vector Base 8
  deriving BEq, Repr, Inhabited

def embed (x : Base) : Scalar := ⟨Vector.ofFn fun i => if i.val == 0 then x else 0⟩
instance : Zero Scalar := ⟨embed 0⟩
instance : One Scalar := ⟨embed 1⟩
instance : Add Scalar := ⟨fun a b => ⟨Vector.ofFn fun i => a.coordinates[i] + b.coordinates[i]⟩⟩
instance : Neg Scalar := ⟨fun a => ⟨a.coordinates.map (- ·)⟩⟩
instance : Sub Scalar := ⟨fun a b => a + -b⟩

/-- Each output coefficient is an independent sum over exactly eight pairs.
Native Plonky3 multiplication is not consulted by this implementation. -/
instance : Mul Scalar := ⟨fun a b => ⟨Vector.ofFn fun k =>
  ((List.finRange 8).map fun i =>
    let j : Fin 8 := ⟨(k.val + 8 - i.val) % 8, Nat.mod_lt _ (by decide)⟩
    a.coordinates[i] * b.coordinates[j] * (if i.val > k.val then 3 else 1)).sum⟩⟩

def power (x : Scalar) (n : Nat) : Scalar :=
  if _h : n = 0 then 1 else
    let half := power x (n / 2)
    let square := half * half
    if n % 2 == 0 then square else square * x
termination_by n

def inverse (x : Scalar) : Result Scalar := do
  ensure (x != 0) "inverse-zero"
  let y := power x (Bindings.koalaBearModulus ^ 8 - 2)
  ensure (x * y == 1) "inverse-nonunit"
  return y

abbrev Data := ScalarReference.Data Scalar

def scalar (json : Lean.Json) : Result Scalar := do
  let xs ← Decode.array json 8
  ensure (xs.length == 8) "extension-coordinate-count"
  let xs ← xs.mapM (ScalarReference.decodeScalar .koalaBear)
  let a := xs.toArray
  if h : a.size = 8 then return ⟨⟨a, h⟩⟩
  else throw "extension-coordinate-count"

def scalarJson (x : Scalar) : Lean.Json :=
  .arr (x.coordinates.toArray.map fun c => .str (toString c.val))

def decode (kind : String) (json : Lean.Json) : Result Data := do
  if kind == "field" then return .field (← scalar json)
  if kind == "matrix" then
    let [rows, columns, entries] ← Decode.array json 3 | throw "matrix-record"
    let entries ← (← Decode.array entries FiniteMatrices.nonzeroLimit).mapM fun entry => do
      let [r, c, a] ← Decode.array entry 3 | throw "matrix-entry"
      pure (FiniteMatrices.Entry.mk (← Decode.natural r) (← Decode.natural c) (← scalar a))
    let m := FiniteMatrices.Matrix.mk (← Decode.natural rows) (← Decode.natural columns) entries
    ensure m.valid "matrix-canonical"
    return .matrix m
  let xs ← (← Decode.array json FiniteVectors.limit).mapM scalar
  if kind == "vector" then return .vector xs
  if kind == "polynomial" then
    let value := ScalarReference.Data.polynomial xs
    ensure value.valid "polynomial-normalization"
    return value
  if kind == "round" then
    let [a, b, c] := xs | throw "reference-round"
    return .round ⟨a, b, c⟩
  throw "reference-extension-kind"

def json (value : Data) : Lean.Json :=
  let sequence := fun xs => Lean.Json.arr (xs.map scalarJson).toArray
  match value with
  | .index n => .str (toString n)
  | .indices ns => .arr (ns.map (fun n => Lean.Json.str (toString n))).toArray
  | .field x => scalarJson x
  | .matrix m => .arr #[.str (toString m.rows), .str (toString m.columns),
      .arr (m.entries.map fun e => Lean.Json.arr #[.str (toString e.row),
        .str (toString e.column), scalarJson e.coefficient]).toArray]
  | .vector xs | .polynomial xs => sequence xs
  | .round r => sequence [r.constant, r.linear, r.quadratic]
  | .boolean b => .str (if b then "true" else "false")

private def sum (xs : List Scalar) : Scalar := xs.foldl (· + ·) 0
private def dot (xs ys : List Scalar) : Result Scalar := do
  return sum (← FiniteVectors.zipExact (· * ·) xs ys)
private def evaluate (xs : List Scalar) (x : Scalar) : Scalar :=
  xs.foldr (fun c rest => c + x * rest) 0
private def boundary (xs : List Scalar) : Scalar := evaluate xs 0 + evaluate xs 1
private def matrixProduct (m : FiniteMatrices.Matrix Scalar) (xs : List Scalar)
    (transpose : Bool) : Result (List Scalar) := do
  ensure (xs.length == if transpose then m.rows else m.columns) "matrix-shape"
  return (List.range (if transpose then m.columns else m.rows)).map fun i =>
    sum (m.entries.filterMap fun e =>
      if (if transpose then e.column else e.row) == i then
        some (e.coefficient * xs[if transpose then e.row else e.column]!) else none)

/-- Pure extension computation. Shape-only helpers are shared; no unproved
algebraic typeclass is needed to run the coordinate operations. -/
def compute (contract : String) (attrs : List String) (inputs : List Data) : Result (List Data) := do
  Bindings.attributes false contract attrs Bindings.koalaBearExt8
  ensure (inputs.all ScalarReference.Data.valid) "reference-extension-value"
  let natural := fun s => Decode.natural (.str s)
  let constant := fun s => do pure (embed (← ScalarReference.decodeScalar .koalaBear (.str s)))
  if ScalarReference.dynamicSupported contract then
    return ← ScalarReference.dynamicCompute (fun n => embed (n : Base)) inverse true contract attrs inputs
  match contract, inputs, attrs with
  | "field.constant", [], [s] => return [.field (← constant s)]
  | "field.add", [.field a, .field b], [] => return [.field (a + b)]
  | "field.sub", [.field a, .field b], [] => return [.field (a - b)]
  | "field.mul", [.field a, .field b], [] => return [.field (a * b)]
  | "field.neg", [.field a], [] => return [.field (-a)]
  | "field.inverse", [.field a], [] => return [.field (← inverse a)]
  | "field.equal", [.field a, .field b], [] => return [.boolean (a == b)]
  | "vector.constant", [], literals => do
      FiniteVectors.bounded literals
      return [.vector (← literals.mapM constant)]
  | "vector.empty", [], [] => return [.vector []]
  | "vector.append", [.vector xs, .field x], [] => return [.vector (← FiniteVectors.concat xs [x])]
  | "vector.splat", [.field x], [length] => do
      let n ← natural length
      ensure (n ≤ FiniteVectors.limit) "vector-limit"
      return [.vector (List.replicate n x)]
  | "vector.powers", [.field x], [length] => do
      let n ← natural length
      ensure (n ≤ FiniteVectors.limit) "vector-limit"
      return [.vector ((List.range n).map (power x))]
  | "vector.add", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.zipExact (· + ·) xs ys)]
  | "vector.sub", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.zipExact (· - ·) xs ys)]
  | "vector.mul", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.zipExact (· * ·) xs ys)]
  | "vector.scale", [.vector xs, .field x], [] => return [.vector (xs.map (· * x))]
  | "vector.sum", [.vector xs], [] => return [.field (sum xs)]
  | "vector.dot", [.vector xs, .vector ys], [] => return [.field (← dot xs ys)]
  | "vector.split", [.vector xs], [] => do
      let (a, b) ← FiniteVectors.split xs
      return [.vector a, .vector b]
  | "vector.concat", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.concat xs ys)]
  | "vector.at", [.vector xs], [index] => do
      let some x := xs[← natural index]? | throw "vector-index"
      return [.field x]
  | "vector.length_check", [.vector xs], [length] => return [.boolean (xs.length == (← natural length))]
  | "vector.gather", [.vector xs], indices => return [.vector (← FiniteVectors.gather xs (← indices.mapM natural))]
  | "vector.scatter_sum", [.vector xs], length :: indices => do
      let n ← natural length
      let indices ← indices.mapM natural
      ensure (xs.length == indices.length) "vector-shape"
      ensure (indices.all (· < n)) "vector-index"
      ensure (n ≤ FiniteVectors.limit) "vector-limit"
      return [.vector ((List.range n).map fun i => sum ((xs.zip indices).filterMap
        fun (x, j) => if i == j then some x else none))]
  | "vector.kronecker", [.vector xs, .vector ys], [] => do
      ensure (xs.length * ys.length ≤ FiniteVectors.limit) "vector-limit"
      return [.vector (xs.flatMap fun x => ys.map (x * ·))]
  | "vector.matvec", [.vector xs, .vector ys], [rows, columns, transpose] => do
      let rows ← natural rows
      let columns ← natural columns
      ensure (rows ≤ FiniteVectors.limit && columns ≤ FiniteVectors.limit && rows * columns ≤ FiniteVectors.limit) "vector-limit"
      let transposed := transpose == "1"
      ensure (xs.length == rows * columns && ys.length == if transposed then rows else columns) "matrix-shape"
      return [.vector ((List.range (if transposed then columns else rows)).map fun i =>
        sum (ys.zipIdx |>.map fun (y, j) => xs[if transposed then j * columns + i else i * columns + j]! * y))]
  | "matrix.mul_vector", [.matrix m, .vector xs], [] => return [.vector (← matrixProduct m xs false)]
  | "matrix.transpose_mul_vector", [.matrix m, .vector xs], [] => return [.vector (← matrixProduct m xs true)]
  | "matrix.bilinear", [.matrix m, .vector ys, .vector xs], [] =>
      return [.field (← dot ys (← matrixProduct m xs false))]
  | "matrix.shape_check", [.matrix m], [rows, columns] =>
      return [.boolean (m.rows == (← natural rows) && m.columns == (← natural columns))]
  | "poly.from_coefficients", [.vector xs], [] => return [.polynomial ((xs.reverse.dropWhile (· == 0)).reverse)]
  | "poly.coefficients", [.polynomial xs], [] => return [.vector xs]
  | "poly.degree_check", [.polynomial xs], [maximum] =>
      return [.boolean (xs.isEmpty || xs.length - 1 ≤ (← natural maximum))]
  | "poly.univariate_evaluate", [.polynomial xs, .field x], [] => return [.field (evaluate xs x)]
  | "poly.univariate_boundary", [.polynomial xs], [] => return [.field (boundary xs)]
  | "poly.boundary", [.round r], [] => return [.field (boundary [r.constant, r.linear, r.quadratic])]
  | "poly.round_evaluate", [.round r, .field x], [] => return [.field (evaluate [r.constant, r.linear, r.quadratic] x)]
  | _, _, _ => throw "reference-extension-contract"

end Tools.Interactive.ExtensionReference
