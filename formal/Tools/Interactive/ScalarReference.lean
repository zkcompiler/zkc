import Tools.Interactive.Field
import Tools.Interactive.Bindings
import Zkc.Algebra.FiniteVectors
import Zkc.Algebra.FiniteMatrices

/-! One materialized scalar interpretation for the installed prime-field domains.
There is no physical layout in this carrier and no group arithmetic surrogate. -/

set_option autoImplicit false

namespace Tools.Interactive.ScalarReference
open Zkc.Algebra

inductive Domain where
  | bls | ristretto | koalaBear | bn254
  deriving BEq, DecidableEq, Repr

def Domain.identity : Domain → String
  | .bls => Bindings.fr | .ristretto => Bindings.ristrettoScalar
  | .koalaBear => Bindings.koalaBear
  | .bn254 => Bindings.bn254Fr

def Domain.modulus : Domain → Nat
  | .bls => fieldModulus | .ristretto => Bindings.ristrettoModulus
  | .koalaBear => Bindings.koalaBearModulus
  | .bn254 => Bindings.bn254Modulus

instance (d : Domain) : NeZero d.modulus := ⟨by cases d <;> decide⟩

abbrev Scalar (d : Domain) := ZMod d.modulus

def Domain.parse (identity : String) : Result Domain :=
  if identity == Bindings.fr then .ok .bls
  else if identity == Bindings.ristrettoScalar then .ok .ristretto
  else if identity == Bindings.koalaBear then .ok .koalaBear
  else if identity == Bindings.bn254Fr then .ok .bn254
  else .error "reference-field-domain"

inductive Data (F : Type) where
  | index (value : Nat)
  | indices (values : List Nat)
  | field (value : F)
  | matrix (value : FiniteMatrices.Matrix F)
  | vector (values : List F)
  | polynomial (coefficients : List F)
  | round (value : Math.Round F)
  | boolean (value : Bool)
  deriving BEq, Repr

def Data.kind {F : Type} : Data F → String
  | .index _ => "index" | .indices _ => "indices"
  | .matrix _ => "matrix"
  | .field _ => "field" | .vector _ => "vector" | .polynomial _ => "polynomial"
  | .round _ => "round" | .boolean _ => "bool"

def Data.size {F : Type} : Data F → Nat
  | .indices xs => 1 + xs.length
  | .matrix m => 3 + 3 * m.entries.length
  | .vector xs | .polynomial xs => 1 + xs.length
  | .round _ => 4
  | _ => 1

def Data.valid {F : Type} [Zero F] [BEq F] : Data F → Bool
  | .index n => n < 2^64
  | .indices xs => xs.length ≤ FiniteVectors.limit && xs.all (· < 2^64)
  | .matrix m => m.valid
  | .vector xs => xs.length ≤ FiniteVectors.limit
  | .polynomial xs => xs.length ≤ FiniteVectors.limit &&
      (xs.isEmpty || xs.getLast? != some 0)
  | _ => true

def decodeScalar (d : Domain) (json : Lean.Json) : Result (Scalar d) := do
  let n ← Decode.natural json
  ensure (n < d.modulus) "noncanonical-field"
  return (n : Scalar d)

def decode (d : Domain) (kind : String) (json : Lean.Json) : Result (Data (Scalar d)) := do
  if kind == "index" then
    let n ← Decode.natural json
    ensure (n < 2^64) "index-overflow"
    return .index n
  if kind == "indices" then
    let ns ← (← Decode.array json FiniteVectors.limit).mapM Decode.natural
    ensure (ns.all (· < 2^64)) "index-overflow"
    return .indices ns
  if kind == "field" then return .field (← decodeScalar d json)
  if kind == "matrix" then
    let [rows, columns, entries] ← Decode.array json 3 | throw "matrix-record"
    let rows ← Decode.natural rows
    let columns ← Decode.natural columns
    ensure (rows ≤ FiniteMatrices.dimensionLimit && columns ≤ FiniteMatrices.dimensionLimit) "matrix-dimension-limit"
    let entries ← (← Decode.array entries FiniteMatrices.nonzeroLimit).mapM fun e => do
      let [r,c,a] ← Decode.array e 3 | throw "matrix-entry"
      pure (FiniteMatrices.Entry.mk (← Decode.natural r) (← Decode.natural c) (← decodeScalar d a))
    let m := FiniteMatrices.Matrix.mk rows columns entries
    ensure m.valid "matrix-canonical"
    return .matrix m
  let xs ← (← Decode.array json FiniteVectors.limit).mapM (decodeScalar d)
  if kind == "vector" then return .vector xs
  if kind == "polynomial" then
    let value := Data.polynomial xs
    ensure value.valid "polynomial-normalization"
    return value
  if kind == "round" then
    let [a, b, c] := xs | throw "reference-round"
    return .round ⟨a, b, c⟩
  throw "reference-scalar-kind"

def json (d : Domain) (value : Data (Scalar d)) : Lean.Json :=
  let scalar := fun (x : Scalar d) => Lean.Json.str (toString x.val)
  let sequence := fun xs => Lean.Json.arr (xs.map scalar).toArray
  match value with
  | .matrix m => .arr #[.str (toString m.rows), .str (toString m.columns),
      .arr (m.entries.map fun e => Lean.Json.arr #[.str (toString e.row), .str (toString e.column), scalar e.coefficient]).toArray]
  | .index n => .str (toString n)
  | .indices ns => .arr (ns.map (fun n => Lean.Json.str (toString n))).toArray
  | .field x => scalar x
  | .vector xs | .polynomial xs => sequence xs
  | .round r => sequence [r.constant, r.linear, r.quadratic]
  | .boolean b => .str (if b then "true" else "false")

/-- Numerical reference exponentiation; no native field implementation is called. -/
def powerValue {F : Type} [One F] [Mul F] (x : F) (n : Nat) : F :=
  if _h : n = 0 then 1 else
    let y := powerValue x (n / 2)
    if n % 2 == 0 then y * y else y * y * x
termination_by n

def dynamicSupported (name : String) : Bool :=
  name.startsWith "index." || name.startsWith "indices." ||
  ["vector.slice", "vector.get", "vector.length", "vector.rotate", "vector.interleave", "vector.prefix_product",
   "vector.prefix_sum", "vector.inverse", "vector.fill", "vector.geometric", "field.from_index",
   "poly.coefficient_count", "poly.divide_opening", "poly.coset_evaluate", "poly.coset_interpolate",
   "poly.domain_root", "poly.domain_point", "poly.domain_points", "poly.even_odd_fold", "poly.opening_quotient"].contains name

/-- Bounded executable oracle using lists and direct evaluation/interpolation.
No ring laws are assumed for the coordinate-only extension reference. -/
def dynamicCompute {F : Type} [Zero F] [One F] [Add F] [Sub F] [Mul F] [BEq F]
    (cast : Nat → F) (inverse : F → Result F) (twoAdic : Bool)
    (name : String) (attrs : List String) (inputs : List (Data F))
    (maxPower : Nat := 24) (maximalRoot : Nat := 1791270792) : Result (List (Data F)) := do
  let checkedIndex := fun n => do ensure (n < 2^64) "index-overflow"; pure [Data.index n]
  let vector := fun xs => do ensure (xs.length ≤ FiniteVectors.limit) "vector-limit"; pure [Data.vector xs]
  let evaluate := fun cs x => cs.foldr (fun c acc => c + x * acc) 0
  let normalize := fun cs => (cs.reverse.dropWhile (· == 0)).reverse
  let root := fun n => do
    ensure twoAdic "coset-field"
    ensure (n > 0 && n == 2^(Nat.log2 n) && Nat.log2 n ≤ maxPower) "coset-size"
    ensure (n ≤ FiniteVectors.limit) "coset-element-limit"
    pure (powerValue (cast maximalRoot) (2^(maxPower-Nat.log2 n)))
  let points := fun n shift => do
    ensure (shift != 0) "coset-zero-shift"
    let g ← root n
    pure ((List.range n).map fun i => shift * powerValue g i)
  match name, inputs, attrs with
  | "index.constant", [], [s] => checkedIndex (← Decode.natural (.str s))
  | "index.add", [.index a, .index b], [] => checkedIndex (a+b)
  | "index.sub", [.index a, .index b], [] => do ensure (b ≤ a) "index-underflow"; checkedIndex (a-b)
  | "index.mul", [.index a, .index b], [] => checkedIndex (a*b)
  | "index.div", [.index a, .index b], [] => do ensure (b > 0) "index-zero-divisor"; checkedIndex (a/b)
  | "index.mod", [.index a, .index b], [] => do ensure (b > 0) "index-zero-divisor"; checkedIndex (a%b)
  | "index.equal", [.index a, .index b], [] => return [.boolean (a==b)]
  | "index.less", [.index a, .index b], [] => return [.boolean (a<b)]
  | "indices.empty", [], [] => return [.indices []]
  | "indices.append", [.indices ns, .index n], [] => do
      ensure (ns.length < FiniteVectors.limit) "vector-limit"; return [.indices (ns++[n])]
  | "indices.length", [.indices ns], [] => checkedIndex ns.length
  | "indices.at", [.indices ns, .index i], [] => do
      let some n := ns[i]? | throw "index-bounds"
      checkedIndex n
  | "field.from_index", [.index n], [] => return [.field (cast n)]
  | "vector.length", [.vector xs], [] => checkedIndex xs.length
  | "poly.coefficient_count", [.polynomial xs], [] => checkedIndex xs.length
  | "vector.slice", [.vector xs, .index start, .index count], [] => do
      vector (← FiniteVectors.slice xs start count)
  | "vector.get", [.vector xs, .index i], [] => do
      let some x := xs[i]? | throw "vector-index"
      return [.field x]
  | "vector.rotate", [.vector xs, .index i], [] => do
      ensure (i < xs.length) "vector-rotation"; vector (xs.drop i ++ xs.take i)
  | "vector.interleave", [.vector xs, .vector ys], [] => do
      ensure (xs.length == ys.length) "length-mismatch"
      vector ((xs.zip ys).flatMap fun (x,y) => [x,y])
  | "vector.fill", [.field x, .index n], [] => do
      ensure (n ≤ FiniteVectors.limit) "vector-limit"; vector (List.replicate n x)
  | "vector.geometric", [.field x, .index n], [] => do
      ensure (n ≤ FiniteVectors.limit) "vector-limit"; vector ((List.range n).map (powerValue x))
  | "vector.prefix_sum", [.vector xs], [] => vector ((xs.scanl (· + ·) 0).drop 1)
  | "vector.prefix_product", [.vector xs], [] => vector ((xs.scanl (· * ·) 1).drop 1)
  | "vector.inverse", [.vector xs], [] => vector (← xs.mapM inverse)
  | "poly.divide_opening", [.polynomial cs, .field z, .field y], [] => do
      ensure (evaluate cs z == y) "polynomial-opening-value"
      -- Successive reversed prefixes evaluate the coefficient suffixes at z.
      let suffixes := (cs.reverse.scanl (fun acc c => c + z * acc) 0).drop 1
      return [.polynomial (normalize (suffixes.take (cs.length - 1)).reverse)]
  | "poly.domain_root", [.index n], [] => return [.field (← root n)]
  | "poly.domain_point", [.field shift, .index n, .index i], [] => do
      ensure (shift != 0) "coset-zero-shift"; let g ← root n
      ensure (i<n) "coset-coordinate"; return [.field (shift * powerValue g i)]
  | "poly.domain_points", [.field shift, .index n], [] => vector (← points n shift)
  | "poly.coset_evaluate", [.polynomial cs, .field shift, .index n], [] => do
      ensure (cs.length ≤ n) "coset-coefficient-count"
      ensure (n ≤ 128) "reference-numerical-work-limit"
      vector ((← points n shift).map (evaluate cs))
  | "poly.coset_interpolate", [.vector xs, .field shift], [] => do
      let n := xs.length
      ensure (n ≤ 128) "reference-numerical-work-limit"
      ensure (shift != 0) "coset-zero-shift"
      let g ← inverse (← root n)
      let scale ← inverse (cast n)
      let shiftInv ← inverse shift
      let cs := (List.range n).map fun j =>
        scale * powerValue shiftInv j *
          ((xs.zipIdx.map fun (x,i) => x * powerValue g (i*j)).foldl (· + ·) 0)
      return [.polynomial (normalize cs)]
  | "poly.even_odd_fold", [.vector xs, .field shift, .field challenge], [] => do
      ensure (xs.length ≥ 2) "coset-fold-size"
      let ps ← points xs.length shift
      let half := xs.length/2
      let twoInv ← inverse (cast 2)
      let ys ← (List.range half).mapM fun i => do
        let some a := xs[i]? | throw "coset-coordinate"
        let some b := xs[i+half]? | throw "coset-coordinate"
        let some x := ps[i]? | throw "coset-coordinate"
        pure ((a+b)*twoInv + challenge*(a-b)*twoInv*(← inverse x))
      vector ys
  | "poly.opening_quotient", [.vector xs, .field shift, .field z, .field y], [] => do
      let ps ← points xs.length shift
      ensure (ps.all (· != z)) "coset-opening-point"
      vector (← (xs.zip ps).mapM fun (v,x) => do pure ((v-y)*(← inverse (x-z))))
  | _, _, _ => throw "reference-numerical-operands"

/-- Pure scalar work, independent of native implementations and execution
state. Domain dispatch only chooses the ring; all sequence algorithms are shared. -/
def compute (d : Domain) (contract : String) (attrs : List String)
    (inputs : List (Data (Scalar d))) : Result (List (Data (Scalar d))) := do
  Bindings.attributes false contract attrs d.identity
  ensure (inputs.all Data.valid) "reference-scalar-value"
  let natural := fun text => Decode.natural (.str text)
  if dynamicSupported contract then
    return ← dynamicCompute (fun n => (n : Scalar d))
      (fun x => do ensure (x != 0) "inverse-zero"; pure x⁻¹) (d == .koalaBear || d == .bn254) contract attrs inputs
      (if d == .bn254 then 28 else 24)
      (if d == .bn254 then 19103219067921713944291392827692070036145651957329286315305642004821462161904 else 1791270792)
  match contract, inputs, attrs with
  | "field.constant", [], [literal] => return [.field (← decodeScalar d (.str literal))]
  | "field.add", [.field a, .field b], [] => return [.field (a + b)]
  | "field.sub", [.field a, .field b], [] => return [.field (a - b)]
  | "field.mul", [.field a, .field b], [] => return [.field (a * b)]
  | "field.neg", [.field a], [] => return [.field (-a)]
  | "field.inverse", [.field a], [] => return [.field (← FiniteVectors.inverse a)]
  | "field.equal", [.field a, .field b], [] => return [.boolean (a == b)]
  | "matrix.mul_vector", [.matrix m, .vector x], [] =>
      return [.vector (← FiniteMatrices.mulVector m x)]
  | "matrix.transpose_mul_vector", [.matrix m, .vector y], [] =>
      return [.vector (← FiniteMatrices.mulVector m y true)]
  | "matrix.bilinear", [.matrix m, .vector y, .vector x], [] =>
      return [.field (← FiniteMatrices.bilinear m y x)]
  | "matrix.shape_check", [.matrix m], [rows,columns] =>
      return [.boolean (m.rows == (← natural rows) && m.columns == (← natural columns))]
  | "vector.constant", [], literals => do
      ensure (literals.length ≤ FiniteVectors.limit) "vector-limit"
      return [.vector (← literals.mapM fun text => decodeScalar d (.str text))]
  | "vector.scatter_sum", [.vector xs], length :: indices =>
      return [.vector (← FiniteVectors.scatterSum xs (← natural length) (← indices.mapM natural))]
  | "vector.empty", [], [] => return [.vector []]
  | "vector.append", [.vector xs, .field x], [] => return [.vector (← FiniteVectors.concat xs [x])]
  | "vector.splat", [.field x], [length] => do
      let n ← natural length
      ensure (n ≤ FiniteVectors.limit) "vector-limit"
      return [.vector (List.replicate n x)]
  | "vector.powers", [.field x], [length] => return [.vector (← FiniteVectors.powers x (← natural length))]
  | "vector.add", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.zipExact (· + ·) xs ys)]
  | "vector.sub", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.zipExact (· - ·) xs ys)]
  | "vector.mul", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.zipExact (· * ·) xs ys)]
  | "vector.scale", [.vector xs, .field x], [] => return [.vector (xs.map (· * x))]
  | "vector.sum", [.vector xs], [] => return [.field xs.sum]
  | "vector.dot", [.vector xs, .vector ys], [] => return [.field (← FiniteVectors.dot xs ys)]
  | "vector.split", [.vector xs], [] => do
      let (lo, hi) ← FiniteVectors.split xs
      return [.vector lo, .vector hi]
  | "vector.concat", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.concat xs ys)]
  | "vector.at", [.vector xs], [index] => do
      let some x := xs[← natural index]? | throw "vector-index"
      return [.field x]
  | "vector.length_check", [.vector xs], [length] => return [.boolean (xs.length == (← natural length))]
  | "vector.gather", [.vector xs], indices => return [.vector (← FiniteVectors.gather xs (← indices.mapM natural))]
  | "vector.kronecker", [.vector xs, .vector ys], [] => return [.vector (← FiniteVectors.kronecker xs ys)]
  | "vector.matvec", [.vector matrix, .vector vector], [rows, columns, transpose] =>
      return [.vector (← FiniteVectors.matvec (← natural rows) (← natural columns)
        (transpose == "1") matrix vector)]
  | "poly.from_coefficients", [.vector xs], [] => return [.polynomial (FiniteVectors.normalize xs)]
  | "poly.coefficients", [.polynomial xs], [] => return [.vector xs]
  | "poly.degree_check", [.polynomial xs], [maximum] => return [.boolean (FiniteVectors.degreeCheck xs (← natural maximum))]
  | "poly.univariate_evaluate", [.polynomial xs, .field x], [] => return [.field (FiniteVectors.evaluate xs x)]
  | "poly.univariate_boundary", [.polynomial xs], [] => return [.field (FiniteVectors.boundary xs)]
  | "poly.boundary", [.round r], [] => return [.field r.boundary]
  | "poly.round_evaluate", [.round r, .field x], [] => return [.field (r.at x)]
  | _, _, _ => throw "reference-scalar-contract"

/-- Exactly the pure scalar contracts. Unsupported vector conversions retain
separate BLS-only interpretation, established by nominal admission. -/
def supported (contract : String) : Bool :=
  dynamicSupported contract ||
  ["field.constant", "field.add", "field.sub", "field.mul", "field.neg", "field.inverse", "field.equal",
   "matrix.mul_vector", "matrix.transpose_mul_vector", "matrix.bilinear", "matrix.shape_check",
   "vector.constant", "vector.scatter_sum", "vector.empty", "vector.append", "vector.splat", "vector.powers", "vector.add", "vector.sub", "vector.mul",
   "vector.scale", "vector.sum", "vector.dot", "vector.split", "vector.concat", "vector.at", "vector.length_check",
   "vector.gather", "vector.kronecker", "vector.matvec", "poly.from_coefficients", "poly.coefficients",
   "poly.degree_check", "poly.univariate_evaluate", "poly.univariate_boundary", "poly.boundary", "poly.round_evaluate"].contains contract

end Tools.Interactive.ScalarReference
