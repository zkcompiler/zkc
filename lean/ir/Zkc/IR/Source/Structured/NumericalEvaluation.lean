module

public import Zkc.IR.Source.Structured.DomainModels
public import Zkc.Program.Execution

@[expose] public section

/-! Computable numerical equations on the existing nominal model. Polynomial
interpolation is the coefficient-level Lagrange formula, independent of FFTs.
Only checked u64 representation bounds are imposed here; CPU allocation and
work policies require a separate adequacy relation. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace Numerical

abbrev Result := Except PIR.Stop

local instance (model : FieldModel) (d : String) : Inhabited (model.Field d) := ⟨0⟩

def require (condition : Prop) [Decidable condition] : Result Unit :=
  if condition then .ok () else .error .refused

def size (n : Nat) : Result Unit :=
  if n < indexLimit then .ok () else .error .exhausted

def finish {α : Type} : Result α → PIR.Outcome α
  | .ok value => .returned value
  | .error stop => .stopped stop

mutual
  /-- Logical u64 ingress bounds; scalar range errors and unrepresentable
  collection lengths retain their distinct refusal/exhaustion outcomes. -/
  def checkValue (model : FieldModel) : (ty : Ty) → model.Value ty → Result Unit
    | .index, n => require (n < indexLimit)
    | .indices, xs => do
      size xs.length
      require (xs.all (· < indexLimit) = true)
    | .vector _, xs | .groups _, xs => size xs.length
    | .polynomial _, p => do
      size p.coefficients.length
      require (p.zero = 0)
    | .sequence ty, xs => do
      size xs.length
      xs.forM (checkValue model ty)
    | .product _ _ fields, value => checkProduct model fields value
    | _, _ => .ok ()
  def checkProduct (model : FieldModel) : (fields : ProductFields) →
      model.ProductValue fields → Result Unit
    | .nil, _ => .ok ()
    | .cons ty rest, (value, values) => do
      checkValue model ty value
      checkProduct model rest values
end

def checkValues (model : FieldModel) : {types : List Ty} →
    Values model.Value types → Result Unit
  | [], .nil => .ok ()
  | ty :: _, .cons value rest => do
    checkValue model ty value
    checkValues model rest

def inverse (model : FieldModel) (d : String) (value : model.Field d) : Result (model.Field d) := do
  require (value ≠ 0)
  let some inv := model.inverse d | .error .refused
  return inv value

/-- Select the stored base-field root, embedded into the operation's field.
The length check precedes the shift check. No extension-field root is chosen. -/
def domainRoot (model : FieldModel) (d : String) (n : Nat) : Result (model.Field d) := do
  require (0 < n ∧ n < indexLimit ∧ 2 ^ n.log2 = n)
  let some family := model.twoAdic d | .error .refused
  let some value := family.roots[n.log2]? | .error .refused
  return model.embed d family.base value

def points (model : FieldModel) (d : String) (shift : model.Field d) (n : Nat) :
    Result (List (model.Field d)) := do
  let generator ← domainRoot model d n
  require (shift ≠ 0)
  return (List.range n).map fun i ↦ shift * generator ^ i

/-- Ascending coefficients, evaluated by Horner's equation. -/
def evaluate {F : Type} [CommRing F] (coefficients : List F) (x : F) : F :=
  coefficients.foldr (fun a acc ↦ a + x * acc) 0

def add {F : Type} [CommRing F] : List F → List F → List F
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: add as bs

def multiply {F : Type} [CommRing F] : List F → List F → List F
  | [], _ => []
  | a :: as, b => add (b.map (a * ·)) (0 :: multiply as b)

/-- Direct Lagrange coefficients; an absent inverse is a refusal, and a
duplicate abscissa cannot silently become a truncated interpolant. -/
def interpolate (model : FieldModel) (d : String) (values : List (model.Field d))
    (shift : model.Field d) : Result (List (model.Field d)) := do
  let xs ← points model d shift values.length
  let terms ← (List.range values.length).mapM fun i ↦ do
    let xi := xs[i]!
    let others := (xs.zipIdx).filter (fun pair ↦ pair.2 != i) |>.map Prod.fst
    let denominator := (others.map (xi - ·)).foldl (· * ·) 1
    let inv ← inverse model d denominator
    let basis := others.foldl (fun acc x ↦ multiply acc [-x, 1]) [1]
    return basis.map (fun a ↦ a * (values[i]! * inv))
  return terms.foldl add []

def batchShape {F : Type} (values : List F) (width height : Nat) : Result Unit := do
  size (width * height)
  require (values.length = width * height)

def evaluateBatch (model : FieldModel) (d : String) (coefficients : List (model.Field d))
    (width height : Nat) (shift : model.Field d) (n : Nat) : Result (List (model.Field d)) := do
  batchShape coefficients width height
  size (width * n)
  if width = 0 then return []
  let xs ← points model d shift n
  let columns ← (List.range width).mapM fun column ↦ do
    let cs := (coefficients.drop (column * height)).take height
    require ((cs.drop n).all (· == 0) = true)
    return xs.map (evaluate cs)
  return columns.flatten

def bitReverse (bits index : Nat) : Nat :=
  (List.range bits).foldl (fun acc i ↦ 2 * acc + (index / 2 ^ i) % 2) 0

def inclusivePrefix {F : Type} (combine : F → F → F) : List F → F → List F
  | [], _ => []
  | x :: xs, acc => let next := combine acc x; next :: inclusivePrefix combine xs next

/-- Ascending polynomial-basis coordinates; natural casts would lose binary bits. -/
def binaryBasisValue {F : Type} [CommRing F] (basis : List F) (bits : Nat) : F :=
  basis.zipIdx.foldl
    (fun acc pair ↦ if (bits / 2 ^ pair.2) % 2 = 1 then acc + pair.1 else acc) 0

/-- Fixed bit interpretation from a stored ascending polynomial basis. -/
def binaryValue (model : FieldModel) (d : String) (bits : Nat) : Result (model.Field d) := do
  let some data := model.binary d | .error .refused
  require (bits < 2 ^ data.basis.length)
  return binaryBasisValue data.basis bits

def evaluateOn (model : FieldModel) (d base : String) : (op : Numerical) →
    Values model.Value (op.arguments d base) →
      PIR.Outcome (Values model.Value (op.results d base))
  | .fieldInverse, .cons x .nil => finish do
    return .cons (← inverse model d x) .nil
  | .indicesEmpty, .nil => .returned (.cons [] .nil)
  | .indicesAppend, .cons xs (.cons i .nil) => finish do
    size (xs.length + 1)
    return .cons (xs ++ [i]) .nil
  | .indicesAt, .cons xs (.cons i .nil) => finish do
    let some x := xs[i]? | .error .refused
    return .cons x .nil
  | .indicesLength, .cons xs .nil => finish do
    size xs.length
    return .cons xs.length .nil
  | .polyFromCoefficients, .cons xs .nil =>
    .returned (.cons (PolynomialValue.ofCoefficients 0 xs) .nil)
  | .polyCoefficients, .cons p .nil => .returned (.cons p.coefficients .nil)
  | .polyEvaluate, .cons p (.cons x .nil) =>
    .returned (.cons (evaluate p.coefficients x) .nil)
  | .polyInterpolate, .cons xs (.cons shift .nil) => finish do
    return .cons (PolynomialValue.ofCoefficients 0 (← interpolate model d xs shift)) .nil
  | .polyRoot, .cons n .nil => finish do
    return .cons (← domainRoot model d n) .nil
  | .polyPoint, .cons shift (.cons n (.cons i .nil)) => finish do
    let generator ← domainRoot model d n
    require (shift ≠ 0)
    require (i < n)
    return .cons (shift * generator ^ i) .nil
  | .polyPoints, .cons shift (.cons n .nil) => finish do
    return .cons (← points model d shift n) .nil
  | .polyFold, .cons xs (.cons shift (.cons beta .nil)) => finish do
    let domain ← points model d shift xs.length
    require (2 ≤ xs.length)
    let half ← inverse model d 2
    let folded ← (List.range (xs.length / 2)).mapM fun i ↦ do
      let xi := domain[i]!
      let inv ← inverse model d xi
      let a := xs[i]!
      let b := xs[i + xs.length / 2]!
      return (a + b) * half + beta * (a - b) * half * inv
    return .cons folded .nil
  | .vectorConcat, .cons xs (.cons ys .nil) => finish do
    size (xs.length + ys.length)
    return .cons (xs ++ ys) .nil
  | .vectorFill, .cons x (.cons n .nil) => .returned (.cons (List.replicate n x) .nil)
  | .vectorGet, .cons xs (.cons i .nil) => finish do
    let some x := xs[i]? | .error .refused
    return .cons x .nil
  | .vectorAdd, .cons xs (.cons ys .nil) => finish do
    require (xs.length = ys.length)
    return .cons (List.zipWith (· + ·) xs ys) .nil
  | .vectorSub, .cons xs (.cons ys .nil) => finish do
    require (xs.length = ys.length)
    return .cons (List.zipWith (· - ·) xs ys) .nil
  | .vectorMul, .cons xs (.cons ys .nil) => finish do
    require (xs.length = ys.length)
    return .cons (List.zipWith (· * ·) xs ys) .nil
  | .vectorScale, .cons xs (.cons a .nil) => .returned (.cons (xs.map (· * a)) .nil)
  | .vectorInverse, .cons xs .nil => finish do
    require (xs.all (· != 0) = true)
    return .cons (← xs.mapM (inverse model d)) .nil
  | .vectorGeometric, .cons a (.cons n .nil) =>
    .returned (.cons ((List.range n).map (a ^ ·)) .nil)
  | .vectorSlice, .cons xs (.cons start (.cons count .nil)) => finish do
    require (start + count < indexLimit ∧ start ≤ xs.length ∧ start + count ≤ xs.length)
    return .cons ((xs.drop start).take count) .nil
  | .vectorTranspose, .cons xs (.cons rows (.cons cols .nil)) => finish do
    require (rows * cols < indexLimit ∧ xs.length = rows * cols)
    if rows * cols = 0 then return .cons [] .nil
    return .cons ((List.range cols).flatMap fun c ↦
      (List.range rows).map fun r ↦ xs[r * cols + c]!) .nil
  | .vectorEmbed, .cons xs .nil => .returned (.cons (xs.map (model.embed d base)) .nil)
  | .vectorRotate, .cons xs (.cons k .nil) => finish do
    require (k < xs.length)
    return .cons (xs.drop k ++ xs.take k) .nil
  | .vectorBitReverseRows, .cons xs (.cons width .nil) => finish do
    require (0 < width ∧ xs.length % width = 0)
    let height := xs.length / width
    require (0 < height ∧ 2 ^ height.log2 = height)
    return .cons ((List.range height).flatMap fun r ↦
      (xs.drop (bitReverse height.log2 r * width)).take width) .nil
  | .vectorPrefixSum, .cons xs .nil => .returned (.cons (inclusivePrefix (· + ·) xs 0) .nil)
  | .vectorPrefixProduct, .cons xs .nil => .returned (.cons (inclusivePrefix (· * ·) xs 1) .nil)
  | .polyEvaluateBatch, .cons xs (.cons w (.cons h (.cons s (.cons n .nil)))) => finish do
    return .cons (← evaluateBatch model d xs w h s n) .nil
  | .polyEvaluateAt, .cons xs (.cons w (.cons h (.cons s (.cons z .nil)))) => finish do
    batchShape xs w h
    if w = 0 then return .cons [] .nil
    let columns ← (List.range w).mapM fun j ↦ do
      let cs ← interpolate model d ((xs.drop (j * h)).take h) s
      return evaluate cs z
    return .cons columns .nil
  | .polyExtend, .cons xs (.cons w (.cons h (.cons s (.cons t (.cons n .nil))))) => finish do
    batchShape xs w h
    size (w * n)
    if w = 0 then return .cons [] .nil
    let columns ← (List.range w).mapM fun j ↦ do
      let cs ← interpolate model d ((xs.drop (j * h)).take h) s
      evaluateBatch model d cs 1 cs.length t n
    return .cons columns.flatten .nil
  | .polyOpeningSum,
      .cons xs (.cons w (.cons h (.cons s (.cons columns (.cons zs
        (.cons claims (.cons weights (.cons initial .nil)))))))) => finish do
    batchShape xs w h
    require (columns.length = zs.length ∧ columns.length = claims.length ∧
      columns.length = weights.length ∧ initial.length = h)
    if columns.isEmpty then return .cons initial .nil
    let domain ← points model d s h
    -- Validate all descriptors, even those with zero weights, in source order.
    let inverses ← (List.range columns.length).mapM fun j ↦ do
      require (columns[j]! < w)
      require (domain.all (· != zs[j]!) = true)
      domain.mapM fun x ↦ inverse model d (x - zs[j]!)
    let result := (List.range h).map fun i ↦
      initial[i]! + ((List.range columns.length).map fun j ↦
        weights[j]! * (xs[columns[j]! * h + i]! - claims[j]!) * (inverses[j]!)[i]!).foldl
          (· + ·) 0
    return .cons result .nil

/-- Every argument is checked, including values unused by an empty branch. -/
def checkedEvaluateOn (model : FieldModel) (d base : String) (op : Numerical)
    (args : Values model.Value (op.arguments d base)) :
    PIR.Outcome (Values model.Value (op.results d base)) :=
  match checkValues model args with
  | .ok () => evaluateOn model d base op args
  | .error stop => .stopped stop

end Numerical
end Zkc.Source.Structured
