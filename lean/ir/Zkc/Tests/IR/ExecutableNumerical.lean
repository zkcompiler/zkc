import Zkc.IR.Executable.Installed
import Mathlib.Algebra.Field.ZMod

/-! Controls for native numerical expression calls in the executable meaning.

The decoder reads the physical plan the compiled Sumcheck fold carries, and
refuses, each with its named reason, a bare expression without its plan, a
payload that is not the canonical encoding of a plan, an oversized plan or
expression, a constant outside the field, an operand that does not point
backward, an unreachable node, an embedding, a declared input outside the
call's field, more than one output, declared inputs that are not the mask's
positions, lanes, slot counts and locations out of range or leaving a slot
unused, and slot schedules that read an overwritten operand or overwrite a value
needed across chunks. Resolution through the installed vocabulary admits one
row for every mask and refuses a mask that is malformed, longer than 1023
positions or of another length than the expression's inputs. Evaluation on a
small concrete field (`ZMod 5`) broadcasts scalars over the rows, and refuses
an operand count or kind other than the mask's and a vector of another length.
-/

namespace Tests.ExecutableNumerical
open Zkc.Construction Zkc.Executable Zkc.Algebra.RingExpression

section DecimalCount
open Numerical

/-- The transparent counter agrees with the standard decimal formatter for
all structural bounds, including zero. -/
theorem digitCountWith_eq_length (fuel value : Nat) (suffix : List Char) :
    digitCountWith fuel value + suffix.length = (Nat.toDigitsCore 10 fuel value suffix).length := by
  induction fuel generalizing value suffix with
  | zero => simp [digitCountWith, Nat.toDigitsCore]
  | succ fuel ih =>
      simp only [digitCountWith, Nat.toDigitsCore]
      by_cases small : value < 10
      · have zero : value / 10 = 0 := Nat.div_eq_of_lt small
        simp [small, zero, Nat.add_comm]
      · have nonzero : value / 10 ≠ 0 := by omega
        simp only [small, nonzero, ite_false]
        rw [← ih]
        simp [Nat.add_assoc, Nat.add_comm]

theorem digitCount_eq_length (value : Nat) : digitCount value = (Nat.toDigits 10 value).length := by
  simpa only [digitCount, Nat.toDigits, List.length_nil, Nat.add_zero] using
    digitCountWith_eq_length (value + 1) value []

end DecimalCount

/-- The plan the compiled Sumcheck fold carries: `low + r (high - low)` written
as `in0 + in2 * (in1 + (-in0))`, with the challenge `in2` a broadcast scalar. -/
def interpolation : String :=
  "[\"zkc.numerical-plan/0\",[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",2],[\"input\",1],[\"neg\",0],[\"add\",2,3],[\"mul\",1,4],[\"add\",0,5]],[6]],256,4,[1,0,2,3,2,2,1]]"

/-- The decoded interpolation. -/
def interpolationTree : Expr Nat Nat :=
  .add (.input 0) (.mul (.input 2) (.add (.input 1) (.neg (.input 0))))

/-- The plan of `expression` with the given lanes, slot count and locations. -/
def plan (expression : String) (lanes slots : Nat) (locations : String) : String :=
  "[\"zkc.numerical-plan/0\"," ++ expression ++ "," ++ toString lanes ++ "," ++ toString slots ++ "," ++
    locations ++ "]"

/-- A one-node plan of `expression`. -/
def single (expression : String) : String := plan expression 1 1 "[0]"

def decodeScalar (mask : List Bool) (body : String) : Except Numerical.Refusal (Expr Nat Nat) :=
  Numerical.decode scalarField scalarCharacteristic mask body

def refusal (body : String) (mask : List Bool := [true]) : Option Numerical.Refusal :=
  match decodeScalar mask body with
  | .error reason => some reason
  | .ok _ => none

theorem interpolation_decodes : decodeScalar [true, true, false] interpolation = .ok interpolationTree := by
  decide +kernel

/-! ## Refused payloads -/

/-- The bare expression is not a plan. -/
theorem bare_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0]]" = some .syntax := by decide +kernel

/-- Whitespace: the runtime refuses a payload other than its canonical encoding. -/
theorem spaced_refused :
    refusal (plan "[\"zkc.ring/0\", [\"bls12-381.fr\"], [[\"input\",0]], [0]]" 1 1 "[0]") = some .syntax := by
  decide +kernel

/-- A number with a leading zero is not canonical. -/
theorem leadingZero_refused :
    refusal (plan "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0]]" 1 1 "[00]") = some .syntax := by
  decide +kernel

/-- A string with an escape is not a canonical payload. -/
theorem escape_refused :
    refusal (single "[\"zkc.ring/0\",[\"bls12\\u002d381.fr\"],[[\"input\",0]],[0]]") = some .syntax := by
  decide +kernel

/-- An unknown node kind. -/
theorem kind_refused :
    refusal (single "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"sub\",0,0]],[0]]") = some .syntax := by
  decide +kernel

/-- Another plan version, and a plan with an extra field. -/
theorem version_refused :
    refusal "[\"zkc.numerical-plan/1\",[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0]],1,1,[0]]" =
        some .syntax ∧
      refusal (plan "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0]]" 1 1 "[0],[]") = some .syntax := by
  decide +kernel

/-- A plan of more than 16384 bytes is refused before it is read. -/
theorem oversized_refused (body : String) (mask : List Bool)
    (oversized : Numerical.planLimit < Numerical.byteLength body.toList) :
    decodeScalar mask body = .error .bytes := by
  simp only [decodeScalar, Numerical.decode, Numerical.plan?, oversized, ite_true]
  rfl

/-- 16385 one-byte characters are more than 16384 bytes. -/
theorem oversized_example : Numerical.planLimit < Numerical.byteLength (List.replicate 16385 ' ') := by
  decide +kernel

/-- A literal equal to the characteristic is not a field element. -/
theorem literal_refused :
    refusal (single "[\"zkc.ring/0\",[],[[\"constant\",\"bls12-381.fr\",\"52435875175126190479447740508185965837690552500527637822603658699938581184513\"]],[0]]")
      [] = some .literal := by
  decide +kernel

/-- A literal with a leading zero is not canonical. -/
theorem literalZero_refused :
    refusal (single "[\"zkc.ring/0\",[],[[\"constant\",\"bls12-381.fr\",\"07\"]],[0]]") [] = some .literal := by
  decide +kernel

/-- The largest literal below the characteristic is admitted. -/
theorem literal_admitted :
    decodeScalar [] (single "[\"zkc.ring/0\",[],[[\"constant\",\"bls12-381.fr\",\"52435875175126190479447740508185965837690552500527637822603658699938581184512\"]],[0]]") =
      .ok (.constant 52435875175126190479447740508185965837690552500527637822603658699938581184512) := by
  decide +kernel

/-- An operand that names a later node. -/
theorem forward_refused :
    refusal (plan "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"neg\",1],[\"input\",0]],[0]]" 1 2 "[0,1]") =
      some .edge := by
  decide +kernel

/-- An output that names no node. -/
theorem output_refused :
    refusal (single "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[1]]") = some .edge := by decide +kernel

/-- An input node outside the declared inputs. -/
theorem slot_refused :
    refusal (single "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",1]],[0]]") = some .input := by decide +kernel

/-- A node the output does not reach. -/
theorem unreachable_refused :
    refusal (plan "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0],[\"neg\",0],[\"input\",0]],[1]]" 1 3 "[0,1,2]") =
      some .unreachable := by
  decide +kernel

/-- An embedding. -/
theorem embedding_refused :
    refusal (plan "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0],[\"embed\",\"bls12-381.fr\",0]],[1]]" 1 2 "[0,1]") =
      some .embedding := by
  decide +kernel

/-- A declared input of another field. -/
theorem field_refused :
    refusal (single "[\"zkc.ring/0\",[\"bn254.fr\"],[[\"input\",0]],[0]]") = some .field := by decide +kernel

/-- Two outputs. -/
theorem outputs_refused :
    refusal (single "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0,0]]") = some .outputs := by decide +kernel

/-- Declared inputs that are not the mask's positions. -/
theorem slots_refused : refusal interpolation [true, true] = some .slots := by decide +kernel

/-! ## Lanes, slots and locations -/

/-- The schedule fixture of the runtime reader: `(in0 + in1 * in1) ^ 2`. -/
def square : String :=
  "[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",1],[\"mul\",1,1],[\"add\",0,2],[\"mul\",3,3]],[4]]"

theorem square_admitted :
    (decodeScalar [true, false] (plan square 8 2 "[1,0,0,1,1]")).isOk = true ∧
      (decodeScalar [true, false] (plan square 256 5 "[0,1,2,3,4]")).isOk = true ∧
      (decodeScalar [false, true] (plan square 1 5 "[0,1,2,3,4]")).isOk = true := by
  decide +kernel

theorem planShape_refused :
    refusal (plan square 0 2 "[1,0,0,1,1]") [true, false] = some .shape ∧
      refusal (plan square 257 2 "[1,0,0,1,1]") [true, false] = some .shape ∧
      refusal (plan square 8 0 "[1,0,0,1,1]") [true, false] = some .shape ∧
      refusal (plan square 8 6 "[0,1,2,3,4]") [true, false] = some .shape ∧
      refusal (plan square 8 3 "[1,0,0,1,1]") [true, false] = some .shape ∧
      refusal (plan square 8 2 "[1,0,0,1]") [true, false] = some .shape ∧
      refusal (plan square 8 2 "[1,0,0,1,2]") [true, false] = some .shape := by
  decide +kernel

/-- A stale slot map reads an overwritten operand or overwrites the persistent
invariant `in1 * in1`; the same map under another mask overwrites the persistent
invariant input. -/
theorem schedule_refused :
    refusal (plan square 8 2 "[0,0,0,1,1]") [true, false] = some .schedule ∧
      refusal (plan square 8 2 "[1,0,0,0,1]") [true, false] = some .schedule ∧
      refusal (plan square 8 2 "[1,0,0,1,0]") [true, false] = some .schedule ∧
      refusal (plan square 8 2 "[1,0,0,1,1]") [false, true] = some .schedule := by
  decide +kernel

/-! ## Running an admitted schedule -/

/-- The nodes of `square`. -/
def squareNodes : List Numerical.Node :=
  [.input 0, .input 1, .mul 1 1, .add 0 2, .mul 3 3]

/-- Chunk `k` of the square plan on naturals: the vector operand is `3 + k` and
the scalar operand is `2`. -/
def squareSteps (chunk : Nat) : Numerical.Node → List Nat → Nat
  | .input 0, _ => 3 + chunk
  | .input _, _ => 2
  | .add _ _, [a, b] => a + b
  | .mul _ _, [a, b] => a * b
  | _, _ => 0

/-- The schedule that reuses both slots runs every chunk, keeping the invariant
`in1 * in1` across chunks: the output slot holds `(in0 + in1 * in1) ^ 2` of the
last chunk run, `(3 + 4) ^ 2` and then `(4 + 4) ^ 2`. -/
theorem square_runs :
    ((Numerical.schedule [true, false] squareNodes 2 4 [1, 0, 0, 1, 1]).bind fun schedule =>
        schedule.run squareSteps 0).map (·.getD 1 none) = some (some 49) ∧
      ((Numerical.schedule [true, false] squareNodes 2 4 [1, 0, 0, 1, 1]).bind fun schedule =>
        schedule.run squareSteps 1).map (·.getD 1 none) = some (some 64) := by
  decide +kernel

/-! ## Resolution -/

def mapBinding (mask : String) : Binding :=
  ⟨"numerical", "numerical.map", [scalarField, mask], "arkworks/numerical.map", []⟩

/-- One installed row resolves every admissible mask. -/
theorem interpolation_resolves :
    installed.resolve (mapBinding "110") [.text interpolation] =
      some (.compute (.numerical .map scalarField [true, true, false] interpolationTree)) := by
  decide +kernel

/-- The same row resolves a sum over another mask. -/
theorem sum_resolves :
    installed.resolve ⟨"numerical", "numerical.sum", [scalarField, "1"], "arkworks/numerical.sum", []⟩
        [.text (single "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0]]")] =
      some (.compute (.numerical .sum scalarField [true] (.input 0))) := by
  decide +kernel

/-- A bare expression has no meaning. -/
theorem bare_unresolved :
    installed.resolve (mapBinding "1") [.text "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0]]"] = none := by
  decide +kernel

/-- A mask whose length is not the expression's inputs. -/
theorem maskMismatch_refused : installed.resolve (mapBinding "11") [.text interpolation] = none := by
  decide +kernel

/-- A mask position other than `0` or `1`. -/
theorem maskDigit_refused : installed.resolve (mapBinding "120") [.text interpolation] = none := by
  decide +kernel

/-- A mask of more than 1023 positions is refused. -/
theorem mask_bound (text : String) (long : Numerical.slotLimit < text.toList.length) :
    Numerical.mask? text = none := by
  simp [Numerical.mask?, Nat.not_le.mpr long]

/-- A binding without its mask names no installed row. -/
theorem unmasked_uninstalled :
    installed.installed? ⟨"numerical", "numerical.map", [scalarField], "arkworks/numerical.map", []⟩ = none := by
  decide +kernel

/-- A refused payload has no meaning. -/
theorem malformed_unresolved :
    installed.resolve (mapBinding "110") [.text (interpolation ++ " ")] = none := by
  decide +kernel

/-! ## Expression size within a plan -/

/-- A chain of `count` negations of the single input. -/
def chain (count : Nat) : String :=
  "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]" ++
    String.join ((List.range count).map fun index => ",[\"neg\"," ++ toString index ++ "]") ++
    "]," ++ "[" ++ toString count ++ "]]"

/-- Its plan in one slot per node. -/
def chainPlan (count : Nat) : String :=
  plan (chain count) 1 (count + 1)
    ("[" ++ ",".intercalate ((List.range (count + 1)).map toString) ++ "]")

/-- The expression bound applies to the nested expression alone: a plan within
16384 bytes whose expression is just over 4096 bytes is refused, and one just
under it is admitted. -/
def sizes : IO Unit := do
  let under := (List.range 500).reverse.find? fun count => (chain count).utf8ByteSize ≤ 4096
  let some under := under | throw (IO.userError "no chain fits the expression bound")
  unless (chain (under + 1)).utf8ByteSize > 4096 && (chainPlan (under + 1)).utf8ByteSize ≤ 16384 do
    throw (IO.userError "chain sizes do not straddle the expression bound")
  unless (decodeScalar [true] (chainPlan under)).isOk do
    throw (IO.userError "an expression within its bound refused")
  unless refusal (chainPlan (under + 1)) == some .bytes do
    throw (IO.userError "an expression over its bound admitted")
  IO.println s!"numerical plan size controls passed at {under} and {under + 1} nodes"

#eval sizes

/-! ## Evaluation on a concrete field -/

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5
abbrev G := ZMod 5

def apply (reduction : Numerical.Reduction) (mask : List Bool) (expression : Expr Nat Nat)
    (arguments : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  (Computation.numerical reduction scalarField mask expression).apply arguments

def vector (values : List F) : Value F G := .vector scalarField values
def scalar (value : F) : Value F G := .data (.field scalarField value)

/-- The scalar is broadcast: each row is `low + 2 * (high - low)`. -/
theorem map_rows :
    apply .map [true, true, false] interpolationTree [.index 2, vector [1, 2], vector [3, 4], scalar 2] =
      .returned [vector [0, 1]] := by
  decide +kernel

/-- A sum and a product over the rows. -/
theorem sum_and_product :
    apply .sum [true] (.input 0) [.index 3, vector [1, 2, 3]] = .returned [scalar 1] ∧
      apply .product [true] (.input 0) [.index 3, vector [1, 2, 3]] = .returned [scalar 1] ∧
      apply .sum [true] (.input 0) [.index 0, vector []] = .returned [scalar 0] ∧
      apply .product [true] (.input 0) [.index 0, vector []] = .returned [scalar 1] := by
  decide +kernel

/-- An operand missing for a mask position. -/
theorem operandCount_refused :
    apply .map [true, true, false] interpolationTree [.index 2, vector [1, 2], vector [3, 4]] =
      .stopped .refused := by
  decide +kernel

/-- A scalar where the mask names a vector. -/
theorem operandKind_refused :
    apply .map [true, true, false] interpolationTree [.index 2, vector [1, 2], scalar 3, scalar 2] =
      .stopped .refused := by
  decide +kernel

/-- A vector whose length is not the row count, including one the expression
does not read. -/
theorem shape_refused :
    apply .map [true, true, false] interpolationTree [.index 2, vector [1, 2], vector [3, 4, 0], scalar 2] =
      .stopped .refused ∧
      apply .map [true, true] (.input 0) [.index 2, vector [1, 2], vector [3]] = .stopped .refused := by
  decide +kernel

/-! ## Exact physical specialization -/

def observeBinding (physical : List PhysicalType) : Binding :=
  ⟨"observe", "transcript.native.indexed.observe.data", [nativeSuite, "field:bls12-381.fr"],
    "arkworks/transcript.native.indexed.observe.data", physical⟩

theorem missing_observation_specialization_refused :
    installed.installed? (observeBinding []) = none := by decide +kernel

theorem explicit_observation_installed :
    (installed.installed? (observeBinding
      [⟨.data (.field scalarField), "arkworks.fr/0"⟩])).isSome = true := by decide +kernel

/-- The logical field does not authorize a different physical layout. -/
theorem foreign_observation_layout_refused :
    installed.installed? (observeBinding
      [⟨.data (.field scalarField), "foreign.fr/0"⟩]) = none := by decide +kernel

/-- A known layout of a different payload cannot substitute for the field. -/
theorem crossed_observation_layout_refused :
    installed.installed? (observeBinding
      [⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩]) = none := by decide +kernel

theorem duplicate_observation_layout_refused :
    installed.installed? (observeBinding
      [⟨.data (.field scalarField), "arkworks.fr/0"⟩,
       ⟨.data (.field scalarField), "arkworks.fr/0"⟩]) = none := by decide +kernel

/-- Admitting a transcript layout grants no specialization to other kernels. -/
theorem numerical_specialization_refused :
    installed.installed? { mapBinding "1" with
      physicalArguments := [⟨.data (.field scalarField), "arkworks.fr/0"⟩] } = none := by decide +kernel

end Tests.ExecutableNumerical
