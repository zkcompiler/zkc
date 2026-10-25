import Zkc.Executable.Installed
import Mathlib.Algebra.Field.ZMod

/-! Controls for native numerical expression calls in the executable meaning.

The decoder reads the expression the compiled Sumcheck fold carries, and
refuses, each with its named reason, a body that is not the canonical encoding
of an arena, an oversized body, a constant outside the field, an operand that
does not point backward, an unreachable node, an embedding, a declared input
outside the call's field, more than one output, and declared inputs that are
not the mask's positions. Resolution through the installed vocabulary admits
one row for every mask and refuses a mask that is malformed, longer than 1023
positions or of another length than the expression's inputs. Evaluation on
a small concrete field (`ZMod 5`) broadcasts scalars over the rows, and refuses
an operand count or kind other than the mask's and a vector of another length.
-/

namespace Tests.ExecutableNumerical
open Zkc.Construction Zkc.Executable Zkc.Algebra.RingExpression

/-- The expression the compiled Sumcheck fold carries: `low + (high - low) r`
written as `in0 + (in1 + (-in0)) * in2`. -/
def interpolation : String :=
  "[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",1],[\"input\",2],[\"neg\",0],[\"add\",1,3],[\"mul\",4,2],[\"add\",0,5]],[6]]"

def decodeScalar (slots : Nat) (body : String) : Except Numerical.Refusal (Expr Nat Nat) :=
  Numerical.decode scalarField scalarCharacteristic slots body

def refusal (body : String) (slots : Nat := 1) : Option Numerical.Refusal :=
  match decodeScalar slots body with
  | .error reason => some reason
  | .ok _ => none

theorem interpolation_decodes :
    decodeScalar 3 interpolation = .ok (.add (.input 0) (.mul (.add (.input 1) (.neg (.input 0))) (.input 2))) := by
  decide +kernel

/-! ## Refused payloads -/

/-- Whitespace: the runtime refuses a body other than its canonical encoding. -/
theorem spaced_refused :
    refusal "[\"zkc.ring/0\", [\"bls12-381.fr\"], [[\"input\",0]], [0]]" = some .syntax := by decide +kernel

/-- A number with a leading zero is not canonical. -/
theorem leadingZero_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",00]],[0]]" = some .syntax := by decide +kernel

/-- A string with an escape is not a canonical payload. -/
theorem escape_refused :
    refusal "[\"zkc.ring/0\",[\"bls12\\u002d381.fr\"],[[\"input\",0]],[0]]" = some .syntax := by decide +kernel

/-- An unknown node kind. -/
theorem kind_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"sub\",0,0]],[0]]" = some .syntax := by decide +kernel

/-- A body of more than 4096 bytes is refused before it is read. -/
theorem oversized_refused (body : String) (slots : Nat)
    (oversized : Numerical.bodyLimit < Numerical.byteLength body.toList) :
    decodeScalar slots body = .error .bytes := by
  simp only [decodeScalar, Numerical.decode, oversized, ite_true]
  rfl

/-- 4097 one-byte characters are more than 4096 bytes. -/
theorem oversized_example : Numerical.bodyLimit < Numerical.byteLength (List.replicate 4097 ' ') := by
  decide +kernel

/-- A literal equal to the characteristic is not a field element. -/
theorem literal_refused :
    refusal "[\"zkc.ring/0\",[],[[\"constant\",\"bls12-381.fr\",\"52435875175126190479447740508185965837690552500527637822603658699938581184513\"]],[0]]"
      0 = some .literal := by
  decide +kernel

/-- A literal with a leading zero is not canonical. -/
theorem literalZero_refused :
    refusal "[\"zkc.ring/0\",[],[[\"constant\",\"bls12-381.fr\",\"07\"]],[0]]" 0 = some .literal := by
  decide +kernel

/-- The largest literal below the characteristic is admitted. -/
theorem literal_admitted :
    decodeScalar 0 "[\"zkc.ring/0\",[],[[\"constant\",\"bls12-381.fr\",\"52435875175126190479447740508185965837690552500527637822603658699938581184512\"]],[0]]" =
      .ok (.constant 52435875175126190479447740508185965837690552500527637822603658699938581184512) := by
  decide +kernel

/-- An operand that names a later node. -/
theorem forward_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"neg\",1],[\"input\",0]],[0]]" = some .edge := by
  decide +kernel

/-- An output that names no node. -/
theorem output_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[1]]" = some .edge := by decide +kernel

/-- An input node outside the declared inputs. -/
theorem slot_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",1]],[0]]" = some .input := by decide +kernel

/-- A node the output does not reach. -/
theorem unreachable_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0],[\"neg\",0],[\"input\",0]],[1]]" =
      some .unreachable := by
  decide +kernel

/-- An embedding. -/
theorem embedding_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0],[\"embed\",\"bls12-381.fr\",0]],[1]]" =
      some .embedding := by
  decide +kernel

/-- A declared input of another field. -/
theorem field_refused :
    refusal "[\"zkc.ring/0\",[\"bn254.fr\"],[[\"input\",0]],[0]]" = some .field := by decide +kernel

/-- Two outputs. -/
theorem outputs_refused :
    refusal "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0,0]]" = some .outputs := by decide +kernel

/-- Declared inputs that are not the mask's positions. -/
theorem slots_refused : refusal interpolation 2 = some .slots := by decide +kernel

/-! ## Resolution -/

def mapBinding (mask : String) : Binding :=
  ⟨"numerical", "numerical.map", [scalarField, mask], "arkworks/numerical.map", []⟩

/-- One installed row resolves every admissible mask. -/
theorem interpolation_resolves :
    installed.resolve (mapBinding "110") [.text interpolation] =
      some (.compute (.numerical .map scalarField [true, true, false]
        (.add (.input 0) (.mul (.add (.input 1) (.neg (.input 0))) (.input 2))))) := by
  decide +kernel

/-- The same row resolves a sum over another mask. -/
theorem sum_resolves :
    installed.resolve ⟨"numerical", "numerical.sum", [scalarField, "1"], "arkworks/numerical.sum", []⟩
        [.text "[\"zkc.ring/0\",[\"bls12-381.fr\"],[[\"input\",0]],[0]]"] =
      some (.compute (.numerical .sum scalarField [true] (.input 0))) := by
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

/-! ## Evaluation on a concrete field -/

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5
abbrev G := ZMod 5

def interpolationTree : Expr Nat Nat := .add (.input 0) (.mul (.add (.input 1) (.neg (.input 0))) (.input 2))

def apply (reduction : Numerical.Reduction) (mask : List Bool) (expression : Expr Nat Nat)
    (arguments : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  (Computation.numerical reduction scalarField mask expression).apply arguments

def vector (values : List F) : Value F G := .vector scalarField values
def scalar (value : F) : Value F G := .data (.field scalarField value)

/-- The scalar is broadcast: each row is `low + (high - low) * 2`. -/
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

theorem default_observation_installed :
    (installed.installed? (observeBinding [])).isSome = true := by decide +kernel

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
