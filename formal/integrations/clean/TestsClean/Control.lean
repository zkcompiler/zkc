import ZkcClean.Control
import TestsClean.Bits
import TestsClean.Nested

/-! The native comparison control for the pinned Clean revision.

`lake env lean --run TestsClean/Control.lean` prints the control document on one
line. The maintained copy is `tests/fixtures/clean/air-control.json`; the
optional runner requires it to be byte-identical to this output.

Rows named `input-*` come from Clean's witness generator. `input-16` and the
input `p - 1` violate `toBits`' prover assumption `x < 16`; Clean rejects the
generated rows. `six`, `wrong-bit` and `non-boolean` are the rows of the kernel
controls in `TestsClean.Bits`, and the three mutations rewrite the actual export
into exactly the artifacts that `TestsClean.Mutations` relates to those
controls. The `is-equal-2` invalid rows change one witness cell of a generated
row.
-/

set_option autoImplicit false

namespace TestsClean.Control

open ZkcClean

def presentation : PrimePresentation KoalaBear := .ofPrime "koala-bear" koalaBear

def repository : String := "https://github.com/Verified-zkEVM/clean"
def revision : String := "b449bf590f93e13827c3c7e747e392d6969aa380"

def toBitsMutations : List (String × Mutation) :=
  [("altered-constant", .constant 4 2 3),
   ("altered-column", .column 4 1 2),
   ("deleted-assertion", .delete 0)]

def toBits : ComponentControl KoalaBear :=
  { name := "to-bits-4", declaration := "Gadgets.ToBits.toBits", component := Bits.component,
    rows :=
      ((List.range 17 ++ [koalaBear - 1]).map fun (x : Nat) =>
        (s!"input-{x}", generatedRow Bits.component [(x : KoalaBear)])) ++
      [("six", List.ofFn Bits.six), ("wrong-bit", List.ofFn Bits.wrongBit),
       ("non-boolean", List.ofFn Bits.nonBoolean)],
    mutations := toBitsMutations }

/-- Inputs `x₀ x₁ y₀ y₁`; equal pairs, a single differing coordinate, both
coordinates differing and values near the modulus. -/
def isEqualInputs : List (List KoalaBear) :=
  [[0, 0, 0, 0], [1, 2, 1, 2], [1, 2, 1, 3], [5, 7, 6, 7], [-1, 3, -1, 4], [0, 1, 1, 0]]

def isEqual : ComponentControl KoalaBear :=
  let generated := isEqualInputs.map (generatedRow Nested.component)
  let differing := generatedRow Nested.component [1, 2, 1, 3]
  { name := "is-equal-2", declaration := "Gadgets.IsEqual.circuit", component := Nested.component,
    rows :=
      (generated.zipIdx.map fun (row, index) => (s!"input-{index}", row)) ++
      -- Columns: inputs 0-3, then (inverse, flag) for each coordinate.
      [("flipped-flag", differing.set 7 1), ("wrong-inverse", differing.set 6 1)],
    mutations := [] }

def document : Except String Lean.Json := do
  unless generatedRow Bits.component [6] = List.ofFn Bits.six do
    throw "Clean's witness for 6 differs from the kernel control row"
  controlDocument presentation repository revision [toBits, isEqual]

end TestsClean.Control

/-- The process entry used by `lake env lean --run`. -/
def main : IO UInt32 := do
  match TestsClean.Control.document with
  | .ok json =>
      IO.println json.compress
      return 0
  | .error message =>
      IO.eprintln s!"clean-air-control: {message}"
      return 1
