import Zkc.Tests.Formal.MemberResolution

/-!
The rows that the finite model interprets mean the arithmetic.

A row of the vocabulary that the standard model does not interpret is given a constant. The
negation of a field element was such a row: at `x = 1`, `-x == 0` held in the finite model and
`0 - x == 0` did not. Each case is a function that tells the two apart by its value.
-/

open Zkc.Tests.Formal.MemberResolution

namespace Zkc.Tests.Formal.RowMeaning

/-- A function of one field element, applied to 1, whose value says whether `y` is zero. -/
def probe (y : String) : String :=
  "module client\n" ++
  "type F = primitive(\"bls12-381.fr\")\n" ++
  s!"pub def probe(x: F) -> nat:\n    y = {y}\n    return if y == 0 then 7 else 4\n" ++
  "pub def run() -> nat: probe(1)\n"

#eval show IO Unit from do
  expectValue "the element itself" (outcome (probe "x")) 4 []
  expectValue "zero minus the element" (outcome (probe "0 - x")) 4 []
  expectValue "the negation of the element" (outcome (probe "-x")) 4 []
  expectValue "the element minus itself" (outcome (probe "x - x")) 7 []
  expectValue "the element plus its negation" (outcome (probe "x + -x")) 7 []
  IO.println "the negation of a field element is the element taken from zero, in the finite model (5 cases)"

end Zkc.Tests.Formal.RowMeaning
