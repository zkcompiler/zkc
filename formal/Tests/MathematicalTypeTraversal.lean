import Tests.MathematicalGraph
import Tests.Checks

/-! Wide structural types exercise the actual admission walkers. Run this file
with `LEAN_STACK_SIZE_KB=8192` to constrain the interpreter stack as well as the
declared constructor capacity. This is a regression suite, not a stack theorem.
-/

set_option autoImplicit false
namespace Tests.MathematicalTypeTraversal
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (Ty number publicPort algebra)

def rootSize (type : Ty) : Option TypeSize :=
  (Data.capacity.measure type).map (fun certificate => (Data.capacity.measurement certificate).size)

/-- The fixture builder is iterative too, so its stack usage cannot mask a
failure in aggregation. Every occurrence shares the same leaf certificate. -/
def children (count : Nat) : (types : List Ty) × Values Data.capacity.Measured types :=
  let certificate : Data.capacity.Measured number :=
    .boundary ⟨⟨1, 1⟩, rfl, rfl, by decide⟩
  (List.range count).foldl
    (fun acc _ => ⟨number :: acc.1, .cons certificate acc.2⟩) ⟨[], .nil⟩

def productSize (count : Nat) : Option TypeSize :=
  (Data.capacity.measureProduct (children count).2).map
    (fun certificate => (Data.capacity.measurement certificate).size)

def wrapped (count : Nat) (type : Ty) : Ty :=
  (List.range count).foldl (fun inner _ => .product [inner]) type

-- Distinct values catch order reversal even when a heterogeneous list has
-- repeated type indices. These equations are checked by the kernel.
example : (Values.cons (Value := fun _ : Nat => Nat) (ty := 0) 7
    (.cons (ty := 0) 9 .nil)).reverse = .cons 9 (.cons 7 .nil) := rfl

example : Values.ofList? (Value := fun _ : Nat => Nat) (fun n => some (n + 10)) [1, 3, 2] =
    some (.cons 11 (.cons 13 (.cons 12 .nil))) := rfl

example : Values.ofList? (Value := fun _ : Nat => Nat)
    (fun n => if n = 3 then none else some n) [1, 3, 2] = none := rfl

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (rootSize (.product (List.replicate 65535 number)) == some ⟨65536, 2⟩)
    "wide product accepts the exact constructor limit"
  checks.holds (rootSize (.product (List.replicate 65536 number)) == none)
    "wide product refuses one constructor beyond the limit"
  checks.holds (!(Data.Shape.measure 2 8 (.product (List.replicate 65535 number))).isSome)
    "small node allowance refuses a wide product"
  checks.holds (rootSize (wrapped 63 (.product (List.replicate 65472 number))) == some ⟨65536, 65⟩)
    "wide nested product reaches both structural boundaries"
  checks.holds (rootSize (wrapped 64 (.product (List.replicate 65471 number))) == none)
    "same node count refuses beyond the height boundary"
  checks.holds (productSize 65535 == some ⟨65536, 2⟩)
    "cached wide product accepts the exact constructor limit"
  checks.holds (productSize 65536 == none)
    "cached wide product includes its own root before acceptance"
  checks.holds (!(Data.capacity.aggregate (children 65537).2).isSome)
    "cached aggregation refuses an oversized prefix"
  checks.holds (Data.capacity.measureTypes (List.replicate 65535 number)).isSome
    "wide type list is assembled without recursive sibling frames"
  checks.holds (!(Data.capacity.measureTypes
    (List.replicate 65535 number ++ [wrapped 65 number])).isSome)
    "late malformed type refuses after a wide valid prefix"
  checks.holds ((Graph.decode (algebra := algebra) [0, 1] Data.capacity (fun _ => true) 65
    (List.replicate 65535 publicPort) (.outputs [])).isOk)
    "wide external context is measured by graph admission"
  checks.finish "mathematical structural traversal"

#eval run
end Tests.MathematicalTypeTraversal
