import Zkc.Algebra.RingExpression.Sharing
import Tests.Checks

/-! Executable controls for arena sharing: the native sharing test's first
arena, its shared form and node map, and maps the law must reject. -/

set_option autoImplicit false

namespace Tests.RingExpressionSharing

open Zkc.Algebra.RingExpression

/-- `x*y + x*y` built twice, a repeated literal, repeated negations and a
repeated output position. -/
private def original : Arena Int Nat :=
  [.input 0, .input 1, .mul 0 1, .input 0, .input 1, .mul 3 4, .add 2 5,
   .constant 3, .constant 3, .mul 6 7, .add 8 9, .neg 2, .neg 5, .add 11 12]

private def shared : Arena Int Nat :=
  [.input 0, .input 1, .mul 0 1, .add 2 2, .constant 3, .mul 3 4, .add 4 5,
   .neg 2, .add 7 7]

private def image : List Nat := [0, 1, 2, 0, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8]
private def f (i : Nat) : Nat := image.getD i 0
private def outputs : List Nat := [10, 13, 10, 6]

example : original.WellFormed := by decide
example : shared.WellFormed := by decide
example : original.Hom f shared := by decide

-- Remapping x to y keeps every kind but not every slot.
example : ¬ original.Hom (fun i => if i = 3 then 1 else f i) shared := by decide

-- Swapped operands are a different node.
private def swapped : Arena Int Nat :=
  [.input 0, .input 1, .mul 1 0, .add 2 2, .constant 3, .mul 3 4, .add 4 5,
   .neg 2, .add 7 7]
example : ¬ original.Hom f swapped := by decide

-- A product by zero is not the literal zero, and a sum is not its value.
example : ¬ Arena.Hom (fun _ => 0) ([.input 0, .constant 0, .mul 0 1] : Arena Int Nat)
    [.constant 0] := by decide
example : ¬ Arena.Hom (fun _ => 0) ([.constant 1, .constant 2, .add 0 1] : Arena Int Nat)
    [.constant 3] := by decide

-- A map into an index the target does not have is not a node map.
example : ¬ original.Hom (fun i => if i = 13 then 9 else f i) shared := by decide

private def assignment (i : Nat) : Int := if i = 0 then 5 else 11

def run : IO Unit := do
  let checks ← Tests.Checks.start
  let trees := outputs.map (original.unfold original.length)
  checks.holds (trees == (outputs.map f).map (shared.unfold shared.length))
    "ordered outputs unfold to the trees of their images"
  checks.holds (outputs.map f == [6, 8, 6, 3]) "repeated output position kept"
  checks.holds (trees.map (Option.map (Expr.eval assignment)) ==
    [some 333, some (-110), some 333, some 110]) "reference values"
  checks.holds ((shared.unfold shared.length 6).map (Expr.degree fun _ => 1) == some 2)
    "unit-weight degree of the shared output"
  checks.holds ((shared.unfold shared.length 6).map (Expr.inputs) == some [0, 1, 0, 1])
    "syntactic input list of the shared output"
  checks.holds (original.unfold 4 10 == none) "fuel below the depth resolves nothing"
  checks.holds (shared.unfold 100 6 == shared.unfold 7 6) "fuel above the index is stable"
  checks.finish "arena sharing controls"

#eval run

end Tests.RingExpressionSharing
