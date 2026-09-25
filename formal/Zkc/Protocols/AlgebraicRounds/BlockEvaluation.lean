import Zkc.Protocols.AlgebraicRounds.Scalar
import Zkc.Compiler.Blocks.Rewriting

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.BlockEvaluation
open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Compiler.Blocks
def inputs {F : Type} [Zero F] (g : Round F) : Nat → F
  | 0 => g.a | 1 => g.b | 2 => g.c | 3 => g.r | _ => 0

def moduleValue {F : Type} [Semiring F] (block : Block F) (slot : Nat)
    (g : Round F) : F := runBlock Zkc.Compiler.Blocks.arithmetic (fun _ => false) block (inputs g) slot

-- This consumes the actual executed template predicate and its soundness
-- theorem, rather than assuming a separately authored Horner evaluator equal.
theorem checked_values {F : Type} [CommRing F] [DecidableEq F]
    (source target : Block F) (ss ts : Nat)
    (ok : Zkc.Compiler.Blocks.hornerCheck source target ss ts = true) (g : Round F) :
    moduleValue source ss g = value g ∧ moduleValue target ts g = value g := by
  have form := of_decide_eq_true ok
  have hs := Zkc.Compiler.Blocks.expansion_sound Zkc.Compiler.Blocks.arithmetic (fun _ : F => false)
    (inputs g) source Expr.input ss
  rw [form.1] at hs
  have hquad : eval Zkc.Compiler.Blocks.arithmetic (fun _ : F => false) (inputs g) Zkc.Compiler.Blocks.quadratic =
      value g := by simp [eval, Zkc.Compiler.Blocks.quadratic, Zkc.Compiler.Blocks.arithmetic, inputs, value, add_assoc]
  have hsource : moduleValue source ss g = value g := hs.symm.trans hquad
  have heq := Zkc.Compiler.Blocks.checked_horner (fun _ : F => false) source target ss ts ok (inputs g) trivial
  simp only [Zkc.Compiler.Blocks.exports, List.map_cons, List.map_nil, List.cons.injEq, and_true] at heq
  exact ⟨hsource, heq.symm.trans hsource⟩


end Zkc.Protocols.AlgebraicRounds.BlockEvaluation
