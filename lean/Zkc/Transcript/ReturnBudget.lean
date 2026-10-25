module

public import Zkc.Transcript.Budget
public import Zkc.Semantics.Boundary

public section

/-! Return-sensitive composition of the existing path bound. The caller relates
its logical phase to the actual walk position and proves that each walk edge
preserves that relation. No cost evaluator or operational semantics is added.
-/

set_option autoImplicit false
namespace Zkc.Transcript.Walk

variable {I : PIR.Signature} {A B Position Cost : Type}
  [AddCommMonoid Cost] [Preorder Cost] [IsOrderedAddMonoid Cost]

/-- The suffix budget is required only at related returns. Both the return
fact and the relation follow the actual typed reply and `walk.next` edge.
Stops do not execute a suffix. Choosing the constantly true relation recovers
the conservative rule requiring a suffix bound at every position. -/
theorem Bound.bind_of_returns (walk : Walk I Position Cost)
    (nonneg : ∀ cost : Cost, 0 ≤ cost) (interaction : PIR.Interaction I)
    (post : A → interaction.Phase → Prop)
    (related : interaction.Phase → Position → Prop)
    (preserved : ∀ phase position operation reply later,
      related phase position → walk.next position operation reply later →
        related (interaction.advance phase operation reply) later)
    (next : A → PIR.Process I B) {second : Cost}
    (suffix : ∀ value phase position, post value phase → related phase position →
      walk.Bound (next value) position second) :
    ∀ (first : PIR.Process I A) phase position budget,
      PIR.Boundary.Returns interaction post first phase →
      related phase position → walk.Bound first position budget →
        walk.Bound (first.bind next) position (budget + second)
  | .done value, phase, position, budget, returns, link, _ =>
      Bound.mono walk _ (suffix value phase position returns link)
        (le_add_of_nonneg_left (nonneg budget))
  | .halt _, _, _, _, _, _, _ => trivial
  | .call operation continuation, phase, position, budget, returns, link,
      ⟨admitted, rest, bounded, after⟩ =>
      ⟨admitted, rest + second, by rw [← add_assoc]; exact add_le_add_left bounded second,
        fun reply later reached => Bound.bind_of_returns walk nonneg interaction post
          related preserved next suffix (continuation reply)
          (interaction.advance phase operation reply) later rest (returns reply)
          (preserved phase position operation reply later link reached)
          (after reply later reached)⟩

end Zkc.Transcript.Walk
