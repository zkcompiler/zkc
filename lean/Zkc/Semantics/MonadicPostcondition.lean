module

public import Std.Do.Internal.Ensures.Lemmas

@[expose] public section

/-! Complete-result postconditions use Lean's bind-faithful refinement predicate.
These conveniences construct and consume that predicate without defining another
execution semantics or requiring a particular monad's support or probability model.
-/

set_option autoImplicit false
namespace Zkc.MonadicPostcondition

open Std.Do.Internal

variable {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type}

/-- An exact erasure equation constructs Lean's stronger, continuation-facing witness. -/
theorem of_refinement {post : A → Prop} {computation : m A}
    (checked : m {value // post value})
    (erase : computation = (checked >>= fun value ↦ pure value.val)) :
    Ensures post computation := by
  refine ⟨⟨checked, ⟨?_⟩⟩⟩
  intro B next
  rw [erase, bind_assoc]
  simp only [pure_bind]

/-- A known complete result satisfies any proved predicate on that result. -/
theorem pure (post : A → Prop) (value : A) (valid : post value) :
    Ensures (m := m) post (Pure.pure value) :=
  (Ensures.pure value).weaken fun _ same ↦ by simpa only [same] using valid

/-- Transport a proved result predicate through deterministic postprocessing. -/
theorem map {pre : A → Prop} {post : B → Prop} {first : m A}
    (head : Ensures pre first) (change : A → B) (law : ∀ value, pre value → post (change value)) :
    Ensures post (first >>= fun value ↦ Pure.pure (change value)) :=
  head.bind fun value valid ↦ pure post (change value) (law value valid)

omit [LawfulMonad m] in
/-- A live result invariant can rewrite continuations without changing any monadic effect. -/
theorem continuation {post : A → Prop} {computation : m A}
    (law : Ensures post computation) (left right : A → m B)
    (agree : ∀ value, post value → left value = right value) :
    (computation >>= left) = (computation >>= right) := by
  obtain ⟨checked, erase⟩ := law.exists_refinement
  rw [← erase.bind_eq left, ← erase.bind_eq right]
  exact bind_congr fun value ↦ agree value.val value.property

/-- With exact attachment, the same predicate describes every reachable result.
OracleComp supplies this instance, so probability-facing support proofs can reuse it. -/
theorem iff_forall_canReturn [MonadAttach m] [LawfulMonadAttach m]
    {post : A → Prop} {computation : m A} :
    Ensures post computation ↔ ∀ value, MonadAttach.CanReturn computation value → post value := by
  constructor
  · intro law value member
    exact (MayReturn.of_canReturn member).imp law
  · intro law
    exact Ensures.canReturn.weaken law

/-- Exact support lets independently established postconditions meet on
the same complete result, including its stopped outcome and auxiliary state. -/
theorem conjunction [MonadAttach m] [LawfulMonadAttach m]
    {first second : A → Prop} {computation : m A}
    (left : Ensures first computation) (right : Ensures second computation) :
    Ensures (fun value ↦ first value ∧ second value) computation :=
  iff_forall_canReturn.mpr fun value reached ↦
    ⟨iff_forall_canReturn.mp left value reached, iff_forall_canReturn.mp right value reached⟩

end Zkc.MonadicPostcondition
