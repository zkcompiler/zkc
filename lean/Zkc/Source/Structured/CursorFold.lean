module

public import Zkc.Source.Structured.DeterministicFold

@[expose] public section

/-! Deterministic folds whose mathematical state advances a checked cursor.
The list, encoder and transition are arbitrary. Empty folds perform no cursor
check; the caller must separately establish the source domain's admission. -/
set_option autoImplicit false
namespace Zkc.Source.Finite

theorem fold_cursor_encode {I : PIR.Signature} {A S T : Type}
    (step : T → A → PIR.Process I T) (encode : S → T)
    (transition : S → A → S) (cursor : S → Nat) (limit : Nat)
    (advances : ∀ state item, cursor (transition state item) = cursor state + 1)
    (law : ∀ state item, cursor state + 1 < limit →
      step (encode state) item = .done (encode (transition state item)))
    (items : List A) (initial : S) (bound : cursor initial + items.length < limit) :
    fold step items (encode initial) = .done (encode (items.foldl transition initial)) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    have next : cursor initial + 1 < limit := by
      simp only [List.length_cons] at bound
      omega
    rw [fold, law initial item next]
    exact ih (transition initial item) (by
      rw [advances]
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using bound)

end Zkc.Source.Finite

namespace Zkc.Source.Structured.Evaluation

theorem denoteFoldOn_cursor_encode {carriers : Carriers} {I : PIR.Signature} {A S : Type}
    (table : HelperTable carriers.Value I) (spec : FoldSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (items : List A) (pack : A → Values carriers.Value spec.domain.items)
    (encode : S → Values carriers.Value spec.state) (initial : S)
    (admitted : spec.domain.admit arguments = .returned (items.map pack))
    (transition : S → A → S) (cursor : S → Nat) (limit : Nat)
    (advances : ∀ state item, cursor (transition state item) = cursor state + 1)
    (law : ∀ state item, cursor state + 1 < limit →
      foldTransitionOn table spec arguments captures (encode state) (pack item) =
        .done (encode (transition state item)))
    (bound : cursor initial + items.length < limit) :
    denoteFoldOn table spec (arguments.append ((encode initial).append captures)) =
      .done (encode (items.foldl transition initial)) := by
  simp only [denoteFoldOn, Values.split_append, admitted, Finite.admitThen, Finite.fold_map]
  exact Finite.fold_cursor_encode _ encode transition cursor limit advances law items initial bound

end Zkc.Source.Structured.Evaluation
