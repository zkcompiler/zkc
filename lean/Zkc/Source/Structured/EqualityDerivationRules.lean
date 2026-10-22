module

public import Zkc.Source.DerivationLaws
public import Zkc.Source.Structured.Meaning

@[expose] public section

namespace Zkc.Source.Structured

/-- One nondefinitional equality orientation law, shared across scalar and
 group operations. It is explicit mathematics, not part of source traversal. -/
theorem Evaluation.decide_equality_reverse {α : Type} [DecidableEq α] (left right : α) :
    decide (left = right) = decide (right = left) := by
  exact decide_eq_decide.mpr eq_comm

variable {F G : Type} {I : PIR.Signature}
  [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem fieldEqual_reverse_law (observations : SiteObservations I)
    (table : Evaluation.Meanings F G I) (domain : String) (left right : F) :
    (Evaluation.meaning observations table).OperationLaw (fun op => .call op .done)
      (.fieldEqual domain) (.cons left (.cons right .nil)) .nil
      (.done (.cons (decide (right = left)) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change @Eq (PIR.Process _ (Values (assignment F G) [.boolean]))
    (.done (.cons (decide (left = right)) .nil)) (.done (.cons (decide (right = left)) .nil))
  rw [Evaluation.decide_equality_reverse left right]

theorem groupEqual_reverse_law (observations : SiteObservations I)
    (table : Evaluation.Meanings F G I) (domain : String) (left right : G) :
    (Evaluation.meaning observations table).OperationLaw (fun op => .call op .done)
      (.groupEqual domain) (.cons left (.cons right .nil)) .nil
      (.done (.cons (decide (right = left)) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change @Eq (PIR.Process _ (Values (assignment F G) [.boolean]))
    (.done (.cons (decide (left = right)) .nil)) (.done (.cons (decide (right = left)) .nil))
  rw [Evaluation.decide_equality_reverse left right]

end Zkc.Source.Structured
