module

public import Zkc.Source.DerivationLaws
public import Zkc.Source.Structured.Participant

@[expose] public section

namespace Zkc.Source.Structured

variable {F G : Type} {I : PIR.Signature}
  [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- A nondefinitional local rewrite, shared by closed and optional participants. -/
theorem Evaluation.fieldAdd_reverse (observations : SiteObservations I)
    (table : Evaluation.Meanings F G I) (domain : String) (a b : F) :
    Evaluation.operation observations table (.fieldAdd domain)
      (.cons a (.cons b .nil)) .nil = .done (.cons (b + a) .nil) := by
  change @Eq (PIR.Proc _ (Values (assignment F G) [.field domain]))
    (.done (.cons (a + b) .nil)) (.done (.cons (b + a) .nil))
  rw [add_comm a b]

/-- Closed operation rule; neither the helper table nor the source body is copied. -/
theorem fieldAdd_reverse_law (observations : SiteObservations I)
    (table : Evaluation.Meanings F G I) (domain : String) (a b : F) :
    (Evaluation.meaning observations table).OperationLaw (fun op => .call op .done)
      (.fieldAdd domain) (.cons a (.cons b .nil)) .nil (.done (.cons (b + a) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  exact Evaluation.fieldAdd_reverse observations table domain a b

/-- Optional operands remain independent. Absent operands stay absent, and the
same scalar rewrite is used only when both operands are available. -/
theorem calculate_fieldAdd_reverse_law (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (tables : Evaluation.ComponentTables F G I) (self : Nat)
    (protocols : ProtocolTable (assignment F G) I) (context : ProtocolContext)
    (domain : String) (allowed : (Op.fieldAdd domain).isCalculation = true) (a b : Option F) :
    (participantMeaningWith observations actions tables self protocols context).OperationLaw
      (fun op => .call op .done) (.calculate (.fieldAdd domain) allowed)
      (.cons a (.cons b .nil)) .nil
      (.done (.cons (a.bind fun x => b.map fun y => y + x) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      change (Evaluation.operation observations tables.closed (.fieldAdd domain)
        (.cons a (.cons b .nil)) .nil).bind (fun result => .done result.present) = _
      rw [Evaluation.fieldAdd_reverse]
      rfl

end Zkc.Source.Structured
