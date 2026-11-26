module

public import ZkcFormal.Written.Soundness
public import ZkcFormal.Written.SiteCaps
import Mathlib.Tactic.DSimpPercent

@[expose] public section

/-! The written goal with fees uses the selected decision's return bound at the total of
its cap table. Its accounting judgment and counted result keep the table explicit. -/

namespace ZkcFormal.Written.Goal

open Zkc.Core Zkc.Subject ProbabilisticProcess
open scoped ENNReal Soundness

open Internal
variable {V : Vocabulary} (M : Model V)
variable {pkg : Package V} {scheme : WrittenRoot pkg} (g : WrittenGoal scheme)

/-- Rejection on the statement operands of this goal. -/
def Rejected (p : Typed V) (relation : Member p.headers.fns g.decision.relation.header)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins) : Prop :=
  rejectionAt%(M, g.decision, p, relation, xs)

/-- The decision and fee goal select the same rejection predicate. Refolding this name in
the legacy definitions preserves the existing `unfold ClaimOf` and `unfold Witnessed` steps. -/
theorem rejected_at_decision (p : Typed V) (relation : Member p.headers.fns g.decision.relation.header)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins) :
    Soundness.Rejected M g.decision p relation xs = Rejected M g p relation xs := rfl

variable (draws : LawDraws M)

/-- The selected verifier's probability bound at the total of this goal's caps. -/
def ClaimOf (p : Typed V) (root : Member p.headers.protocols scheme.entry.header)
    (relation : Member p.headers.fns g.decision.relation.header) : Prop :=
  dsimp% -zeta only [Soundness.BoundOf, rejected_at_decision]
    Soundness.BoundOf M g.decision draws g.fields.caps.total p root relation

/-- The claim at the two members in the installation. -/
def Claim : Prop :=
  ClaimOf M g draws pkg.installed scheme.entry.member g.decision.relation.member

/-- Look up both named entries in the same admitted program before applying its claim. -/
def admission (stored : NamedProgram V) (association : Association)
    (rootHeader : ProtocolHeader V) (rootKey : Key) (relationHeader : FnHeader V) (relationKey : Key)
    (claim : (p : Typed V) → Member p.headers.protocols rootHeader →
      Member p.headers.fns relationHeader → Prop) : Prop :=
  dsimp% -zeta only [Soundness.admission]
    Soundness.admission stored association rootHeader rootKey relationHeader relationKey claim

/-- Admission at the headers and keys selected by this decision. -/
def admittedAt (claim : (p : Typed V) → Member p.headers.protocols scheme.entry.header →
    Member p.headers.fns g.decision.relation.header → Prop) : Prop :=
  admission pkg.stored pkg.association scheme.entry.header scheme.entry.header.key
    g.decision.relation.header g.decision.relation.header.key claim

set_option linter.dupNamespace false in
/-- The written claim at the entries found by admission. -/
def Goal : Prop := admittedAt g (ClaimOf M g draws)

/-- Coverage and the cap count on the stored program accompany the supplied goal. -/
def countedResult (stored : NamedProgram V) (rootKey relationKey : Key) (caps : CapTable)
    (covers : NamedProgram V → Key → Key → Bool) (goal : Prop) : Prop :=
  covers stored rootKey relationKey = true ∧ caps.counted stored rootKey = true ∧ goal

/-- The result at the keys and caps selected by this goal. -/
def resultOf (covers : NamedProgram V → Key → Key → Bool) (goal : Prop) : Prop :=
  countedResult pkg.stored scheme.entry.header.key g.decision.relation.header.key g.fields.caps
    covers goal

/-- Coverage, cap counts, and the written goal. -/
def Result (covers : NamedProgram V → Key → Key → Bool) : Prop :=
  resultOf g covers (Goal M g draws)

/-- The joint service and rejection receipt for the selected decision. -/
def Witnessed : Prop :=
  dsimp% -zeta only [Soundness.Witnessed, rejected_at_decision] Soundness.Witnessed M g.decision draws

/-- The installed verifier is judged never to return, with each fee paid at its site within
the goal's budget. -/
def Judged : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Rejected M g pkg.installed g.decision.relation.member xs →
      (roleMeaning M pkg.installed scheme.entry.member scheme.verifier path xs).interpret
        (.charged (Permitted M) (paysWithin (lawSamplers M draws) (g.fields.caps.allowance M path)))
        (fun _ _ ↦ False) (fun _ _ ↦ True) g.fields.caps.budget

/-- A judgment with fees gives the installed probability bound. -/
theorem claim_of_judged (judged : Judged M g draws) : Claim M g draws :=
  fun path ↦ Internal.mapInputs M _ _ _ _ (fun _ h rejected ↦
    returnsWithin_of_never _ _ _ _ _ (h rejected)) (judged path)

/-- Valid verifier inputs and installed rejection meet the hypotheses with the given service. -/
theorem witnessed_of (served : Served (lawSamplers M draws) (Permitted M)) :
    inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
      Rejected M g pkg.installed g.decision.relation.member xs → Witnessed M g draws :=
  Soundness.witnessed_of M g.decision draws served

end ZkcFormal.Written.Goal
