module

public import ZkcSecurity.Families.Sumcheck.TableComponent

@[expose] public section

/-! Root rules for the installed table component. These are reusable Process
presentations, not source-specific subjects. An actual root must prove one full
binding to its selected presentation, including its terminal checker.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Obligations

variable {F : Type} [Field F] [DecidableEq F]
  {I : PIR.Signature} {Context : Type} {State : Nat → Type}
  {program : Program I Context State (Message.endpoints F)}
  {E P : Type} {Raw : E → Type} {absorb : Interface I E P Raw}
  [∀ event, SampleableType (Raw event)] {charge : List E → E → ENNReal}

/-- The terminal relation on the represented one-entry residual. Actual source
checkers can use this presentation only after their exact checker law. -/
def terminal (layout : Layout program) (s : State 0) : PIR.Process I Bool :=
  .done (decide (program.claim s = (layout.entries s).sum))

noncomputable def root (layout : Layout program) (count : Nat) (context : Context)
    (s : State (0 + count)) : PIR.Process I Bool :=
  (program.remaining (n := 0) count context s).bind (terminal layout)

/-- A false raw sum is preserved to the actual terminal relation. No input
truth or honest-message assumption occurs in this soundness reading. -/
noncomputable def rootResidual (layout : Layout program)
    (queries : QueryInterface program absorb)
    (sampling : queries.ConditionalBound layout.representation 1 1 charge)
    (count : Nat) (context : Context) (s : State (0 + count)) (history : List E)
    (wrong : program.claim s ≠ (layout.entries s).sum) :
    Derivation absorb (boundedEscape charge) (fun _ accepted => accepted ≠ true)
      history (root layout count context s) := by
  apply (Consumers.residual layout.representation Message.endpoints_laws TableReference.laws
    queries sampling count context s history ((layout.no_iff s).mpr wrong)).bind
  intro reached result residual
  apply Derivation.done
  simp only [ne_eq, decide_eq_true_eq]
  exact (layout.no_iff result).mp residual

/-- Both actual child calls run in source order, even when the first terminal
returns false. The complete first poststate therefore reaches the second. -/
noncomputable def twoRoots (layout : Layout program)
    (leftCount rightCount : Nat) (leftContext rightContext : Context)
    (left : State (0 + leftCount)) (right : State (0 + rightCount)) : PIR.Process I Bool :=
  (root layout leftCount leftContext left).bind fun leftAccepted =>
    (root layout rightCount rightContext right).bind fun rightAccepted =>
      .done (leftAccepted && rightAccepted)

/-- False conjunction composition uses the actual two histories. It does not
identify their challenges or infer independence or a maximum error bound. -/
noncomputable def twoRootsResidual (layout : Layout program)
    (queries : QueryInterface program absorb)
    (sampling : queries.ConditionalBound layout.representation 1 1 charge)
    (leftCount rightCount : Nat) (leftContext rightContext : Context)
    (left : State (0 + leftCount)) (right : State (0 + rightCount)) (history : List E)
    (wrong : ¬ (program.claim left = (layout.entries left).sum ∧
      program.claim right = (layout.entries right).sum)) :
    Derivation absorb (boundedEscape charge) (fun _ accepted => accepted ≠ true)
      history (twoRoots layout leftCount rightCount leftContext rightContext left right) := by
  by_cases leftWrong : program.claim left ≠ (layout.entries left).sum
  · apply (rootResidual layout queries sampling leftCount leftContext left history leftWrong).bind
    intro reached leftAccepted leftFalse
    apply (ZkcSecurity.Obligations.unrestricted (root layout rightCount rightContext right) reached).bind
    intro final rightAccepted _
    exact .done (by cases leftAccepted <;> cases rightAccepted <;> simp_all)
  · have rightWrong : program.claim right ≠ (layout.entries right).sum := by
      intro rightTrue
      exact wrong ⟨Classical.not_not.mp leftWrong, rightTrue⟩
    apply (ZkcSecurity.Obligations.unrestricted (root layout leftCount leftContext left) history).bind
    intro reached leftAccepted _
    apply (rootResidual layout queries sampling rightCount rightContext right reached rightWrong).bind
    intro final rightAccepted rightFalse
    exact .done (by cases leftAccepted <;> cases rightAccepted <;> simp_all)

/-- Generated root bindings transport the entire root equation once. The
mathematical root rule contains no protocol name or source-specific pipeline. -/
noncomputable def boundRootResidual (layout : Layout program)
    (queries : QueryInterface program absorb)
    (sampling : queries.ConditionalBound layout.representation 1 1 charge)
    (count : Nat) (context : Context) (s : State (0 + count)) (history : List E)
    (actual : PIR.Process I Bool) (binding : actual = root layout count context s)
    (wrong : program.claim s ≠ (layout.entries s).sum) :
    Derivation absorb (boundedEscape charge) (fun _ accepted => accepted ≠ true) history actual :=
  (rootResidual layout queries sampling count context s history wrong).transport binding

end ZkcSecurity.Families.Sumcheck.TableComponent
