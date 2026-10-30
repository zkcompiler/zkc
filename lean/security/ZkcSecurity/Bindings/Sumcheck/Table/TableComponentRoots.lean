module

public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponent

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
