module

public import Zkc.Tests.Protocol.Construction.Readings.Sumcheck
public import Zkc.Tests.Protocol.Construction.Readings.ExactThreeMove
public import Zkc.Protocol.Logic.Transcript.Interactive

/-! Boundary controls for the proposition-valued readings. False requests are refuted through
the same adequacy theorems the endpoints use, and a well-typed but false loop invariant does not
let the constructor prove a request. The readings are rejection-oriented: a stop is never a
violation, so a triple does not show that an execution returns. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Transcript Std.WP ProtocolProof
open ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open ZkcSecurity.FiatShamir.Typed
open scoped ENNReal

namespace ProtocolProofExamples.ReadingControls

section Exact
open ProtocolProofExamples.ExactThreeMove

attribute [local instance] ExactThreeMove.logic

/-- Under the exact reading every reply is constrained: with a check that always fails, the
request that every run accepts is refuted at one run. -/
example : ¬ ⦃fun _ => ⟨True⟩⦄
      verifier.denote (meaning (A := Unit) (C := Unit) (Z := Unit) fun _ _ _ => false).regionMeaning
        Values.nil.get
    ⦃fun out _ => ⟨(out.get .here).2.2.2 = true⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  intro triple
  have charged := charged_of_triple absorb exactEscape exactEscape_antitone triple [] trivial
  exact charged (.inl ()) () rfl () ⟨(), rfl, fun returned =>
    Bool.false_ne_true (returned (.inr ()) () rfl)⟩

end Exact

section Charged
open ProtocolProofExamples.ChargedSumcheck

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

attribute [local instance] ChargedSumcheck.logic

/-- Stops are not successes: a verifier without rounds returns its decision, so requiring that
no run returns is refuted. -/
example (S : List F → F) (start : List F × F) (wrong : start.2 ≠ S start.1) :
    ¬ ⦃Wrong S start⦄ game S 0 start ⦃fun _ _ => ⟨False⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ :=
  fun triple => triple.le_wp [] wrong

/-- What the invariant `True` leaves for the loop: an arbitrary state, at any history, is wrong.
It is needed both for the next round's precondition and at the end of the loop. -/
def ForgottenWrong (S : List F → F) : Prop :=
  ∀ (st : List F × F) (_history : List (Ev F)), st.2 ≠ S st.1

/-- A well-typed invariant that forgets the wrong claim cannot establish it at the end of the
loop. With the invariant `True`, the constructor leaves obligations that are exactly instances of
`ForgottenWrong S` at an arbitrary state, and simplification does not close them. -/
example (S : List F → F) (laws : Laws S) (count : Nat)
    (env : Environment (meaning S).Value [.state]) :
    ⦃Wrong S (env .here)⦄
      (rounds count).denote (meaning S).regionMeaning env
    ⦃fun out => Wrong S (out.get .here); estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold rounds
  fail_if_success
    solve
    | construct_region with_invariants [fun _ _ => fun _ => ⟨True⟩]
      all_goals simp
  construct_region with_invariants [fun _ st => Wrong S st]

/-- The obligations of the forgetful invariant, discharged by `ForgottenWrong S` directly. -/
example (S : List F → F) (laws : Laws S) (count : Nat)
    (env : Environment (meaning S).Value [.state]) (forgotten : ForgottenWrong S) :
    ⦃Wrong S (env .here)⦄
      (rounds count).denote (meaning S).regionMeaning env
    ⦃fun out => Wrong S (out.get .here); estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold rounds
  construct_region with_invariants [fun _ _ => fun _ => ⟨True⟩]
  · exact forgotten _ []
  · exact forgotten _

/-- Those obligations are false: a state that agrees with the reference is not wrong. -/
example (S : List F → F) (point : List F) : ¬ ForgottenWrong S :=
  fun forgotten => forgotten (point, S point) [] rfl

end Charged

section Cost
open ProtocolProofExamples.ChargedSumcheck

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

attribute [local instance] ChargedSumcheck.budget

/-- A query is paid at its site: a draw cannot be performed on a zero budget. -/
example : ¬ ⦃fun _ cost => ⟨cost = 0⟩⦄ (Process.call (I := VSig F) VOp.draw .done)
    ⦃fun _ _ _ => ⟨True⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  intro triple
  obtain ⟨remaining, paid, _⟩ := costBound_of_triple absorb charge triple [] 0 rfl
  have positive : (0 : ℝ≥0∞) < 1 / (Fintype.card F : ℝ≥0∞) := by simp
  exact absurd ((le_self_add (a := 1 / (Fintype.card F : ℝ≥0∞))).trans paid) (not_le.mpr positive)

end Cost

/-! ### Stops satisfy every rejection-oriented triple

A refused operation and a query whose decoder rejects every raw answer both stop the run. The
charged and exact readings accept every stop, so their triples hold even with false return and
stop assertions, while the actual executions stop `refused` and `exhausted`. Neither execution
accepts, which is the intended meaning of a reading that bounds acceptance; it is also why a
triple alone does not show completeness. `ZkcSecurity.Interactive.returns_of_exact` states when
it does: over a total interface, with a false stop assertion. -/

section Stops

abbrev UnitSignature : Signature := ⟨Unit, fun _ => Unit⟩

def body : Process UnitSignature Unit := .call () fun _ => .done ()

/-- Refuses its only operation. -/
def refusing : Interface UnitSignature Unit Unit (fun _ => Unit) := fun _ => .refuse

/-- Its only operation is a query whose decoder rejects every raw answer. -/
def undecodable : Interface UnitSignature Unit Unit (fun _ => Unit) :=
  fun _ => .query () (fun _ => none)

/-- The exact reading accepts the refused operation with false return and stop assertions. -/
example : ChargedTriple refusing exactEscape exactEscape_antitone body (fun _ => ⟨True⟩)
    (fun _ _ => ⟨False⟩) estack⟨fun _ _ => ⟨False⟩⟩ := by
  let := chargedMonad refusing exactEscape exactEscape_antitone
  unfold body
  construct_region

/-- So does the bounded charged reading, even at charge zero. -/
example : ChargedTriple refusing (boundedEscape fun _ _ => 0) (boundedEscape_antitone _) body
    (fun _ => ⟨True⟩) (fun _ _ => ⟨False⟩) estack⟨fun _ _ => ⟨False⟩⟩ := by
  let := chargedMonad refusing (boundedEscape fun _ _ => 0) (boundedEscape_antitone _)
  unfold body
  construct_region

/-- The actual run stops refused, in the transform and in the interactive experiment. -/
example : transform (m := Id) refusing (fun _ _ => ()) body [] [] = (.stopped .refused, []) := rfl

example (strategy : ZkcSecurity.Interactive.Strategy Unit Unit fun _ => Unit) :
    ZkcSecurity.Interactive.interact refusing strategy body [] [] = pure (.stopped .refused, []) :=
  rfl

/-- The exact reading accepts the undecodable query with false return and stop assertions. -/
example : ChargedTriple undecodable exactEscape exactEscape_antitone body (fun _ => ⟨True⟩)
    (fun _ _ => ⟨False⟩) estack⟨fun _ _ => ⟨False⟩⟩ := by
  let := chargedMonad undecodable exactEscape exactEscape_antitone
  unfold body
  construct_region
  rintro raw ⟨value, decoded, -⟩
  cases decoded

/-- The actual run stops exhausted. -/
example : transform (m := Id) undecodable (fun _ _ => ()) body [] [] = (.stopped .exhausted, []) :=
  rfl

/-- An interface that admits its only operation: a receive that recovers every message. -/
def admitting : Interface UnitSignature Unit Unit (fun _ => Unit) := fun _ => .receive id some

theorem admitting_total : ZkcSecurity.Interactive.Total admitting := fun _ _ => rfl

attribute [local construction_simp] admitting

theorem admitting_exact : ChargedTriple admitting exactEscape exactEscape_antitone body
    (fun _ => ⟨True⟩) (fun _ _ => ⟨True⟩) estack⟨fun _ _ => ⟨False⟩⟩ := by
  let := chargedMonad admitting exactEscape exactEscape_antitone
  unfold body
  construct_region

/-- Over the total interface, with a false stop assertion, the exact triple shows that every
interactive run returns. -/
theorem admitting_returns (strategy : ZkcSecurity.Interactive.Strategy Unit Unit fun _ => Unit) :
    ∀ result ∈ support (ZkcSecurity.Interactive.interact admitting strategy body [] []),
      ∃ value, result.1 = .returned value :=
  fun result member =>
    let ⟨value, returned, _⟩ := ZkcSecurity.Interactive.returns_of_exact admitting strategy
      admitting_total admitting_exact [] trivial [] result member
    ⟨value, returned⟩

#print axioms admitting_returns

end Stops

end ProtocolProofExamples.ReadingControls
