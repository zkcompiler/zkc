module

public import Zkc.Obligations.Component
public import Zkc.Semantics.Yields
public import Zkc.Semantics.WeakestPrecondition
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Independent obligations for a symbolic repetition of an installed component.
All contracts refer to the same `component.body`, including its entire runtime
result. Representation and frames quantify over every typed reply, without a
claim-truth premise. Honest execution additionally excludes every stop. The No
contract is the existing escape derivation; it does not imply honest success.
These are proof interfaces over Process, not another family evaluator. -/

set_option autoImplicit false
namespace Zkc.Obligations.RepeatedComponent
open Zkc.Transcript

variable {I : PIR.Signature} {E P R S : Type} {Raw : E → Type}
  (component : ComponentInterface I E R R)

/-- The mathematical carrier can change with the remaining dimension. A
readback is partial so malformed runtime states need no invented reference.
The relation may describe reply-dependent updates, including shared challenges.
Neither representation nor its preservation assumes the input claim is true. -/
structure Representation (Reference : Nat → Type) where
  readback : (remaining : Nat) → R → Option (Reference remaining)
  transition : (remaining : Nat) → Reference (remaining + 1) → Reference remaining → Prop
  preserves : ∀ remaining runtime reference,
    readback (remaining + 1) runtime = some reference →
    PIR.Yields (fun result => ∃ next,
      readback remaining result = some next ∧ transition remaining reference next)
      (component.body runtime)

/-- An all-replies private/residual frame, independent of No and honest input. -/
def FrameContract (frame : Nat → R → Prop) : Prop :=
  ∀ remaining runtime, frame (remaining + 1) runtime →
    PIR.Yields (frame remaining) (component.body runtime)

theorem frame_repeatN {frame : Nat → R → Prop}
    (preserves : FrameContract component frame) :
    ∀ count runtime, frame count runtime →
      PIR.Yields (frame 0) (PIR.repeatN count component.body runtime)
  | 0, _, holds => holds
  | count + 1, runtime, holds =>
      (preserves count runtime holds).bind fun returned valid =>
        frame_repeatN preserves count returned valid

/-- Representation is available even for false claims and non-honest replies. -/
theorem representation_repeatN {Reference : Nat → Type}
    (representation : Representation component Reference) :
    ∀ count runtime, (∃ reference, representation.readback count runtime = some reference) →
      PIR.Yields (fun result => ∃ reference, representation.readback 0 result = some reference)
        (PIR.repeatN count component.body runtime) := by
  apply frame_repeatN component
  intro remaining runtime represented
  obtain ⟨reference, same⟩ := represented
  exact (representation.preserves remaining runtime reference same).mono
    (fun _ ⟨next, decoded, _⟩ => ⟨next, decoded⟩)

/-- No/escape is indexed by the actual accumulated history, never a fresh
history at the next component. Family `SoundnessContract` instances supply
these steps after the caller establishes their scope and input readback. -/
abbrev NoContract (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    (invariant : List E → Nat → R → Prop) : Type 1 :=
  ∀ reached remaining runtime, invariant reached (remaining + 1) runtime →
    Derivation absorb escape (fun final => invariant final remaining) reached (component.body runtime)

/-- Use an installed family contract without changing its meaning. The caller
discharges scope/input No on entry and the mathematical invariant on exit; the
body and every reached history are shared with representation and framing. -/
def NoContract.ofSoundness {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
    (soundness : SoundnessContract component absorb escape)
    (parameters : Nat → component.Parameters) (invariant : List E → Nat → R → Prop)
    (enter : ∀ remaining history runtime, invariant history (remaining + 1) runtime →
      component.Scope (parameters remaining) runtime history ∧
        component.InputNo (parameters remaining) runtime history)
    (exit : ∀ remaining runtime history returned,
      component.OutputNo (parameters remaining) runtime history returned → invariant history remaining returned) :
    NoContract component absorb escape invariant :=
  fun history remaining runtime holds =>
    (soundness (parameters remaining) runtime history (enter remaining history runtime holds).1
      (enter remaining history runtime holds).2).consequence (exit remaining runtime)

def no_repeatN {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
    {invariant : List E → Nat → R → Prop}
    (steps : NoContract component absorb escape invariant)
    (count : Nat) (history : List E) (runtime : R) (holds : invariant history count runtime) :
    Derivation absorb escape (fun final => invariant final 0) history
      (PIR.repeatN count component.body runtime) :=
  Derivation.repeatN component.body invariant steps count history runtime holds

/-- A deterministic honest-return contract. State and history are threaded
together; even rejection is unsuccessful. The existing WP adequacy theorem
`PIR.WeakestPrecondition.triple_iff_returned` reads this as an actual return. -/
def HonestContract (handler : PIR.Handler I S E)
    (invariant : List E → Nat → R → S → Prop) : Prop :=
  ∀ reached remaining runtime state, invariant reached (remaining + 1) runtime state →
    PIR.WeakestPrecondition.satisfies ((component.body runtime).run handler state)
      (fun returned final history => invariant history remaining returned final)
      (fun _ _ _ => False) reached

theorem honest_repeatN (handler : PIR.Handler I S E)
    (invariant : List E → Nat → R → S → Prop)
    (steps : HonestContract component handler invariant) :
    ∀ count history runtime state, invariant history count runtime state →
      PIR.WeakestPrecondition.satisfies
        ((PIR.repeatN count component.body runtime).run handler state)
        (fun returned final reached => invariant reached 0 returned final)
        (fun _ _ _ => False) history := by
  intro count
  induction count with
  | zero =>
    intro history runtime state holds
    simpa only [PIR.repeatN, PIR.Process.run, PIR.WeakestPrecondition.satisfies,
      List.append_nil] using holds
  | succ count ih =>
    intro history runtime state holds
    have honestStep := steps history count runtime state holds
    change PIR.WeakestPrecondition.runWP handler
      ((component.body runtime).bind (PIR.repeatN count component.body))
      (fun returned final reached => invariant reached 0 returned final)
      estack⟨fun _ _ _ => False⟩ state history
    rw [PIR.WeakestPrecondition.runWP_bind]
    unfold PIR.WeakestPrecondition.runWP PIR.WeakestPrecondition.satisfies at honestStep ⊢
    split at honestStep
    · exact ih _ _ _ honestStep
    · exact honestStep.elim

/-- Source finite folds with an index-independent callback use the same loop
rule. Index-dependent callbacks retain the index in the carried runtime. -/
def no_fold {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
    {invariant : List E → Nat → R → Prop}
    (steps : NoContract component absorb escape invariant)
    (start count : Nat) (history : List E) (runtime : R) (holds : invariant history count runtime) :
    Derivation absorb escape (fun final => invariant final 0) history
      (Zkc.Source.Finite.fold (fun state (_ : Nat) => component.body state)
        (List.range' start count) runtime) := by
  rw [Zkc.Source.Finite.fold_range_repeatN]
  exact no_repeatN component steps count history runtime holds

end Zkc.Obligations.RepeatedComponent
