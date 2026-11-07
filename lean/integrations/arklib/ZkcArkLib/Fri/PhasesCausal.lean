module

public import ZkcArkLib.Fri.Certificate
public import ZkcArkLib.Fri.Phases
public import Zkc.Semantics.MonadExecution
public import Zkc.Semantics.Yields

/-!
# Causal publication and adaptive folding

The existing FRI operation signature supplies mathematical publications, challenges and the
terminal message. A word is a reply to publication before the challenge is sampled. Every
prover boundary returns a complete `Execution`, including stops, poststates and events.
`handler` samples a fresh field element before the challenge delivery callback. No honest
next-word recurrence is required. This is an ideal mathematical interface for the source
publication profile, not an interpreter of source actions or a commitment realization.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.Phases

open OracleComp Domain
open _root_.Fri (FoldTrace FoldingAgreementFailure)

variable {F S E A B : Type} [Field F] [DecidableEq F]

/-- A returned event keeps its original mass; every stopped execution is outside it. -/
def returned (post : A → Prop) (result : PIR.Execution S E A) : Prop :=
  match result.outcome with
  | .returned value => post value
  | .stopped _ => False

@[simp] theorem returned_false (result : PIR.Execution S E A) :
    returned (fun _ ↦ False) result = False := by
  cases eq : result.outcome <;> simp only [returned, eq]

/-- Repack only a successful reply, preserving every stop, poststate and event. -/
def repack (f : A → B) (result : PIR.Execution S E A) : PIR.Execution S E B :=
  result.follow (fun value state ↦ ⟨.returned (f value), state, []⟩)

@[simp] theorem returned_repack (post : B → Prop) (f : A → B)
    (result : PIR.Execution S E A) :
    returned post (repack f result) = returned (fun value ↦ post (f value)) result := by
  cases result with | mk outcome state events => cases outcome <;> rfl

/-- The only prover choices required for the ideal commit phase. Each callback sees the
current hidden state, and challenge delivery also sees the challenge already sampled. -/
structure CausalProver (F S E : Type) where
  publish : (round logSize : ℕ) → S → ProbComp (PIR.Execution S E (Fin (2 ^ logSize) → F))
  coefficients : S → ProbComp (PIR.Execution S E (List F))
  deliver : (round : ℕ) → F → S → ProbComp (PIR.Execution S E Unit)

variable [SampleableType F]

/-- Explicit causal handler on the existing mathematical operations. The unused aggregate
position operation refuses: the scalar/block phase has its own exact request history. -/
def CausalProver.handler (prover : CausalProver F S E) :
    PIR.MonadHandler ProbComp (operations F) S E
  | .word round logSize, state => prover.publish round logSize state
  | .final, state => prover.coefficients state
  | .fold round, state => do
      let beta ← $ᵗ F
      let delivery ← prover.deliver round beta state
      pure (repack (fun _ ↦ beta) delivery)
  | .positions _ _, state => pure ⟨.stopped .refused, state, []⟩

/-- Commit from a word already fixed at a successful publication. Later words can depend
on all earlier replies. Only the exact terminal-length guard is included here; installed
domain/shape/numerical guards belong to the source association and can additionally stop. -/
def commitTail (t : ℕ) : {m R : ℕ} → ℕ → (Fin (2 ^ (m + 1)) → F) →
    PIR.Process (operations F) (Layers F (m + 1) (R + 1))
  | _, 0, round, word => .call (.fold round) fun beta =>
      .call .final fun cs =>
        if exactCoefficients t cs then .done (.fold word beta (.final cs)) else .halt .reject
  | 0, _ + 1, round, _ => .call (.fold round) fun _ => .halt .refused
  | m + 1, R + 1, round, word => .call (.fold round) fun beta =>
      .call (.word (round + 1) (m + 1)) fun next =>
        (commitTail t (R := R) (round + 1) next).bind
          (fun rest ↦ .done (.fold word beta rest))

/-- The first successful publication is the statement checkpoint. -/
def commit (t : ℕ) (m R : ℕ) :
    PIR.Process (operations F) ((Fin (2 ^ (m + 1)) → F) × Layers F (m + 1) (R + 1)) :=
  .call (.word 0 (m + 1)) fun word =>
    (commitTail t (R := R) 0 word).bind (fun layers ↦ .done (word, layers))

omit [SampleableType F] [DecidableEq F] in
theorem commitTail_initial (t : ℕ) : ∀ {m R : ℕ} (round : ℕ)
    (word : Fin (2 ^ (m + 1)) → F) (D : SmoothCosetFftDomain (m + 1) F),
    PIR.Yields (fun layers ↦ (toTrace t D layers).initial = word ∧
      exactCoefficients t layers.coefficients = true) (commitTail t (R := R) round word)
  | _, 0, _, _, _ => by
      simp only [commitTail, PIR.Yields]
      intro beta cs
      split
      · exact ⟨rfl, by assumption⟩
      · trivial
  | 0, _ + 1, _, _, _ => fun _ ↦ trivial
  | m + 1, R + 1, round, word, D => by
      simp only [commitTail, PIR.Yields]
      intro beta next
      apply (commitTail_initial t (round + 1) next (D.subdomain 1)).bind
      intro rest hrest
      exact ⟨rfl, hrest.2⟩

/-- `Yields` supplies only returned-value facts. Executing it with the existing runner also
retains every stopped state/event prefix; this lemma observes only successful outputs. -/
theorem yields_runM {I : PIR.Signature} {post : A → Prop} {process : PIR.Process I A}
    (yields : PIR.Yields post process) (handler : PIR.MonadHandler ProbComp I S E)
    (state : S) (result : PIR.Execution S E A)
    (member : result ∈ support (process.runM handler state)) :
    ∀ value, result.outcome = .returned value → post value := by
  induction process generalizing state result with
  | done a =>
      simp only [PIR.Process.runM, mem_support_pure_iff] at member
      subst result
      intro value eq
      cases eq
      exact yields
  | halt why =>
      simp only [PIR.Process.runM, mem_support_pure_iff] at member
      subst result
      intro value eq
      cases eq
  | call op next ih =>
      simp only [PIR.Process.runM, mem_support_bind_iff] at member
      obtain ⟨step, _, member⟩ := member
      cases step with
      | mk outcome final events =>
          cases outcome with
          | stopped why =>
              simp only [PIR.Execution.followM, mem_support_pure_iff] at member
              subst result
              intro value eq
              cases eq
          | returned reply =>
              simp only [PIR.Execution.followM, mem_support_bind_iff] at member
              obtain ⟨tail, htail, member⟩ := member
              simp only [mem_support_pure_iff] at member
              subst result
              exact ih reply (yields reply) final tail htail

/-- A stopped prefix cannot execute or condition the continuation. -/
theorem followM_stopped (reason : PIR.Stop) (state : S) (events : List E)
    (next : A → S → ProbComp (PIR.Execution S E B)) :
    (PIR.Execution.mk (.stopped reason) state events).followM next =
      pure ⟨.stopped reason, state, events⟩ := rfl

theorem prEvent_followM (head : PIR.Execution S E A)
    (next : A → S → ProbComp (PIR.Execution S E B)) (post : B → Prop) :
    Pr{let result ← head.followM next}[returned post result] =
      match head.outcome with
      | .stopped _ => 0
      | .returned value => Pr{let result ← next value head.state}[returned post result] := by
  cases head with
  | mk outcome state events =>
      cases outcome <;> simp [PIR.Execution.followM, returned]
      rfl

/-- Uniform continuation bounds remain valid after any complete prefix, including aborts. -/
theorem prEvent_followM_le (head : PIR.Execution S E A)
    (next : A → S → ProbComp (PIR.Execution S E B)) (post : B → Prop) (error : ENNReal)
    (bound : ∀ value state, Pr{let result ← next value state}[returned post result] ≤ error) :
    Pr{let result ← head.followM next}[returned post result] ≤ error := by
  rw [prEvent_followM]
  cases head.outcome with
  | stopped why => exact bot_le
  | returned value => exact bound value head.state

/-- Mapping only the return of an existing Process does not change the mass of any event. -/
theorem prEvent_runM_repack {I : PIR.Signature} (process : PIR.Process I A)
    (handler : PIR.MonadHandler ProbComp I S E) (state : S) (f : A → B) (post : B → Prop) :
    Pr{let result ← (process.bind (fun value ↦ .done (f value))).runM handler state}[
      returned post result] =
        Pr{let result ← process.runM handler state}[
          returned (fun value ↦ post (f value)) result] := by
  rw [PIR.runM_bind]
  simp only [← bind_pure_comp, bind_assoc]
  apply prEvent_bind_congr_of_support
  intro result _
  simp only [bind_pure_comp]
  rw [prEvent_followM]
  cases result with
  | mk outcome final events =>
      cases outcome <;> simp [PIR.Process.runM, returned]

/-- All arbitrary prover messages and aborts are handled at their original probability mass.
The word for the first challenge is an argument fixed before that challenge is sampled. -/
theorem commitTail_escape_le (t : ℕ) (θ : ℝ) (prover : CausalProver F S E) :
    ∀ {m R : ℕ} (round : ℕ) (D : SmoothCosetFftDomain (m + 1) F)
      (error : ℕ → ENNReal), FoldingEscapes t θ D (R + 1) error →
      ∀ (word : Fin (2 ^ (m + 1)) → F) (state : S),
      Pr{let result ← (commitTail t (R := R) round word).runM prover.handler state}[
        returned (fun layers ↦ ¬ (toTrace t D layers).Safe θ) result] ≤
          ∑ r ∈ Finset.range (R + 1), error r := by
  intro m R
  induction R generalizing m with
  | zero =>
      intro round D error escapes word state
      obtain ⟨head, _⟩ := escapes
      simp only [commitTail, PIR.Process.runM, CausalProver.handler, bind_assoc, pure_bind]
      refine (prEvent_bind_le_prEvent_add _ _
        (fun beta ↦ FoldingAgreementFailure D word 1 (degreeBound 0 (2 ^ t)) θ beta) _
        (ε := 0) fun beta good ↦ ?_).trans ?_
      · apply prEvent_bind_le_of_forall_le
        intro delivery
        cases delivery with
        | mk outcome after events =>
            cases outcome with
            | stopped why => simp [repack, PIR.Execution.follow, PIR.Execution.followM, returned]
            | returned acknowledgment =>
                rw [prEvent_followM]
                dsimp only [repack, PIR.Execution.follow]
                apply prEvent_bind_le_of_forall_le
                intro final
                cases final with
                | mk outcome after events =>
                    cases outcome with
                    | stopped why => simp only [prEvent_followM, le_refl]
                    | returned cs =>
                        rw [prEvent_followM]
                        dsimp only
                        split <;> simp_all [PIR.Process.runM, returned,
                          toTrace, FoldTrace.Safe]
      · simpa using head word
  | succ R ih =>
      intro round D error escapes word state
      cases m with
      | zero =>
          simp only [commitTail, PIR.Process.runM, CausalProver.handler, bind_assoc, pure_bind]
          apply prEvent_bind_le_of_forall_le
          intro beta
          apply prEvent_bind_le_of_forall_le
          intro delivery
          cases delivery with
          | mk outcome after events =>
              cases outcome <;>
                simp [repack, PIR.Execution.follow, PIR.Execution.followM, returned]
      | succ m =>
          obtain ⟨head, tail⟩ := escapes
          simp only [commitTail, PIR.Process.runM, CausalProver.handler, bind_assoc, pure_bind]
          refine (prEvent_bind_le_prEvent_add _ _
            (fun beta ↦ FoldingAgreementFailure D word 1 (degreeBound (R + 1) (2 ^ t)) θ beta) _
            (ε := ∑ r ∈ Finset.range (R + 1), error (r + 1)) fun beta good ↦ ?_).trans ?_
          · apply prEvent_bind_le_of_forall_le
            intro delivery
            cases delivery with
            | mk outcome after events =>
                cases outcome with
                | stopped why =>
                    simp [repack, PIR.Execution.follow, PIR.Execution.followM, returned]
                | returned acknowledgment =>
                    rw [prEvent_followM]
                    dsimp only [repack, PIR.Execution.follow]
                    apply prEvent_bind_le_of_forall_le
                    intro publication
                    cases publication with
                    | mk outcome after events =>
                        cases outcome with
                        | stopped why => simp only [prEvent_followM]; exact bot_le
                        | returned next =>
                            rw [prEvent_followM]
                            dsimp only
                            rw [prEvent_runM_repack]
                            simpa only [returned,
                              toTrace, FoldTrace.Safe, good, not_false_eq_true, true_and] using
                              ih (round + 1) (D.subdomain 1) (fun r ↦ error (r + 1)) tail next after
          · calc _ ≤ error 0 + ∑ r ∈ Finset.range (R + 1), error (r + 1) :=
                add_le_add (head word) le_rfl
              _ = ∑ r ∈ Finset.range (R + 2), error r := by
                rw [Finset.sum_range_succ' _ (R + 1)]
                ring

end ZkcSecurity.ArkLib.Fri.Phases
