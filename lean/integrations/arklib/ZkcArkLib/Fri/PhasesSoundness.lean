module

public import ZkcArkLib.Fri.PhasesSampling
public import ZkcArkLib.Fri.PhasesCheck
public import ZkcArkLib.Fri.UniqueDecoding

/-! # Causal ideal soundness

The probability bound uses the actual complete-outcome mathematical phases: first successful
publication, fresh challenges after publication, adaptive later words, scalar or block query
delivery, then guarded fixed-word Check. Stops retain their probability mass and state/event
prefixes. No equality with the historical total `Strategy` experiment is used.

Source association, numeric ingress, primitive implementations and commitment realization
remain outside this ideal theorem. In particular a source handle must denote the same word
fixed before the relevant challenge; an equality of whole-run success probabilities is not
an admissible replacement for that local semantic fact.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.Phases

open OracleComp Domain

variable {F S E : Type} [Field F] [DecidableEq F] [SampleableType F]

def finish (roots : ℕ → F) (t : ℕ) {m R : ℕ} (s : ℕ)
    (policy : QueryPolicy) (prover : QueryProver (m + 1) S E)
    (reader : PIR.MonadHandler ProbComp checkOperations S (SamplingEvent (m + 1) E))
    (layers : Layers F (m + 1) (R + 1)) (shift : F) (state : S) :
    ProbComp (PIR.Execution S (SamplingEvent (m + 1) E) (Result F (m + 1) s)) := do
  let positions ← (queries policy (m + 1) s).runM prover.handler state
  positions.followM fun positions after =>
    (check roots t layers shift positions (fun _ ↦ none)).runM reader after

omit [SampleableType F] in
theorem check_impossible (roots : ℕ → F) (t : ℕ) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1)))
    (reader : PIR.MonadHandler ProbComp checkOperations S E) (state : S)
    (rejected : accepts roots t layers shift positions ≠ true)
    (post : Result F (m + 1) s → Prop) :
    Pr{let result ← (check roots t layers shift positions (fun _ ↦ none)).runM reader state}[
      returned post result] = 0 := by
  apply prEvent_eq_zero_of_forall_mem_support
  intro result member event
  cases eq : result.outcome with
  | stopped why => simp only [returned, eq] at event
  | returned value =>
      exact rejected ((yields_runM (check_yields roots t layers shift positions (fun _ ↦ none))
        reader state result member value eq).1)

omit [SampleableType F] in
/-- Arbitrary read failures can only remove mathematical accepting position vectors. -/
theorem finish_domination (roots : ℕ → F) (t : ℕ) {m R : ℕ} (s : ℕ)
    (policy : QueryPolicy) (prover : QueryProver (m + 1) S E)
    (reader : PIR.MonadHandler ProbComp checkOperations S (SamplingEvent (m + 1) E))
    (layers : Layers F (m + 1) (R + 1)) (shift : F) (state : S)
    (post : Result F (m + 1) s → Prop) :
    Pr{let result ← finish roots t s policy prover reader layers shift state}[
      returned post result] ≤
      Pr{let positions ← $ᵗ (Fin s → Fin (2 ^ (m + 1)))}[
        accepts roots t layers shift positions = true] := by
  unfold finish
  refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _
    (returned (fun positions ↦ accepts roots t layers shift positions = true)) _ ?_).trans
      (queries_domination prover policy s state _)
  intro headResult outside
  rw [prEvent_followM]
  cases headResult with
  | mk outcome after events =>
      cases outcome with
      | stopped why => rfl
      | returned positions =>
          exact check_impossible roots t layers shift positions reader after outside post

omit [SampleableType F] in
theorem finish_escape_le (roots : ℕ → F) (t : ℕ) {m R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (m + 1) F) (shift : F)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (compatible : Compatible roots (m + 1) (R + 1)) (θ δ : ℝ)
    (layers : Layers F (m + 1) (R + 1)) (safe : (toTrace t D layers).Safe θ)
    (far : Far D (degreeBound (R + 1) (2 ^ t)) δ (toTrace t D layers).initial)
    (policy : QueryPolicy) (prover : QueryProver (m + 1) S E)
    (reader : PIR.MonadHandler ProbComp checkOperations S (SamplingEvent (m + 1) E))
    (state : S) (post : Result F (m + 1) s → Prop) :
    Pr{let result ← finish roots t s policy prover reader layers shift state}[
      returned post result] ≤
      ENNReal.ofReal (1 - min θ δ) ^ s :=
  (finish_domination roots t s policy prover reader layers shift state post).trans
    (query_escape_le_of_accepts (toTrace t D layers) θ δ safe far (Equiv.refl _)
      (fun positions ↦ accepts roots t layers shift positions = true)
      (fun positions accepted ↦ accepts_trace roots t D shift geometry compatible layers
        positions accepted))

/-- The aggregate mathematical certificate site is useful to clients of the existing local
`Step`. It describes the product phase after abstraction, never an actual scalar draw. -/
theorem compound_query_step (roots : ℕ → F) (t : ℕ) {m R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (m + 1) F) (shift : F)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (compatible : Compatible roots (m + 1) (R + 1)) (θ δ : ℝ)
    (layers : Layers F (m + 1) (R + 1)) (safe : (toTrace t D layers).Safe θ)
    (far : Far D (degreeBound (R + 1) (2 ^ t)) δ (toTrace t D layers).initial) :
    Step (F := F) (fun process ↦ process = .done false)
      (siteError (fun _ ↦ 0) (ENNReal.ofReal (1 - min θ δ) ^ s))
      (.call (.positions (m + 1) s) fun positions ↦
        .done (accepts roots t layers shift positions)) := by
  change Pr{let positions ← $ᵗ (Fin s → Fin (2 ^ (m + 1)))}[
    ¬ PIR.Process.done (accepts roots t layers shift positions) =
      (PIR.Process.done false : PIR.Process (operations F) Bool)] ≤ _
  simpa only [PIR.Process.done.injEq, Bool.not_eq_false, siteError] using
    query_escape_le_of_accepts (toTrace t D layers) θ δ safe far (Equiv.refl _)
      (fun positions ↦ accepts roots t layers shift positions = true)
      (fun positions accepted ↦ accepts_trace roots t D shift geometry compatible layers
        positions accepted)

/-- The output carries the first published statement word and the full Check result. -/
def experiment (roots : ℕ → F) (t : ℕ) (m R s : ℕ) (shift : F)
    (policy : QueryPolicy) (prover : CausalProver F S (SamplingEvent (m + 1) E))
    (queriesProver : QueryProver (m + 1) S E)
    (reader : PIR.MonadHandler ProbComp checkOperations S (SamplingEvent (m + 1) E))
    (state : S) : ProbComp (PIR.Execution S (SamplingEvent (m + 1) E)
      ((Fin (2 ^ (m + 1)) → F) × Result F (m + 1) s)) := do
  let publication ← prover.publish 0 (m + 1) state
  publication.followM fun word after => do
    let committed ← (commitTail t (R := R) 0 word).runM prover.handler after
    committed.followM fun layers after =>
      repack (fun result ↦ (word, result)) <$>
        finish roots t s policy queriesProver reader layers shift after

theorem soundness (roots : ℕ → F) (t : ℕ) {m R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (m + 1) F) (shift : F)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (compatible : Compatible roots (m + 1) (R + 1)) (θ δ : ℝ) (error : ℕ → ENNReal)
    (escapes : FoldingEscapes t θ D (R + 1) error)
    (policy : QueryPolicy) (prover : CausalProver F S (SamplingEvent (m + 1) E))
    (queriesProver : QueryProver (m + 1) S E)
    (reader : PIR.MonadHandler ProbComp checkOperations S (SamplingEvent (m + 1) E))
    (state : S) :
    Pr{let result ← experiment roots t m R s shift policy prover queriesProver reader state}[
      returned (fun output ↦ output.2.accepted = true ∧
        Far D (degreeBound (R + 1) (2 ^ t)) δ output.1) result] ≤
      (∑ r ∈ Finset.range (R + 1), error r) + ENNReal.ofReal (1 - min θ δ) ^ s := by
  unfold experiment
  apply prEvent_bind_le_of_forall_le
  intro publication
  apply prEvent_followM_le
  intro word after
  refine (prEvent_bind_le_prEvent_add_of_support _ _
    (returned (fun layers ↦ ¬ (toTrace t D layers).Safe θ)) _ ?_).trans
      (add_le_add (commitTail_escape_le t θ prover 0 D error escapes word after) le_rfl)
  intro committed member good
  rw [prEvent_followM]
  cases committed with
  | mk outcome poststate events =>
      cases outcome with
      | stopped why => exact bot_le
      | returned layers =>
          have initial := (yields_runM (commitTail_initial t 0 word D)
            prover.handler after _ member layers rfl).1
          simp only [returned, not_not] at good
          simp only [Functor.map_map, returned_repack]
          by_cases far : Far D (degreeBound (R + 1) (2 ^ t)) δ word
          · apply finish_escape_le roots t s D shift geometry compatible θ δ layers good
              (initial.symm ▸ far) policy queriesProver reader
          · simp only [far, and_false, returned_false, prEvent_false]
            exact bot_le

end ZkcSecurity.ArkLib.Fri.Phases
