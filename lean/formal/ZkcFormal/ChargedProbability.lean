module

public import ZkcFormal.ProbabilisticProcess
public import ZkcFormal.ChargedJudgment
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

/-!
From the judgment with fees to a probability.

A process judged within a budget not to return badly returns badly with toProbability at most the
budget (`charged_bounds_probability`). The statement is for every signature, every service with a
state, and every policy of fees. Two things are asked of the service: what it answers with
positive toProbability is a reply that the judgment allows, and a set that the policy calls small
at a fee has at most that fee of the toProbability of the answers.

The policy that proofs use is the fees of samplers (`paysBy`): some effects have a sampler, and
there a fee pays for a set of replies of at most that toProbability under the sampler. A service
that draws as the samplers do (`Service.Follows`) meets the second hypothesis
(`sampled_bounds_probability`); what it answers at the other effects, and what it does with its
state, is not restricted.
-/

namespace ZkcFormal.ProbabilisticProcess
open Zkc.Core OracleComp
open scoped NNRat NNReal ENNReal

/-- A budget of fees, as a probability. -/
noncomputable def toProbability (budget : ℚ≥0) : ℝ≥0∞ := ((budget : ℝ≥0) : ℝ≥0∞)

theorem toProbability_add (a b : ℚ≥0) : toProbability (a + b) = toProbability a + toProbability b := by
  simp [toProbability]

theorem toProbability_le_iff {a b : ℚ≥0} : toProbability a ≤ toProbability b ↔ a ≤ b := by
  unfold toProbability
  exact_mod_cast Iff.rfl

theorem toProbability_mono {a b : ℚ≥0} (le : a ≤ b) : toProbability a ≤ toProbability b :=
  toProbability_le_iff.mpr le

/-- A count over a positive count, as a probability. -/
theorem toProbability_natCast_div (count total : ℕ) (positive : 0 < total) :
    toProbability ((count : ℚ≥0) / total) = (count : ℝ≥0∞) / total := by
  have nonzero : ((total : ℝ≥0)) ≠ 0 := by exact_mod_cast positive.ne'
  simp [toProbability, ENNReal.coe_div nonzero]

variable {S : Sig} {σ H A : Type}

/-- The run of a process that calls: the service answers, and the run continues with the reply
or ends without one. -/
theorem run_call (service : Service S σ) (op : S.Op) (next : S.Reply op → Process S H A) (s : σ) :
    run service (.call op next) s = (do
      let (reply, state) ← service op s
      match reply with
      | none => pure (.unavailable, state)
      | some v => run service (next v) state) := rfl

/-- An outcome that is no bad return: the toProbability of a bad return is zero. -/
theorem prEvent_pure_not_bad (bad : A → Prop) (o : Outcome H A) (t : σ)
    (clean : ∀ a, o = .returned a → ¬ bad a) :
    Pr{let out ← (pure (o, t) : ProbComp (Outcome H A × σ))}[
        ∃ a, out.1 = .returned a ∧ bad a] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun out reached => ?_
  rw [mem_support_pure_iff] at reached
  subst reached
  rintro ⟨a, same, isBad⟩
  exact clean a same isBad

/-- From the judgment with fees to a probability: a process judged within a budget not to return
badly returns badly with toProbability at most the budget. -/
theorem charged_bounds_probability (service : Service S σ)
    (allowed : ∀ op, S.Reply op → Prop) (small : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop)
    (bad : A → Prop)
    (permitted : ∀ op s reply t, (some reply, t) ∈ support (service op s) → allowed op reply)
    (sound : ∀ op s fee excluded, small op fee excluded →
      Pr{let out ← service op s}[∃ v, out.1 = some v ∧ excluded v] ≤ toProbability fee) :
    ∀ (p : Process S H A) (budget : ℚ≥0) (s : σ),
      p.interpret (.charged allowed small) (fun a _ => ¬ bad a) (fun _ _ => True) budget →
      Pr{let out ← run service p s}[∃ a, out.1 = .returned a ∧ bad a] ≤ toProbability budget := by
  intro p
  induction p with
  | done a =>
      intro budget s good
      have none : Pr{let out ← run service (.done a : Process S H A) s}[
          ∃ a, out.1 = .returned a ∧ bad a] = 0 :=
        prEvent_pure_not_bad bad _ s fun a' same => by cases same; exact good
      rw [none]
      exact zero_le
  | halt h =>
      intro budget s _
      have none : Pr{let out ← run service (.halt h : Process S H A) s}[
          ∃ a, out.1 = .returned a ∧ bad a] = 0 :=
        prEvent_pure_not_bad bad _ s fun a' same => by cases same
      rw [none]
      exact zero_le
  | call op next ih =>
      rintro budget s ⟨fee, excluded, within, isSmall, outside⟩
      rw [run_call]
      refine (prEvent_bind_le_prEvent_add_of_support _ _
        (fun out => ∃ v, out.1 = some v ∧ excluded v) _ (ε := toProbability (budget - fee))
        fun out reached notExcluded => ?_).trans ?_
      · obtain ⟨reply, t⟩ := out
        cases reply with
        | none =>
            show Pr{let out ← (pure (Outcome.unavailable, t) : ProbComp (Outcome H A × σ))}[_] ≤ _
            rw [prEvent_pure_not_bad bad _ t fun a' same => by cases same]
            exact zero_le
        | some v =>
            exact ih v (budget - fee) t
              (outside v (permitted op s v t reached) fun ex => notExcluded ⟨v, rfl, ex⟩)
      · calc Pr{let out ← service op s}[∃ v, out.1 = some v ∧ excluded v] +
              toProbability (budget - fee)
            ≤ toProbability fee + toProbability (budget - fee) :=
              add_le_add (sound op s fee excluded isSmall) le_rfl
          _ = toProbability budget := by rw [← toProbability_add, add_tsub_cancel_of_le within]

/-! ## The fees of samplers -/

/-- What a policy of fees knows of the effects: at some effects, how the reply is drawn. -/
abbrev Samplers (S : Sig) := (op : S.Op) → Option (ProbComp (S.Reply op))

/-- The fees of samplers. The zero fee excludes nothing, at every effect. At an effect with a
sampler, a fee pays for a set of replies whose toProbability under the sampler is at most the fee.
The set is chosen before the reply, from what the process has seen so far. -/
def paysBy (samplers : Samplers S) : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop :=
  fun op fee excluded => (fee = 0 ∧ ∀ v, ¬ excluded v) ∨
    ∃ draw, samplers op = some draw ∧ Pr{let v ← draw}[excluded v] ≤ toProbability fee

/-- A service draws as the samplers do: at an effect with a sampler, in every state, a set of
replies has at most the toProbability under the service that it has under the sampler. The
service may still not answer, and may do with its state what it likes. -/
def Service.Follows (service : Service S σ) (samplers : Samplers S) : Prop :=
  ∀ op draw, samplers op = some draw → ∀ s (excluded : S.Reply op → Prop),
    Pr{let out ← service op s}[∃ v, out.1 = some v ∧ excluded v] ≤ Pr{let v ← draw}[excluded v]

/-- What a fee of samplers pays for has at most the fee of the probability of the answers of a
service that draws as the samplers do. -/
theorem Service.Follows.pays {service : Service S σ} {samplers : Samplers S}
    (follows : service.Follows samplers) (op : S.Op) (s : σ) (fee : ℚ≥0)
    (excluded : S.Reply op → Prop) (pays : paysBy samplers op fee excluded) :
    Pr{let out ← service op s}[∃ v, out.1 = some v ∧ excluded v] ≤ toProbability fee := by
  rcases pays with ⟨_, nothing⟩ | ⟨draw, has, weight⟩
  · have none : Pr{let out ← service op s}[∃ v, out.1 = some v ∧ excluded v] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun _ _ ⟨v, _, ex⟩ => nothing v ex
    rw [none]
    exact zero_le
  · exact (follows op draw has s excluded).trans weight

/-- From the judgment with the fees of samplers to a probability, for every service that draws
as the samplers do and answers only what is allowed. -/
theorem sampled_bounds_probability (service : Service S σ) (samplers : Samplers S)
    (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop)
    (permitted : ∀ op s reply t, (some reply, t) ∈ support (service op s) → allowed op reply)
    (follows : service.Follows samplers) (p : Process S H A) (budget : ℚ≥0) (s : σ)
    (judged : p.interpret (.charged allowed (paysBy samplers)) (fun a _ => ¬ bad a)
      (fun _ _ => True) budget) :
    Pr{let out ← run service p s}[∃ a, out.1 = .returned a ∧ bad a] ≤ toProbability budget :=
  charged_bounds_probability service allowed (paysBy samplers) bad permitted
    (fun op s fee excluded pays => follows.pays op s fee excluded pays) p budget s judged

/-! ## Fees within what each effect is allowed -/

/-- The fees of samplers within allowances: a fee that the sampler of the effect pays for, and
that is at most what the effect is allowed. A bound that is judged under this policy is paid
effect by effect within the allowances, and not only in total: a fee cannot be moved from the
effect that a source charges to another. -/
def paysWithin (samplers : Samplers S) (allowance : S.Op → ℚ≥0) :
    (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop :=
  fun op fee excluded => paysBy samplers op fee excluded ∧ fee ≤ allowance op

/-- From the judgment with fees within allowances to a probability, for every service that draws
as the samplers do and answers only what is allowed. -/
theorem allowed_bounds_probability (service : Service S σ) (samplers : Samplers S)
    (allowance : S.Op → ℚ≥0) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop)
    (permitted : ∀ op s reply t, (some reply, t) ∈ support (service op s) → allowed op reply)
    (follows : service.Follows samplers) (p : Process S H A) (budget : ℚ≥0) (s : σ)
    (judged : p.interpret (.charged allowed (paysWithin samplers allowance)) (fun a _ => ¬ bad a)
      (fun _ _ => True) budget) :
    Pr{let out ← run service p s}[∃ a, out.1 = .returned a ∧ bad a] ≤ toProbability budget :=
  charged_bounds_probability service allowed (paysWithin samplers allowance) bad permitted
    (fun op s fee excluded pays => follows.pays op s fee excluded pays.1) p budget s judged

end ZkcFormal.ProbabilisticProcess
