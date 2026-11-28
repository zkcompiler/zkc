module

public import ZkcFormal.ReturnExperiment
public import VCVio.OracleComp.EvalDist.Sum

@[expose] public section

/-!
The value of a process.

At an effect with a sampler the value is the mean of the continuation's value under the sampler,
over the allowed replies (0 at the others); at an effect without one it is the supremum over
the allowed replies; at a return it is 1 on the event `bad` and 0 off it; at a halt 0. It is
the supremum of what a conforming service makes of the process: the party that answers the
effects without a sampler hears every reply before it answers. The supremum need not be
attained (an effect without a sampler may have infinitely many replies).

- `sound`: every service that draws as the samplers do and answers only what is allowed
  returns a value of `bad` with probability at most the value.
- `chase_attains`: one conforming service, whose state is the rest of the process and a
  target, returns badly with probability above every number below the value.
- `returnsWithin_iff`: the experiment of a bound on returns holds at a limit exactly when the
  value is at most the limit. So a statement of soundness is a statement about the value, and
  no limit below the value holds.
- `exact`: a process whose every effect has a sampler that draws only allowed replies returns
  badly, against a service that answers as the samplers draw, with probability the value.

Nothing here is of a judgment with fees: that a judgment with fees bounds the value is in
`ZkcFormal.ChargedProbability`. The two inductions on a process are stated on `run`, the fold
of the process, and reach the simulation by `prEvent_run`.
-/

namespace ZkcFormal.Value
open Zkc.Core ZkcFormal.ProbabilisticProcess OracleComp
open scoped ENNReal NNRat

noncomputable section

variable {α β : Type}

/-! ## Means of a sampler -/

/-- The mean of a function under a sampler. -/
def mean (d : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' x, Pr{let y ← d}[y = x] * f x

theorem mean_mono (d : ProbComp α) {f g : α → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    mean d f ≤ mean d g := tsum_le_tsum fun x => by gcongr; exact h x

theorem mean_const (d : ProbComp α) (c : ℝ≥0∞) : mean d (fun _ => c) = c :=
  tsum_prEvent_mul_of_const_on_support d fun _ _ => rfl

theorem mean_pure (a : α) (f : α → ℝ≥0∞) : mean (pure a) f = f a := tsum_prEvent_pure_mul a f

theorem mean_map (d : ProbComp α) (h : α → β) (f : β → ℝ≥0∞) :
    mean (h <$> d) f = mean d (fun x => f (h x)) := tsum_prEvent_map_mul ..

theorem mean_bind (d : ProbComp α) (k : α → ProbComp β) (f : β → ℝ≥0∞) :
    mean (d >>= k) f = mean d (fun x => mean (k x) f) := tsum_prEvent_bind_mul ..

theorem mean_mul_const (d : ProbComp α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    mean d (fun x => c * f x) = c * mean d f := by
  unfold mean
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun x => by ring

/-- 1 on an event, 0 off it. -/
def indicator (e : α → Prop) (x : α) : ℝ≥0∞ := by classical exact if e x then 1 else 0

theorem mean_indicator (d : ProbComp α) (e : α → Prop) :
    mean d (indicator e) = Pr{let x ← d}[e x] := by
  classical
  rw [prEvent_eq_tsum_ite]
  exact tsum_congr fun x => by by_cases h : e x <;> simp [indicator, h]

theorem mean_cases (d : ProbComp α) (e : α → Prop) [DecidablePred e] (a b : ℝ≥0∞) :
    mean d (fun x => if e x then a else b) =
      Pr{let x ← d}[e x] * a + Pr{let x ← d}[¬ e x] * b := by
  classical
  rw [prEvent_eq_tsum_ite d e, prEvent_eq_tsum_ite d (fun x => ¬ e x), ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_right, ← tsum_add]
  exact tsum_congr fun x => by by_cases h : e x <;> simp [h]

theorem mean_mono_support (d : ProbComp α) {f g : α → ℝ≥0∞}
    (h : ∀ x ∈ support d, f x ≤ g x) : mean d f ≤ mean d g := by
  refine tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support d
  · gcongr; exact h x hx
  · have hz := prEvent_eq_zero_of_forall_mem_support d (· = x) fun y hy eq => hx (eq ▸ hy)
    simp [hz]

/-- A function where a predicate holds, 0 elsewhere. -/
def mask (p : α → Prop) (f : α → ℝ≥0∞) (x : α) : ℝ≥0∞ := by classical exact if p x then f x else 0

/-- The value at one effect from the values after each reply: the mean under the sampler over
allowed replies where there is a sampler, the supremum over allowed replies where there is none. -/
def node (draw : Option (ProbComp α)) (allowed : α → Prop) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  match draw with
  | some d => mean d (mask allowed f)
  | none => ⨆ x, ⨆ (_ : allowed x), f x

theorem node_mono (d : Option (ProbComp α)) (p : α → Prop) {f g : α → ℝ≥0∞}
    (h : ∀ x, p x → f x ≤ g x) : node d p f ≤ node d p g := by
  classical
  cases d with
  | none => exact iSup_mono fun x => iSup_mono (h x)
  | some d => exact mean_mono d fun x => by by_cases hx : p x <;> simp [mask, hx, h]

theorem node_bound (d : Option (ProbComp α)) (p : α → Prop) {q : α → ℝ≥0∞} {b : ℝ≥0∞}
    (h : ∀ x, p x → q x ≤ b) : node d p q ≤ b := by
  classical
  cases d with
  | none => exact iSup_le fun x => iSup_le (h x)
  | some d =>
    rw [← mean_const d b]
    exact mean_mono d fun x => by by_cases hx : p x <;> simp [mask, hx, h]

/-! ## The value of a process -/

variable {S : Sig} {H A σ : Type}

/-- The judgment of the value: `node` at each effect. -/
def judgment (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) :
    ProcessJudgment S ℝ≥0∞ :=
  ⟨fun op => node (samplers op) (allowed op)⟩

/-- **The value of a process** for the event `bad` of its returns. -/
def value (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop)
    (p : Process S H A) : ℝ≥0∞ :=
  p.interpret (judgment samplers allowed) (indicator bad) (fun _ => 0)

theorem value_call (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop)
    (op : S.Op) (k : S.Reply op → Process S H A) :
    value samplers allowed bad (.call op k) =
      node (samplers op) (allowed op) fun v => value samplers allowed bad (k v) := rfl

theorem value_le_one (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop)
    (p : Process S H A) : value samplers allowed bad p ≤ 1 := by
  classical
  induction p with
  | done a => change indicator bad a ≤ 1; by_cases h : bad a <;> simp [indicator, h]
  | halt h => exact zero_le_one
  | call o k ih => exact node_bound _ _ fun x _ => ih x

/-! ## Soundness: every conforming service returns badly with probability at most the value -/

/-- The first component of an optional reply, valued; 0 where there is no reply. -/
def optional {X : Type} (f : X → ℝ≥0∞) : Option X → ℝ≥0∞
  | some x => f x
  | none => 0

theorem marginal {X : Type} (d : ProbComp (Option X × σ)) (coin : ProbComp X) (f : X → ℝ≥0∞)
    (singles : ∀ x, Pr{let u ← d}[u.1 = some x] ≤ Pr{let y ← coin}[y = x]) :
    mean d (fun u => optional f u.1) ≤ mean coin f := by
  rw [← mean_map d Prod.fst (optional f)]
  unfold mean
  rw [tsum_option _ CompleteLattice.summable]
  simp only [optional, mul_zero, zero_add, prEvent_map]
  exact tsum_le_tsum fun x => by gcongr; exact singles x

theorem optional_node {X : Type} (mx : ProbComp (Option X × σ)) (d : Option (ProbComp X))
    (ok : X → Prop) (f : X → ℝ≥0∞) (g : Option X × σ → ℝ≥0∞)
    (perm : ∀ x s, (some x, s) ∈ support mx → ok x)
    (follows : ∀ coin, d = some coin → ∀ x, Pr{let u ← mx}[u.1 = some x] ≤ Pr{let y ← coin}[y = x])
    (stop : ∀ s, g (none, s) = 0) (step : ∀ x s, g (some x, s) ≤ f x) :
    mean mx g ≤ node d ok f := by
  classical
  cases d with
  | none =>
    rw [← mean_const mx (node none ok f)]
    apply mean_mono_support
    rintro ⟨_ | x, s⟩ hs
    · rw [stop]; exact zero_le
    · exact (step ..).trans (le_iSup_of_le x (le_iSup_of_le (perm _ _ hs) le_rfl))
  | some coin =>
    apply le_trans (b := mean mx (fun u => optional (mask ok f) u.1))
    · apply mean_mono_support
      rintro ⟨_ | x, s⟩ hs
      · exact (stop s).le
      · simpa [optional, mask, perm _ _ hs] using step x s
    · exact marginal mx coin _ (follows coin rfl)

/-- **Soundness of the value**, on `run`. -/
theorem sound (service : Service S σ) (samplers : Samplers S) (allowed : ∀ o, S.Reply o → Prop)
    (perm : ∀ o s v t, (some v, t) ∈ support (service o s) → allowed o v)
    (law : service.Follows samplers) (p : Process S H A) (bad : A → Prop) (s : σ) :
    Pr{let u ← run service p s}[∃ a, u.1 = .returned a ∧ bad a] ≤ value samplers allowed bad p := by
  classical
  induction p generalizing s with
  | done a =>
    change Pr{let u ← (pure (Outcome.returned a, s) : ProbComp (Outcome H A × σ))}[_] ≤ indicator bad a
    by_cases ha : bad a <;> simp [indicator, ha]
  | halt h =>
    change Pr{let u ← (pure (Outcome.halted h, s) : ProbComp (Outcome H A × σ))}[_] ≤ 0
    simp
  | call o k ih =>
    rw [run_call, ← mean_indicator, mean_bind]
    apply optional_node (service o s) (samplers o) (allowed o) (fun x => value samplers allowed bad (k x))
    · exact perm o s
    · intro coin has x
      simpa using law o coin has s (· = x)
    · intro st; simp [mean_indicator]
    · intro x st; simpa [mean_indicator] using ih x st

/-- **The experiment from the value**: a value at most `b` gives `ReturnsWithin` at `b`. -/
theorem returnsWithin_of_value (p : Process S H A) (samplers : Samplers S)
    (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop) {b : ℝ≥0∞}
    (le : value samplers allowed bad p ≤ b) : ReturnsWithin p samplers allowed bad b := by
  intro σ service conforms s
  have bound := (sound service samplers allowed conforms.permitted conforms.follows p bad s).trans le
  rw [prEvent_run service p s fun outcome => ∃ a, outcome = .returned a ∧ bad a] at bound
  refine le_trans (le_of_eq (prEvent_congr _ _ _ fun out => ?_)) bound
  exact exists_congr fun _ => and_congr_left fun _ => outcomeOf_eq_returned.symm

/-! ## Attainment: a conforming service that beats every number below the value -/

theorem exists_scale {t N : ℝ≥0∞} (lt : t < N) (top : N ≠ ⊤) : ∃ c : ℝ≥0∞, c < 1 ∧ t < c * N := by
  have pos : N ≠ 0 := (lt_of_le_of_lt zero_le lt).ne'
  have below : t / N < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl pos) (Or.inl top), one_mul]; exact lt
  obtain ⟨c, hc, c1⟩ := exists_between below
  exact ⟨c, c1, by rwa [ENNReal.div_lt_iff (Or.inl pos) (Or.inl top)] at hc⟩

/-- A scale `c < 1` with `t < c * N` where one exists. -/
def scale (t N : ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact if h : t < N ∧ N ≠ ⊤ then Classical.choose (exists_scale h.1 h.2) else 0

theorem scale_spec {t N : ℝ≥0∞} (lt : t < N) (top : N ≠ ⊤) : scale t N < 1 ∧ t < scale t N * N := by
  classical
  unfold scale
  rw [dite_eq_left ⟨lt, top⟩]
  exact Classical.choose_spec (exists_scale lt top)

theorem scale_le_one (t N : ℝ≥0∞) : scale t N ≤ 1 := by
  classical
  unfold scale
  split
  · next h => exact (Classical.choose_spec (exists_scale h.1 h.2)).1.le
  · exact zero_le

variable (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop)

/-- What the chasing service does at the first effect of what is left, `op` with continuation
`k`, aiming above `t`. At a draw: draw by the sampler, answer an allowed reply and aim at the
scaled value after it. At a message: answer an allowed reply after which the value is above `t`. -/
def chaseStep (op : S.Op) (k : S.Reply op → Process S H A) (t : ℝ≥0∞) :
    ProbComp (Option (S.Reply op) × (Process S H A × ℝ≥0∞)) := by
  classical
  exact match samplers op with
  | some coin =>
    let c := scale t (node (some coin) (allowed op) fun v => value samplers allowed bad (k v))
    coin >>= fun v => if allowed op v then pure (some v, (k v, c * value samplers allowed bad (k v)))
      else pure (none, (k v, 0))
  | none =>
    if h : ∃ v, allowed op v ∧ t < value samplers allowed bad (k v) then
      pure (some h.choose, (k h.choose, t))
    else pure (none, (.call op k, t))

/-- **The chasing service.** Its state is what is left of the process and a target; at the
first effect of what is left it answers by `chaseStep`; at any other effect it does not answer. -/
def chase : Service S (Process S H A × ℝ≥0∞) := fun op st => by
  classical
  exact match st with
  | (.call op' k, t) => if h : op' = op then h ▸ chaseStep samplers allowed bad op' k t
      else pure (none, st)
  | st => pure (none, st)

theorem chase_at (op : S.Op) (k : S.Reply op → Process S H A) (t : ℝ≥0∞) :
    chase samplers allowed bad op (.call op k, t) = chaseStep samplers allowed bad op k t := by
  simp [chase]

theorem chase_off (op : S.Op) (st : Process S H A × ℝ≥0∞)
    (off : ∀ k : S.Reply op → Process S H A, ∀ t, st ≠ (.call op k, t)) :
    chase samplers allowed bad op st = pure (none, st) := by
  obtain ⟨q, t⟩ := st
  cases q with
  | done => rfl
  | halt => rfl
  | call op' k =>
    by_cases h : op' = op
    · subst h; exact absurd rfl (off k t)
    · simp [chase, h]

/-- Where the chasing service answers, its answers cover all of `chaseStep`'s support. -/
theorem chase_cases (op : S.Op) (st : Process S H A × ℝ≥0∞) :
    (∃ k t, st = (.call op k, t) ∧ chase samplers allowed bad op st = chaseStep samplers allowed bad op k t) ∨
      chase samplers allowed bad op st = pure (none, st) := by
  by_cases h : ∃ k t, st = (.call op k, t)
  · obtain ⟨k, t, rfl⟩ := h
    exact Or.inl ⟨k, t, rfl, chase_at ..⟩
  · refine Or.inr (chase_off samplers allowed bad op st fun k t eq => h ⟨k, t, eq⟩)

theorem chaseStep_permitted (op : S.Op) (k : S.Reply op → Process S H A) (t : ℝ≥0∞) (v : S.Reply op)
    (st : Process S H A × ℝ≥0∞) (mem : (some v, st) ∈ support (chaseStep samplers allowed bad op k t)) :
    allowed op v := by
  classical
  unfold chaseStep at mem
  split at mem
  · simp only [mem_support_bind_iff] at mem
    obtain ⟨w, _, hw⟩ := mem
    by_cases hok : allowed op w
    · simp only [hok, ite_true, mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at hw
      exact hw.1 ▸ hok
    · simp [hok] at hw
  · split at mem
    · next h =>
      simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at mem
      exact mem.1 ▸ h.choose_spec.1
    · simp at mem

theorem chaseStep_follows (op : S.Op) (k : S.Reply op → Process S H A) (t : ℝ≥0∞)
    (coin : ProbComp (S.Reply op)) (has : samplers op = some coin) (excluded : S.Reply op → Prop) :
    Pr{let out ← chaseStep samplers allowed bad op k t}[∃ v, out.1 = some v ∧ excluded v] ≤
      Pr{let v ← coin}[excluded v] := by
  classical
  unfold chaseStep
  split
  · next coin' has' =>
    rw [has] at has'
    cases has'
    rw [← mean_indicator, ← mean_indicator, mean_bind]
    refine mean_mono _ fun v => ?_
    by_cases hok : allowed op v
    · simp only [hok, ite_true, mean_pure]
      by_cases he : excluded v <;> simp [indicator, he]
    · simp [hok, mean_pure, indicator]
  · next none' => rw [has] at none'; cases none'

/-- The chasing service conforms. -/
theorem chase_conforms : (chase (H := H) samplers allowed bad).Conforms samplers allowed where
  follows := by
    intro op coin has st excluded
    rcases chase_cases samplers allowed bad op st with ⟨k, t, -, eq⟩ | eq
    · rw [eq]; exact chaseStep_follows samplers allowed bad op k t coin has excluded
    · rw [eq]; simp
  permitted := by
    intro op st v st' mem
    rcases chase_cases samplers allowed bad op st with ⟨k, t, -, eq⟩ | eq
    · rw [eq] at mem; exact chaseStep_permitted samplers allowed bad op k t v st' mem
    · rw [eq] at mem; simp at mem

/-- **Attainment.** Run from the state that holds the process and a target below its value, the
chasing service returns a value of `bad` with probability above the target. -/
theorem chase_attains (p : Process S H A) (t : ℝ≥0∞) (lt : t < value samplers allowed bad p) :
    t < Pr{let u ← run (chase samplers allowed bad) p (p, t)}[∃ a, u.1 = .returned a ∧ bad a] := by
  classical
  induction p generalizing t with
  | done a =>
    change t < indicator bad a at lt
    by_cases ha : bad a
    · change t < Pr{let u ← (pure (Outcome.returned a, (Process.done a, t)) :
        ProbComp (Outcome H A × (Process S H A × ℝ≥0∞)))}[_]
      simpa [ha, indicator] using lt
    · simp [indicator, ha] at lt
  | halt h => exact absurd lt (by simp [value, Process.interpret])
  | call op k ih =>
    rw [run_call, chase_at, ← mean_indicator, mean_bind]
    rw [value_call] at lt
    unfold chaseStep
    split
    · next coin has =>
      rw [has] at lt
      set N := node (some coin) (allowed op) fun v => value samplers allowed bad (k v)
      have top : N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
        (node_bound _ _ fun v _ => value_le_one samplers allowed bad (k v))
      obtain ⟨c1, above⟩ := scale_spec lt top
      refine lt_of_lt_of_le above ?_
      change scale t N * mean coin (mask (allowed op) fun v => value samplers allowed bad (k v)) ≤ _
      rw [mean_bind, ← mean_mul_const]
      refine mean_mono _ fun v => ?_
      by_cases hok : allowed op v
      · simp only [hok, ite_true, mean_pure, mask]
        set a := value samplers allowed bad (k v)
        rw [mean_indicator]
        by_cases a0 : a = 0
        · simp [a0]
        · have small : scale t N * a < a := by
            have atop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (value_le_one ..)
            calc scale t N * a < 1 * a := by
                  rw [mul_comm _ a, mul_comm 1 a]; exact ENNReal.mul_lt_mul_right a0 atop c1
              _ = a := one_mul a
          exact (ih v _ small).le
      · simp [hok, mask, mean_pure]
    · next has =>
      rw [has] at lt
      have exists_v : ∃ v, allowed op v ∧ t < value samplers allowed bad (k v) := by
        obtain ⟨v, hv⟩ := lt_iSup_iff.mp lt
        obtain ⟨ok, hv⟩ := lt_iSup_iff.mp hv
        exact ⟨v, ok, hv⟩
      rw [dite_eq_left exists_v, mean_pure]
      simpa [mean_indicator] using ih _ t exists_v.choose_spec.2

/-- **No bound below the value holds**: a bound of the experiment is at least the value. -/
theorem value_le_of_returnsWithin (p : Process S H A) {b : ℝ≥0∞}
    (within : ReturnsWithin p samplers allowed bad b) : value samplers allowed bad p ≤ b := by
  by_contra above
  push Not at above
  have attained := chase_attains samplers allowed bad p b above
  have bound := within _ (chase samplers allowed bad) (chase_conforms samplers allowed bad) (p, b)
  rw [prEvent_run _ p _ fun outcome => ∃ a, outcome = .returned a ∧ bad a] at attained
  refine absurd (lt_of_lt_of_le attained (le_trans (le_of_eq (prEvent_congr _ _ _ fun out => ?_)) bound))
    (lt_irrefl _)
  exact exists_congr fun _ => and_congr_left fun _ => outcomeOf_eq_returned

/-- **The experiment is the value**: a bound holds against every conforming service exactly when
it is at least the value. -/
theorem returnsWithin_iff (p : Process S H A) (b : ℝ≥0∞) :
    ReturnsWithin p samplers allowed bad b ↔ value samplers allowed bad p ≤ b :=
  ⟨value_le_of_returnsWithin samplers allowed bad p, returnsWithin_of_value p samplers allowed bad⟩

/-! ## A process of draws only -/

/-- Every effect of the process has a sampler, which draws only allowed replies. -/
def drawsOnly (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) : ProcessJudgment S Prop :=
  ⟨fun op next => (∃ d, samplers op = some d ∧ ∀ v ∈ support d, allowed op v) ∧ ∀ v, next v⟩

/-- **Exactness**: against a service that draws as the samplers do, from every state, a process
of draws only returns badly with probability the value. -/
theorem exact (service : Service S σ) (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop)
    (draws : service.Draws samplers) (bad : A → Prop) (p : Process S H A)
    (only : p.interpret (drawsOnly samplers allowed) (fun _ => True) (fun _ => True)) (s : σ) :
    Pr{let u ← run service p s}[∃ a, u.1 = .returned a ∧ bad a] = value samplers allowed bad p := by
  classical
  induction p generalizing s with
  | done a =>
    change Pr{let u ← (pure (Outcome.returned a, s) : ProbComp (Outcome H A × σ))}[_] = indicator bad a
    by_cases ha : bad a <;> simp [indicator, ha]
  | halt h =>
    change Pr{let u ← (pure (Outcome.halted h, s) : ProbComp (Outcome H A × σ))}[_] = 0
    simp
  | call o k ih =>
    obtain ⟨⟨d, has, perm⟩, rest⟩ := only
    rw [run_call, ← mean_indicator, mean_bind, value_call, has]
    change _ = mean d (mask (allowed o) fun v => value samplers allowed bad (k v))
    have step : (fun u : Option (S.Reply o) × σ => mean (match u with
        | (reply, state) => match reply with
          | none => pure (Outcome.unavailable, state)
          | some v => run service (k v) state)
        (indicator fun u => ∃ a, u.1 = .returned a ∧ bad a)) =
        fun u => optional (fun v => value samplers allowed bad (k v)) u.1 := by
      funext ⟨reply, state⟩
      cases reply with
      | none => simp [optional, mean_pure, indicator]
      | some v => rw [mean_indicator]; exact ih v (rest v) state
    refine (congrArg (mean (service o s)) step).trans ?_
    rw [← mean_map (service o s) Prod.fst]
    have same : mean (Prod.fst <$> service o s) (optional fun v =>
        value samplers allowed bad (k v)) =
        mean (Option.some <$> d) (optional fun v => value samplers allowed bad (k v)) := by
      unfold mean
      exact tsum_congr fun x => by rw [(draws o d has s).prEvent_eq (· = x)]
    rw [same, mean_map]
    apply le_antisymm
    · exact mean_mono_support d fun v hv => by simp [optional, mask, perm v hv]
    · exact mean_mono_support d fun v hv => by simp [optional, mask, perm v hv]

end

end ZkcFormal.Value
