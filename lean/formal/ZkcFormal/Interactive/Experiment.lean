module

public import ZkcFormal.ProcessJudgment
public import ZkcFormal.Interactive.FiniteLaw

@[expose] public section

namespace ZkcFormal.Interactive
open Zkc.Core

/-- The reply law at the current operation and state. Stateful adversaries and public-coin
services update their respective state when the operation actually occurs. -/
structure Experiment (S : Sig) (σ : Type) where
  answer : (op : S.Op) → σ → FiniteLaw (S.Reply op × σ)

namespace Experiment
variable {S : Sig} {σ H A B : Type} (K : Experiment S σ)

/-- Interpret one effect using the reply law at the state where it occurs. -/
def expectation : ProcessJudgment S (σ → Mass) where
  node op next s := (K.answer op s).expect fun reply => next reply.1 reply.2

/-- Unconditional expected payoff of the returned value and final state.
Verifier stops, service aborts and missing replies contribute zero. -/
def expect (post : A → σ → Mass) (p : Process S H A) : σ → Mass :=
  p.interpret K.expectation post (fun _ _ => 0)

@[simp] theorem expect_done (post : A → σ → Mass) (a : A) (s : σ) :
    K.expect (H := H) post (.done a) s = post a s := rfl

@[simp] theorem expect_halt (post : A → σ → Mass) (h : H) (s : σ) :
    K.expect post (.halt h) s = 0 := rfl

theorem expect_call (post : A → σ → Mass) (op : S.Op) (next : S.Reply op → Process S H A) (s : σ) :
    K.expect post (.call op next) s = (K.answer op s).expect (fun reply => K.expect post (next reply.1) reply.2) := rfl

/-- A return reachable by a sequence of replies of positive weight. -/
inductive Reaches : Process S H A → σ → A → σ → Prop where
  | done (a : A) (s : σ) : Reaches (.done a) s a s
  | call {op : S.Op} {next : S.Reply op → Process S H A} {s t u : σ} {r : S.Reply op} {a : A}
      (reply : (K.answer op s).Supports (r,t)) (tail : Reaches (next r) t a u) :
      Reaches (.call op next) s a u

theorem Reaches.of_bind {S : Sig} {σ H A B : Type} {K : Experiment S σ}
    {p : Process S H A} {next : A → Process S H B} {s u : σ} {b : B}
    (found : K.Reaches (p.bind next) s b u) : ∃ a t, K.Reaches p s a t ∧ K.Reaches (next a) t b u := by
  induction p generalizing s with
  | done a => exact ⟨a,s,.done ..,found⟩
  | halt why => cases found
  | call op k ih =>
    cases found with
    | call reply tail =>
      obtain ⟨a,t,first,later⟩ := ih _ tail
      exact ⟨a,t,.call reply first,later⟩

theorem Reaches.of_map {S : Sig} {σ H A B : Type} {K : Experiment S σ}
    {p : Process S H A} {f : A → B} {s u : σ} {b : B} (found : K.Reaches (p.map f) s b u) :
    ∃ a, K.Reaches p s a u ∧ f a = b := by
  rw [Process.map_eq_bind] at found
  obtain ⟨a,t,first,last⟩ := found.of_bind
  cases last
  exact ⟨a,first,rfl⟩

theorem expect_bind (p : Process S H A) (next : A → Process S H B) (post : B → σ → Mass) (s : σ) :
    K.expect post (p.bind next) s = K.expect (fun a t => K.expect post (next a) t) p s := by
  exact congrFun (p.interpret_bind K.expectation post (fun _ _ => 0) next) s

theorem expect_mono (p : Process S H A) (s : σ) (f g : A → σ → Mass)
    (le : ∀ a t, K.Reaches p s a t → f a t ≤ g a t) : K.expect f p s ≤ K.expect g p s := by
  induction p generalizing s with
  | done a => exact le a s (.done ..)
  | halt => exact Mass.le_refl
  | call op k ih =>
    apply (K.answer op s).mono
    intro reply reachable
    exact ih reply.1 reply.2 fun a t tail => le a t (.call reachable tail)

theorem expect_add (p : Process S H A) (s : σ) (f g : A → σ → Mass) :
    K.expect (fun a t => f a t + g a t) p s = K.expect f p s + K.expect g p s := by
  induction p generalizing s with
  | done => rfl
  | halt => exact (Mass.add_zero 0).symm
  | call op k ih =>
    simp only [expect_call]
    rw [← FiniteLaw.expect_add]
    exact congrArg (K.answer op s).expect (funext fun reply => ih reply.1 reply.2)

theorem expect_scale (p : Process S H A) (s : σ) (f : A → σ → Mass) (c : Mass) :
    K.expect (fun a t => f a t * c) p s = K.expect f p s * c := by
  induction p generalizing s with
  | done => rfl
  | halt => exact (Mass.zero_mul c).symm
  | call op k ih =>
    simp only [expect_call]
    rw [← FiniteLaw.expect_scale]
    exact congrArg (K.answer op s).expect (funext fun reply => ih reply.1 reply.2)

theorem expect_constant_le (p : Process S H A) (s : σ) {c : Mass} (hc : 0 ≤ c) :
    K.expect (fun _ _ => c) p s ≤ c := by
  induction p generalizing s with
  | done => exact Mass.le_refl
  | halt => exact hc
  | call op k ih =>
    apply Mass.le_trans _ ((K.answer op s).constant_le hc)
    exact (K.answer op s).mono fun reply _ => ih reply.1 reply.2

/-- The probability of returning with the indicated observation. -/
def probability (p : Process S H A) (s : σ) (event : A → σ → Bool) : Mass :=
  K.expect (fun a t => if event a t then 1 else 0) p s

theorem probability_le_one (p : Process S H A) (s : σ) (event : A → σ → Bool) :
    K.probability p s event ≤ 1 := by
  apply Mass.le_trans _ (K.expect_constant_le p s (c := 1) (by decide))
  apply K.expect_mono
  intro a t _
  split <;> first | exact Mass.le_refl | decide

/-- Compose a component bound with its continuation at the state the invocation returns.
For a reached return where the intermediate claim is true the first bound pays for
the entire continuation. At other returns the continuation must supply its own bound. -/
theorem reduction_bind (p : Process S H A) (next : A → Process S H B) (s : σ)
    (middle : A → σ → Bool) (event : B → σ → Bool) {component residual : Mass}
    (first : K.probability p s middle ≤ component) (nonnegative : 0 ≤ residual)
    (rest : ∀ a t, K.Reaches p s a t → middle a t = false →
      K.probability (next a) t event ≤ residual) :
    K.probability (p.bind next) s event ≤ component + residual := by
  unfold probability at first ⊢
  rw [K.expect_bind]
  apply Mass.le_trans (K.expect_mono p s _ (fun a t => (if middle a t then 1 else 0) + residual) ?_) ?_
  · intro a t reached
    cases h : middle a t with
    | false => simpa only [probability, Bool.false_eq_true, ite_false, Mass.zero_add] using rest a t reached h
    | true =>
      have bound := K.probability_le_one (next a) t event
      unfold probability at bound
      simp only [ite_true]
      apply Mass.le_trans bound
      simpa only [Mass.add_zero] using Mass.add_le_add (Mass.le_refl (a := 1)) nonnegative
  · rw [K.expect_add p s (fun a t => if middle a t then 1 else 0) (fun _ _ => residual)]
    have bound := K.expect_constant_le (A := A) p s nonnegative
    exact Mass.add_le_add first bound

end Experiment
end ZkcFormal.Interactive
