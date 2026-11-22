module

public import ZkcFormal.Interactive.Experiment
public import ZkcFormal.ProbabilisticProcess
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace ZkcFormal.FiniteService
open Zkc.Core Interactive ProbabilisticProcess OracleComp
open scoped NNReal ENNReal BigOperators

variable {S : Sig} {σ H A : Type}

/-- Map the project's quotient of rational tickets to nonnegative reals. -/
noncomputable def amount (m : Mass) : ℝ≥0 :=
  Quotient.lift (fun f : Mass.Fraction => (f.num : ℝ≥0) / f.den)
    (fun a b eq => by
      change a.num * b.den = b.num * a.den at eq
      apply (div_eq_div_iff (by exact_mod_cast Nat.ne_of_gt a.positive)
        (by exact_mod_cast Nat.ne_of_gt b.positive)).2
      exact_mod_cast eq) m

noncomputable def embed (m : Mass) : ℝ≥0∞ := amount m

@[simp] theorem embed_fraction (a : Mass.Fraction) :
    embed (Mass.ofFraction a) = ((a.num : ℝ≥0) / a.den : ℝ≥0) := rfl

@[simp] theorem embed_zero : embed 0 = 0 := by
  exact (embed_fraction (.ofNat 0)).trans (by simp [Mass.Fraction.ofNat])

@[simp] theorem embed_one : embed 1 = 1 := by
  exact (embed_fraction (.ofNat 1)).trans (by simp [Mass.Fraction.ofNat])

@[simp] theorem embed_add (a b : Mass) : embed (a + b) = embed a + embed b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    unfold embed
    rw [← ENNReal.coe_add]
    apply congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    change ((a.num * b.den + b.num * a.den : ℕ) : ℝ≥0) / ((a.den * b.den : ℕ) : ℝ≥0) =
      (a.num : ℝ≥0) / a.den + (b.num : ℝ≥0) / b.den
    push_cast
    have ha : (a.den : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt a.positive
    have hb : (b.den : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt b.positive
    field_simp

@[simp] theorem embed_mul (a b : Mass) : embed (a * b) = embed a * embed b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    unfold embed
    rw [← ENNReal.coe_mul]
    apply congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    change ((a.num * b.num : ℕ) : ℝ≥0) / ((a.den * b.den : ℕ) : ℝ≥0) =
      (a.num : ℝ≥0) / a.den * ((b.num : ℝ≥0) / b.den)
    push_cast
    rw [div_mul_div_comm]

/-- Each reachable call samples a finite slot at its current state. Duplicate replies
and a missing reply may occupy several slots. A missing reply may have an external
next state. The returned-event theorem never inspects that state. -/
structure Slots (S : Sig) (σ : Type) where
  width : S.Op → σ → Nat
  answer : (op : S.Op) → (s : σ) → Fin (width op s + 1) → Option (S.Reply op) × σ

def service (t : Slots S σ) : Service S σ :=
  fun op s => t.answer op s <$> ProbComp.uniformFin (t.width op s)

def payoff {R σ : Type} (f : R × σ → Mass) : Option R × σ → Mass
  | (none, _) => 0
  | (some r, s) => f (r,s)

/-- A one-operation equality, independent of the protocol, its stops, and final event. -/
def Agrees (t : Slots S σ) (K : Experiment S σ) : Prop :=
  ∀ op s (f : S.Reply op × σ → Mass),
    embed ((K.answer op s).expect f) =
      (∑ i, embed (payoff f (t.answer op s i))) / (t.width op s + 1)

def observed {H A σ : Type} (event : A → σ → Bool) : Outcome H A × σ → Prop
  | (.returned a, s) => event a s = true
  | (.halted _, _) | (.unavailable, _) => False

/-- The same event in the existing stateful VCVio interpreter and the actual zkc
finite expectation, for every well-founded process and every initial state. -/
theorem return_probability (t : Slots S σ) (K : Experiment S σ)
    (same : Agrees t K) (event : A → σ → Bool) (p : Process S H A) (s : σ) :
    prEvent (observed event <$> run (service t) p s) = embed (K.probability p s event) := by
  classical
  induction p generalizing s with
  | done a =>
    change prEvent (_ <$> pure _) = _
    rw [prEvent_pure]
    cases h : event a s <;> simp [observed, Experiment.probability, h]
  | halt reason =>
    change prEvent (_ <$> pure _) = _
    rw [prEvent_pure]
    simp [observed, Experiment.probability]
  | call op next ih =>
    change prEvent (_ <$> (service t op s >>= _)) = _
    rw [service, bind_map_left, prEvent_bind_eq_lintegral_of_discrete,
      ProbComp.lintegral_evalDist_uniformFin]
    change _ = embed ((K.answer op s).expect (fun rs => K.probability (next rs.1) rs.2 event))
    rw [same]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases h : t.answer op s i with
    | mk reply state =>
      cases reply with
      | none => simp [observed, payoff]
      | some r => simpa [h, Function.comp_def, payoff, service, run] using ih r state


theorem embed_le {a b : Mass} : embed a ≤ embed b ↔ a ≤ b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    unfold embed
    rw [ENNReal.coe_le_coe]
    change (a.num : ℝ≥0) / a.den ≤ (b.num : ℝ≥0) / b.den ↔ a.num * b.den ≤ b.num * a.den
    rw [div_le_div_iff₀ (by exact_mod_cast a.positive) (by exact_mod_cast b.positive)]
    exact_mod_cast Iff.rfl

def slotWeight (n : Nat) : Mass := Mass.ofFraction ⟨1, n+1, by omega⟩

@[simp] theorem embed_weight (n : Nat) : embed (slotWeight n) = (n+1 : ℝ≥0∞)⁻¹ := by
  simp [slotWeight]

def tickets {R σ : Type} (n : Nat) : List (Option R × σ) → List (Weighted (R × σ))
  | [] => []
  | (none, _) :: xs => tickets n xs
  | (some r, s) :: xs =>
      ⟨(r,s), slotWeight n, Mass.zero_le _⟩ :: tickets n xs

theorem counted {R σ : Type} (n : Nat) (f : R × σ → Mass) (xs : List (Option R × σ)) :
    embed (Weighted.total f (tickets n xs)) =
      (xs.map (fun v => embed (payoff f v))).sum / (n+1) := by
  induction xs with
  | nil => simp [tickets, Weighted.total]
  | cons pair rest ih =>
    rcases pair with ⟨_ | r, s⟩
    · simpa [tickets, payoff] using ih
    · simp [tickets, Weighted.total, payoff, ih, div_eq_mul_inv, mul_comm, mul_add]

theorem counted_slots {R σ : Type} (n : Nat) (f : R × σ → Mass)
    (slots : Fin (n+1) → Option R × σ) :
    embed (Weighted.total f (tickets n (List.ofFn slots))) =
      (∑ i, embed (payoff f (slots i))) / (n+1) := by
  rw [counted, List.map_ofFn, List.sum_ofFn]
  rfl

def finite (t : Slots S σ) : Experiment S σ where
  answer op s :=
    { tickets := tickets (t.width op s) (List.ofFn (t.answer op s))
      mass_le_one := by
        apply embed_le.mp
        rw [embed_one, counted_slots]
        let n := t.width op s
        calc
          _ ≤ (∑ _i : Fin (n+1), (1 : ℝ≥0∞)) / (n+1) := by
            gcongr with i
            rcases t.answer op s i with ⟨_ | r, s'⟩ <;> simp [payoff]
          _ = 1 := by simp [ENNReal.div_self] }

theorem finite_agrees (t : Slots S σ) : Agrees t (finite t) :=
  fun op s f => counted_slots (t.width op s) f (t.answer op s)

theorem finite_slots_probability (t : Slots S σ)
    (event : A → σ → Bool) (p : Process S H A) (s : σ) :
    prEvent (observed event <$> run (service t) p s) = embed ((finite t).probability p s event) :=
  return_probability t (finite t) (finite_agrees t) event p s

end ZkcFormal.FiniteService
