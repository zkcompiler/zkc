module

public import Zkc.Tools.Protocol.Readings
public import Zkc.Protocol.Logic.Transcript.Interactive
public import Zkc.Protocol.Library.Mathematics.Algebra.Polynomial

/-! A setup-shaped verifier under the charged reading, with the interactive endpoint.

The verifier is a polynomial-commitment opening in its ideal algebraic interpretation. The prover's
message is the representation of its two group elements over the reference string: coefficient
vectors of a commitment `C` and an opening proof `π` of degree at most `n`. The setup secret `τ`
is the single uniform draw and the only challenge site. The verifier decides the exponent equation
`C(τ) − y = π(τ) · (τ − z)` and returns the message with the decision.

If `C(z) ≠ y`, the polynomial `C − y − π · (X − z)` is nonzero and has degree at most `n + 1`, so
at most `n + 1` secrets satisfy the check: the site is charged `(n + 1) / |F|`. A secret setup
value is not a random-oracle answer, so the endpoint is the interactive experiment, in which the
strategy fixes its message before the secret is drawn and receives no reference string. The
group, pairing and the reduction from the group game to this ideal game are not modelled here. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Transcript Std.WP ProtocolProof
open OracleComp OracleSpec ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open ZkcSecurity.FiatShamir.Typed ZkcSecurity.Interactive
open scoped ENNReal

namespace ProtocolProofExamples.SetupOpening

variable {F : Type} [Field F] {n : ℕ}

/-- The representation of a group element over the reference string `(τ⁰, …, τⁿ)`: the
coefficient vector of a polynomial of degree at most `n`. -/
abbrev Coeffs (F : Type) (n : ℕ) := Fin (n + 1) → F

/-- The proof message: the representations of the commitment and of the opening proof. -/
abbrev Opening (F : Type) (n : ℕ) := Coeffs F n × Coeffs F n

/-- The value of the represented polynomial at a point. -/
def evalAt (coeffs : Coeffs F n) (point : F) : F := ∑ index, coeffs index * point ^ (index : ℕ)

/-- The represented polynomial. -/
noncomputable def toPoly (coeffs : Coeffs F n) : Polynomial F :=
  ∑ index, Polynomial.C (coeffs index) * Polynomial.X ^ (index : ℕ)

theorem eval_toPoly (coeffs : Coeffs F n) (point : F) :
    (toPoly coeffs).eval point = evalAt coeffs point := by
  simp [toPoly, evalAt, Polynomial.eval_finsetSum]

theorem natDegree_toPoly_le (coeffs : Coeffs F n) : (toPoly coeffs).natDegree ≤ n :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun index _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ index.isLt)

inductive Ev (F : Type) (n : ℕ) where
  | opening (commitment proof : Coeffs F n)
  | setup

inductive VOp where
  | recv | draw

abbrev VSig (F : Type) (n : ℕ) : Signature := ⟨VOp, fun | .recv => Opening F n | .draw => F⟩

/-- The receive absorbs the representations; the setup secret is the only query site. -/
def absorb : Interface (VSig F n) (Ev F n) (Opening F n) (fun _ => F) := fun op =>
  match op with
  | .recv => .receive (fun message => Ev.opening message.1 message.2)
      (fun event => match event with
        | .opening commitment proof => some (commitment, proof)
        | .setup => none)
  | .draw => .query Ev.setup (fun raw => some raw)

inductive Ty where
  | msg | secret | out
  deriving DecidableEq

inductive Op where
  | recv | draw | decide

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .recv | .draw => []
    | .decide => [.msg, .secret]
  result
    | .recv => .msg
    | .draw => .secret
    | .decide => .out
  condition := .secret

variable [DecidableEq F]

abbrev meaning (z y : F) : Interpretation language (VSig F n) where
  Value
    | .msg => Opening F n
    | .secret => F
    | .out => Opening F n × Bool
  condition := fun secret => secret = 0
  operation
    | .recv, .nil => .call .recv .done
    | .draw, .nil => .call .draw .done
    | .decide, .cons message (.cons secret .nil) =>
        .done (message,
          decide (evalAt message.1 secret - y = evalAt message.2 secret * (secret - z)))

/-- Receive the representations, draw the setup secret, decide the exponent equation. -/
def verifier : Region (scalarDialect language) [] [.out] :=
  .letOp (.ordinary .recv) .nil .nil
    (.letOp (.ordinary .draw) .nil .nil
      (.letOp (.ordinary .decide) (.cons (.there .here) (.cons .here .nil)) .nil
        (.ret (.cons .here .nil))))

/-- The verifier process itself; nothing is replaced by a model. -/
def game (z y : F) : Process (VSig F n) (Opening F n × Bool) :=
  (verifier.denote (meaning z y).regionMeaning Values.nil.get).bind
    fun out => .done (out.get .here)

section Rules
variable (z y : F)

@[spec] theorem recv_rule : (meaning (n := n) z y).operation .recv .nil = .call .recv .done := rfl

@[spec] theorem draw_rule : (meaning (n := n) z y).operation .draw .nil = .call .draw .done := rfl

@[spec] theorem decide_rule (message : Opening F n) (secret : F) :
    (meaning z y).operation .decide (.cons message (.cons secret .nil)) =
      .done (message,
        decide (evalAt message.1 secret - y = evalAt message.2 secret * (secret - z))) := rfl

end Rules

attribute [local construction_simp] absorb

omit [DecidableEq F] in
/-- The check is satisfiable: a true statement has an opening proof that passes the exponent
equation at every secret, the quotient by `X − z`. This is a sanity check on the model. -/
theorem honest_proof_exists (z y : F) (commitment : Coeffs F n)
    (correct : evalAt commitment z = y) :
    ∃ proof : Coeffs F n, ∀ secret : F,
      evalAt commitment secret - y = evalAt proof secret * (secret - z) := by
  have root : (toPoly commitment - Polynomial.C y).IsRoot z := by
    simp [Polynomial.IsRoot, eval_toPoly, correct]
  obtain ⟨quotient, factored⟩ := Polynomial.dvd_iff_isRoot.mpr root
  have small : quotient.natDegree < n + 1 := by
    by_cases zero : quotient = 0
    · simp [zero]
    · have degree : (toPoly commitment - Polynomial.C y).natDegree ≤ n :=
        (Polynomial.natDegree_sub_le _ _).trans
          (max_le (natDegree_toPoly_le commitment) (by simp))
      rw [factored, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero z) zero,
        Polynomial.natDegree_X_sub_C] at degree
      omega
  refine ⟨fun index => quotient.coeff index, fun secret => ?_⟩
  have value : evalAt (fun index : Fin (n + 1) => quotient.coeff index) secret =
      quotient.eval secret := by
    rw [Polynomial.eval_eq_sum_range' small, evalAt,
      Fin.sum_univ_eq_sum_range (fun index => quotient.coeff index * secret ^ index)]
  have atSecret := congrArg (Polynomial.eval secret) factored
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    eval_toPoly] at atSecret
  rw [value, atSecret]
  ring

variable [Fintype F] [SampleableType F]

/-- A representation of a polynomial whose value at `z` is not `y` passes the exponent equation
at no more than `n + 1` setup secrets. -/
theorem escape_le (z y : F) (commitment proof : Coeffs F n) (wrong : evalAt commitment z ≠ y) :
    Pr{let secret ← $ᵗ F}[
      evalAt commitment secret - y = evalAt proof secret * (secret - z)] ≤
      (n + 1 : ℝ≥0∞) / Fintype.card F := by
  let check : Polynomial F :=
    toPoly commitment - Polynomial.C y - toPoly proof * (Polynomial.X - Polynomial.C z)
  have nonzero : check ≠ 0 := by
    intro zero
    have atPoint := congrArg (Polynomial.eval z) zero
    simp only [check, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_zero, eval_toPoly, sub_self, mul_zero, sub_zero]
      at atPoint
    exact wrong (sub_eq_zero.mp atPoint)
  have degree : check.natDegree ≤ n + 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      exact (natDegree_toPoly_le commitment).trans (Nat.le_succ n)
    · refine Polynomial.natDegree_mul_le.trans ?_
      exact add_le_add (natDegree_toPoly_le proof) (Polynomial.natDegree_X_sub_C_le z)
  have bound := ZkcSecurity.Algebra.Polynomial.root_uniform_le check nonzero degree
  have same : Pr{let secret ← $ᵗ F}[
        evalAt commitment secret - y = evalAt proof secret * (secret - z)] =
      Pr{let secret ← $ᵗ F}[check.eval secret = 0] := by
    refine prEvent_congr ($ᵗ F) _ _ fun secret => ?_
    simp only [check, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, eval_toPoly]
    exact sub_eq_zero.symm
  rw [same]
  simpa using bound

/-- The setup site is charged `(n + 1) / |F|`. -/
noncomputable abbrev charge : List (Ev F n) → Ev F n → ℝ≥0∞ :=
  fun _ _ => (n + 1 : ℝ≥0∞) / Fintype.card F

section Soundness

noncomputable abbrev logic :
    WPMonad (Process (VSig F n)) (Assert (Ev F n)) (StopAssert (Ev F n)) :=
  chargedMonad absorb (boundedEscape charge) (boundedEscape_antitone charge)

attribute [local instance] logic

/-- An accepting run returns a representation of a polynomial whose value at `z` is `y`. -/
theorem game_binds (z y : F) :
    ⦃fun _ => ⟨True⟩⦄ game (n := n) z y
    ⦃fun out _ => ⟨out.2 = true → evalAt out.1.1 z = y⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold game verifier
  construct_region
  -- The one remaining obligation is the mathematics of the setup site.
  intro message value recovered
  obtain rfl : (message.1, message.2) = value := Option.some.inj recovered
  by_cases known : evalAt message.1 z = y
  · -- The statement already holds: no setup secret is excluded.
    refine (prEvent_mono _ _ (fun _ => False) fun raw escaped => ?_).trans (by simp)
    obtain ⟨reply, decoded, outside⟩ := escaped
    exact outside fun _ => known
  · refine (prEvent_mono _ _ _ fun raw escaped => ?_).trans
      (escape_le z y message.1 message.2 known)
    obtain ⟨reply, decoded, outside⟩ := escaped
    obtain rfl : raw = reply := Option.some.inj decoded
    by_contra failed
    exact outside fun accepted => absurd (of_decide_eq_true accepted) failed

end Soundness

section Cost

noncomputable abbrev budget :
    WPMonad (Process (VSig F n)) (CostAssert (Ev F n)) (CostStopAssert (Ev F n)) :=
  costMonad absorb charge

attribute [local instance] budget

omit [SampleableType F] in
/-- The game draws once. -/
theorem game_cost (z y : F) :
    ⦃fun _ cost => ⟨(n + 1 : ℝ≥0∞) / Fintype.card F + 0 ≤ cost⟩⦄ game (n := n) z y
    ⦃fun _ _ cost => ⟨0 ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold game verifier
  construct_region
  intro budget message value _
  exact ⟨0, budget, fun _ => le_rfl⟩

end Cost

/-! ### The interactive endpoint -/

/-- The charged reading of the game, from the derived triple. -/
theorem game_charged (z y : F) :
    absorb.Charged (boundedEscape charge) (fun _ out => out.2 = true → evalAt out.1.1 z = y)
      (game (n := n) z y) [] :=
  charged_of_triple absorb (boundedEscape charge) (boundedEscape_antitone charge)
    (game_binds z y) [] trivial

omit [SampleableType F] in
/-- The pathwise cost of the game, from the derived cost triple. -/
theorem game_priced (z y : F) :
    ChargedCostBound absorb charge (game (n := n) z y) [] ((n + 1 : ℝ≥0∞) / Fintype.card F) :=
  costBound_of_triple absorb charge (game_cost z y) [] _ (by simp)

/-- **The opening check in the ideal algebraic game.** The prover's representations are fixed
before the secret is drawn, and no reference string is published: the strategy's only message is
requested at the empty view, and the secret is the run's single draw. Against every strategy, the
verifier accepts a representation of a polynomial whose value at `z` is not `y` with probability
at most `(n + 1) / |F|` over the secret. This is a root-counting bound for representations fixed
in advance, not evaluation binding of a commitment scheme with a published setup. -/
theorem setup_soundness (z y : F) (strategy : Strategy (Ev F n) (Opening F n) (fun _ => F)) :
    Pr{let result ← interact absorb strategy (game z y) [] []}[
      Accepted (fun out => out.2 = true ∧ evalAt out.1.1 z ≠ y) result.1] ≤
      (n + 1 : ℝ≥0∞) / Fintype.card F :=
  soundness_accepted (A := Opening F n × Bool) absorb strategy charge
    (fun _ out => out.2 = true → evalAt out.1.1 z = y)
    (fun out => out.2 = true ∧ evalAt out.1.1 z ≠ y)
    (fun _ _ holds bad => bad.2 (holds bad.1)) (game z y) [] (game_charged z y)
    ((n + 1 : ℝ≥0∞) / Fintype.card F) (game_priced z y)

/-- The same bound for a randomized adversary. -/
theorem setup_soundness_randomized (z y : F)
    (strategies : ProbComp (Strategy (Ev F n) (Opening F n) (fun _ => F))) :
    Pr{let result ← strategies >>= fun strategy => interact absorb strategy (game z y) [] []}[
      Accepted (fun out => out.2 = true ∧ evalAt out.1.1 z ≠ y) result.1] ≤
      (n + 1 : ℝ≥0∞) / Fintype.card F :=
  soundness_randomized (A := Opening F n × Bool) absorb charge
    (fun _ out => out.2 = true → evalAt out.1.1 z = y)
    (fun out => out.2 = true ∧ evalAt out.1.1 z ≠ y)
    (fun _ _ holds bad => bad.2 (holds bad.1)) (game z y) [] (game_charged z y)
    ((n + 1 : ℝ≥0∞) / Fintype.card F) (game_priced z y) strategies

omit [Fintype F] in
/-- The run of the game: the strategy fixes the representations at the empty view, then the
secret is drawn and the exponent equation is decided. -/
theorem interact_game (z y : F) (strategy : Strategy (Ev F n) (Opening F n) (fun _ => F)) :
    interact absorb strategy (game z y) [] [] =
      ($ᵗ F) >>= fun secret =>
        pure (.returned (strategy [] [],
            decide (evalAt (strategy [] []).1 secret - y =
              evalAt (strategy [] []).2 secret * (secret - z))),
          [Ev.opening (strategy [] []).1 (strategy [] []).2, Ev.setup]) := rfl

/-- The textbook form, as an instance of the endpoint: for representations fixed before the
secret is drawn, the exponent equation holds although `C(z) ≠ y` with probability at most
`(n + 1) / |F|` over the secret alone. -/
theorem setup_soundness_fixed (z y : F) (commitment proof : Coeffs F n) :
    Pr{let secret ← $ᵗ F}[
      evalAt commitment secret - y = evalAt proof secret * (secret - z) ∧
        evalAt commitment z ≠ y] ≤ (n + 1 : ℝ≥0∞) / Fintype.card F := by
  have bound := setup_soundness z y (fun _ _ => (commitment, proof))
  rw [interact_game] at bound
  refine (le_of_eq ?_).trans bound
  simp [Accepted]

#print axioms setup_soundness
#print axioms setup_soundness_randomized
#print axioms setup_soundness_fixed

end ProtocolProofExamples.SetupOpening
