module

public import Zkc.Tools.Protocol.Readings
public import Zkc.Protocol.Logic.Transcript.Interactive
public import Zkc.Protocol.Library.Mathematics.Algebra.Polynomial

/-! A multilinear Sumcheck verifier written as a typed `Region`, under the charged and cost
readings. The verifier receives the pair of half sums, checks it against the running claim, draws
a challenge and folds; the final step compares the claim with the public reference. The program is
the object of proof. The protocol mathematics is two equations about the reference and one
root-counting lemma for the challenge site; the loop invariant is that the running claim is wrong.

One path leads from the `Region` to both endpoints: `construct_region` derives the charged and
cost triples, adequacy turns them into the existing judgments, and the retained Fiat–Shamir
theorem and the interactive theorem bound acceptance of a false claim. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Transcript Std.WP ProtocolProof
open OracleComp OracleSpec ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open ZkcSecurity.FiatShamir.Typed
open scoped ENNReal

namespace ProtocolProofExamples.ChargedSumcheck

variable {F : Type} [Field F] [DecidableEq F]

inductive Ev (F : Type) where
  | msg (low high : F)
  | chal
  deriving DecidableEq

inductive VOp where
  | recv | draw

abbrev VSig (F : Type) : Signature := ⟨VOp, fun | .recv => F × F | .draw => F⟩

/-- A round message is a proof message; the challenge is a query site. -/
def absorb : Interface (VSig F) (Ev F) (F × F) (fun _ => F) := fun op =>
  match op with
  | .recv => .receive (fun m => Ev.msg m.1 m.2)
      (fun event => match event with | .msg low high => some (low, high) | .chal => none)
  | .draw => .query Ev.chal (fun raw => some raw)

inductive Ty where
  | state | msg | chal | bit
  deriving DecidableEq

inductive Op where
  | recv | check | draw | fold | final

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .recv | .draw => []
    | .check => [.state, .msg]
    | .fold => [.state, .msg, .chal]
    | .final => [.state]
  result
    | .recv | .check => .msg
    | .draw => .chal
    | .fold => .state
    | .final => .bit
  condition := .bit

abbrev meaning (S : List F → F) : Interpretation language (VSig F) where
  Value
    | .state => List F × F
    | .msg => F × F
    | .chal => F
    | .bit => Bool
  condition := id
  operation
    | .recv, .nil => .call .recv .done
    | .draw, .nil => .call .draw .done
    | .check, .cons st (.cons m .nil) => if m.1 + m.2 = st.2 then .done m else .halt .reject
    | .fold, .cons st (.cons m (.cons r .nil)) => .done (st.1 ++ [r], (1 - r) * m.1 + r * m.2)
    | .final, .cons st .nil => .done (decide (st.2 = S st.1))

/-- Receive, check, draw, fold. -/
def round : Region (scalarDialect language) [.state] [.state] :=
  .letOp (.ordinary .recv) .nil .nil
    (.letOp (.ordinary .check) (.cons (.there .here) (.cons .here .nil)) .nil
      (.letOp (.ordinary .draw) .nil .nil
        (.letOp (.ordinary .fold)
          (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons .here .nil))) .nil
          (.ret (.cons .here .nil)))))

def rounds (count : Nat) : Region (scalarDialect language) [.state] [.state] :=
  .letOp (.repeat count [] .state) (.cons .here .nil) (.cons round .nil) (.ret (.cons .here .nil))

def verifier (count : Nat) : Region (scalarDialect language) [.state] [.bit] :=
  .bind (rounds count)
    (.letOp (.ordinary .final) (.cons .here .nil) .nil (.ret (.cons .here .nil)))

/-- The verifier process itself; nothing is replaced by a model. -/
def game (S : List F → F) (count : Nat) (start : List F × F) : Process (VSig F) Bool :=
  ((verifier count).denote (meaning S).regionMeaning (Values.singleton start).get).bind
    fun out => .done (out.get .here)

@[spec] theorem recv_rule (S : List F → F) :
    (meaning S).operation .recv .nil = .call .recv .done := rfl

@[spec] theorem draw_rule (S : List F → F) :
    (meaning S).operation .draw .nil = .call .draw .done := rfl

@[spec] theorem check_rule (S : List F → F) (st : List F × F) (m : F × F) :
    (meaning S).operation .check (.cons st (.cons m .nil)) =
      if m.1 + m.2 = st.2 then .done m else .halt .reject := rfl

@[spec] theorem fold_rule (S : List F → F) (st : List F × F) (m : F × F) (r : F) :
    (meaning S).operation .fold (.cons st (.cons m (.cons r .nil))) =
      .done (st.1 ++ [r], (1 - r) * m.1 + r * m.2) := rfl

@[spec] theorem final_rule (S : List F → F) (st : List F × F) :
    (meaning S).operation .final (.cons st .nil) = .done (decide (st.2 = S st.1)) := rfl

attribute [local construction_simp] absorb

variable [Fintype F] [SampleableType F]

/-! ### The mathematics -/

/-- Multilinearity of the public reference in the next variable. -/
structure Laws (S : List F → F) : Prop where
  split : ∀ pt, S pt = S (pt ++ [0]) + S (pt ++ [1])
  line : ∀ pt r, S (pt ++ [r]) = (1 - r) * S (pt ++ [0]) + r * S (pt ++ [1])

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The line through a checked pair for a false claim differs from the reference line. -/
theorem lines_differ {S : List F → F} (laws : Laws S) (pt : List F) (claim low high : F)
    (wrong : claim ≠ S pt) (checked : low + high = claim) :
    Polynomial.C low + Polynomial.X * Polynomial.C (high - low) ≠
      Polynomial.C (S (pt ++ [0])) + Polynomial.X * Polynomial.C (S (pt ++ [1]) - S (pt ++ [0])) := by
  intro same
  have at0 := congrArg (Polynomial.eval 0) same
  have at1 := congrArg (Polynomial.eval 1) same
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, zero_mul, add_zero, one_mul] at at0 at1
  apply wrong
  rw [← checked, laws.split pt, at0]
  have : high = S (pt ++ [1]) := by
    rw [at0] at at1
    linear_combination at1
  rw [this]

/-- A checked pair for a false claim agrees with the reference at one challenge at most. -/
theorem escape_le {S : List F → F} (laws : Laws S) (pt : List F) (claim low high : F)
    (wrong : claim ≠ S pt) (checked : low + high = claim) :
    Pr{let r ← $ᵗ F}[(1 - r) * low + r * high = S (pt ++ [r])] ≤ 1 / Fintype.card F := by
  let p : Polynomial F := Polynomial.C low + Polynomial.X * Polynomial.C (high - low)
  let q : Polynomial F :=
    Polynomial.C (S (pt ++ [0])) + Polynomial.X * Polynomial.C (S (pt ++ [1]) - S (pt ++ [0]))
  have degP : p.natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_mul_C_le _ _).trans Polynomial.natDegree_X_le
  have degQ : q.natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_mul_C_le _ _).trans Polynomial.natDegree_X_le
  have bound := ZkcSecurity.Algebra.Polynomial.agreement_uniform_le p q
    (lines_differ laws pt claim low high wrong checked) degP degQ
  have same : Pr{let r ← $ᵗ F}[(1 - r) * low + r * high = S (pt ++ [r])] =
      Pr{let r ← $ᵗ F}[p.eval r = q.eval r] := by
    refine prEvent_congr ($ᵗ F) _ _ fun r => ?_
    simp only [p, q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    rw [laws.line pt r]
    constructor <;> intro h <;> linear_combination h
  rw [same]
  simpa using bound

/-- Every challenge site is charged `1 / |F|`. -/
noncomputable abbrev charge : List (Ev F) → Ev F → ℝ≥0∞ := fun _ _ => 1 / Fintype.card F

/-! ### The charged triple, by the common constructor -/

section Soundness

/-- The charged reading at the bounded judgment. -/
noncomputable abbrev logic : WPMonad (Process (VSig F)) (Assert (Ev F)) (StopAssert (Ev F)) :=
  chargedMonad absorb (boundedEscape charge) (boundedEscape_antitone charge)

attribute [local instance] logic

/-- The doomed assertion: the running claim differs from the reference. -/
abbrev Wrong (S : List F → F) (st : List F × F) : Assert (Ev F) := fun _ => ⟨st.2 ≠ S st.1⟩

@[spec high] theorem round_wrong {S : List F → F} (laws : Laws S)
    (env : Environment (meaning S).Value [.state]) :
    ⦃Wrong S (env .here)⦄
      round.denote (meaning S).regionMeaning env
    ⦃fun out => Wrong S (out.get .here); estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold round
  construct_region
  -- The one remaining obligation is the mathematics of the challenge site.
  intro wrong message value recovered
  obtain rfl : (message.1, message.2) = value := Option.some.inj recovered
  split
  · rename_i checked
    refine (prEvent_mono _ _ _ fun raw escaped => ?_).trans
      (escape_le laws (env .here).1 (env .here).2 message.1 message.2 wrong checked)
    obtain ⟨reply, decoded, outside⟩ := escaped
    obtain rfl : raw = reply := Option.some.inj decoded
    exact not_not.mp outside
  · trivial

@[spec high] theorem rounds_wrong {S : List F → F} (laws : Laws S) (count : Nat)
    (env : Environment (meaning S).Value [.state]) :
    ⦃Wrong S (env .here)⦄
      (rounds count).denote (meaning S).regionMeaning env
    ⦃fun out => Wrong S (out.get .here); estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold rounds
  construct_region with_invariants [fun _ st => Wrong S st]

/-- A verifier started on a false claim never returns `true`. -/
@[spec high] theorem verifier_rejects {S : List F → F} (laws : Laws S) (count : Nat)
    (env : Environment (meaning S).Value [.state]) :
    ⦃Wrong S (env .here)⦄
      (verifier count).denote (meaning S).regionMeaning env
    ⦃fun out _ => ⟨out.get .here = false⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold verifier
  construct_region
  intro _ _
  rfl

theorem game_rejects {S : List F → F} (laws : Laws S) (count : Nat) (start : List F × F) :
    ⦃Wrong S start⦄ game S count start
    ⦃fun out _ => ⟨out = false⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold game
  construct_region

end Soundness

/-! ### The cost triple of the same program -/

section Cost

noncomputable abbrev budget : WPMonad (Process (VSig F)) (CostAssert (Ev F)) (CostStopAssert (Ev F)) :=
  costMonad absorb charge

attribute [local instance] budget

omit [SampleableType F] in
@[spec high] theorem round_cost (S : List F → F) (rest : ℝ≥0∞)
    (env : Environment (meaning S).Value [.state]) :
    ⦃fun _ cost => ⟨1 / (Fintype.card F : ℝ≥0∞) + rest ≤ cost⟩⦄
      round.denote (meaning S).regionMeaning env
    ⦃fun _ _ cost => ⟨rest ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold round
  construct_region
  intro budget message value _
  split
  · exact ⟨rest, budget, fun _ => le_rfl⟩
  · trivial

omit [SampleableType F] in
@[spec high] theorem rounds_cost (S : List F → F) (count : Nat) (rest : ℝ≥0∞)
    (env : Environment (meaning S).Value [.state]) :
    ⦃fun _ cost => ⟨count * (1 / (Fintype.card F : ℝ≥0∞)) + rest ≤ cost⟩⦄
      (rounds count).denote (meaning S).regionMeaning env
    ⦃fun _ _ cost => ⟨rest ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold rounds
  construct_region with_invariants [fun remaining _ => fun _ cost =>
    ⟨remaining * (1 / (Fintype.card F : ℝ≥0∞)) + rest ≤ cost⟩]
  · intro budget
    refine le_trans (le_of_eq ?_) budget
    push_cast
    ring
  · intro _ cost budget
    simpa using budget

omit [SampleableType F] in
@[spec high] theorem verifier_cost (S : List F → F) (count : Nat)
    (env : Environment (meaning S).Value [.state]) :
    ⦃fun _ cost => ⟨count * (1 / (Fintype.card F : ℝ≥0∞)) + 0 ≤ cost⟩⦄
      (verifier count).denote (meaning S).regionMeaning env
    ⦃fun _ _ cost => ⟨0 ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold verifier
  construct_region

omit [SampleableType F] in
theorem game_cost (S : List F → F) (count : Nat) (start : List F × F) :
    ⦃fun _ cost => ⟨count * (1 / (Fintype.card F : ℝ≥0∞)) + 0 ≤ cost⟩⦄
      game S count start
    ⦃fun _ _ cost => ⟨0 ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold game
  construct_region

end Cost

/-! ### The endpoints

The two triples are the only protocol-specific inputs. Adequacy turns them into the existing
judgments; the random-oracle experiment and its bound are the retained
`ZkcSecurity.FiatShamir.Typed.soundness_charged`, and the interactive experiment and its bound are
`ZkcSecurity.Interactive.soundness_accepted`. -/

/-- The charged reading of the game on a false claim, from the derived triple. -/
theorem game_charged {S : List F → F} (laws : Laws S) (count : Nat) (start : List F × F)
    (wrong : start.2 ≠ S start.1) :
    absorb.Charged (boundedEscape charge) (fun _ out => out = false) (game S count start) [] :=
  charged_of_triple absorb (boundedEscape charge) (boundedEscape_antitone charge)
    (game_rejects laws count start) [] wrong

omit [SampleableType F] in
/-- The pathwise cost of the game, from the derived cost triple. -/
theorem game_priced (S : List F → F) (count : Nat) (start : List F × F) :
    ChargedCostBound absorb charge (game S count start) [] (count * (1 / (Fintype.card F : ℝ≥0∞))) :=
  costBound_of_triple absorb charge (game_cost S count start) [] _ (by simp)

/-- The Fiat–Shamir transform of the `Region` verifier, run on a proof produced by any prover
with at most `queries` random-oracle queries, accepts a false claim with probability at most
`(queries + count) / |F|`. -/
theorem fiat_shamir_soundness {S : List F → F} (laws : Laws S) (count : Nat)
    (start : List F × F) (wrong : start.2 ≠ S start.1)
    (prover : OracleComp (OracleSpec.ofFn fun _ : List (Ev F) => F) (List (F × F)))
    (queries : Nat) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (fixedExperiment absorb (game S count start) [] prover)).run' ∅}[
      Accepted (· = true) result.1] ≤
      (queries + count) * (1 / (Fintype.card F : ℝ≥0∞)) := by
  have bound := soundness_charged
    (certificate (absorb := absorb) (charge := charge) (· = true)
      (Post := fun _ out => out = false) (by intro _ value rejects; simp [rejects]))
    (game S count start) [] (certificate_doomed.mpr (game_charged laws count start wrong)) _
    (game_priced S count start) prover (queries * (1 / (Fintype.card F : ℝ≥0∞)))
    (worstCaseCostBound_of_isTotalQueryBound _
      (keyCharge_le (fun _ _ => le_rfl)) prover queries proverBound)
  simpa [add_mul] using bound

/-- Interactive soundness of the same verifier against a prover that sees every earlier
challenge: a false claim is accepted with probability at most `count / |F|`. -/
theorem interactive_soundness {S : List F → F} (laws : Laws S) (count : Nat)
    (start : List F × F) (wrong : start.2 ≠ S start.1)
    (strategy : ZkcSecurity.Interactive.Strategy (Ev F) (F × F) (fun _ => F)) :
    Pr{let result ← ZkcSecurity.Interactive.interact absorb strategy (game S count start) [] []}[
      Accepted (· = true) result.1] ≤ count * (1 / (Fintype.card F : ℝ≥0∞)) :=
  ZkcSecurity.Interactive.soundness_accepted absorb strategy charge (fun _ out => out = false)
    (· = true) (by intro _ value rejects; simp [rejects]) (game S count start) []
    (game_charged laws count start wrong) _ (game_priced S count start)

#print axioms fiat_shamir_soundness
#print axioms interactive_soundness

end ProtocolProofExamples.ChargedSumcheck
