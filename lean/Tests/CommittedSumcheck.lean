import Zkc.Protocols.Sumcheck.Committed.Security
import Mathlib.Algebra.Field.ZMod

/-! Kernel-checked finite controls and a transparent reference instantiation.
The reference commitment carries its table; it is not a succinct PCS or a
cryptographic implementation. No native_decide or external prover is used.
-/

set_option autoImplicit false

namespace Tests.CommittedSumcheck

open Zkc.Polynomial Zkc.Protocols.Sumcheck Zkc.Protocols.Sumcheck.Committed
open Zkc.Probability
open AdaptiveTape (Tape)

abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def transparentScheme (n : Nat) : Scheme F n where
  Setup := Bool
  ProverKey := Bool
  VerifierKey := Bool
  Commitment := Bool × (Fin (2 ^ n) → F)
  Proof := Unit
  proverKey := id
  verifierKey := id
  commit := fun key values => (key, values)
  check := fun key commitment point value _ => decide (key = commitment.1) &&
    decide (value = Multilinear.extension n (Layout.ofLowStorage commitment.2) point)

def original : Statement (transparentScheme 1) := ⟨true, fun i => i.val, fun _ => 1⟩
def substituted : Statement (transparentScheme 1) := ⟨true, fun _ => 1, fun _ => 1⟩

/-- False claimed sum 3; q(X)=3X passes the round boundary check. Replies 1,1
are correct at the foreign point 1, but the actual challenge below is 2. -/
def foreignReplies {scheme : Scheme F 1} (proof : scheme.Proof) : Adversary scheme Unit where
  send := fun _ => (⟨0, 3, 0⟩, ())
  react := fun _ _ => ()
  openLeft := fun _ _ => (⟨1, proof⟩, ())
  openRight := fun _ _ _ => ⟨1, proof⟩

def check {n : Nat} {scheme : Scheme F n} {S : Type} (statement : Statement scheme)
    (adversary : Adversary scheme S) (claim : F) (state : S) (coins : Tape F n) : Bool :=
  (run statement adversary claim state coins).any (fun terminal => terminal.accepts statement)

theorem accepted_iff_check {n : Nat} {scheme : Scheme F n} {S : Type}
    (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (state : S) (coins : Tape F n) :
    Accepted statement adversary claim state coins ↔ check statement adversary claim state coins = true := by
  cases result : run statement adversary claim state coins <;> simp [Accepted, check, result]

theorem foreign_opening_rejected_at_actual_point :
    check original (foreignReplies ()) 3 () (2, ()) = false := by
  decide +kernel

/-- The failed left opening leaves the actual point 2 and claim 1 intact and
does not issue the second query. Correctness is not required to reach this state. -/
theorem arbitrary_reply_does_not_rewrite_query :
    (run original (foreignReplies ()) 3 () (2, ())).map
      (fun terminal => (terminal.query.point 0, terminal.query.claim, terminal.right.isNone)) =
        some (2, 1, true) := by
  decide +kernel

def wrongRight {scheme : Scheme F 1} (proof : scheme.Proof) : Adversary scheme Unit :=
  { foreignReplies proof with
    openLeft := fun _ _ => (⟨2, proof⟩, ())
    openRight := fun _ _ left => ⟨left.value, proof⟩ }

theorem second_opening_failure :
    check original (wrongRight ()) 3 () (2, ()) = false ∧
    (run original (wrongRight ()) 3 () (2, ())).map (fun terminal =>
      (leftCheck original terminal.query terminal.left,
        terminal.right.map (rightCheck original terminal.query))) = some (true, some false) := by
  decide +kernel

def foreignTerminal : Terminal (transparentScheme 1) :=
  ⟨⟨fun _ => 1, 1⟩, ⟨1, ()⟩, some ⟨1, ()⟩⟩

/-- A foreign query would satisfy the opening/product checks, while the actual
direct source rejects on the same malicious rounds and the actual tape. -/
theorem foreign_query_is_a_counterexample :
    foreignTerminal.accepts original = true ∧
    (Execution.run (foreignReplies (scheme := transparentScheme 1) ()).send
      (foreignReplies (scheme := transparentScheme 1) ()).react original.polynomial 3 ()
      (tapeList 1 (2, ()))).outcome = .returned false := by
  decide +kernel

def actualTerminal : Terminal (transparentScheme 1) :=
  ⟨⟨fun _ => 2, 1⟩, ⟨1, ()⟩, some ⟨1, ()⟩⟩

/-- Even keeping the point fixed does not justify substituting originals. -/
theorem original_substitution_is_a_counterexample :
    actualTerminal.accepts substituted = true ∧ actualTerminal.accepts original = false ∧
      original.polynomial.eval (fun _ => 2) = 2 ∧ substituted.polynomial.eval (fun _ => 2) = 1 := by
  decide +kernel

/-- An intentionally unsound checker makes the excluded bad-opening event
observable. Honest computation of commitments alone is insufficient. -/
def permissiveScheme : Scheme F 1 := { transparentScheme 1 with check := fun _ _ _ _ _ => true }
def permissiveOriginal : Statement permissiveScheme := ⟨true, fun i => i.val, fun _ => 1⟩

theorem false_opening_can_make_false_sum_accept :
    check permissiveOriginal (foreignReplies ()) 3 () (2, ()) = true ∧
      permissiveOriginal.polynomial.booleanSum ≠ 3 := by
  decide +kernel

theorem accepted_false_opening_is_in_joint_event :
    BadOpening permissiveOriginal (foreignReplies ()) 3 () (2, ()) := by
  refine ⟨_, rfl, ?_⟩
  exact ⟨by decide +kernel, Or.inl (by decide +kernel)⟩

/-- Correlated replies can make only the second accepted opening false. -/
theorem second_false_opening_is_in_joint_event :
    BadOpening permissiveOriginal (wrongRight ()) 3 () (2, ()) := by
  refine ⟨_, rfl, ?_⟩
  refine ⟨by decide +kernel, Or.inr ⟨_, rfl, ?_, ?_⟩⟩ <;> decide +kernel

def adaptiveScheme : Scheme F 2 := { transparentScheme 2 with check := fun _ _ _ _ _ => true }
def adaptiveStatement : Statement adaptiveScheme := ⟨true, fun _ => 0, fun _ => 1⟩

/-- Later rounds depend on the previous challenge; opening replies use the
actual terminal private state. Nothing restricts them to honest evaluations. -/
def adaptiveAdversary : Adversary adaptiveScheme F where
  send := fun state => (⟨0, state, 0⟩, state)
  react := fun _ challenge => challenge
  openLeft := fun state _ => (⟨state, ()⟩, state)
  openRight := fun _ _ left => ⟨left.value - 3, ()⟩

theorem adaptive_state_and_same_query :
    (run adaptiveStatement adaptiveAdversary 1 1 (3, 4, ())).map
      (fun terminal => (terminal.query.point 0, terminal.query.point 1,
        terminal.query.claim, terminal.left.value, terminal.right.map Reply.value)) =
          some (3, 4, 2, 4, some 1) := by
  decide +kernel

/-- The opening assumption is strictly separate from final acceptance: this
adaptive run has a checked false opening, but fails the product equality. -/
theorem joint_bad_event_does_not_require_terminal_acceptance :
    BadOpening adaptiveStatement adaptiveAdversary 1 1 (3, 4, ()) ∧
      check adaptiveStatement adaptiveAdversary 1 1 (3, 4, ()) = false := by
  constructor
  · refine ⟨_, rfl, ?_⟩
    exact ⟨by decide +kernel, Or.inl (by decide +kernel)⟩
  · decide +kernel

def prefixAdversary : Adversary (transparentScheme 2) Nat where
  send := fun state => (if state = 0 then ⟨0, 1, 0⟩ else ⟨0, 0, 0⟩, state + 1)
  react := fun state _ => state
  openLeft := fun state _ => (⟨0, ()⟩, state + 100)
  openRight := fun _ _ _ => ⟨0, ()⟩

def prefixStatement : Statement (transparentScheme 2) := ⟨true, fun _ => 0, fun _ => 1⟩

theorem first_failure_retains_prefix :
    (roundExecution prefixAdversary 2 0 (3, 4, ())).state = (1, [3, 4]) ∧
    (roundExecution prefixAdversary 2 0 (3, 4, ())).events =
      [.message ⟨0, 1, 0⟩, .reject] ∧
    (run prefixStatement prefixAdversary 2 0 (3, 4, ())).isNone = true := by
  decide +kernel

theorem later_failure_retains_only_consumed_challenge :
    (roundExecution prefixAdversary 1 0 (3, 4, ())).state = (2, [4]) ∧
    (roundExecution prefixAdversary 1 0 (3, 4, ())).events =
      [.message ⟨0, 1, 0⟩, .challenge 3, .message ⟨0, 0, 0⟩, .reject] ∧
    (run prefixStatement prefixAdversary 1 0 (3, 4, ())).isNone = true := by
  decide +kernel

def constantStatement : Statement (transparentScheme 0) := ⟨true, fun _ => 2, fun _ => 3⟩
def constantAdversary : Adversary (transparentScheme 0) Unit where
  send := fun _ => (⟨0, 0, 0⟩, ())
  react := fun _ _ => ()
  openLeft := fun _ _ => (⟨2, ()⟩, ())
  openRight := fun _ _ _ => ⟨3, ()⟩

theorem zero_arity_math_case :
    check constantStatement constantAdversary 1 () () = true ∧
    check constantStatement constantAdversary 0 () () = false ∧
      (roundExecution constantAdversary 1 () ()).events = [] := by
  decide +kernel

def honestReference {n : Nat} (statement : Statement (transparentScheme n)) :
    Adversary (transparentScheme n) (Security.HonestState F) where
  send := Security.honestSend
  react := Security.honestReact
  openLeft := fun state query => (⟨statement.leftValue query.point, ()⟩, state)
  openRight := fun _ query _ => ⟨statement.rightValue query.point, ()⟩

theorem honest_acceptance_includes_nonboolean_challenges :
    ∀ r : F, check original (honestReference original) 1 ⟨1, original.polynomial⟩ (r, ()) = true := by
  decide +kernel

def zeroOriginal : Statement (transparentScheme 1) := ⟨true, fun _ => 0, fun _ => 1⟩
def twoRootAdversary : Adversary (transparentScheme 1) Unit where
  send := fun _ => (⟨1, 0, 1⟩, ())
  react := fun _ _ => ()
  openLeft := fun _ _ => (⟨0, ()⟩, ())
  openRight := fun _ _ _ => ⟨1, ()⟩

/-- A false sum actually attains the ordinary 2/5 loss with correct openings.
This exercises the committed event probability, not only pointwise acceptance. -/
theorem tight_committed_probability :
    acceptanceProbability zeroOriginal twoRootAdversary 3 () = (2 : ℚ) / 5 := by
  classical
  have event (coins : Tape F 1) :
      (if Accepted zeroOriginal twoRootAdversary 3 () coins then (1 : ℚ) else 0) =
        (if check zeroOriginal twoRootAdversary 3 () coins = true then (1 : ℚ) else 0) := by
    by_cases accepted : Accepted zeroOriginal twoRootAdversary 3 () coins
    · rw [if_pos accepted, if_pos ((accepted_iff_check _ _ _ _ _).mp accepted)]
    · rw [if_neg accepted, if_neg (fun passed => accepted ((accepted_iff_check _ _ _ _ _).mpr passed))]
  unfold acceptanceProbability probability
  rw [show (fun coins : Tape F 1 => if Accepted zeroOriginal twoRootAdversary 3 () coins then (1 : ℚ) else 0) =
    (fun coins => if check zeroOriginal twoRootAdversary 3 () coins = true then (1 : ℚ) else 0) from funext event]
  simp only [UniformTape.average]
  change (∑ r : F, (if check zeroOriginal twoRootAdversary 3 () (r, ()) = true then (1 : ℚ) else 0)) / 5 = 2 / 5
  rw [show (Finset.univ : Finset F) = {0, 1, 2, 3, 4} by decide +kernel]
  simp (disch := decide +kernel) only [Finset.sum_insert, Finset.sum_singleton]
  simp (disch := decide +kernel) only [if_pos, if_neg]
  norm_num

/-- This ideal reference supplies a nonvacuous zero-loss instantiation for
every hostile strategy, not just the displayed finite transcripts. -/
theorem transparent_no_bad {n : Nat} (statement : Statement (transparentScheme n))
    (terminal : Terminal (transparentScheme n)) : ¬ terminal.badOpening statement := by
  intro ⟨leftPass, wrong⟩
  have leftCorrect : terminal.left.value = statement.leftValue terminal.query.point := by
    simpa [leftCheck, transparentScheme, Statement.leftCommitment, Statement.leftValue,
      Layout.extension_eq] using leftPass
  rcases wrong with leftWrong | ⟨right, _, rightPass, rightWrong⟩
  · exact leftWrong leftCorrect
  · apply rightWrong
    simpa [rightCheck, transparentScheme, Statement.rightCommitment, Statement.rightValue,
      Layout.extension_eq] using rightPass

theorem transparent_zero_loss {n : Nat} {S : Type} (statement : Statement (transparentScheme n))
    (adversary : Adversary (transparentScheme n) S) (claim : F) (state : S) :
    badOpeningProbability statement adversary claim state = 0 := by
  have never (coins : Tape F n) : ¬ BadOpening statement adversary claim state coins := by
    rintro ⟨terminal, _, bad⟩
    exact transparent_no_bad statement terminal bad
  simp [badOpeningProbability, probability, never, UniformTape.constant]

theorem transparent_soundness {n : Nat} {S : Type} (statement : Statement (transparentScheme n))
    (adversary : Adversary (transparentScheme n) S) (claim : F) (state : S)
    (falseClaim : claim ≠ statement.polynomial.booleanSum) :
    acceptanceProbability statement adversary claim state ≤ (2 * (n : ℚ)) / 5 := by
  have bound := Committed.soundness statement adversary claim state 0 falseClaim
    (le_of_eq (transparent_zero_loss statement adversary claim state))
  simpa using bound

end Tests.CommittedSumcheck
