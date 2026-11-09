module

public import ProtocolProof.Claims.Assembly

/-!
# A complete frozen-oracle proximity experiment

The environment fixes a two-cell table and a claimed constant codeword before any sample.
Every query samples a fresh index, records it, and compares that fixed cell with the claim.
Both whole-game soundness and honest completeness use the common Process contracts and
root assembly. This is a finite proximity model, not an FRI implementation.
-/

public section
noncomputable section
open PIR ProtocolProof MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProtocolProofExamples.OracleProximity
abbrev Sampling : Signature := ⟨Unit, fun _ ↦ Bool⟩

def half : ℝ≥0∞ := 1 / 2
private theorem halves : half + half = 1 := ENNReal.add_halves 1

structure Environment where
  first : Bool
  second : Bool
  claim : Bool
  deriving DecidableEq, Fintype

def cell (e : Environment) (index : Bool) : Bool := if index then e.second else e.first

def agreesAt (e : Environment) (index : Bool) : Bool := cell e index == e.claim

def good (e : Environment) : Prop := e.first = e.claim ∧ e.second = e.claim

def weight (accepted : Bool) (value : ℝ≥0∞) : ℝ≥0∞ := if accepted then value else 0

def reward (value : ℝ≥0∞) (outcome : Outcome Bool) (_state : Unit × List Bool) : ℝ≥0∞ :=
  match outcome with
  | .returned accepted => weight accepted value
  | .stopped _ => 0

def agreement (e : Environment) : ℝ≥0∞ :=
  half * weight (agreesAt e false) 1 + half * weight (agreesAt e true) 1

noncomputable def system : System Environment Sampling Unit Bool where
  operations _ _ := Kernel.const Unit
    (half • Measure.dirac ((⟨.returned false, (), [false]⟩ : Execution Unit Bool Bool)) +
      half • Measure.dirac ((⟨.returned true, (), [true]⟩ : Execution Unit Bool Bool)))
  initial _ := Measure.dirac ()
  operation_mass _ _ _ := by simpa using halves
  initial_probability _ := inferInstance

def spec : OperationSpec Sampling Unit Bool := fun _ post current ↦
  half * post (.returned false) ((), current.2 ++ [false]) +
    half * post (.returned true) ((), current.2 ++ [true])

private theorem spec_mono : spec.Monotone := by
  intro _ f g h current
  exact add_le_add (mul_le_mul_right (h _ _) half) (mul_le_mul_right (h _ _) half)

private theorem local_law (e : Environment) (op : Sampling.Op)
    (post : Outcome Bool → (Unit × List Bool) → ℝ≥0∞) (current : Unit × List Bool) :
    opExpectation (I := Sampling) (system.accumulatedOperations e) op post current = spec op post current := by
  change (∫⁻ out, post out.1 out.2 ∂system.accumulatedOperations e op current) = _
  rw [system.accumulatedOperations_apply]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [system, spec, lintegral_add_measure, lintegral_smul_measure]

/-- The table is frozen outside the random continuation. -/
def query (e : Environment) (_round : Nat) (accepted : Bool) : Process Sampling Bool :=
  (Process.call (I := Sampling) () .done).bind fun index ↦ .done (accepted && agreesAt e index)

def verifier (count : Nat) (e : Environment) : Process Sampling Bool :=
  (List.range count).foldlM (fun accepted round ↦ query e round accepted) true

private theorem step (e : Environment) (accepted : Bool) (value : ℝ≥0∞) :
    half * weight (accepted && agreesAt e false) value +
      half * weight (accepted && agreesAt e true) value =
    weight accepted (agreement e * value) := by
  cases accepted <;> cases h0 : agreesAt e false <;> cases h1 : agreesAt e true <;>
    simp [weight, agreement, h0, h1, add_mul]

private theorem query_upper (e : Environment) (round : Nat) (accepted : Bool)
    (value : ℝ≥0∞) : UpperBound spec (query e round accepted) (reward value)
      (fun _ ↦ weight accepted (agreement e * value)) := by
  apply (UpperBound.operation ()
    (fun answer current ↦ match answer with
      | .returned index => reward value (.returned (accepted && agreesAt e index)) current
      | .stopped _ => 0)
    (fun _ ↦ (step e accepted value).le)).bind spec_mono
  · intro index
    exact UpperBound.pure _ le_rfl
  · intro reason current
    exact le_rfl

private theorem query_lower (e : Environment) (round : Nat) (accepted : Bool)
    (value : ℝ≥0∞) : LowerBound spec (query e round accepted) (reward value)
      (fun _ ↦ weight accepted (agreement e * value)) := by
  apply (LowerBound.operation ()
    (fun answer current ↦ match answer with
      | .returned index => reward value (.returned (accepted && agreesAt e index)) current
      | .stopped _ => 0)
    (fun _ ↦ (step e accepted value).ge)).bind spec_mono
  · intro index
    exact LowerBound.pure _ le_rfl
  · intro reason current
    exact le_rfl

private theorem remaining (e : Environment) (count round : Nat) (h : round < count) :
    agreement e * agreement e ^ (count - (round + 1)) = agreement e ^ (count - round) := by
  have heq : count - round = count - (round + 1) + 1 := by omega
  rw [heq, pow_succ']

private theorem verifier_upper (count : Nat) (e : Environment) :
    UpperBound spec (verifier count e) (reward 1) (fun _ ↦ agreement e ^ count) := by
  change UpperBound spec (verifier count e) (reward 1)
    (reward (agreement e ^ count) (.returned true))
  simpa only [verifier, Nat.sub_self, pow_zero, Nat.sub_zero] using UpperBound.iterate spec_mono (query e)
    (fun round ↦ reward (agreement e ^ (count - round))) count
    (fun round h value ↦ by
      change UpperBound spec (query e round value)
        (reward (agreement e ^ (count - (round + 1))))
        (fun _ ↦ weight value (agreement e ^ (count - round)))
      simpa only [remaining e count round h] using
        query_upper e round value (agreement e ^ (count - (round + 1))))
    (fun _ _ _ _ ↦ le_rfl) true

private theorem verifier_lower (count : Nat) (e : Environment) :
    LowerBound spec (verifier count e) (reward 1) (fun _ ↦ agreement e ^ count) := by
  change LowerBound spec (verifier count e) (reward 1)
    (reward (agreement e ^ count) (.returned true))
  simpa only [verifier, Nat.sub_self, pow_zero, Nat.sub_zero] using LowerBound.iterate spec_mono (query e)
    (fun round ↦ reward (agreement e ^ (count - round))) count
    (fun round h value ↦ by
      change LowerBound spec (query e round value)
        (reward (agreement e ^ (count - (round + 1))))
        (fun _ ↦ weight value (agreement e ^ (count - round)))
      simpa only [remaining e count round h] using
        query_lower e round value (agreement e ^ (count - (round + 1))))
    (fun _ _ _ _ ↦ le_rfl) true

def accepting : Set (Execution Unit Bool Bool) := {out | out.outcome = .returned true}

private theorem reward_accepting (outcome : Outcome Bool) (state : Unit × List Bool) :
    accepting.indicator 1 ⟨outcome, state.1, state.2⟩ = reward 1 outcome state := by
  cases outcome with
  | stopped reason => simp [accepting, reward]
  | returned value => cases value <;> simp [accepting, reward, weight]

noncomputable def upperRequest (count : Nat) : UpperRequest Environment (Execution Unit Bool Bool) where
  experiment := system.experiment (verifier count)
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound e := agreement e ^ count

noncomputable def lowerRequest (count : Nat) : LowerRequest Environment (Execution Unit Bool Bool) where
  experiment := system.experiment (verifier count)
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound e := agreement e ^ count

private noncomputable def upperEvidence (count : Nat) :
    UpperEvidence (upperRequest count) system system (verifier count) (fun _ ↦ Eq) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := spec
  local_bound e _ op post current := (local_law e op post current).le
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ same h := by subst same; exact h
  potential e _ := agreement e ^ count
  mathematics e _ := by simpa only [reward_accepting] using verifier_upper count e
  budget _ _ := by simp [system, upperRequest, System.initialWithEvents]

private noncomputable def lowerEvidence (count : Nat) :
    LowerEvidence (lowerRequest count) system system (verifier count) (fun _ ↦ Eq) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := spec
  local_bound e _ op post current := (local_law e op post current).ge
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ same h := by subst same; exact h
  potential e _ := agreement e ^ count
  mathematics e _ := by simpa only [reward_accepting] using verifier_lower count e
  budget _ _ := by simp [system, lowerRequest, System.initialWithEvents]

/-- Exact acceptance mass for every finite query count and every fixed table. -/
theorem acceptance (count : Nat) (e : Environment) :
    (system.experiment (verifier count)).run e accepting = agreement e ^ count :=
  le_antisymm ((upperEvidence count).establish e trivial)
    ((lowerEvidence count).establish e trivial)

private theorem agreement_good (e : Environment) (h : good e) : agreement e = 1 := by
  rcases e with ⟨first, second, claim⟩
  cases first <;> cases second <;> cases claim <;>
    simp_all [good, agreement, agreesAt, cell, weight, halves]

private theorem agreement_bad (e : Environment) (h : ¬good e) : agreement e ≤ half := by
  rcases e with ⟨first, second, claim⟩
  cases first <;> cases second <;> cases claim <;>
    simp_all [good, agreement, agreesAt, cell, weight]

/-- Honest completeness and proximity soundness use the same exact execution theorem. -/
theorem honest_completeness (count : Nat) (e : Environment) (h : good e) :
    (system.experiment (verifier count)).run e accepting = 1 := by
  rw [acceptance, agreement_good e h, one_pow]

theorem proximity_soundness (count : Nat) (e : Environment) (h : ¬good e) :
    (system.experiment (verifier count)).run e accepting ≤ half ^ count := by
  rw [acceptance]
  exact pow_le_pow_left' (agreement_bad e h) count

/-- Nontrivial tight boundary: a table with one wrong cell survives q tests with mass 2^-q. -/
theorem one_wrong_cell (count : Nat) :
    (system.experiment (verifier count)).run ⟨false, true, false⟩ accepting = half ^ count := by
  rw [acceptance]
  simp [agreement, agreesAt, cell, weight]

/-- Canonical soundness for a fixed public oracle statement. The theorem below quantifies
all tables; evidence cannot select a different table or negative region. -/
noncomputable def soundnessRequest (count : Nat) (table : Environment) :
    SoundnessRequest Unit (Execution Unit Bool Bool) Environment where
  experiment := (system.experiment (verifier count)).reindex (fun _ ↦ table)
  admissible _ := True
  accepts out := out.outcome = .returned true
  statement _ := table
  problem := PromiseProblem.ofPredicate good
  measurable_bad := MeasurableSet.of_discrete
  error _ := half ^ count

noncomputable def completenessRequest (count : Nat) (table : Environment) :
    CompletenessRequest Unit (Execution Unit Bool Bool) where
  experiment := (system.experiment (verifier count)).reindex (fun _ ↦ table)
  admissible _ := good table
  accepts := accepting
  measurable_accepts := MeasurableSet.of_discrete
  error _ := 0

theorem soundness (count : Nat) (table : Environment) : (soundnessRequest count table).Holds := by
  intro _ _
  by_cases honest : good table
  · simp [SoundnessRequest.toUpper, soundnessRequest, PromiseProblem.ofPredicate, honest]
  · simpa [SoundnessRequest.toUpper, soundnessRequest, PromiseProblem.ofPredicate,
      Experiment.reindex, honest, accepting] using proximity_soundness count table honest

theorem completeness (count : Nat) (table : Environment) :
    (completenessRequest count table).Holds := by
  intro _ honest
  change 1 - 0 ≤ (system.experiment (verifier count)).run table accepting
  rw [honest_completeness count table honest]
  simp

end ProtocolProofExamples.OracleProximity
