import ZkcSecurity.Transformations.FiatShamir.Obligations
import TestsSecurity.Counterexamples.Support
import VCVio.EvalDist.Monad.Branch

/-! Security attacks on misplaced and incomplete proof-of-work gates.

Every key of the ideal oracle is one TranscriptQuery and is answered with one of
sixteen values; a gate passes, and a challenge hits the bad set, on zero, each
with probability `1 / 16`. Budgets count TranscriptQueries in every experiment:
a gate attempt is one TranscriptQuery, and so is a challenge.

Three flawed constructions let one passing witness serve many challenges. Each
has its own key type, a verifier that asks the gate key and the challenge key of
the proof and accepts when both answer zero, and the reusing adversary
(`reuser`): it searches `k` candidates of the first stage, then `n` candidates of
the second stage with the first stage's found value, `k + n` TranscriptQueries
in all (`reuser_queryBound`).

- **A message between the gate and the request.** The gate key is the witness;
  the challenge key is the witness and the producer message absorbed after the
  gate step. One gate key is shared by every message (`misplaced_gate_shared`),
  and the challenge keys of distinct messages are distinct
  (`misplaced_keys_distinct`).
- **A gate without the transcript state.** The gate key is the witness alone;
  the challenge key is the transcript state and the witness, so one witness
  serves every state (`stateless_gate_shared`, `stateless_keys_distinct`).
- **A gated value that has not absorbed the witness.** The challenge key is the
  state alone; the gate key is the state and the witness, so the adversary first
  finds a state whose challenge hits, then grinds a witness for it
  (`unabsorbed_challenge_shared`, `unabsorbed_keys_distinct`).

From the distinct-key facts, the reusing adversary is accepted with probability
`(1 - (15 / 16) ^ k) · (1 - (15 / 16) ^ n)` (`experiment_acceptance`, and
`misplaced_acceptance`, `stateless_acceptance`, `unabsorbed_acceptance` at
`k = n = 32`). A placed gate asks one key per attempt, answered with a gate value
and a challenge together: every prover with `Q` TranscriptQueries is accepted
with probability at most `(Q + 1) / 256` (`placed_bound`, from the typed
engine's soundness theorem). With 64 TranscriptQueries the reusing adversary
succeeds with probability above `0.76`, every adversary against the placed gate
with at most `65 / 256`, below `0.26` (`reuse_beats_placed`). Each flawed
construction violates one admission condition of its actual gate site
(`misplaced_violates`, `misplaced_not_determined`, `stateless_violates`,
`unabsorbed_violates`); the placed construction meets all of them
(`placed_meets`).
-/

namespace TestsSecurity.Counterexamples.Gates
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Obligations
open TestsSecurity.Counterexamples
open scoped ENNReal

/-- One TranscriptQuery's answer. -/
abbrev Answer := Fin 16

theorem answer_miss : Pr{let answer ← $ᵗ Answer}[¬ answer = 0] = 15 / 16 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun answer : Answer => ¬ answer = 0).card = 15 := by decide
  rw [count, Fintype.card_fin]
  rfl

/-! ### The reusing adversary -/

section TwoStage
variable {Key : Type}

/-- Search the candidates in order for one whose key answers zero. -/
def search {X : Type} (key : X → Key) : List X → OracleComp (Key →ₒ Answer) (Option X)
  | [] => pure none
  | candidate :: rest => do
      let answer ← liftM ((Key →ₒ Answer).query (key candidate))
      if answer = 0 then pure (some candidate) else search key rest

theorem search_queryBound {X : Type} (key : X → Key) :
    ∀ candidates : List X, IsTotalQueryBound (search key candidates) candidates.length
  | [] => trivial
  | candidate :: rest => by
      simp only [search, List.length_cons]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨Nat.succ_pos _, fun answer => ?_⟩
      split
      · trivial
      · simpa using search_queryBound key rest

theorem evalWithAnswerFn_search {X : Type} (key : X → Key) (table : Key → Answer) :
    ∀ candidates : List X,
      evalWithAnswerFn (QueryImpl.ofFn table) (search key candidates) =
        candidates.find? fun candidate => decide (table (key candidate) = 0)
  | [] => rfl
  | candidate :: rest => by
      simp only [search, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
        List.find?_cons]
      by_cases zero : table (key candidate) = 0
      · simp [zero]
      · simp only [zero, ↓reduceIte, decide_false]
        exact evalWithAnswerFn_search key table rest

variable {k n : ℕ} (first : Fin k → Key) (second : Fin k → Fin n → Key)

/-- Search the first stage, then the second stage with the found first-stage
value. -/
def reuser : OracleComp (Key →ₒ Answer) (Option (Fin k × Fin n)) := do
  let found ← search first (List.finRange k)
  match found with
  | none => pure none
  | some value => (Option.map fun other => (value, other)) <$> search (second value) (List.finRange n)

theorem reuser_queryBound : IsTotalQueryBound (reuser first second) (k + n) := by
  unfold reuser
  refine isTotalQueryBound_bind (by simpa using search_queryBound first (List.finRange k))
    fun found => ?_
  cases found with
  | none => trivial
  | some value =>
      show IsTotalQueryBound ((Option.map fun other => (value, other)) <$>
        search (second value) (List.finRange n)) n
      rw [map_eq_bind_pure_comp]
      have composed := isTotalQueryBound_bind (n₂ := 0)
        (ob := pure ∘ Option.map fun other => (value, other))
        (by simpa using search_queryBound (second value) (List.finRange n))
        fun result => (show IsTotalQueryBound
          (pure (result.map fun other => (value, other)) :
            OracleComp (Key →ₒ Answer) (Option (Fin k × Fin n))) 0 from trivial)
      rwa [add_zero] at composed

/-- The verifier: ask the gate key and the challenge key of the proof and accept
when both answer zero. -/
def check : Option (Fin k × Fin n) → OracleComp (Key →ₒ Answer) Bool
  | none => pure false
  | some (value, other) => do
      let firstAnswer ← liftM ((Key →ₒ Answer).query (first value))
      let secondAnswer ← liftM ((Key →ₒ Answer).query (second value other))
      pure (decide (firstAnswer = 0 ∧ secondAnswer = 0))

/-- The reusing adversary, then the verifier, in one oracle. -/
def experiment : OracleComp (Key →ₒ Answer) Bool := reuser first second >>= check first second

/-- Success read on the answers of the two stages: the first stage finds a value,
and the second stage hits at some candidate with that value. -/
def Succeeds (firstAnswers : Fin k → Answer) (secondAnswers : Fin k → Fin n → Answer) : Prop :=
  ∃ value, (List.finRange k).find? (fun candidate => decide (firstAnswers candidate = 0)) =
    some value ∧ ∃ other, secondAnswers value other = 0

theorem experiment_accepts (table : Key → Answer) :
    evalWithAnswerFn (QueryImpl.ofFn table) (experiment first second) = true ↔
      Succeeds (fun value => table (first value)) fun value other => table (second value other) := by
  unfold experiment reuser Succeeds
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_search]
  rcases found : (List.finRange k).find? (fun candidate => decide (table (first candidate) = 0)) with
    _ | value
  · simp [check]
  · have passing : table (first value) = 0 := by simpa using List.find?_some found
    simp only [evalWithAnswerFn_map, evalWithAnswerFn_search, Option.some.injEq, exists_eq_left']
    rcases hit : (List.finRange n).find? (fun candidate => decide (table (second value candidate) = 0))
      with _ | other
    · rw [List.find?_eq_none] at hit
      simp only [Option.map_none, check, evalWithAnswerFn_pure, Bool.false_eq_true, false_iff,
        not_exists]
      intro other
      simpa using hit other (List.mem_finRange other)
    · have hitting : table (second value other) = 0 := by simpa using List.find?_some hit
      simp only [Option.map_some, check, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, evalWithAnswerFn_pure, passing, hitting, and_self, decide_true,
        true_iff]
      exact ⟨other, hitting⟩

/-- The keys of the two stages as one finite role type. -/
abbrev Role (k n : ℕ) := Fin k ⊕ (Fin k × Fin n)

/-- The keys the experiment can ask. -/
def roles : Role k n → Key
  | .inl value => first value
  | .inr pair => second pair.1 pair.2

/-- Split a table of the roles into the two stages' answers. -/
def stages (answers : (Fin k → Answer) × (Fin k → Fin n → Answer)) : Role k n → Answer
  | .inl value => answers.1 value
  | .inr pair => answers.2 pair.1 pair.2

theorem stages_bijective : Function.Bijective (stages (k := k) (n := n)) := by
  constructor
  · intro first second same
    have firstSame : first.1 = second.1 := funext fun value => congrFun same (.inl value)
    have secondSame : first.2 = second.2 :=
      funext fun value => funext fun other => congrFun same (.inr (value, other))
    exact Prod.ext firstSame secondSame
  · intro table
    refine ⟨(fun value => table (.inl value), fun value other => table (.inr (value, other))), ?_⟩
    funext role
    cases role <;> rfl

variable [Fintype Key] [DecidableEq Key]

/-- With injective, disjoint stage keys, the reusing adversary is accepted with
probability `(1 - (15 / 16) ^ k) · (1 - (15 / 16) ^ n)`. -/
theorem experiment_acceptance (firstInjective : Function.Injective first)
    (secondInjective : ∀ value value' other other', second value other = second value' other' →
      value = value' ∧ other = other')
    (disjoint : ∀ value value' other, first value ≠ second value' other) :
    Pr{let accepted ← (simulateQ randomOracle (experiment first second)).run' ∅}[accepted = true] =
      (1 - (15 / 16) ^ k) * (1 - (15 / 16) ^ n) := by
  have injective : Function.Injective (roles (k := k) (n := n) first second) := by
    rintro (value | ⟨value, other⟩) (value' | ⟨value', other'⟩) same
    · exact congrArg Sum.inl (firstInjective same)
    · exact absurd same (disjoint value value' other')
    · exact absurd same.symm (disjoint value' value other)
    · obtain ⟨rfl, rfl⟩ := secondInjective value value' other other' same
      rfl
  rw [prEvent_randomOracle_table, prEvent_congr _ _
    (fun table : Key → Answer => Succeeds (fun value => table (roles first second (.inl value)))
      fun value other => table (roles first second (.inr (value, other))))
    fun table => experiment_accepts first second table]
  rw [prEvent_roles (roles first second) injective
    (fun answers : Role k n → Answer => Succeeds (fun value => answers (.inl value))
      fun value other => answers (.inr (value, other)))]
  rw [← prEvent_of_bijective stages_bijective
    (fun answers : Role k n → Answer => Succeeds (fun value => answers (.inl value))
      fun value other => answers (.inr (value, other)))]
  change Pr{let answers ← $ᵗ ((Fin k → Answer) × (Fin k → Fin n → Answer))}[
    Succeeds answers.1 answers.2] = _
  rw [SampleableType.prEvent_uniformSample_prod]
  have firstStage : Pr{let firstAnswers ← $ᵗ (Fin k → Answer)}[
      ((List.finRange k).find? fun candidate => decide (firstAnswers candidate = 0)).isSome] =
      1 - (15 / 16) ^ k := by
    rw [prEvent_congr _ _ (fun firstAnswers : Fin k → Answer => ∃ index, firstAnswers index = 0)
      fun firstAnswers => by simp [List.find?_isSome]]
    exact prEvent_exists_uniform k (· = 0) answer_miss
  have secondStage : Pr{let row ← $ᵗ (Fin n → Answer)}[∃ other, row other = 0] =
      1 - (15 / 16) ^ n :=
    prEvent_exists_uniform n (· = 0) answer_miss
  rw [← firstStage, ← secondStage]
  refine Eq.trans ?_ (prEvent_bind_eq_mul_of_ite ($ᵗ (Fin k → Answer))
    (fun firstAnswers => (fun secondAnswers => (firstAnswers, secondAnswers)) <$>
      ($ᵗ (Fin k → Fin n → Answer)))
    (fun firstAnswers => ((List.finRange k).find? fun candidate =>
      decide (firstAnswers candidate = 0)).isSome) (fun pair => Succeeds pair.1 pair.2)
    ($ᵗ (Fin n → Answer)) (fun row => ∃ other, row other = 0) fun firstAnswers => ?_)
  · simp only [bind_assoc, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
  rw [prEvent_map]
  rcases found : (List.finRange k).find? (fun candidate => decide (firstAnswers candidate = 0)) with
    _ | value
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    refine prEvent_eq_zero_of_forall_not _ _ fun _ ⟨_, same, _⟩ => ?_
    rw [found] at same
    cases same
  · simp only [Option.isSome_some, ↓reduceIte]
    rw [prEvent_congr _ _ (fun secondAnswers : Fin k → Fin n → Answer =>
        ∃ other, secondAnswers value other = 0) fun secondAnswers => by
          simp only [Succeeds, found, Option.some.injEq, exists_eq_left']]
    exact prEvent_coordinate value (fun row : Fin n → Answer => ∃ other, row other = 0)

end TwoStage

/-! ### Three flawed gates -/

/-- Thirty-two gate attempts and thirty-two challenge attempts. -/
abbrev Attempts := Fin 32

/-- The probability of each flawed construction's reusing adversary. -/
noncomputable abbrev reuseProbability : ENNReal := (1 - (15 / 16) ^ 32) * (1 - (15 / 16) ^ 32)

/-- Keys of the misplaced gate: the gate step at a witness, and the request
after the producer message absorbed behind the gate. -/
inductive MisplacedKey where
  | gate (witness : Attempts)
  | request (witness message : Attempts)
  deriving DecidableEq, Fintype

/-- The misplaced gate site over contexts (witness, message): its gate key, its
challenge key and the message absorbed in between are those the verifier uses. -/
def misplacedSite : GateSite (Attempts × Attempts) MisplacedKey Unit Attempts Attempts MisplacedKey :=
  ⟨fun context => .gate context.1, fun _ => (), Prod.fst, fun context => [context.2],
    fun context => .request context.1 context.2⟩

theorem misplaced_gate_shared (witness message message' : Attempts) :
    misplacedSite.gateInput (witness, message) = misplacedSite.gateInput (witness, message') := rfl

theorem misplaced_keys_distinct :
    Function.Injective MisplacedKey.gate ∧
      (∀ witness witness' message message', MisplacedKey.request witness message =
        MisplacedKey.request witness' message' → witness = witness' ∧ message = message') ∧
      ∀ witness witness' message, MisplacedKey.gate witness ≠ MisplacedKey.request witness' message :=
  ⟨fun _ _ same => MisplacedKey.gate.inj same,
    fun _ _ _ _ same => MisplacedKey.request.inj same, fun _ _ _ same => by cases same⟩

theorem misplaced_acceptance :
    Pr{let accepted ← (simulateQ randomOracle
        (experiment (k := 32) (n := 32) MisplacedKey.gate MisplacedKey.request)).run' ∅}[
      accepted = true] = reuseProbability :=
  experiment_acceptance _ _ misplaced_keys_distinct.1 misplaced_keys_distinct.2.1
    misplaced_keys_distinct.2.2

/-- A message is absorbed between the gate step and the request. -/
theorem misplaced_violates : ¬ misplacedSite.Placement := fun placed =>
  absurd (placed (0, 0)) (by simp [misplacedSite])

/-- The gate key does not even determine the challenge key. -/
theorem misplaced_not_determined : ¬ misplacedSite.GateDetermines :=
  not_determines (first := (0, 0)) (second := (0, 1)) rfl (by decide)

/-- Keys of the gate without the transcript state: the gate at a witness alone,
the request at a state and a witness. -/
inductive StatelessKey where
  | gate (witness : Attempts)
  | request (state witness : Attempts)
  deriving DecidableEq, Fintype

/-- The stateless gate site over contexts (state, witness). -/
def statelessSite : GateSite (Attempts × Attempts) StatelessKey Attempts Attempts Attempts StatelessKey :=
  ⟨fun context => .gate context.2, Prod.fst, Prod.snd, fun _ => [],
    fun context => .request context.1 context.2⟩

theorem stateless_gate_shared (state state' witness : Attempts) :
    statelessSite.gateInput (state, witness) = statelessSite.gateInput (state', witness) := rfl

theorem stateless_keys_distinct :
    Function.Injective StatelessKey.gate ∧
      (∀ witness witness' state state', StatelessKey.request state witness =
        StatelessKey.request state' witness' → witness = witness' ∧ state = state') ∧
      ∀ witness witness' state, StatelessKey.gate witness ≠ StatelessKey.request state witness' := by
  refine ⟨fun _ _ same => StatelessKey.gate.inj same, fun _ _ _ _ same => ?_,
    fun _ _ _ same => by cases same⟩
  obtain ⟨sameState, sameWitness⟩ := StatelessKey.request.inj same
  exact ⟨sameWitness, sameState⟩

/-- First search a witness, then the states with that witness. -/
theorem stateless_acceptance :
    Pr{let accepted ← (simulateQ randomOracle (experiment (k := 32) (n := 32) StatelessKey.gate
        fun witness state => StatelessKey.request state witness)).run' ∅}[accepted = true] =
      reuseProbability :=
  experiment_acceptance _ _ stateless_keys_distinct.1 stateless_keys_distinct.2.1
    fun witness witness' state => stateless_keys_distinct.2.2 witness witness' state

theorem stateless_violates : ¬ statelessSite.ReadsState :=
  not_determines (first := (0, 0)) (second := (1, 0)) rfl (by decide)

/-- Keys of the gated value that has not absorbed the witness: the request at a
state alone, the gate at a state and a witness. -/
inductive UnabsorbedKey where
  | request (state : Attempts)
  | gate (state witness : Attempts)
  deriving DecidableEq, Fintype

/-- The unabsorbed gate site over contexts (state, witness). -/
def unabsorbedSite :
    GateSite (Attempts × Attempts) UnabsorbedKey Attempts Attempts Attempts UnabsorbedKey :=
  ⟨fun context => .gate context.1 context.2, Prod.fst, Prod.snd, fun _ => [],
    fun context => .request context.1⟩

theorem unabsorbed_challenge_shared (state witness witness' : Attempts) :
    unabsorbedSite.requestInput (state, witness) = unabsorbedSite.requestInput (state, witness') :=
  rfl

theorem unabsorbed_keys_distinct :
    Function.Injective UnabsorbedKey.request ∧
      (∀ state state' witness witness', UnabsorbedKey.gate state witness =
        UnabsorbedKey.gate state' witness' → state = state' ∧ witness = witness') ∧
      ∀ state state' witness, UnabsorbedKey.request state ≠ UnabsorbedKey.gate state' witness :=
  ⟨fun _ _ same => UnabsorbedKey.request.inj same,
    fun _ _ _ _ same => UnabsorbedKey.gate.inj same, fun _ _ _ same => by cases same⟩

/-- First search a state whose challenge hits, then grind a witness for it. -/
theorem unabsorbed_acceptance :
    Pr{let accepted ← (simulateQ randomOracle
        (experiment (k := 32) (n := 32) UnabsorbedKey.request UnabsorbedKey.gate)).run' ∅}[
      accepted = true] = reuseProbability :=
  experiment_acceptance _ _ unabsorbed_keys_distinct.1 unabsorbed_keys_distinct.2.1
    unabsorbed_keys_distinct.2.2

theorem unabsorbed_violates : ¬ unabsorbedSite.AbsorbsWitness :=
  not_determines (first := (0, 0)) (second := (0, 1)) rfl (by decide)

/-! ### The placed gate -/

/-- The placed gate site: one key for the gate and the gated value. -/
def placedSite : GateSite (Attempts × Attempts) (Attempts × Attempts) Attempts Attempts Unit
    (Attempts × Attempts) :=
  ⟨id, Prod.fst, Prod.snd, fun _ => [], id⟩

theorem placed_meets :
    placedSite.Placement ∧ placedSite.GateDetermines ∧ placedSite.ReadsState ∧
      placedSite.AbsorbsWitness :=
  ⟨fun _ => rfl, determines_of_factor id fun _ => rfl, determines_of_factor Prod.fst fun _ => rfl,
    determines_of_factor Prod.snd fun _ => rfl⟩

inductive PlacedOp where
  | context
  | draw

abbrev placedSignature : PIR.Signature where
  Op := PlacedOp
  Reply
    | .context => Attempts × Attempts
    | .draw => Answer × Answer

inductive PlacedEvent where
  | context (state witness : Attempts)
  | gated
  deriving DecidableEq

/-- One TranscriptQuery per attempt, answered with a gate value and a
challenge. -/
abbrev PlacedRaw : PlacedEvent → Type := fun _ => Answer × Answer

/-- The history oracle answers every history with a gate value and a challenge. -/
abbrev PlacedHistoryRaw : List PlacedEvent → Type := fun _ => Answer × Answer

def recoverContext : PlacedEvent → Option (Attempts × Attempts)
  | .context state witness => some (state, witness)
  | .gated => none

def placedAbsorb : Typed.Interface placedSignature PlacedEvent (Attempts × Attempts) PlacedRaw
  | .context => .receive (fun context => .context context.1 context.2) recoverContext
  | .draw => .query .gated fun raw => some raw

/-- Accept when the gate passes and the challenge hits. -/
def placedDraw : PIR.Process placedSignature Bool :=
  .call PlacedOp.draw fun raw => .done (decide (raw = (0, 0)))

def placedValidator : PIR.Process placedSignature Bool := .call PlacedOp.context fun _ => placedDraw

def placedDoomed (process : PIR.Process placedSignature Bool) : Prop :=
  process = placedValidator ∨ process = placedDraw ∨ process = .done false ∨
    ∃ stop, process = .halt stop

theorem done_true_not_doomed : ¬ placedDoomed (.done true) := by
  rintro (same | same | same | ⟨_, same⟩) <;> cases same

/-- The placed gate's local error: `1 / 256`. -/
def placedCertificate : Typed.Certificate placedAbsorb (· = true) (fun _ => 1 / 256) where
  doomed := placedDoomed
  step process member := by
    rcases member with rfl | rfl | rfl | ⟨stop, rfl⟩
    · intro _
      exact Or.inr (Or.inl rfl)
    · change Pr{let raw ← $ᵗ (Answer × Answer)}[
        ∃ value, some raw = some value ∧ ¬ placedDoomed (.done (decide (value = (0, 0))))] ≤ 1 / 256
      rw [prEvent_congr _ _ (fun raw : Answer × Answer => raw = (0, 0)) fun raw => by
        constructor
        · rintro ⟨value, same, escapes⟩
          cases Option.some.inj same
          by_contra different
          exact escapes (Or.inr (Or.inr (Or.inl (by simp [different]))))
        · rintro rfl
          exact ⟨(0, 0), rfl, by simpa using done_true_not_doomed⟩,
        SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_prod, Fintype.card_fin]
      numerals
    · show ¬ (false = true)
      simp
    · trivial

theorem placedValidator_queryBound : Typed.QueryBound placedAbsorb placedValidator 1 :=
  fun _ => ⟨Nat.one_pos, fun _ => trivial⟩

/-- Every prover with at most `queries` TranscriptQueries is accepted by the
placed validator with probability at most `(queries + 1) / 256`. -/
theorem placed_bound (prover : OracleComp (OracleSpec.ofFn PlacedHistoryRaw) (List (Attempts × Attempts)))
    (queries : ℕ) (bounded : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (Typed.fixedExperiment placedAbsorb placedValidator [] prover)).run' ∅}[
      Accepted (· = true) result.1] ≤ (queries + 1) * (1 / 256) := by
  have total := Typed.soundness placedCertificate (fun _ => le_rfl) placedValidator (Or.inl rfl) 1
    placedValidator_queryBound [] prover queries bounded
  rwa [Nat.cast_one] at total

/-- With 64 TranscriptQueries, each flawed gate's reusing adversary succeeds with
probability above `0.76`; against the placed gate every adversary with 64
TranscriptQueries succeeds with probability at most `65 / 256`, below `0.26`. -/
theorem reuse_beats_placed :
    ((64 : ℕ) + 1 : ENNReal) * (1 / 256) < 26 / 100 ∧ (76 / 100 : ENNReal) < reuseProbability := by
  constructor
  · numerals
  · rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le (pow_le_one₀ (by positivity) (by numerals)) ENNReal.one_ne_top]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num

end TestsSecurity.Counterexamples.Gates
