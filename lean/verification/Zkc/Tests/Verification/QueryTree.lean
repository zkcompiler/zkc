import Zkc.Protocol.Library.Transformations.FiatShamir.QueryTree
import Zkc.Protocol.Library.Transformations.FiatShamir.QueryTreeSimulation
import Zkc.Tools.Program.DeclarationAudit

/-! Kernel controls for complete query trees, adaptive caching and invalid grouping claims. -/

set_option autoImplicit false

namespace TestsSecurity.QueryTree
open OracleComp OracleSpec ZkcSecurity.FiatShamir.QueryTree
open ZkcSecurity.FiatShamir.Provider
open ZkcSecurity.FiatShamir
open SampleableType (prEvent_uniformSample prEvent_uniformSample_eq_singleton
  prEvent_replicate_uniformSample)
open scoped ENNReal

abbrev Bit := Fin 2
abbrev Node2 := Node Bit 2
abbrev Node3 := Node Bit 3

def root2 : Node2 := .inl ()
def child2 (first : Bit) : Node2 := .inr (first, .inl ())
def root3 : Node3 := .inl ()
def child3 (first : Bit) : Node3 := .inr (first, .inl ())
def suffix3 (first second : Bit) : Node3 := .inr (first, .inr (second, .inl ()))

theorem two_level_nodes : Fintype.card Node2 = 3 := by decide
theorem three_level_nodes : Fintype.card Node3 = 7 := by decide

/-- Depth remains part of a node even when its decoded index repeats. -/
theorem repeated_indices_distinct_nodes :
    root3 ≠ child3 0 ∧ child3 0 ≠ suffix3 0 0 := by decide

theorem duplicate_decoded_indices : path id 3 (fun _ ↦ (0 : Bit)) = [0, 0, 0] := rfl

def decodeFour (raw : Fin 4) : Bit := ⟨raw.val % 2, Nat.mod_lt _ (by decide)⟩

/-- Two raw replies can represent one observable history edge. The tree branches on that edge,
not on an unobservable raw value. -/
theorem decoder_collides : decodeFour 0 = decodeFour 2 ∧ (0 : Fin 4) ≠ 2 := by decide

theorem decoded_product_three :
    (do let tree ← $ᵗ (Tree (Fin 4) Bit 3); pure (path decodeFour 3 tree)) =ᵈ
      samples decodeFour 3 := path_product decodeFour 3

/-- A path-only vector cannot answer this suffix without fixing its off-path coordinate. -/
def suffixFirst : OracleComp ((Bit × Node3) →ₒ Bit) (Bit × Bit × Bit × Bit) := do
  let suffix ← ((Bit × Node3) →ₒ Bit).query (0, suffix3 1 0)
  let repeated ← ((Bit × Node3) →ₒ Bit).query (0, suffix3 1 0)
  let other ← ((Bit × Node3) →ₒ Bit).query (1, root3)
  let parent ← ((Bit × Node3) →ₒ Bit).query (0, root3)
  pure (suffix, repeated, other, parent)

theorem suffix_first_full_history :
    let observed := (simulateQ loggingOracle suffixFirst).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (simulator.translate observed ())).run' ∅ :=
  adaptive_logged_exact suffixFirst

/-- All four primitive occurrences survive, with the repeated suffix's exact answer. -/
theorem suffix_first_trace (table : Bit → Node3 → Bit) :
    evalWithAnswerFn (QueryImpl.ofFn table)
        (simulator.translate (simulateQ loggingOracle suffixFirst).run ()) =
      ((table 0 (suffix3 1 0), table 0 (suffix3 1 0), table 1 root3, table 0 root3),
        [⟨(0, suffix3 1 0), table 0 (suffix3 1 0)⟩,
          ⟨(0, suffix3 1 0), table 0 (suffix3 1 0)⟩,
          ⟨(1, root3), table 1 root3⟩, ⟨(0, root3), table 0 root3⟩]) := by
  rw [translate_table]
  simp [suffixFirst, loggingOracle, evalWithAnswerFn_map]

theorem suffix_first_allocates :
    (simulator.handle (0, suffix3 1 0)).run
        ((simulator (Root := Bit) (Raw := Bit)).start ()) =
      (fun tree ↦ (tree (suffix3 1 0), simulator.record (simulator.start ()) 0 tree)) <$>
        liftM ((Bit →ₒ (Node3 → Bit)).query 0) :=
  first_node_checkpoint Provider.Simulator.Runs.start 0 (suffix3 1 0) (by simp)

/-- A repeated coordinate is a cache hit with exactly its old raw answer. -/
theorem repeated_coordinate (tree : Node3 → Bit) :
    (simulator.handle (0, suffix3 1 0)).run
        (simulator.record ((simulator (Root := Bit) (Raw := Bit)).start ()) 0 tree) =
      pure (tree (suffix3 1 0), simulator.record (simulator.start ()) 0 tree) := by
  apply Provider.Simulator.handle_recorded
  · rfl
  · simp [simulator]

def typedEncoding : KeyEncoding (Bit × Node3) Bit Node3 where
  encode := id
  parse := some
  parse_encode _ := rfl
  encode_parse _ _ parsed := Option.some.inj parsed |>.symm

theorem disjoint_roots : typedEncoding.encode (0, root3) ≠
    typedEncoding.encode (1, suffix3 0 0) :=
  typedEncoding.disjoint_roots (by decide) root3 (suffix3 0 0)

/-- Allocating another root preserves the entire first tree. -/
theorem other_root_preserved (first second : Node3 → Bit) :
    simulator.record (simulator.record (simulator.start ()) (0 : Bit) first) 1 second 0 =
      some first := by simp [simulator]

/-- Reusing one primitive key for both roots cannot satisfy the checked parsing interface. -/
theorem alias_roots_unparsable : ¬ Nonempty (KeyEncoding Unit Bit Unit) := by
  rintro ⟨encoding⟩
  have same : encoding.encode (0, ()) = encoding.encode (1, ()) := Subsingleton.elim _ _
  have impossible := congrArg Prod.fst (encoding.injective same)
  exact (by decide : (0 : Bit) ≠ 1) impossible

theorem independent_pair_diagonal :
    Pr{let pair ← $ᵗ (Bit × Bit)}[pair.1 = pair.2] = (2 : ℝ≥0∞)⁻¹ := by
  have count : (Finset.univ.filter (fun pair : Bit × Bit ↦ pair.1 = pair.2)).card = 2 := by
    decide
  rw [prEvent_uniformSample]
  rw [count]
  norm_num only [Fintype.card_prod, Fintype.card_fin]
  rw [← one_div]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr
  norm_num

/-- A shared primitive key gives equal replies with probability one; replacing it by two
independent root cells changes that probability to one half. -/
theorem alias_roots_changes_joint_law :
    Pr{let bit ← $ᵗ Bit}[bit = bit] = 1 ∧
      Pr{let pair ← $ᵗ (Bit × Bit)}[pair.1 = pair.2] < 1 := by
  constructor
  · simp [ENNReal.div_self]
  · rw [independent_pair_diagonal]
    norm_num

theorem samples_id (n : ℕ) : samples (id : Bit → Bit) n =
    OracleComp.replicate n ($ᵗ Bit) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [samples, ih, OracleComp.replicate_succ_bind, id_eq]

theorem vector_probability_two :
    Pr{let tree ← $ᵗ (Tree Bit Bit 2)}[path id 2 tree = [0, 0]] =
      (4 : ℝ≥0∞)⁻¹ := by
  have calibrated : (id : Bit → Bit) <$> ($ᵗ Bit) =ᵈ ($ᵗ Bit) := by
    rw [id_map]
  simpa using path_vector_probability id calibrated 2 [0, 0] rfl

/-- Every ordered length-three vector has its exact product probability, even [0,0,0]. -/
theorem vector_probability_three :
    Pr{let tree ← $ᵗ (Tree Bit Bit 3)}[path id 3 tree = [0, 0, 0]] =
      (8 : ℝ≥0∞)⁻¹ := by
  have exactPath := (path_product (id : Bit → Bit) 3).prEvent_eq (· = [0, 0, 0])
  simp only [prEvent_norm, samples_id] at exactPath
  rw [exactPath, prEvent_replicate_uniformSample (by rfl)]
  norm_num

/-- A tree with its first two on-path replies already known. -/
def knownPrefix (last : Bit) : Tree Bit Bit 3 := fun node ↦
  match node with
  | .inl _ => 0
  | .inr (_, .inl _) => 0
  | .inr (_, .inr (_, _)) => last

theorem known_prefix_path (last : Bit) : path id 3 (knownPrefix last) = [0, 0, last] := rfl

/-- At the last key, after the first two replies are fixed, all-zero success costs one half,
not the whole-vector one eighth. This is a complete fresh-last-coordinate experiment. -/
theorem last_key_whole_vector_claim_false :
    Pr{let last ← $ᵗ Bit}[path id 3 (knownPrefix last) = [0, 0, 0]] =
        (2 : ℝ≥0∞)⁻¹ ∧
      ¬ Pr{let last ← $ᵗ Bit}[path id 3 (knownPrefix last) = [0, 0, 0]] ≤
        (8 : ℝ≥0∞)⁻¹ := by
  have event : (fun last : Bit ↦ path id 3 (knownPrefix last) = [0, 0, 0]) =
      fun last ↦ last = 0 := by
    funext last
    simp only [known_prefix_path, List.cons.injEq, and_true, true_and]
  rw [event, prEvent_uniformSample_eq_singleton]
  norm_num

theorem suffix_family_bound :
    FamilyQueryBound (fun _ : Bit × Node3 ↦ ()) suffixFirst (fun _ ↦ 4) := by
  change 0 < 4 ∧ ∀ _, 0 < 3 ∧ ∀ _, 0 < 2 ∧ ∀ _, 0 < 1 ∧ ∀ _, True
  decide

theorem simulator_budget_four :
    IsTotalQueryBound (simulator.translate suffixFirst ()) 4 := by
  simpa using translate_budget (fun _ : Bit × Node3 ↦ ()) suffixFirst (fun _ ↦ 4)
    suffix_family_bound

/-- The new instance feeds the existing simulation API's weighted budget without a height
divisor. The event is arbitrary, and the four primitive calls keep budget four. -/
theorem grouping_weighted (event : (Bit × Bit × Bit × Bit) → Prop)
    (weight : Bit → ℝ≥0∞) (bound : ℝ≥0∞) (bounded : ∀ root, weight root ≤ bound) :
    ∀ program ∈ support
        ((groupingSimulation (fun _ : Bit × Node3 ↦ ()) event (fun _ : Unit ↦ 0)).translate
          (fun _ ↦ 4) suffixFirst),
      WorstCaseCostBound program ⟨weight⟩ (4 * bound) := by
  simpa only [groupingSimulation, Finset.sum_const, Finset.card_univ, Fintype.card_unique,
    one_smul, Nat.cast_ofNat] using
    (groupingSimulation (fun _ : Bit × Node3 ↦ ()) event (fun _ : Unit ↦ 0)).weightedBudget
      weight bounded suffixFirst (fun _ ↦ 4) suffix_family_bound

/-- A verifier's cached logical macro access contributes its root to the verifier log. -/
theorem verifier_hit_logged (tree : Node3 → Bit) :
    ((randomOracle.withLogging (0 : Bit)).run).run
        (QueryCache.ofFn (fun _ : Bit ↦ some tree)) =
      (pure ((tree, [⟨0, tree⟩]), QueryCache.ofFn (fun _ : Bit ↦ some tree)) :
        ProbComp (((Node3 → Bit) × QueryLog (Bit →ₒ (Node3 → Bit))) ×
          (Bit →ₒ (Node3 → Bit)).QueryCache)) :=
  verifier_cache_hit_logged _ 0 tree rfl

/-- A suffix answer chooses a new, genuinely unbounded namespace and its queried coordinate. -/
def adaptiveNatRoots (initial : ℕ) :
    OracleComp ((ℕ × Node3) →ₒ Bit) (Bit × Bit × ℕ × Bit × Bit) := do
  let suffix ← ((ℕ × Node3) →ₒ Bit).query (initial, suffix3 1 0)
  let repeated ← ((ℕ × Node3) →ₒ Bit).query (initial, suffix3 1 0)
  let chosen := initial + 1 + suffix.val
  let other ← ((ℕ × Node3) →ₒ Bit).query (chosen, suffix3 suffix 1)
  let parent ← ((ℕ × Node3) →ₒ Bit).query (initial, root3)
  pure (suffix, repeated, chosen, other, parent)

theorem adaptive_nat_full_history (initial : ℕ) :
    let observed := (simulateQ loggingOracle (adaptiveNatRoots initial)).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (simulator.translate observed ())).run' ∅ :=
  adaptive_logged_exact (adaptiveNatRoots initial)

theorem adaptive_nat_trace (initial : ℕ) (table : ℕ → Node3 → Bit) :
    let answer := table initial (suffix3 1 0)
    let chosen := initial + 1 + answer.val
    evalWithAnswerFn (QueryImpl.ofFn table)
        (simulator.translate (simulateQ loggingOracle (adaptiveNatRoots initial)).run ()) =
      ((answer, answer, chosen, table chosen (suffix3 answer 1), table initial root3),
        [⟨(initial, suffix3 1 0), answer⟩, ⟨(initial, suffix3 1 0), answer⟩,
          ⟨(chosen, suffix3 answer 1), table chosen (suffix3 answer 1)⟩,
          ⟨(initial, root3), table initial root3⟩]) := by
  rw [translate_table]
  simp [adaptiveNatRoots, loggingOracle, evalWithAnswerFn_map]

/-- Appending the previous raw reply makes the second root depend on the observed history. -/
def adaptiveHistoryRoots (initialHistory : List Bit) :
    OracleComp ((List Bit × Node3) →ₒ Bit) (Bit × Bit × Bit × Bit) := do
  let suffix ← ((List Bit × Node3) →ₒ Bit).query (initialHistory, suffix3 1 0)
  let next := initialHistory ++ [suffix]
  let other ← ((List Bit × Node3) →ₒ Bit).query (next, suffix3 suffix 0)
  let repeated ← ((List Bit × Node3) →ₒ Bit).query (initialHistory, suffix3 1 0)
  let parent ← ((List Bit × Node3) →ₒ Bit).query (initialHistory, root3)
  pure (suffix, other, repeated, parent)

theorem adaptive_history_full_log (initialHistory : List Bit) :
    let observed := (simulateQ loggingOracle (adaptiveHistoryRoots initialHistory)).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (simulator.translate observed ())).run' ∅ :=
  adaptive_logged_exact (adaptiveHistoryRoots initialHistory)

/-- A cache hit remains in the ordered primitive log after an adaptive access to another root. -/
theorem adaptive_history_trace (initialHistory : List Bit) (table : List Bit → Node3 → Bit) :
    let answer := table initialHistory (suffix3 1 0)
    let next := initialHistory ++ [answer]
    evalWithAnswerFn (QueryImpl.ofFn table)
        (simulator.translate
          (simulateQ loggingOracle (adaptiveHistoryRoots initialHistory)).run ()) =
      ((answer, table next (suffix3 answer 0), answer, table initialHistory root3),
        [⟨(initialHistory, suffix3 1 0), answer⟩,
          ⟨(next, suffix3 answer 0), table next (suffix3 answer 0)⟩,
          ⟨(initialHistory, suffix3 1 0), answer⟩,
          ⟨(initialHistory, root3), table initialHistory root3⟩]) := by
  rw [translate_table]
  simp [adaptiveHistoryRoots, loggingOracle, evalWithAnswerFn_map]

theorem adaptive_history_separate (initialHistory : List Bit) (answer : Bit) :
    initialHistory ++ [answer] ≠ initialHistory := by
  intro same
  have lengths := congrArg List.length same
  simp at lengths

/-- The event alphabet itself need not be finite or inhabited. -/
theorem arbitrary_event_histories {Event α : Type} [DecidableEq Event]
    (program : OracleComp ((List Event × Node3) →ₒ Bit) α) :
    let observed := (simulateQ loggingOracle program).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (simulator.translate observed ())).run' ∅ :=
  adaptive_logged_exact program

/-- The same public provider package works on arbitrary natural-number roots. -/
noncomputable def natGrouping (event : (Bit × Bit × ℕ × Bit × Bit) → Prop) :=
  groupingSimulation (Raw := Bit) (fun _ : ℕ × Node3 ↦ ()) event (fun _ : Unit ↦ 0)

/-- A private query after the suffix has an answer-dependent range. Both private replies and
the suffix reply choose the next history root; the old suffix is subsequently queried again. -/
def interleavedHistoryRoots (initialHistory : List ℕ) :
    OracleComp (unifSpec + ((List ℕ × Node3) →ₒ Bit)) (ℕ × ℕ × Bit × Bit × Bit) := do
  let first ← (unifSpec + ((List ℕ × Node3) →ₒ Bit)).query (.inl 1)
  let suffix ← (unifSpec + ((List ℕ × Node3) →ₒ Bit)).query
    (.inr (initialHistory, suffix3 1 0))
  let second ← (unifSpec + ((List ℕ × Node3) →ₒ Bit)).query (.inl (suffix.val + 1))
  let chosen := initialHistory ++ [first.val, suffix.val, second.val]
  let other ← (unifSpec + ((List ℕ × Node3) →ₒ Bit)).query
    (.inr (chosen, suffix3 suffix 1))
  let repeated ← (unifSpec + ((List ℕ × Node3) →ₒ Bit)).query
    (.inr (initialHistory, suffix3 1 0))
  pure (first.val, second.val, suffix, other, repeated)

theorem interleaved_history_full_log (initialHistory : List ℕ) :
    let observed := logInterleaved (interleavedHistoryRoots initialHistory)
    (simulateQ (unifSpec.passthrough + randomOracle) observed).run' ∅ =ᵈ
      (do let fixed ← privatePrograms observed
          (simulateQ randomOracle (simulator.translate fixed ())).run' ∅) :=
  adaptive_interleaved_logged_exact (interleavedHistoryRoots initialHistory)

/-- Three primitive entries survive, including the cache hit. Neither private draw is logged. -/
theorem interleaved_history_trace (initialHistory : List ℕ)
    (coins : (bound : ℕ) → Fin (bound + 1)) (table : List ℕ → Node3 → Bit) :
    let impl : QueryImpl (unifSpec + ((List ℕ × Node3) →ₒ Bit)) Id :=
      fun | .inl bound => coins bound | .inr key => table key.1 key.2
    let answer := table initialHistory (suffix3 1 0)
    let first := (coins 1).val
    let second := (coins (answer.val + 1)).val
    let chosen := initialHistory ++ [first, answer.val, second]
    evalWithAnswerFn impl (logInterleaved (interleavedHistoryRoots initialHistory)) =
      ((first, second, answer, table chosen (suffix3 answer 1), answer),
        [⟨(initialHistory, suffix3 1 0), answer⟩,
          ⟨(chosen, suffix3 answer 1), table chosen (suffix3 answer 1)⟩,
          ⟨(initialHistory, suffix3 1 0), answer⟩]) := by
  simp only [interleavedHistoryRoots, logInterleaved_uniform_bind, logInterleaved_oracle_bind,
    logInterleaved_pure, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
    evalWithAnswerFn_pure, evalWithAnswerFn_map]

/-- Equal private query parameters denote separate draws at their two occurrences. -/
def repeatedPrivateDraws :
    OracleComp (unifSpec + ((ℕ × Node3) →ₒ Bit)) (Bit × Bit) := do
  let first ← (unifSpec + ((ℕ × Node3) →ₒ Bit)).query (.inl 1)
  let second ← (unifSpec + ((ℕ × Node3) →ₒ Bit)).query (.inl 1)
  pure (first, second)

theorem private_draws_are_not_cached :
    ((0, 1) : Bit × Bit) ∈ support
      ((simulateQ (unifSpec.passthrough + randomOracle) repeatedPrivateDraws).run' ∅) := by
  change ((0, 1) : Bit × Bit) ∈ support (do
    let first ← ProbComp.uniformFin 1
    let second ← ProbComp.uniformFin 1
    pure (first, second))
  simp

private def allowedPrivate (call : ℕ ⊕ (List ℕ × Node3)) (remaining : Unit → ℕ) : Prop :=
  Sum.elim (fun _ _ ↦ True) (fun _ remaining ↦ 0 < remaining ()) call remaining

private def costPrivate (call : ℕ ⊕ (List ℕ × Node3)) (remaining : Unit → ℕ) : Unit → ℕ :=
  Sum.elim (fun _ remaining ↦ remaining)
    (fun _ remaining ↦ Function.update remaining () (remaining () - 1)) call remaining

theorem interleaved_budget_three (history : List ℕ) :
    IsQueryBound (interleavedHistoryRoots history) (fun _ : Unit ↦ 3)
      allowedPrivate costPrivate := by
  simp [interleavedHistoryRoots, isQueryBound_query_bind_iff, allowedPrivate, costPrivate]

theorem interleaved_budget_two_refused (history : List ℕ) :
    ¬ IsQueryBound (interleavedHistoryRoots history) (fun _ : Unit ↦ 2)
      allowedPrivate costPrivate := by
  simp [interleavedHistoryRoots, isQueryBound_query_bind_iff, allowedPrivate, costPrivate]

theorem interleaved_macro_budget_three (history : List ℕ)
    {fixed : OracleComp ((List ℕ × Node3) →ₒ Bit) (ℕ × ℕ × Bit × Bit × Bit)}
    (sampled : fixed ∈ support (privatePrograms (interleavedHistoryRoots history))) :
    IsTotalQueryBound (simulator.translate fixed ()) 3 := by
  have bound : IsQueryBound (interleavedHistoryRoots history) (fun _ : Unit ↦ 3)
      allowedPrivate costPrivate := by
    simp [interleavedHistoryRoots, isQueryBound_query_bind_iff, allowedPrivate, costPrivate]
  simpa only [Finset.univ_unique, Finset.sum_singleton] using
    privatePrograms_translate_budget (fun _ : List ℕ × Node3 ↦ ())
      (interleavedHistoryRoots history) (fun _ : Unit ↦ 3) bound sampled

end TestsSecurity.QueryTree

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Protocol.Library.Transformations.FiatShamir.QueryTree, `Zkc.Protocol.Library.Transformations.FiatShamir.QueryTreeRandomness, `Zkc.Protocol.Library.Transformations.FiatShamir.QueryTreeSimulation] "QUERY-TREE-AXIOMS-PASS"
run_cmd ZkcTools.DeclarationAudit.checkCurrent "QUERY-TREE-CONTROLS-AXIOMS-PASS"
