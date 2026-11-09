module

public import Zkc.Protocol.Library.Transformations.FiatShamir.ProviderSimulation
public import Zkc.Protocol.Library.Transformations.FiatShamir.QueryTreeRandomness
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

@[expose] public section

/-!
# Cached primitive queries grouped by an arbitrary root

The primitive domain is the *checked typed* pair `(root, coordinate)`. Coordinates can be
`QueryTree.Node Step height`. Every root owns an independent complete answer table. First
access to any coordinate asks the macro oracle for that table; later accesses read it.

`adaptive_exact` quantifies over every adaptive `OracleComp`, not just a scalar sampler.
`adaptive_logged_exact` preserves all primitive inputs and answers, including cache repeats.
The macro oracle exposes the whole table, so this is a stronger adversary interface and makes
no efficiency claim. The primitive budget is retained, not divided by the tree height.
The distribution theorems require finite coordinates and sampleable finite raw replies, but
no finiteness of roots. A common finite restriction covers every adaptive primitive branch
and every translated macro branch, including branches selected by off-path tree replies.

Source key parsing, native byte decoding, source event reconstruction and correspondence of
verifier/extraction checkpoints require separate connections. In particular a verifier must
make its own logical macro query even if the adversary already allocated the root. The
simulator's cache-hit branch deliberately makes no new macro query.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.QueryTree
open OracleComp OracleSpec MeasureTheory Provider

/-- A source adapter must prove both directions of its constituent-key parser. -/
structure KeyEncoding (Key Root Coordinate : Type) where
  encode : Root × Coordinate → Key
  parse : Key → Option (Root × Coordinate)
  parse_encode : ∀ pair, parse (encode pair) = some pair
  encode_parse : ∀ key pair, parse key = some pair → encode pair = key

theorem KeyEncoding.injective {Key Root Coordinate : Type}
    (encoding : KeyEncoding Key Root Coordinate) : Function.Injective encoding.encode := by
  intro first second same
  have parsed := congrArg encoding.parse same
  simpa only [encoding.parse_encode, Option.some.injEq] using parsed

/-- Different roots have disjoint encoded node sets. This follows from the checked parser,
not from the names assigned to events. -/
theorem KeyEncoding.disjoint_roots {Key Root Coordinate : Type}
    (encoding : KeyEncoding Key Root Coordinate) {first second : Root} (different : first ≠ second)
    (a b : Coordinate) : encoding.encode (first, a) ≠ encoding.encode (second, b) := by
  intro same
  exact different (congrArg Prod.fst (encoding.injective same))

section Simulator
variable {Root Coordinate Raw : Type} [DecidableEq Root] [Nonempty Raw]

/-- A direct instance of the existing provider simulator, with no second FS engine. -/
noncomputable def simulator :
    Provider.Simulator ((Root × Coordinate) →ₒ Raw) (fun _ : Root ↦ Coordinate → Raw) Unit where
  State := Root → Option (Coordinate → Raw)
  start _ := fun _ ↦ none
  attempt _ call := some call.1
  recorded state root := state root
  record state root tree := Function.update state root (some tree)
  shared call _ tree := tree call.2
  respond state _ := (Classical.arbitrary Raw, state)
  together first second := first.1 = second.1
  recorded_start _ _ := rfl
  recorded_record _ _ _ := by simp
  recorded_record_of_ne _ _ _ _ different := by simp [different]
  recorded_respond _ _ _ := rfl
  attempt_record _ _ _ _ _ assigned := assigned
  attempt_respond _ _ _ _ assigned := assigned
  attempt_together _ _ _ same := by simp [same]

/-- Every already allocated tree agrees with the fixed complete macro table. -/
def Consistent (table : Root → Coordinate → Raw)
    (state : (simulator (Root := Root) (Coordinate := Coordinate) (Raw := Raw)).State) : Prop :=
  ∀ root tree, state root = some tree → tree = table root

theorem consistent_start (table : Root → Coordinate → Raw) :
    Consistent table (simulator.start ()) := by
  intro root tree impossible
  cases impossible

theorem consistent_record (table : Root → Coordinate → Raw)
    {state : Root → Option (Coordinate → Raw)}
    (agrees : Consistent table state) (root : Root) :
    Consistent table (simulator.record state root (table root)) := by
  intro other tree recorded
  by_cases same : other = root
  · subst other
    simpa [simulator] using recorded.symm
  · exact agrees other tree (by simpa [simulator, same] using recorded)

/-- Deterministic evaluation of one call preserves its exact reply and the table invariant. -/
theorem handle_table (table : Root → Coordinate → Raw)
    (state : Root → Option (Coordinate → Raw)) (agrees : Consistent table state)
    (call : Root × Coordinate) :
    let result := evalWithAnswerFn (QueryImpl.ofFn table) ((simulator.handle call).run state)
    result.1 = table call.1 call.2 ∧ Consistent table result.2 := by
  rcases cached : state call.1 with _ | tree
  · rw [simulator.handle_fresh (by rfl) cached, evalWithAnswerFn_map]
    exact ⟨rfl, consistent_record table agrees call.1⟩
  · rw [simulator.handle_recorded (by rfl) cached, evalWithAnswerFn_pure]
    exact ⟨congrFun (agrees call.1 tree cached) call.2, agrees⟩

/-- Pointwise adaptive execution preserves its result and the allocation invariant. -/
theorem run_table {α : Type} (program : OracleComp ((Root × Coordinate) →ₒ Raw) α)
    (table : Root → Coordinate → Raw) (state : Root → Option (Coordinate → Raw))
    (agrees : Consistent table state) :
    let result := evalWithAnswerFn (QueryImpl.ofFn table)
      ((simulateQ simulator.handle program).run state)
    result.1 = evalWithAnswerFn (QueryImpl.ofFn (Function.uncurry table)) program ∧
      Consistent table result.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => exact ⟨rfl, agrees⟩
  | query_bind call next ih =>
      have reduction :
          (simulateQ simulator.handle
            (liftM (((Root × Coordinate) →ₒ Raw).query call) >>= next)).run state =
            (simulator.handle call).run state >>= fun result ↦
              (simulateQ simulator.handle (next result.1)).run result.2 := by
        rw [simulateQ_bind, simulateQ_spec_query]
        rfl
      dsimp only
      rw [reduction, evalWithAnswerFn_bind]
      obtain ⟨answer, preserved⟩ := handle_table table state agrees call
      obtain ⟨value, final⟩ := ih _ _ preserved
      refine ⟨?_, final⟩
      rw [value, answer, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
      rfl

/-- Every fixed macro table answers the translated program exactly as its flat primitive table. -/
theorem translate_table {α : Type} (program : OracleComp ((Root × Coordinate) →ₒ Raw) α)
    (table : Root → Coordinate → Raw) :
    evalWithAnswerFn (QueryImpl.ofFn table) (simulator.translate program ()) =
      evalWithAnswerFn (QueryImpl.ofFn (Function.uncurry table)) program := by
  unfold Provider.Simulator.translate
  rw [StateT.run'_eq, evalWithAnswerFn_map]
  exact (run_table program table _ (consistent_start table)).1

/-- Every primitive occurrence on a simulator run belongs to its parsed root. -/
theorem runs_attempt {trace : List (Answered ((Root × Coordinate) →ₒ Raw) Root)}
    {state : simulator.State} (runs : simulator.Runs () trace state) :
    ∀ entry ∈ trace, entry.attempt = some entry.query.1 := by
  induction runs with
  | start => simp
  | step _ _ ih =>
      intro entry member
      rcases List.mem_append.mp member with old | new
      · exact ih entry old
      · rw [List.mem_singleton] at new
        subst new
        rfl

/-- The first access to any node, including an off-path suffix, is the root's unique
allocation checkpoint. Source/extractor checkpoint correspondence still needs a source map. -/
theorem first_node_checkpoint {trace : List (Answered ((Root × Coordinate) →ₒ Raw) Root)}
    {state : simulator.State} (runs : simulator.Runs () trace state)
    (root : Root) (coordinate : Coordinate)
    (first : ∀ entry ∈ trace, entry.query.1 ≠ root) :
    (simulator.handle (root, coordinate)).run state =
      (fun tree ↦ (tree coordinate, simulator.record state root tree)) <$>
        liftM ((Root →ₒ (Coordinate → Raw)).query root) := by
  apply Provider.Simulator.Runs.first_call simulator runs rfl
  intro entry member assigned
  rw [runs_attempt runs entry member] at assigned
  exact first entry member (Option.some.inj assigned)

/-- All calls of one root, in any order, use the same entire tree. -/
theorem nodes_share {trace : List (Answered ((Root × Coordinate) →ₒ Raw) Root)}
    {state : simulator.State} (runs : simulator.Runs () trace state)
    {first second : Answered ((Root × Coordinate) →ₒ Raw) Root}
    (firstIn : first ∈ trace) (secondIn : second ∈ trace)
    (sameRoot : first.query.1 = second.query.1) :
    ∃ tree : Coordinate → Raw,
      first.reply = tree first.query.2 ∧ second.reply = tree second.query.2 := by
  exact Provider.Simulator.Runs.shared_answer simulator runs firstIn secondIn
    (runs_attempt runs first firstIn)
    ((runs_attempt runs second secondIn).trans (congrArg some sameRoot.symm))

end Simulator

/-- Lift an adaptive lazy execution to any finite table with distinct cells for all its
possible keys. Coverage ranges over every response branch. The extension law only specifies
individual answers; it is not an assumed equality of simulations or distributions. -/
theorem randomOracle_finite_cover {Key Cell Reply α : Type} [DecidableEq Key]
    [Fintype Cell] [DecidableEq Cell] [SampleableType Reply] [MeasurableSpace α]
    (program : OracleComp (Key →ₒ Reply) α) (keys : Finset Key)
    (covered : AllQueriesSatisfy program (· ∈ keys))
    (cell : keys → Cell) (distinct : Function.Injective cell)
    (answers : (Cell → Reply) → Key → Reply)
    (agrees : ∀ table key, answers table key.val = table (cell key)) :
    𝒟[(simulateQ randomOracle program).run' ∅] =
      𝒟[do
        let table ← $ᵗ (Cell → Reply)
        pure (evalWithAnswerFn (QueryImpl.ofFn (answers table)) program)] := by
  classical
  let : MeasurableSpace Reply := ⊤
  have empty : restrictCache keys (∅ : (Key →ₒ Reply).QueryCache) = ∅ := by
    ext key
    rfl
  rw [← randomOracle_restrictQueries keys program covered ∅, empty,
    evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable]
  have projection := EvalDistEq.of_evalDist_eq (evalDist_map_table_comp_injective
    ($ᵗ (keys → Reply)) ($ᵗ (Cell → Reply))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample distinct)
  have restricted := (projection.bind_left fun table ↦
    pure (evalWithAnswerFn (QueryImpl.ofFn table)
      (restrictQueries keys program covered))).evalDist_eq
  rw [bind_map_left] at restricted
  rw [← restricted]
  apply evalDist_bind_congr
  intro table
  have assignment : table ∘ cell = fun key : keys ↦ answers table key.val := by
    funext key
    exact (agrees table key).symm
  rw [assignment, evalWithAnswerFn_restrictQueries]

section Distribution
variable {Root Coordinate Raw : Type} [DecidableEq Root]
  [Fintype Coordinate] [DecidableEq Coordinate] [SampleableType Raw]

/-- A common finite root set covers every primitive response branch and every branch of the
translated program. In particular no preselected adversary query set is a hypothesis. -/
noncomputable def possibleRoots {α : Type}
    (program : OracleComp ((Root × Coordinate) →ₒ Raw) α) : Finset Root :=
  (possibleQueryKeys program).image Prod.fst ∪
    possibleQueryKeys (simulator.translate program ())

theorem primitive_roots_covered {α : Type}
    (program : OracleComp ((Root × Coordinate) →ₒ Raw) α) :
    AllQueriesSatisfy program (fun key ↦ key.1 ∈ possibleRoots program) :=
  (allQueriesSatisfy_possibleQueryKeys program).mono fun key member ↦
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨key, member, rfl⟩)

theorem macro_roots_covered {α : Type}
    (program : OracleComp ((Root × Coordinate) →ₒ Raw) α) :
    AllQueriesSatisfy (simulator.translate program ()) (· ∈ possibleRoots program) :=
  (allQueriesSatisfy_possibleQueryKeys (simulator.translate program ())).mono
    fun _ member ↦ Finset.mem_union_right _ member

/-- Lossless cached primitive-to-tree simulation for every adaptive program over arbitrary
roots, including unbounded transcript histories. Both sides use actual lazy random oracles.
All response branches on both sides are finitely restricted before using independent tables
and the pointwise execution theorem. Arbitrary returned failure/stop values are preserved. -/
theorem adaptive_exact {α : Type} [MeasurableSpace α]
    (program : OracleComp ((Root × Coordinate) →ₒ Raw) α) :
    𝒟[(simulateQ randomOracle program).run' ∅] =
      𝒟[(simulateQ randomOracle (simulator.translate program ())).run' ∅] := by
  classical
  let roots := possibleRoots program
  let keys := roots ×ˢ (Finset.univ : Finset Coordinate)
  have covered : AllQueriesSatisfy program (· ∈ keys) :=
    (primitive_roots_covered program).mono fun key member ↦
      Finset.mem_product.mpr ⟨member, Finset.mem_univ _⟩
  let cell : keys → roots × Coordinate :=
    fun key ↦ (⟨key.val.1, (Finset.mem_product.mp key.property).1⟩, key.val.2)
  have distinct : Function.Injective cell := by
    intro first second same
    apply Subtype.ext
    exact Prod.ext (congrArg (fun pair ↦ pair.1.val) same)
      (congrArg (fun pair : roots × Coordinate ↦ pair.2) same)
  have primitive := randomOracle_finite_cover program keys covered cell distinct
    (fun table ↦ Function.uncurry (extendTable roots (Function.curry table)))
    (by intro table key; simp [Function.uncurry, Function.curry, cell, extendTable,
          (Finset.mem_product.mp key.property).1])
  have grouped := randomOracle_finite_cover (simulator.translate program ()) roots
    (macro_roots_covered program) id Function.injective_id
    (fun table ↦ extendTable roots table)
    (by intro table root; simp [extendTable, root.property])
  rw [primitive, grouped]
  simp_rw [translate_table]
  let : MeasurableSpace (roots × Coordinate → Raw) := ⊤
  let : MeasurableSpace (roots → Coordinate → Raw) := ⊤
  exact (evalDist_bind_bijective_uniform_cross
    ($ᵗ (roots → Coordinate → Raw)) ($ᵗ (roots × Coordinate → Raw))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
    (Equiv.curry roots Coordinate Raw).symm (Equiv.curry roots Coordinate Raw).symm.bijective
    (fun table ↦ pure (evalWithAnswerFn
      (QueryImpl.ofFn (Function.uncurry (extendTable roots (Function.curry table))))
      program))).symm

/-- Equality of full ordered primitive query/answer histories, including repeats and off-path
queries. A caller may return source events or extraction checkpoints in `α` too. -/
theorem adaptive_logged_exact {α : Type}
    (program : OracleComp ((Root × Coordinate) →ₒ Raw) α) :
    let observed := (simulateQ loggingOracle program).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (simulator.translate observed ())).run' ∅ := by
  let : MeasurableSpace (α × QueryLog ((Root × Coordinate) →ₒ Raw)) := ⊤
  exact EvalDistEq.of_evalDist_eq (adaptive_exact ((simulateQ loggingOracle program).run))

/-- Private randomness drawn before the adaptive interaction is preserved too. -/
theorem adaptive_mixture_exact {α : Type}
    (programs : ProbComp (OracleComp ((Root × Coordinate) →ₒ Raw) α)) :
    (do let program ← programs; (simulateQ randomOracle program).run' ∅) =ᵈ
      (do let program ← programs;
          (simulateQ randomOracle (simulator.translate program ())).run' ∅) := by
  let : MeasurableSpace α := ⊤
  exact EvalDistEq.bind_right programs fun program ↦
    EvalDistEq.of_evalDist_eq (adaptive_exact program)

/-- Interleaved private uniform sampling is exactly converted to an outer mixture before
applying the existing provider translation. Private draws may depend on preceding replies;
no fixed tape or nonadaptive-query hypothesis is assumed. -/
theorem adaptive_interleaved_exact {α : Type}
    (program : OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α) :
    (simulateQ (unifSpec.passthrough + randomOracle) program).run' ∅ =ᵈ
      (do let fixed ← privatePrograms program
          (simulateQ randomOracle (simulator.translate fixed ())).run' ∅) := by
  let : MeasurableSpace (α × ((Root × Coordinate) →ₒ Raw).QueryCache) := ⊤
  have joint := EvalDistEq.of_evalDist_eq (privatePrograms_stateful randomOracle program ∅)
  have output := joint.map Prod.fst
  simp only [map_bind, ← StateT.run'_eq] at output
  exact output.trans (adaptive_mixture_exact (privatePrograms program))

/-- Observe every primitive query and reply, in order, while forwarding private draws.
The log includes cache hits and excludes the independent private sampling operations. -/
def logInterleaved {α : Type}
    (program : OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α) :
    OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw))
      (α × QueryLog ((Root × Coordinate) →ₒ Raw)) :=
  (simulateQ (unifSpec.passthrough +
    QueryImpl.withLogging (spec := (Root × Coordinate) →ₒ Raw)
      (fun key ↦ (liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inr key)) :
        OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) Raw))) program).run

omit [DecidableEq Root] [Fintype Coordinate] [DecidableEq Coordinate] [SampleableType Raw] in
@[simp] theorem logInterleaved_pure {α : Type} (value : α) :
    logInterleaved (pure value : OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α) =
      pure (value, []) := rfl

omit [DecidableEq Root] [Fintype Coordinate] [DecidableEq Coordinate] [SampleableType Raw] in
@[simp] theorem logInterleaved_uniform_bind {α : Type} (bound : ℕ)
    (next : Fin (bound + 1) → OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α) :
    logInterleaved
        (liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inl bound)) >>= next) =
      liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inl bound)) >>=
        fun reply ↦ logInterleaved (next reply) := by
  unfold logInterleaved
  rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
  change ((fun reply ↦ (reply, [])) <$>
    liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inl bound))) >>= _ = _
  simp only [bind_map_left, List.nil_append, Prod.mk.eta]
  apply bind_congr
  intro reply
  exact id_map _

omit [DecidableEq Root] [Fintype Coordinate] [DecidableEq Coordinate] [SampleableType Raw] in
@[simp] theorem logInterleaved_oracle_bind {α : Type} (key : Root × Coordinate)
    (next : Raw → OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α) :
    logInterleaved
        (liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inr key)) >>= next) =
      liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inr key)) >>=
        fun reply ↦ (fun result ↦ (result.1, ⟨key, reply⟩ :: result.2)) <$>
          logInterleaved (next reply) := by
  simp [logInterleaved]

omit [Fintype Coordinate] in
/-- Observing before interpretation gives the usual logged lazy-oracle execution, including
its final cache. Private samples are passed through and never cached or logged. -/
theorem logInterleaved_randomOracle {α : Type}
    (program : OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α)
    (cache : ((Root × Coordinate) →ₒ Raw).QueryCache) :
    (simulateQ (unifSpec.passthrough + randomOracle) (logInterleaved program)).run cache =
      ((simulateQ (unifSpec.passthrough + randomOracle.withLogging) program).run).run cache := by
  let outer : QueryImpl (unifSpec + ((Root × Coordinate) →ₒ Raw))
      (StateT ((Root × Coordinate) →ₒ Raw).QueryCache ProbComp) :=
    unifSpec.passthrough + randomOracle
  let inner : QueryImpl (unifSpec + ((Root × Coordinate) →ₒ Raw))
      (WriterT (QueryLog ((Root × Coordinate) →ₒ Raw))
        (OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)))) :=
    unifSpec.passthrough +
      QueryImpl.withLogging (spec := (Root × Coordinate) →ₒ Raw)
        (fun key ↦ (liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inr key)) :
          OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) Raw))
  have handlers : outer.writerTMapBase inner =
      unifSpec.passthrough + randomOracle.withLogging := by
    funext call
    cases call with
    | inl bound =>
        apply WriterT.ext
        change simulateQ outer ((fun reply ↦ (reply, [])) <$>
          liftM ((unifSpec + ((Root × Coordinate) →ₒ Raw)).query (.inl bound))) = _
        rw [simulateQ_map, simulateQ_spec_query]
        rfl
    | inr key =>
        apply WriterT.ext
        simp [QueryImpl.writerTMapBase, outer, inner]
  change (simulateQ outer ((simulateQ inner program).run)).run cache = _
  rw [QueryImpl.simulateQ_writerTMapBase_run, handlers]

/-- Joint output and full ordered primitive-log equality with arbitrary interleaved private
sampling, arbitrary roots, and the unchanged provider simulator on each outer-mixture program. -/
theorem adaptive_interleaved_logged_exact {α : Type}
    (program : OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α) :
    let observed := logInterleaved program
    (simulateQ (unifSpec.passthrough + randomOracle) observed).run' ∅ =ᵈ
      (do let fixed ← privatePrograms observed
          (simulateQ randomOracle (simulator.translate fixed ())).run' ∅) :=
  adaptive_interleaved_exact (logInterleaved program)

omit [Fintype Coordinate] [DecidableEq Coordinate] in
/-- Conservative one-macro-query-per-primitive-query budget. -/
theorem translate_budget {Family α : Type} [Fintype Family] [DecidableEq Family]
    (family : Root × Coordinate → Family)
    (program : OracleComp ((Root × Coordinate) →ₒ Raw) α) (budget : Budget Family)
    (bounded : FamilyQueryBound family program budget) :
    IsTotalQueryBound (simulator.translate program ()) (∑ kind, budget kind) := by
  have bound := simulator.translate_queryBound family (fun _ ↦ True)
    (fun _ _ _ _ ↦ trivial) program budget bounded ()
  simpa [chargedBudget] using bound

omit [Fintype Coordinate] [DecidableEq Coordinate] in
/-- Interleaved private draws do not increase the primitive family budget. Every fixed
program sampled by the outer mixture inherits the same conservative macro-query bound. -/
theorem privatePrograms_translate_budget {Family α : Type}
    [Fintype Family] [DecidableEq Family]
    (family : Root × Coordinate → Family)
    (program : OracleComp (unifSpec + ((Root × Coordinate) →ₒ Raw)) α)
    (budget : Budget Family)
    (bounded : IsQueryBound program budget
      (Sum.elim (fun _ _ ↦ True) (fun query remaining ↦ 0 < remaining (family query)))
      (Sum.elim (fun _ remaining ↦ remaining) (fun query remaining ↦
        Function.update remaining (family query) (remaining (family query) - 1))))
    {fixed : OracleComp ((Root × Coordinate) →ₒ Raw) α}
    (sampled : fixed ∈ support (privatePrograms program)) :
    IsTotalQueryBound (simulator.translate fixed ()) (∑ kind, budget kind) :=
  translate_budget family fixed budget
    (privatePrograms_queryBound program _ _ bounded sampled)

/-- Failure probability of an arbitrary complete primitive experiment. Any verifier work in
this program is included; separating prover/verifier budgets is a consumer obligation. -/
noncomputable def concreteEvent {α ExecBound : Type} (event : α → Prop)
    (program : OracleComp ((Root × Coordinate) →ₒ Raw) α) (_ : ExecBound) : ENNReal :=
  Pr{let value ← (simulateQ randomOracle program).run' ∅}[event value]

/-- The same returned event for a mixture of macro-oracle programs. -/
noncomputable def idealEvent {α ExecBound : Type} (event : α → Prop)
    (programs : ProbComp (OracleComp (Root →ₒ (Coordinate → Raw)) α))
    (_ : ExecBound) : ENNReal :=
  Pr{let program ← programs; let value ← (simulateQ randomOracle program).run' ∅}[event value]

/-- Exact typed grouping packaged for the existing provider simulation/weighted-budget API.
Loss is zero, cost is the sum of primitive family budgets. This packages a complete program;
it does not supply the source verifier's separate execution bound or checkpoint relation. -/
noncomputable def groupingSimulation {Family α ExecBound : Type}
    [Fintype Family] [DecidableEq Family] (family : Root × Coordinate → Family)
    (event : α → Prop) (expansion : ExecBound → ℕ) :
    Provider.Simulation ((Root × Coordinate) →ₒ Raw) family
      (fun _ : Root ↦ Coordinate → Raw)
      (concreteEvent (ExecBound := ExecBound) event)
      (idealEvent (ExecBound := ExecBound) event) where
  Tape _ := Unit
  tapeSampleable _ := inferInstance
  simulator _ := simulator
  charged _ := True
  chargedDecidable _ := inferInstance
  carries _ _ _ _ _ := trivial
  queryCost := {
    cost := fun budget ↦ ∑ kind, budget kind
    monotone := fun _ _ bounded ↦ Finset.sum_le_sum fun kind _ ↦ bounded kind
    expansion := expansion
    loss := fun _ _ ↦ 0 }
  covers budget := by simp [chargedBudget]
  bound program _ _ _ := by
    let : MeasurableSpace α := ⊤
    have equality := (EvalDistEq.of_evalDist_eq (adaptive_exact program)).prEvent_eq event
    have constant : (fun tape : Unit ↦
        (simulateQ randomOracle (simulator.translate program tape)).run' ∅) =
        fun _ : Unit ↦ (simulateQ randomOracle (simulator.translate program ())).run' ∅ := by
      funext tape
      cases tape
      rfl
    have mixture : 𝒟[($ᵗ Unit : ProbComp Unit) >>= fun tape ↦
        (simulateQ randomOracle (simulator.translate program tape)).run' ∅] =
        𝒟[(simulateQ randomOracle (simulator.translate program ())).run' ∅] := by
      rw [constant]
      exact OracleComp.evalDist_bind_const _ _
    simpa only [concreteEvent, idealEvent, bind_assoc, pure_bind, add_zero, prEvent_norm] using
      (equality.trans ((EvalDistEq.of_evalDist_eq mixture).prEvent_eq event).symm).le

/-- A verifier's *logical* macro access remains logged when the tree is already cached.
Use this handler (or an established equivalent) for verifier accesses; `simulator.handle`
only logs macro allocations and therefore cannot establish verifier log membership alone. -/
theorem verifier_cache_hit_logged
    (cache : (Root →ₒ (Coordinate → Raw)).QueryCache)
    (root : Root) (tree : Coordinate → Raw)
    (cached : cache root = some tree) :
    ((randomOracle.withLogging root).run).run cache =
      (pure ((tree, [⟨root, tree⟩]), cache) :
        ProbComp (((Coordinate → Raw) × QueryLog (Root →ₒ (Coordinate → Raw))) ×
          (Root →ₒ (Coordinate → Raw)).QueryCache)) := by
  rw [QueryImpl.run_withLogging_apply, StateT.run_bind,
    QueryImpl.withCaching_run_some _ cached]
  rfl

end Distribution

end ZkcSecurity.FiatShamir.QueryTree
