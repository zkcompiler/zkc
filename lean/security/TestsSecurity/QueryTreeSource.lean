import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Verifier
import ZkcSecurity.Bindings.Transcript.ServiceSampling
import ZkcTools.DeclarationAudit

/-! Controls for authenticated typed keys, suffix exposure, repeated cache accesses,
primitive budgets and the verifier's own macro call. -/
set_option autoImplicit false
namespace TestsSecurity.QueryTreeSource
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir
open QueryTreeSource QueryTree OracleComp OracleSpec Provider
abbrev carriers := Structured.uniformCarriers (Fin 2) Unit
abbrev Bit := Fin 2
abbrev Node3 := Node Bit 3
def context : Context := .fiatShamir "source" ["prover", "verifier"] 0 1 5
  "random.scalar/0" (some (.sampleIndex 2)) "typed-suite" [("query", "delivery")]
def segment : Segment := ⟨context.query "query" (.sampleIndex 2),
  context.message "delivery" 1 0, [4]⟩
def rootNode : Node3 := .inl ()
def childNode (first : Bit) : Node3 := .inr (first, .inl ())
def suffixNode (first second : Bit) : Node3 := .inr (first, .inr (second, .inl ()))
def key (history : Domain.History carriers) (node : Node3) : ScalarKey carriers 2 :=
  ⟨encode segment (history, node), rfl⟩
/-- A well-addressed query still refuses a malformed predecessor. -/
def childAccepts (history : Domain.History carriers) : Bool :=
  (parse (bound := 2) (height := 3) segment (history, segment.queryAt 1)).isSome

#guard childAccepts [.challenge (segment.queryAt 0), .message (segment.deliveryAt 0) (.index 1)]
#guard !childAccepts [.challenge (segment.queryAt 1), .message (segment.deliveryAt 0) (.index 1)]
#guard !childAccepts [.challenge (segment.queryAt 0), .message (segment.deliveryAt 1) (.index 1)]
#guard !childAccepts [.challenge (segment.queryAt 0), .message (segment.deliveryAt 0) (.index 2)]
#guard !childAccepts [.challenge (segment.queryAt 0), .message (segment.deliveryAt 0) (.boolean true)]
#guard !childAccepts [.challenge (segment.queryAt 0)]

noncomputable instance (α : Type) : DecidableEq α := Classical.decEq α
noncomputable instance rawSampleable (event : Domain.Event carriers) :
    SampleableType (Domain.Raw event) := ServiceSampling.raw carriers (fun _ ↦ inferInstance) event

theorem located_key (history : Domain.History carriers) (node : Node3) :
    locate (height := 3) segment (key history node) = (.inl history, .inl node) :=
  locate_encode segment rfl _

theorem complete_key_roundtrip (history : Domain.History carriers) (node : Node3) :
    parse segment (encode segment (history, node)) = some (history, node) :=
  parse_encode segment _

theorem distinct_scalar_keys (history : Domain.History carriers) :
    key history rootNode ≠ key history (childNode 0) ∧
      key history (childNode 0) ≠ key history (suffixNode 0 0) := by
  constructor <;> intro same
  all_goals
    have nodes := congrArg Prod.snd (encode_injective segment (congrArg Subtype.val same))
    cases nodes

theorem separated_roots (first second : Domain.History carriers) (different : first ≠ second)
    (left right : Node3) : key first left ≠ key second right := by
  intro same
  exact different (congrArg Prod.fst (encode_injective segment (congrArg Subtype.val same)))

def omitPayloads (history : Domain.History carriers) (node : Node3) : Key carriers :=
  let original := encode segment (history, node)
  (original.1.map (fun event ↦ match event with
    | .message origin _ => .message origin (.index 0)
    | other => other), original.2)

/-- Dropping delivery payloads collapses two different actual successor keys while retaining
the ordered event tags and the complete message/query origins. -/
theorem omitted_payload_invalid (history : Domain.History carriers) :
    encode segment (history, childNode 0) ≠ encode segment (history, childNode 1) ∧
      omitPayloads history (childNode 0) = omitPayloads history (childNode 1) := by
  constructor
  · intro same
    have nodes := congrArg Prod.snd (encode_injective segment same)
    have values : (0 : Bit) = 1 := congrArg Prod.fst (Sum.inr.inj nodes)
    exact (by decide : (0 : Bit) ≠ 1) values
  · simp only [omitPayloads, encode, nodePrefix, childNode, events, List.map_append,
      List.map_cons, List.map_nil, List.length_singleton]

theorem scalar_block_nonidentification (history : Domain.History carriers) :
    (encode segment (history, rootNode)).2 ≠
      Domain.atCoordinates (context.query "query" (.sampleIndices 2 3)) [4, 0] := by
  intro same
  have requests := congrArg Origin.request same
  change some (Request.sampleIndex 2) = some (.sampleIndices 2 3) at requests
  exact (by decide : Request.sampleIndex 2 ≠ Request.sampleIndices 2 3) (Option.some.inj requests)

def outside : ScalarKey carriers 2 :=
  ⟨([], .query "outside" "query" "input_5" "random.scalar/0" "verifier" (.sampleIndex 2)), rfl⟩

theorem outside_unparsed : parse (height := 3) (bound := 2) segment outside.val = none := by
  cases parsed : parse (height := 3) (bound := 2) segment outside.val with
  | none => rfl
  | some pair =>
    have encoded := encode_parse segment outside.val pair parsed
    have entries := congrArg (fun key : Key carriers ↦ key.2.entry) encoded
    simp [encode, Segment.queryAt, Domain.atCoordinates, segment, context, Context.query,
      outside] at entries
    change "source" = "outside" at entries
    exact False.elim ((by decide : ("source" : String) ≠ "outside") entries)

theorem outside_preserved : locate (height := 3) segment outside = (.inr outside, .inr ()) := by
  simp only [locate, outside_unparsed]

def suffixFirst (history : Domain.History carriers) :
    OracleComp ((ScalarKey carriers 2) →ₒ Bit) (Bit × Bit × Bit) := do
  let suffix ← ((ScalarKey carriers 2) →ₒ Bit).query (key history (suffixNode 1 0))
  let repeated ← ((ScalarKey carriers 2) →ₒ Bit).query (key history (suffixNode 1 0))
  let parent ← ((ScalarKey carriers 2) →ₒ Bit).query (key history rootNode)
  pure (suffix, repeated, parent)

theorem complete_typed_experiment (history : Domain.History carriers) :
    let observed := (simulateQ loggingOracle (suffixFirst history)).run
    (simulateQ randomOracle (typedRenaming.translate observed)).run' ∅ =ᵈ
      (simulateQ randomOracle (translate (height := 3) segment observed)).run' ∅ :=
  typed_source_logged segment _

theorem suffix_first_trace (history : Domain.History carriers)
    (table : Root carriers 2 → Coordinate 2 3 → Bit) :
    evalWithAnswerFn (QueryImpl.ofFn table)
      (translate (height := 3) segment (simulateQ loggingOracle (suffixFirst history)).run) =
      ((table (.inl history) (.inl (suffixNode 1 0)),
        table (.inl history) (.inl (suffixNode 1 0)), table (.inl history) (.inl rootNode)),
        [⟨key history (suffixNode 1 0), table (.inl history) (.inl (suffixNode 1 0))⟩,
          ⟨key history (suffixNode 1 0), table (.inl history) (.inl (suffixNode 1 0))⟩,
          ⟨key history rootNode, table (.inl history) (.inl rootNode)⟩]) := by
  rw [translate, translate_table, RandomOracleRouting.evalWithAnswerFn_route]
  simp [suffixFirst, loggingOracle, evalWithAnswerFn_map, located_key]

theorem primitive_budget_three (history : Domain.History carriers) :
    FamilyQueryBound (fun _ : ScalarKey carriers 2 ↦ ()) (suffixFirst history)
      (fun _ : Unit ↦ 3) := by
  simp [suffixFirst, FamilyQueryBound, isQueryBound_query_bind_iff]

theorem primitive_budget_two_refused (history : Domain.History carriers) :
    ¬ FamilyQueryBound (fun _ : ScalarKey carriers 2 ↦ ()) (suffixFirst history)
      (fun _ : Unit ↦ 2) := by
  simp [suffixFirst, FamilyQueryBound, isQueryBound_query_bind_iff]

theorem macro_budget_three (history : Domain.History carriers) :
    IsTotalQueryBound (translate (height := 3) segment (suffixFirst history)) 3 := by
  simpa only [Finset.univ_unique, Finset.sum_singleton] using source_budget segment
    (fun _ : Root carriers 2 × Coordinate 2 3 ↦ ()) (suffixFirst history)
    (fun _ : Unit ↦ 3) (primitive_budget_three history)

def outsideRepeats (history : Domain.History carriers) :
    OracleComp ((ScalarKey carriers 2) →ₒ Bit) Bit := do
  let _ ← ((ScalarKey carriers 2) →ₒ Bit).query outside
  let _ ← ((ScalarKey carriers 2) →ₒ Bit).query outside
  liftM (((ScalarKey carriers 2) →ₒ Bit).query (key history (suffixNode 1 0)))

theorem outside_repeats_counted (history : Domain.History carriers) :
    FamilyQueryBound (fun _ : ScalarKey carriers 2 ↦ ()) (outsideRepeats history)
      (fun _ : Unit ↦ 3) ∧
    ¬ FamilyQueryBound (fun _ : ScalarKey carriers 2 ↦ ()) (outsideRepeats history)
      (fun _ : Unit ↦ 2) := by
  simp [outsideRepeats, FamilyQueryBound, isQueryBound_query_bind_iff, isQueryBound_query_iff]

theorem suffix_first_checkpoint (history : Domain.History carriers) :
    (simulator.handle (locate (height := 3) segment (key history (suffixNode 1 0)))).run
      ((simulator (Root := Root carriers 2) (Coordinate := Coordinate 2 3)
        (Raw := Bit)).start ()) =
      (fun tree ↦ (tree (.inl (suffixNode 1 0)),
        simulator.record (simulator.start ()) (.inl history) tree)) <$>
        liftM (((Root carriers 2) →ₒ (Coordinate 2 3 → Bit)).query (.inl history)) :=
  source_checkpoint segment rfl history (suffixNode 1 0) Provider.Simulator.Runs.start (by simp)

theorem verifier_log_after_prover (history : Domain.History carriers)
    (tree : Coordinate 2 3 → Bit) :
    ((randomOracle.withLogging (.inl history)).run).run
      ((∅ : ((Root carriers 2) →ₒ (Coordinate 2 3 → Bit)).QueryCache).cacheQuery
        (.inl history) tree) =
      pure ((tree, [⟨.inl history, tree⟩]),
        (∅ : ((Root carriers 2) →ₒ (Coordinate 2 3 → Bit)).QueryCache).cacheQuery
          (.inl history) tree) := by
  apply verifier_cached
  exact QueryCache.cacheQuery_self _ _ _

/-- The consumer's actual verifier operation has a logical root call of its own. -/
theorem verifier_operation_log (history : Domain.History carriers)
    (table : Root carriers 2 → Coordinate 2 3 → Bit) :
    evalWithAnswerFn (QueryImpl.ofFn table)
      (simulateQ loggingOracle (verifierAsk (height := 3) segment (key history rootNode))).run =
        (table (.inl history) (.inl rootNode), [⟨.inl history, table (.inl history)⟩]) := by
  simp [verifierAsk, loggingOracle, evalWithAnswerFn_map, located_key]

theorem actual_prover_verifier (history : Domain.History carriers) :
    (simulateQ randomOracle (typedRenaming.translate (suffixFirst history >>= fun _ ↦
      liftM (((ScalarKey carriers 2) →ₒ Bit).query (key history rootNode))))).run' ∅ =ᵈ
      (simulateQ randomOracle (withVerifier (height := 3) segment (suffixFirst history)
        (fun _ ↦ liftM (((ScalarKey carriers 2) →ₒ Bit).query (key history rootNode))))).run' ∅ :=
  typed_withVerifier_exact segment _ _

end TestsSecurity.QueryTreeSource

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcSecurity.Bindings.Transcript.QueryTreeSource.Keys,
      `ZkcSecurity.Bindings.Transcript.QueryTreeSource.Reading,
      `ZkcSecurity.Bindings.Transcript.QueryTreeSource.Simulation,
      `ZkcSecurity.Bindings.Transcript.QueryTreeSource.Adapter,
      `ZkcSecurity.Bindings.Transcript.QueryTreeSource.Typed,
      `ZkcSecurity.Bindings.Transcript.QueryTreeSource.Verifier] "QUERY-TREE-SOURCE-AXIOMS-PASS"
run_cmd ZkcTools.DeclarationAudit.checkCurrent "QUERY-TREE-SOURCE-CONTROLS-AXIOMS-PASS"
