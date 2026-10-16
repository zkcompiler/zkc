import Zkc.Source.Structured.ClosedProjection

/-! Independent controls of retained protocol application semantics. Most use
hand-built typed bodies; ClosedSelection additionally checks a complete synthetic
source unit. None asserts native refinement or a security result. -/

set_option autoImplicit false
namespace Tests.StructuredApplicationSemantics
open Zkc.Source Zkc.Source.Structured

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev service : Ty := .service "random.bls12-381.fr/0"

private def checked (signature : ProtocolSignature)
    (body : Region protocolDialect signature.inputs signature.outputs) : CheckedProtocol where
  toProtocolSignature := signature
  raw := body.erase
  body := body
  formed := body.elaborate_erase

private def leafSignature : ProtocolSignature :=
  ⟨"Leaf", ["sender", "receiver"], [scalar], [scalar], [[0, 1]], [[0, 1]]⟩
private def leafBody : Region protocolDialect [scalar] [scalar] :=
  .letOp (.exchange scalar 0 1 "C") (.cons .here .nil) .nil (.ret (.cons .here .nil))
private def leaf : CheckedProtocol := checked leafSignature leafBody

private def middleSignature : ProtocolSignature :=
  ⟨"Middle", ["a", "b", "c"], [scalar], [scalar], [[0, 1, 2]], [[0, 2]]⟩
private def middle : CheckedProtocol := checked middleSignature
  (.letOp (.protocolApply leafSignature [2, 0] "B") (.cons .here .nil) .nil
    (.ret (.cons .here .nil)))

private def rootSignature : ProtocolSignature :=
  ⟨"Root", ["r0", "r1", "r2", "r3"], [scalar], [scalar], [[0, 1, 2, 3]], [[2, 3]]⟩
private def root : CheckedProtocol := checked rootSignature
  (.letOp (.protocolApply middleSignature [2, 0, 3] "A") (.cons .here .nil) .nil
    (.ret (.cons .here .nil)))

variable (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private def protocols : ProtocolTable (assignment F G) (observedInterface F G) :=
  [leaf, middle, root].foldl (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩) []

/-- Two proper-subset injections are not involutions; root self is unchanged. -/
theorem nested_receiver (copy : Option F) :
    (invokeProtocol (protocols F G) rootSignature {} 2 (.cons copy .nil)).interpret forgetSites =
      .call (.receive scalar "apply_11_apply_1_A_B_C" 3)
        (fun received => .done (.cons (some received) .nil)) := rfl

theorem nested_sender (sent : F) :
    (invokeProtocol (protocols F G) rootSignature {} 3 (.cons (some sent) .nil)).interpret forgetSites =
      .call (Participant.Action.send (ty := scalar) "apply_11_apply_1_A_B_C" 2 sent)
        (fun _ => .done (.cons (some sent) .nil)) := rfl

theorem nested_outsider (copy : Option F) :
    invokeProtocol (protocols F G) rootSignature {} 1 (.cons copy .nil) =
      .done (.cons none .nil) := rfl

theorem middle_outside_leaf (copy : Option F) :
    invokeProtocol (protocols F G) rootSignature {} 0 (.cons copy .nil) =
      .done (.cons none .nil) := rfl

theorem nested_coordinates :
    let context := (({} : ProtocolContext).enter "A" [2, 0, 3]).enter "B" [2, 0]
    context.roles 0 = 3 ∧ context.roles 1 = 2 := by decide +kernel

theorem nested_qualification :
    qualifyProtocolSite (some (qualifyProtocolSite (some "A") "B")) "C" =
      "apply_11_apply_1_A_B_C" := by decide +kernel

theorem qualification_not_right_nested :
    qualifyProtocolSite (some (qualifyProtocolSite (some "A") "B")) "C" ≠
      qualifyProtocolSite (some "A") (qualifyProtocolSite (some "B") "C") := by decide +kernel

/-- This tests the logical renderer, not admission's ASCII identifier profile. -/
theorem utf8_qualification :
    qualifyProtocolSite (some "λ") "x" = "apply_2_λ_x" ∧
    qualifyProtocolSite (some "한") "x" = "apply_3_한_x" := by decide +kernel

theorem empty_mark_is_empty :
    protocolOperation (F := F) (G := G) ⟨[], []⟩ 2 (.mark "") .nil .nil []
      ⟨some "previous", id⟩ = .call (.mark "") (fun _ => .done .nil) := rfl

private def querySignature : ProtocolSignature :=
  ⟨"Query", ["owner"], [service], [scalar], [[0]], [[0]]⟩
private def query : CheckedProtocol := checked querySignature
  (.letOp (.draw 0 "bls12-381.fr" "C") (.cons .here .nil) .nil (.ret (.cons .here .nil)))

private def firstSite {IValue : Ty → Type} {A : Type} :
    PIR.Proc (Participant.interface Nat Ty services IValue) A → Option String
  | .call (.query site _ _) _ => some site
  | .call (.send site _ _) _ => some site
  | .call (.receive _ site _) _ => some site
  | _ => none

/-- Removing internal marks does not erase a qualified provider action label. -/
theorem false_forgetSites_prefix_erasure (handle : Nat) :
    query.participant (F := F) (G := G) ⟨[], []⟩ 0 (.cons (some handle) .nil) []
        ⟨some (qualifyProtocolSite (some "A") "B"), id⟩ ≠
      query.participant ⟨[], []⟩ 0 (.cons (some handle) .nil) := by
  intro equal
  have sites := congrArg firstSite equal
  change some "apply_11_apply_1_A_B_C" = some "C" at sites
  exact (by decide +kernel : (some "apply_11_apply_1_A_B_C" : Option String) ≠ some "C") sites

private def zeroSignature : ProtocolSignature :=
  ⟨"Stop", ["owner"], [.boolean], [], [[0]], []⟩
private def zeroStop : CheckedProtocol := checked zeroSignature
  (.letOp (.guard 0 "guard") (.cons .here .nil) .nil (.ret .nil))
private def zeroTable : ProtocolTable (assignment F G) (observedInterface F G) :=
  extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] zeroStop

theorem reached_zero_result_stops :
    (protocolOperation (F := F) (G := G) ⟨[], []⟩ 2
      (.protocolApply zeroSignature [2] "stop") (.cons (some false) .nil) .nil
      (zeroTable F G)).bind (fun _ => .call (.mark "suffix") (fun _ => .done ())) =
      .halt .reject := rfl

theorem outside_zero_result_continues :
    (protocolOperation (F := F) (G := G) ⟨[], []⟩ 1
      (.protocolApply zeroSignature [2] "stop") (.cons (some false) .nil) .nil
      (zeroTable F G)).bind (fun _ => .call (.mark "suffix") (fun _ => .done ())) =
      .call (.mark "suffix") (fun _ => .done ()) := rfl

private def optionalSignature : ProtocolSignature :=
  ⟨"Optional", ["owner"], [scalar, scalar], [scalar], [[0], [0]], [[0]]⟩
private def optional : CheckedProtocol := checked optionalSignature
  (.ret (.cons .here .nil))

theorem missing_unused_protocol_input (value : F) :
    protocolOperation (F := F) (G := G) ⟨[], []⟩ 0
      (.protocolApply optionalSignature [0] "optional") (.cons (some value) (.cons none .nil)) .nil
      (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] optional) =
      .done (.cons (some value) .nil) := rfl

private def projectionBody : Region dialect [scalar, scalar] [scalar] :=
  .ret (.cons .here .nil)
private def projectionHelper : CheckedDefinition :=
  ⟨"projection", .math, [scalar, scalar], [scalar], projectionBody.erase,
    projectionBody, projectionBody.elaborate_erase⟩
private def mathCaller : CheckedProtocol := checked optionalSignature
  (.letOp (.calculate (.invoke projectionHelper.helper) rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))

/-- Optional protocol entry continues through a real Math helper with an unused input. -/
theorem missing_unused_math_input (value : F) :
    let helperTable := Evaluation.ComponentTables.extend (observedSites F G) ⟨[], []⟩ projectionHelper
    protocolOperation (F := F) (G := G) helperTable 0
      (.protocolApply optionalSignature [0] "optional") (.cons (some value) (.cons none .nil)) .nil
      (extendProtocolTable (observedSites F G) observeAction helperTable [] mathCaller) =
      .done (.cons (some value) .nil) := rfl

private def rawStopBody : Region dialect [] [] :=
  .letOp (.mark "helper_stop") .nil .nil (.stop .abort)
private def rawStop : CheckedDefinition :=
  ⟨"raw_stop", .local, [], [], rawStopBody.erase, rawStopBody, rawStopBody.elaborate_erase⟩
private def helpers : OpenTables F G :=
  Evaluation.ComponentTables.extend (observedSites F G) ⟨[], []⟩ rawStop
private def helperCallerSignature : ProtocolSignature :=
  ⟨"HelperCaller", ["owner"], [], [], [], []⟩
private def helperCaller : CheckedProtocol := checked helperCallerSignature
  (.letOp (.mark "local") .nil .nil
    (.letOp (.localCall rawStop.helper rfl 0 "local") .nil .nil (.ret .nil)))

theorem helper_stop_raw_under_prefix (prefixSite : String) :
    helperCaller.observed (helpers F G) 0 .nil [] ⟨some prefixSite, id⟩ =
      .call (.mark (qualifyProtocolSite (some prefixSite) "local"))
        (fun _ => .call (.mark "helper_stop") (fun _ => .halt .abort)) := rfl

private def maskedSignature : ProtocolSignature :=
  ⟨"Masked", ["left", "right"], [scalar, scalar], [scalar, scalar], [[0], [1]], [[0], [1]]⟩
private def masked : CheckedProtocol := checked maskedSignature
  (.ret (.cons .here (.cons (.there .here) .nil)))

theorem mapped_masks_full_order (left right : F) :
    masked.observed (F := F) (G := G) ⟨[], []⟩ 3 (.cons (some left) (.cons (some right) .nil)) []
      ⟨some "A", roleSubstitution [3, 1]⟩ = .done (.cons (some left) (.cons none .nil)) := rfl

/-- The same name and value ABI do not excuse an altered roster or scope. -/
theorem exact_scope_lookup_refuses (value : F) :
    invokeProtocol (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] optional)
      { optionalSignature with outputScopes := [[]] } {} 0 (.cons (some value) (.cons none .nil)) =
      .halt .refused := rfl

theorem exact_roster_lookup_refuses (value : F) :
    invokeProtocol (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] optional)
      { optionalSignature with roles := ["different"] } {} 0 (.cons (some value) (.cons none .nil)) =
      .halt .refused := rfl

/-- A later invocation receives its own immutable context even after a stop. -/
theorem independent_context_after_stop (value : F) :
    let stopped := helperCaller.observed (helpers F G) 0 .nil [] ⟨some "earlier", id⟩
    (stopped, optional.observed (F := F) (G := G) ⟨[], []⟩ 0 (.cons (some value) (.cons none .nil))) =
      (.call (.mark "apply_7_earlier_local") (fun _ => .call (.mark "helper_stop")
        (fun _ => .halt .abort)), .done (.cons (some value) .nil)) := rfl

private def scriptedReceiver : PIR.Handler (participantInterface F G) Nat (String × Nat)
  | .receive (.field _) site sender, state => ⟨.returned 19, state + 1, [(site, sender)]⟩
  | _, state => ⟨.stopped .refused, state, []⟩

/-- Scripted 19 is independent of the sender/local copy 7, including state/events. -/
theorem received_nineteen_not_seven :
    ((invokeProtocol (protocols F G) rootSignature {} 2 (.cons (some 7) .nil)).interpret
      forgetSites).run (scriptedReceiver F G) 0 =
      ⟨.returned (.cons (some 19) .nil), 1, [("apply_11_apply_1_A_B_C", 3)]⟩ := rfl

private def unusedLocalBody : Region dialect [scalar, scalar] [] := .ret .nil
private def unusedLocal : CheckedDefinition :=
  ⟨"unused_local", .local, [scalar, scalar], [], unusedLocalBody.erase,
    unusedLocalBody, unusedLocalBody.elaborate_erase⟩
private def strictSignature : ProtocolSignature :=
  ⟨"Strict", ["owner"], [scalar, scalar], [], [[0], [0]], []⟩
private def strictCaller : CheckedProtocol := checked strictSignature
  (.letOp (.mark "local") .nil .nil
    (.letOp (.localCall unusedLocal.helper rfl 0 "local")
      (.cons .here (.cons (.there .here) .nil)) .nil (.ret .nil)))

theorem missing_unused_local_input (value : F) (prefixSite : String) :
    strictCaller.observed
      (Evaluation.ComponentTables.extend (observedSites F G) ⟨[], []⟩ unusedLocal)
      0 (.cons (some value) (.cons none .nil)) [] ⟨some prefixSite, id⟩ =
      .call (.mark (qualifyProtocolSite (some prefixSite) "local"))
        (fun _ => .halt .incomplete) := rfl

private def zeroQuerySignature : ProtocolSignature :=
  ⟨"ZeroQuery", ["owner"], [service], [], [[0]], []⟩
private def zeroQuery : CheckedProtocol := checked zeroQuerySignature
  (.letOp (.draw 0 "bls12-381.fr" "query") (.cons .here .nil) .nil (.ret .nil))
private def stoppingProvider : PIR.Handler (observedInterface F G) Nat String
  | .mark site, state => ⟨.returned (), state, [site]⟩
  | .action (.query site _ _), state => ⟨.stopped .abort, state + 1, [site]⟩
  | .action _, state => ⟨.stopped .refused, state, []⟩

/-- The zero-output child retains prefix events and provider state; suffix is absent. -/
theorem zero_result_provider_stop_prefix :
    (PIR.Proc.call (I := observedInterface F G) (.mark "before") (fun _ =>
      (protocolOperation (F := F) (G := G) ⟨[], []⟩ 0
        (.protocolApply zeroQuerySignature [0] "A") (.cons (some 8) .nil) .nil
        (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] zeroQuery)).bind
        (fun _ => .call (.mark "suffix") (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))))).run (stoppingProvider F G) 10 =
      ⟨.stopped .abort, 11, ["before", "apply_1_A_query"]⟩ := rfl

/-- The protocol callback carrier uses optional values even in a future loop shape. -/
private def optionalCallback : Regions protocolDialect [([.index, scalar], [scalar])] :=
  .cons (.ret (.cons (.there .here) .nil)) .nil

theorem callback_keeps_optional_component (value : Option F) :
    (optionalCallback.denote (participantMeaning (F := F) (G := G) ⟨[], []⟩ 0)).get .here
      (.cons none (.cons value .nil)) = .done (.cons value .nil) := rfl

private def privateInputSignature : ProtocolSignature :=
  ⟨"PrivateInput", ["left", "right"], [scalar], [scalar], [[0]], [[0, 1]]⟩
private def privateInput : CheckedProtocol := checked privateInputSignature (.ret (.cons .here .nil))

theorem supplied_unexposed_input_cannot_flow (value : F) :
    protocolOperation (F := F) (G := G) ⟨[], []⟩ 1
      (.protocolApply privateInputSignature [3, 1] "private") (.cons (some value) .nil) .nil
      (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] privateInput) =
      .done (.cons none .nil) := rfl

private def emptyAfterQuery : CheckedProtocol := checked zeroQuerySignature
  (.letOp (.draw 0 "bls12-381.fr" "query") (.cons .here .nil) .nil
    (.letOp (.mark "") .nil .nil (.stop .abort)))
private def recordingProvider : PIR.Handler (observedInterface F G) Nat String
  | .mark site, state => ⟨.returned (), state, [site]⟩
  | .action (.query site _ _), state => ⟨.returned (show F from 11), state + 1, [site]⟩
  | .action _, state => ⟨.stopped .refused, state, []⟩

theorem empty_mark_after_request_keeps_state :
    (emptyAfterQuery.observed (F := F) (G := G) ⟨[], []⟩ 0 (.cons (some 4) .nil) []
      ⟨some "A", id⟩).run (recordingProvider F G) 10 =
      ⟨.stopped .abort, 11, ["apply_1_A_query", ""]⟩ := rfl

theorem exact_scope_order_lookup_refuses (value : F) :
    invokeProtocol (protocols F G) { leafSignature with inputScopes := [[1, 0]] }
      {} 0 (.cons (some value) .nil) = .halt .refused := rfl

/-- Outside skip does not consult even a stopping zero-arity helper body. -/
theorem outside_zero_arity_helper_stops_skipped :
    (protocolOperation (helpers F G) 1 (.protocolApply helperCallerSignature [2] "outside")
      .nil .nil (extendProtocolTable (observedSites F G) observeAction (helpers F G) [] helperCaller)).bind
      (fun _ => .call (.mark "suffix") (fun _ => .done ())) =
      .call (.mark "suffix") (fun _ => .done ()) := rfl

private def constantChildSignature : ProtocolSignature :=
  ⟨"ConstantChild", ["owner"], [], [], [], []⟩
private def constantChild : CheckedProtocol := checked constantChildSignature
  (.letOp (.mark "constant") .nil .nil
    (.letOp (.calculate (.fieldConstant "bls12-381.fr" 9) rfl) .nil .nil
      (.letOp (.calculate (.invoke projectionHelper.helper) rfl)
        (.cons .here (.cons .here .nil)) .nil
        (.letOp (.calculate (.booleanConstant false) rfl) .nil .nil
          (.letOp (.guard 0 "guard") (.cons .here .nil) .nil (.ret .nil))))))

/-- Outside skip includes zero-input/zero-output constants, Math work and a guard. -/
theorem outside_constants_math_and_guard_skipped :
    let helperTable := Evaluation.ComponentTables.extend (observedSites F G) ⟨[], []⟩ projectionHelper
    (protocolOperation helperTable 1 (.protocolApply constantChildSignature [2] "outside")
      .nil .nil (extendProtocolTable (observedSites F G) observeAction helperTable [] constantChild)).bind
      (fun _ => .call (.mark "suffix") (fun _ => .done ())) =
      .call (.mark "suffix") (fun _ => .done ()) := rfl

/-- Inside reaches the false guard after the constant and Math projection.
This hand-built body contains exactly its authored constant mark. -/
theorem inside_constants_math_and_guard_reject :
    let helperTable := Evaluation.ComponentTables.extend (observedSites F G) ⟨[], []⟩ projectionHelper
    (protocolOperation helperTable 2 (.protocolApply constantChildSignature [2] "outside")
      .nil .nil (extendProtocolTable (observedSites F G) observeAction helperTable [] constantChild)).bind
      (fun _ => .call (.mark "suffix") (fun _ => .done ())) =
      .call (.mark "apply_7_outside_constant") (fun _ => .halt .reject) := rfl

theorem inside_constants_math_and_guard_run (initial : Nat) :
    let helperTable := Evaluation.ComponentTables.extend (observedSites F G) ⟨[], []⟩ projectionHelper
    ((protocolOperation helperTable 2 (.protocolApply constantChildSignature [2] "outside")
      .nil .nil (extendProtocolTable (observedSites F G) observeAction helperTable [] constantChild)).bind
      (fun _ => .call (.mark "suffix") (fun _ => .done ()))).run (recordingProvider F G) initial =
      ⟨.stopped .reject, initial, ["apply_7_outside_constant"]⟩ := by
  exact congrArg (fun process => process.run (recordingProvider F G) initial)
    (inside_constants_math_and_guard_reject F G)

private def markedZeroQuery : CheckedProtocol := checked zeroQuerySignature
  (.letOp (.mark "query") .nil .nil
    (.letOp (.draw 0 "bls12-381.fr" "query") (.cons .here .nil) .nil
      (.letOp (.mark "stop") .nil .nil (.stop .abort))))

/-- Generic execution propagation is usable with marks and a successful request
before the child's halt, for an arbitrary caller continuation. -/
theorem marked_child_apply_run_stops {A : Type} (initial : Nat)
    (next : Values (Component (assignment F G)) [] → PIR.Proc (observedInterface F G) A) :
    ((protocolOperation (F := F) (G := G) ⟨[], []⟩ 0
      (.protocolApply zeroQuerySignature [0] "A") (.cons (some 8) .nil) .nil
      (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] markedZeroQuery)).bind
      next).run (recordingProvider F G) initial =
      ⟨.stopped .abort, initial + 1,
        ["apply_1_A_query", "apply_1_A_query", "apply_1_A_stop"]⟩ := by
  exact apply_run_stops (observedSites F G) observeAction ⟨[], []⟩
    (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] markedZeroQuery)
    zeroQuerySignature [0] "A" {} 0 (.cons (some 8) .nil) rfl
    (recordingProvider F G) initial (initial + 1)
    ["apply_1_A_query", "apply_1_A_query", "apply_1_A_stop"] .abort rfl next

/-- A provider stop retains both the preceding mark and its own event; the
child's later stop mark and every caller suffix are absent. -/
theorem marked_child_provider_run_stops {A : Type} (initial : Nat)
    (next : Values (Component (assignment F G)) [] → PIR.Proc (observedInterface F G) A) :
    ((protocolOperation (F := F) (G := G) ⟨[], []⟩ 0
      (.protocolApply zeroQuerySignature [0] "A") (.cons (some 8) .nil) .nil
      (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] markedZeroQuery)).bind
      next).run (stoppingProvider F G) initial =
      ⟨.stopped .abort, initial + 1, ["apply_1_A_query", "apply_1_A_query"]⟩ := by
  exact apply_run_stops (observedSites F G) observeAction ⟨[], []⟩
    (extendProtocolTable (observedSites F G) observeAction ⟨[], []⟩ [] markedZeroQuery)
    zeroQuerySignature [0] "A" {} 0 (.cons (some 8) .nil) rfl
    (stoppingProvider F G) initial (initial + 1)
    ["apply_1_A_query", "apply_1_A_query"] .abort rfl next

theorem decimal_spelling_boundaries :
    [0, 9, 10, 99, 100, 4096, 65536, 18446744073709551615].map protocolSiteDecimal =
      ["0", "9", "10", "99", "100", "4096", "65536", "18446744073709551615"] := by
  decide +kernel

theorem metadata_shared_utf8_label (state : ApplicationMetadata.SiteState) :
    (ApplicationMetadata.renderSite (some "한") "λ").run { state with visits := 7, bytes := 10 } =
      .ok ("apply_3_한_λ", { state with visits := 7, bytes := 24 }) := by rfl

theorem metadata_nested_label (state : ApplicationMetadata.SiteState) :
    (ApplicationMetadata.renderSite (some (qualifyProtocolSite (some "A") "B")) "C").run
      { state with visits := 7, bytes := 10 } =
      .ok ("apply_11_apply_1_A_B_C", { state with visits := 7, bytes := 32 }) := by rfl

theorem metadata_empty_sentinel (state : ApplicationMetadata.SiteState) :
    (ApplicationMetadata.renderSite (some "captured") "").run { state with bytes := 10 } =
      .ok ("", { state with bytes := 10 }) := by rfl

/-- Cumulative accounting refuses before constructing the generated label. -/
theorem metadata_byte_limit_refuses (state : ApplicationMetadata.SiteState) :
    (ApplicationMetadata.renderSite (some "A") "B").run { state with bytes := 16777206 } =
      .error "structured-effective-site-limit" := by rfl

/-- Exhausted native-summary depth refuses before a cached suffix can be used.
This records the Lean diagnostic boundary; it makes no native diagnostic claim. -/
theorem metadata_cached_depth_zero_refuses (snapshot : Snapshot) (function : Function)
    (cached : ApplicationSummary) :
    (ApplicationMetadata.summarizeFunction snapshot 0 function).run [(function.name, cached)] =
      .error "structured-application-depth" := rfl

namespace ClosedSelection

private def flatSignature : ProtocolSignature := ⟨"Flat", ["A"], [], [], [], []⟩
private def flatBody : Region protocolDialect [] [] := .ret .nil
private def flat : CheckedProtocol := checked flatSignature flatBody
private def dormantSignature : ProtocolSignature := ⟨"Dormant", ["A"], [], [], [], []⟩
private def dormantBody : Region protocolDialect [] [] :=
  .letOp (.mark "call") .nil .nil
    (.letOp (.protocolApply flatSignature [0] "call") .nil .nil (.ret .nil))
private def dormant : CheckedProtocol := checked dormantSignature dormantBody
private def snapshot : Snapshot :=
  (let contractDefinitions : List Definition := [
    .function ⟨"Dormant", .protocol, .publicDef, [], [], some ⟨["A"], [], []⟩, [], none,
      .block [.instruction (.protocolApply "Flat" ["A"]) [] [] [] "call"] (.ret [])⟩,
    .function ⟨"Flat", .protocol, .publicDef, [], [], some ⟨["A"], [], []⟩, [], none,
      .block [] (.ret [])⟩]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "Flat", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none)⟩)
set_option smartUnfolding false in
private def unit : UnitPayload where
  definitions := []
  protocols := [flat, dormant]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := by rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel
private def program : Program := ⟨snapshot, unit⟩

set_option smartUnfolding false in
theorem kernel_admission : check snapshot = .ok program := by rfl
private def imported : Imported snapshot := ⟨program, kernel_admission⟩
theorem exact_subject : program.snapshot = snapshot := imported.exactSubject
theorem flat_signature : flat.signature = flatSignature := rfl
theorem flat_raw : flat.raw = flatBody.erase := rfl
theorem flat_member : flat ∈ unit.protocols := List.mem_cons_self
theorem dormant_signature : dormant.signature = dormantSignature := rfl
theorem dormant_raw : dormant.raw = dormantBody.erase := rfl
theorem dormant_member : dormant ∈ unit.protocols := List.mem_cons_of_mem _ List.mem_cons_self
theorem selected_flat : unit.entry = flat := rfl

private def closedPayload : Payload where
  definitions := []
  entry := ⟨"Flat", [], [], .ret [], .ret .nil, rfl⟩
  linked := by decide +kernel
  entryLinked := by decide +kernel
private def closed : ClosedProgram := ⟨program, closedPayload, by rfl⟩

/-- A dormant caller may apply the selected root without invalidating its closed view. -/
theorem closed_projection_with_dormant_apply : program.closedPayload = .ok closedPayload :=
  closed.projected

theorem dormant_apply_preserves_flat_meaning :
    program.participant F G 0 .nil = .done .nil := by
  have projection := closed.participant_eq_denote (F := F) (G := G) .nil
  exact projection

/-- Selecting the applying body refuses; no flattening is hidden in the closed view. -/
theorem selected_apply_refuses :
    ({ snapshot := { snapshot with entry := "Dormant" },
       payload := { unit with entryIndex := ⟨1, by decide⟩ } } : Program).closedPayload =
      .error "structured-open-profile" := rfl

end ClosedSelection

end Tests.StructuredApplicationSemantics
