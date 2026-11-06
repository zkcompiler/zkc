import Zkc.Source.Structured.OracleExecution
import Zkc.Source.Structured.OracleValueObservations

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured

namespace Tests.OracleExecution

private abbrev model : DomainModel := ringModel Int Int
private abbrev baseKind : OracleKind := .table .index none
private abbrev foldedKind : OracleKind := .table .index (some 1)

private def predicate : Function :=
  ⟨"admissible", .math, .privateDef, [.indices], [.boolean], none, [], none,
    .block [.instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0])⟩

private def sum : Function :=
  ⟨"sum", .math, .privateDef, [.index, .index], [.index], none, [], none,
    .block [.instruction .indexWrappingAdd [0, 1] [.index] [] ""] (.ret [0])⟩

private def declaration : OracleDeclaration :=
  ⟨"Pair", [.oracle baseKind, .index], foldedKind, "pair_admissible", [], [],
    .block [
      .instruction (.oracle (.query none baseKind)) [0, 1] [.index] [] "low",
      .instruction (.indexConstant "1") [] [.index] [] "",
      .instruction .indexWrappingAdd [3, 0] [.index] [] "",
      .instruction (.oracle (.query none baseKind)) [3, 0] [.index] [] "high",
      .instruction (.call "sum") [3, 0] [.index] [] ""] (.ret [0])⟩

private def snapshot : Snapshot :=
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000", "main", [],
    [⟨"pair_admissible", .privateDef, "zkc.language.formula/0", "pair", "0",
      [.indices], [.boolean], ["oracle-admissibility"], some "admissible", []⟩], [],
    [.function predicate, .oracle declaration, .function sum], [], blsRows, {}⟩

private def predicateRaw : RawRegion Ty Op :=
  .letOp (.booleanConstant true) [] [.boolean] .nil (.ret [0])

private def predicateChecked : CheckedDefinition :=
  ⟨"admissible", .math, [.indices], [.boolean], predicateRaw,
    .letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil)), rfl⟩

private def sumRaw : RawRegion Ty Op :=
  .letOp .indexWrappingAdd [0, 1] [.index] .nil (.ret [0])

private def sumChecked : CheckedDefinition :=
  ⟨"sum", .math, [.index, .index], [.index], sumRaw,
    .letOp .indexWrappingAdd (.cons .here (.cons (.there .here) .nil)) .nil
      (.ret (.cons .here .nil)), rfl⟩

private def math : OracleMathEnvironment where
  definitions := [predicateChecked, sumChecked]
  linked := by simp [DeclarationsLinked, CheckedDefinition.helpers, predicateChecked,
    predicateRaw, sumChecked, sumRaw, RawRegion.operations, RawRegions.operations, Op.helpers,
    CheckedDefinition.helper]
  pureBodies := by
    intro checked member
    have cases : checked = predicateChecked ∨ checked = sumChecked := by simpa using member
    rcases cases with rfl | rfl <;> exact ⟨rfl, rfl⟩

private theorem associated : math.Associated snapshot [] := by
  constructor
  · intro checked member
    have cases : checked = predicateChecked ∨ checked = sumChecked := by simpa [math] using member
    rcases cases with rfl | rfl
    · exact ⟨predicate, by simp [snapshot], rfl, rfl, rfl⟩
    · exact ⟨sum, by simp [snapshot], rfl, rfl, rfl⟩
  · intro function member kind
    have cases : function = predicate ∨ function = sum := by
      simpa [snapshot, List.mem_cons, List.mem_singleton] using member
    rcases cases with rfl | rfl
    · exact ⟨predicateChecked, by simp [math], rfl⟩
    · exact ⟨sumChecked, by simp [math], rfl⟩

private def dormantSnapshot : Snapshot :=
  {snapshot with definitions := snapshot.definitions ++ [.oracle
    {declaration with name := "Dormant", body := .block [
      .instruction (.oracle (.query none baseKind)) [0, 1] [.index] [] "same",
      .instruction (.oracle (.query none baseKind)) [1, 2] [.index] [] "same"] (.ret [0])}]}

private theorem dormantAssociated : math.Associated dormantSnapshot [] := by
  constructor
  · intro checked member
    have cases : checked = predicateChecked ∨ checked = sumChecked := by simpa [math] using member
    rcases cases with rfl | rfl
    · exact ⟨predicate, by simp [dormantSnapshot, snapshot], rfl, rfl, rfl⟩
    · exact ⟨sum, by simp [dormantSnapshot, snapshot], rfl, rfl, rfl⟩
  · intro function member _
    have cases : function = predicate ∨ function = sum := by
      simpa [dormantSnapshot, snapshot, List.mem_cons, List.mem_singleton] using member
    rcases cases with rfl | rfl
    · exact ⟨predicateChecked, by simp [math], rfl⟩
    · exact ⟨sumChecked, by simp [math], rfl⟩

private def checked : CheckedOracle snapshot [] math :=
  (checkOracle snapshot [] math associated 1).toOption.get (by decide)

private def location (iteration : Nat) : OracleLocation :=
  ⟨⟨0, [.application 2 [1], .iteration 2 [3] iteration]⟩, 2, [7, 1, 5]⟩

private def baseAnchor : OracleAnchor := (location 0).anchor
private def virtualAnchor : OracleAnchor := (location 1).anchor

private def baseTable (rows : Nat := 2) : OracleStoredTable model snapshot [] math .index :=
  ⟨baseAnchor, rows, 0, [1], .base (some [10, 20])⟩

private def virtualTable : OracleStoredTable model snapshot [] math .index :=
  ⟨virtualAnchor, 1, 0, [1], .virtual checked rfl (.cons baseAnchor .nil)⟩

/-- Provider stops deliberately update state and retain their attempted event. -/
private def provide (bad : Option Nat) (kind : OracleKind) (position state : Nat) :
    PIR.Execution Nat Nat (model.Value kind.answer) :=
    match kind with
    | .table .index _ =>
      if bad == some position then ⟨.stopped .abort, state + 1, [position]⟩
      else ⟨.returned (if position == 0 then (10 : Nat) else (20 : Nat)), state + 1, [position]⟩
    | _ => ⟨.stopped .refused, state + 1, [position]⟩

private def provider (bad : Option Nat) :
    PIR.Handler (oracleReadInterface model.toCarriers) Nat Nat :=
  fun request state ↦ provide bad request.kind request.position state

private def state (rows : Nat := 2) : OracleRuntimeState model snapshot [] math Nat :=
  ⟨0, [⟨.index, virtualTable⟩, ⟨.index, baseTable rows⟩], 0, 0⟩

private def query (position : Nat) : OracleRead :=
  ⟨foldedKind, virtualAnchor, position, location 2, []⟩

private def runQuery (rows position : Nat) (bad : Option Nat := none) :=
  OracleStore.read model (provider bad) (query position) (state rows)

private def trace (events : List (OracleEvent Nat)) : List Nat :=
  events.filterMap (fun event ↦ match event with | .provider position => some position | _ => none)

private def operation (op : OracleOp)
    (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (current : OracleRuntimeState model snapshot [] math Nat := state 2) :=
  Zkc.Source.Structured.OracleExecution.operation model [checked] (provider none)
    (location 3) current.self id op args current

private def anchorValue (anchor : OracleAnchor) : ProtocolValue model.toCarriers (.oracle baseKind) :=
  ProtocolValue.ofConcrete _ anchor

private def sequenceValue (anchors : List OracleAnchor) :
    ProtocolValue model.toCarriers (.oracleSequence baseKind 2) := ProtocolValue.ofConcrete _ anchors

private def singleResult {type : Ty}
    (result : PIR.Execution (OracleRuntimeState model snapshot [] math Nat) (OracleEvent Nat)
      (Values (Component (ProtocolValue model.toCarriers)) [type])) :
    Option (ProtocolValue model.toCarriers type) :=
  match result.outcome with
  | .returned values => values.get .here
  | .stopped _ => none

private def lowerError (body : Block) : Option String :=
  match OracleBody.lower snapshot [] math 1 {declaration with body := body} with
  | .error error => some error.code
  | .ok _ => none

private def run : IO Unit := do
  let mut count := 0
  let test (name : String) (condition : Bool) : IO Unit := do
    unless condition do throw (IO.userError name)
  test "retained source declaration is checked" (checkOracle snapshot [] math associated 1).isOk
  count := count + 1
  let result : PIR.Execution _ _ Nat := runQuery 2 0
  test "actual body returns the two source answers' sum" (result.outcome == .returned 30)
  test "ordered low then high provider reads" (trace result.events == [0, 1])
  test "outer plus two reached child queries" (result.state.queries == 3 && result.state.provider == 2)
  count := count + 3
  let outside : PIR.Execution _ _ Nat := runQuery 2 1
  test "outer domain check precedes all body execution"
    (outside.outcome == .stopped .refused && outside.state.queries == 1 &&
      outside.state.provider == 0 && (trace outside.events).isEmpty)
  let first : PIR.Execution _ _ Nat := runQuery 0 0
  test "first child domain failure suppresses second child"
    (first.outcome == .stopped .refused && first.state.queries == 2 && first.state.provider == 0)
  let second : PIR.Execution _ _ Nat := runQuery 1 0
  test "second child failure retains first child"
    (second.outcome == .stopped .refused && second.state.queries == 3 &&
      second.state.provider == 1 && trace second.events == [0])
  let providerFailure : PIR.Execution _ _ Nat := runQuery 2 0 (some 1)
  test "provider abort preserves updated state and attempted event"
    (providerFailure.outcome == .stopped .abort && providerFailure.state.provider == 2 &&
      trace providerFailure.events == [0, 1])
  count := count + 4
  let append := operation (.sequenceAppend baseKind 2 [0, 1])
    (.cons (some (sequenceValue [baseAnchor, baseAnchor])) (.cons (some (anchorValue baseAnchor)) .nil))
  test "full capacity refuses even if result ignored" (match append.outcome with
    | .stopped .refused => true | _ => false)
  let selected := operation (.sequenceAt baseKind 2 [0, 1])
    (.cons (some (sequenceValue [baseAnchor]))
      (.cons (some (ProtocolValue.ofConcrete .index 1)) .nil))
  test "at checks actual count" (match selected.outcome with | .stopped .refused => true | _ => false)
  let length := operation (.sequenceLength baseKind 2)
    (.cons (some (sequenceValue [baseAnchor])) .nil)
  test "length is independent of capacity" (match length.outcome with
    | .returned (.cons (some value) .nil) => value.toConcrete == some 1 | _ => false)
  count := count + 3
  let contents := operation (.contents baseKind 0) (.cons (some (anchorValue baseAnchor)) .nil)
  test "contents returns a lazy view with no read" (match contents.outcome with
    | .returned (.cons (some value) .nil) => value.toConcrete.isNone && contents.state.queries == 0
    | _ => false)
  let wrongHolder := operation (.contents baseKind 1) (.cons (some (anchorValue baseAnchor)) .nil)
    {state 2 with self := 1}
  test "receiver cannot claim holder extraction" (match wrongHolder.outcome with
    | .stopped .refused => true | _ => false)
  count := count + 2
  let dataView : OracleDataView (.singleton baseKind) :=
    ⟨0, [1], ⟨baseAnchor, .cons 2 .nil⟩⟩
  let demand : PIR.Execution _ _ (List Nat) := OracleStore.demandBase (E := Nat)
    ⟨0, .singleton baseKind, dataView⟩ (location 4) (state 2)
  test "base data demand returns actual stored contents" (demand.outcome == .returned [10, 20])
  let forged := {dataView with references := ⟨baseAnchor, .cons 1 .nil⟩}
  let mismatch : PIR.Execution _ _ (List Nat) := OracleStore.demandBase (E := Nat)
    ⟨0, .singleton baseKind, forged⟩ (location 4) (state 2)
  test "same payload identity with unequal actual shape refuses" (mismatch.outcome == .stopped .refused)
  let virtualView : OracleDataView (.singleton foldedKind) :=
    ⟨0, [1], ⟨virtualAnchor, .cons 1 .nil⟩⟩
  let deferred : PIR.Execution _ _ (List Nat) := OracleStore.demandBase (E := Nat)
    ⟨0, .singleton foldedKind, virtualView⟩ (location 4) (state 2)
  test "concrete virtual demand is a located refusal without child reads"
    (deferred.outcome == .stopped .refused && deferred.state.queries == 0 &&
      deferred.events.any (fun event ↦ match event with
        | .refusal actual "oracle-virtual-concrete-demand" => actual == location 4 | _ => false))
  count := count + 3
  test "identical construction payload at different structural occurrences stays distinct"
    ((location 0).anchor != (location 1).anchor)
  count := count + 1
  let repeated := operation (.components (.sequence baseKind 2) 0 [1])
    (.cons (some (sequenceValue [baseAnchor, baseAnchor])) .nil)
  let roundtrip := match repeated.outcome with
    | .returned (.cons (some data) (.cons _ .nil)) =>
      let fields : ProductFields := .cons (.sequence .indices) (.cons (.oracleSequence baseKind 2) .nil)
      let record := ProtocolValue.product "SavedPair" "SavedPair" fields
        (.cons data (.cons (sequenceValue [baseAnchor, baseAnchor]) .nil))
      let restored := operation (.input (.sequence baseKind 2) 0 [1] [("rows", 2)])
        (.cons (some (record.project .here)) (.cons none .nil))
      ((singleResult restored).bind ProtocolValue.toConcrete) == some [baseAnchor, baseAnchor] &&
        restored.state.queries == 0
    | _ => false
  test "components through record projection preserve ordered duplicate sequence pair" roundtrip
  let emptyWrongCapacity : ProtocolValue model.toCarriers (.sequence .indices) :=
    .deferred (sort := .sequence baseKind 1) ⟨0, [1], []⟩
  let capacityPair := operation (.input (.sequence baseKind 2) 0 [1] [("rows", 2)])
    (.cons (some emptyWrongCapacity) (.cons none .nil))
  test "empty data sequence retains capacity in its pair identity" (match capacityPair.outcome with
    | .stopped .refused => true | _ => false)
  let shape := operation (.shape baseKind "rows") (.cons (some (anchorValue baseAnchor)) .nil)
  test "pure shape observes metadata without forcing contents"
    (((singleResult shape).bind ProtocolValue.toConcrete) == some 2 && shape.state.queries == 0)
  let unknown := operation (.sequenceAppend baseKind 2 [0, 1])
    (.cons (some (sequenceValue [])) (.cons (some (anchorValue (location 99).anchor)) .nil))
  test "sequence append refuses a missing anchor even if result is unused" (match unknown.outcome with
    | .stopped .refused => true | _ => false)
  count := count + 4
  test "answer-dependent query position refuses"
    (lowerError (.block [
      .instruction (.oracle (.query none baseKind)) [0, 1] [.index] [] "first",
      .instruction (.oracle (.query none baseKind)) [1, 0] [.index] [] "second"] (.ret [0])) ==
      some "oracle-body-adaptive-position")
  test "duplicate query labels refuse"
    (lowerError (.block [
      .instruction (.oracle (.query none baseKind)) [0, 1] [.index] [] "again",
      .instruction (.oracle (.query none baseKind)) [1, 2] [.index] [] "again"] (.ret [0])) ==
      some "oracle-body-duplicate-site")
  test "empty query label refuses"
    (lowerError (.block [
      .instruction (.oracle (.query none baseKind)) [0, 1] [.index] [] ""] (.ret [0])) ==
      some "oracle-body-query-site")
  test "inherited source cannot be another query answer"
    (lowerError (.block [
      .instruction (.oracle (.query none baseKind)) [0, 1] [.index] [] "first",
      .instruction (.oracle (.query none baseKind)) [0, 2] [.index] [] "second"] (.ret [0])) ==
      some "oracle-body-source")
  count := count + 4
  let initial : OracleRuntimeState model snapshot [] math Nat := ⟨0, [], 0, 0⟩
  let constructed := operation (.send baseKind 0 [1] [("rows", 2)])
    (.cons (some (ProtocolValue.ofConcrete .indices [10, 20]))
      (.cons (some (ProtocolValue.ofConcrete .index 2)) .nil)) initial
  test "base send installs actual holder data at the structural anchor" (match constructed.outcome with
    | .returned _ => constructed.state.entries.length == 1 && constructed.state.queries == 0
    | _ => false)
  let instantiated := Zkc.Source.Structured.OracleExecution.operation model [checked] (provider none)
    (location 4) 0 id (.virtual declaration.signature 0 [1])
    (.cons (some (anchorValue (location 3).anchor)) .nil) constructed.state
  test "virtual construction is lazy and uses the checked source signature" (match instantiated.outcome with
    | .returned _ => instantiated.state.entries.length == 2 && instantiated.state.queries == 0
    | _ => false)
  let reached : PIR.Execution _ _ Nat := OracleStore.read model (provider none)
    ⟨foldedKind, (location 4).anchor, 0, location 5, []⟩ instantiated.state
  test "constructed virtual table executes its retained body"
    (reached.outcome == .returned 30 && trace reached.events == [0, 1])
  let duplicate := operation (.send baseKind 0 [1] [("rows", 2)])
    (.cons (some (ProtocolValue.ofConcrete .indices [10, 20]))
      (.cons (some (ProtocolValue.ofConcrete .index 2)) .nil)) constructed.state
  test "same structural occurrence refuses a duplicate construction" (match duplicate.outcome with
    | .stopped .refused => duplicate.state.entries.length == 1 | _ => false)
  count := count + 4
  test "all stored oracles are checked, including a dormant malformed body"
    (match checkOracles dormantSnapshot [] math dormantAssociated with
    | .error error => error.code == "oracle-body-duplicate-site" && error.definition == 3
    | .ok _ => false)
  let sequenceView : OracleDataView (.sequence baseKind 2) :=
    ⟨0, [1], [dataView.references, dataView.references]⟩
  let deferredSequence : ProtocolValue model.toCarriers (.sequence .indices) := .deferred sequenceView
  test "deferred data sequence length reads no contents"
    (deferredSequence.observedLength == some 2)
  let selectedData := ProtocolValue.selectData baseKind 2 deferredSequence 1
  test "pure data sequence selection preserves its exact singleton reference"
    (match selectedData.bind (Zkc.Source.Structured.OracleExecution.deferredView (.singleton baseKind)) with
    | some selected => OracleStore.samePair selected dataView | none => false)
  test "pure data sequence selection refuses out of count"
    ((ProtocolValue.selectData baseKind 2 deferredSequence 2).isNone)
  test "pure data selection retains indexed capacity"
    ((ProtocolValue.selectData baseKind 1 deferredSequence 0).isNone)
  test "deferred singleton length uses actual rows"
    ((ProtocolValue.deferred dataView : ProtocolValue model.toCarriers .indices).observedLength == some 2)
  count := count + 6
  IO.println s!"oracle-execution: {count} controls passed"

#eval run

end Tests.OracleExecution
