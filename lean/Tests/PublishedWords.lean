import Zkc.Source.Structured.PublishedWordsLaws
import Tests.OracleProcessData
import Zkc.Source.KernelRfl

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
open Zkc.Source.Structured.PublishedWords
namespace Tests.PublishedWords

abbrev model := OracleProcessData.model
abbrev kind : OracleKind := .table .index none
structure History where
  seed : Nat := 0
  choices : List Nat := []
  wordCounts : List Nat := []
  events : List String := []

abbrev Store := State model History

private def choose (failure : Option PIR.Stop := none) : Chooser Id model History String :=
  fun request words auxiliary ↦
    let after := {auxiliary with
      choices := auxiliary.choices ++ [auxiliary.seed]
      wordCounts := auxiliary.wordCounts ++ [words.length]
      events := auxiliary.events ++ ["choose"]}
    let outcome : PIR.Outcome (List (model.Value request.kind.answer)) := match failure with
      | some reason => .stopped reason
      | none => match request with
        | ⟨.table .index _, _, _, _, _, _, _⟩ =>
          .returned [10 + auxiliary.seed, 20 + auxiliary.seed]
        | _ => .stopped .refused
    ⟨outcome, after, ["choose"]⟩

private def ordinary (challenge : Int := 7) : Table model →
    PIR.MonadHandler Id (participantInterfaceOn model.toCarriers) History String :=
  fun _ action auxiliary ↦
    let after := {auxiliary with
      seed := auxiliary.seed + 100 + challenge.toNat
      events := auxiliary.events ++ ["challenge", "aux-update"]}
    match action with
    | .query _ (.draw _) _ => ⟨.returned challenge, after, ["challenge", "aux-update"]⟩
    | _ => ⟨.stopped .refused, after, ["unexpected"]⟩

private def location (row : List Nat := [7, 1, 2]) : OracleLocation :=
  ⟨⟨3, [.application 1 [7, 1, 0], .iteration 1 [7, 1, 3] 4]⟩, 0, row⟩

private def request : Zkc.Source.Structured.OraclePublication.Request model :=
  ⟨kind, (location).anchor, 2, 0, [1, 1, 0], location, none⟩

private def query (position : Nat := 0) : OracleRead :=
  ⟨kind, request.anchor, position, location [9], []⟩

private def stopped {S E A : Type} (result : PIR.Execution S E A) (reason : PIR.Stop) : Bool :=
  match result.outcome with | .stopped actual => actual == reason | _ => false

private def resultCell (result : PIR.Execution Store String Nat) : Option Nat :=
  match result.outcome with | .returned cell => some cell | _ => none

private def controls : IO Unit := do
  let count ← IO.mkRef (0 : Nat)
  let test (name : String) (condition : Bool) : IO Unit := do
    unless condition do throw (IO.userError name)
    count.modify (· + 1)
  let initial : Store := ⟨[], {}⟩
  let published := publishM (choose none) request initial
  test "receiver chooses a whole finite word" (published.state.words.length == 1 &&
    resultCell (read query published.state) == some 10 &&
    resultCell (read (query 1) published.state) == some 20)
  let some stored := find published.state.words .index request.anchor
    | throw (IO.userError "missing word")
  test "exact original metadata" (stored.kind == kind && stored.rows == 2 &&
    stored.holder == 0 && stored.receivers == [1, 1, 0] && stored.location == location)
  let draw : (participantInterfaceOn model.toCarriers).Op :=
    .query "challenge" (.draw "bls12-381.fr") (.cons 0 .nil)
  let advanced := liftM (ordinary 7) draw published.state
  test "ordinary effect updates auxiliary state and keeps words"
    (advanced.state.auxiliary.seed == 107 &&
    resultCell (read query advanced.state) == some 10)
  let later := {request with location := location [7, 1, 5], anchor := (location [7, 1, 5]).anchor}
  let republished := publishM (choose none) later advanced.state
  test "later publication depends on reached challenge" (resultCell (read
    {query with anchor := later.anchor} republished.state) == some 117)
  test "old word survives later publication"
    (resultCell (read query republished.state) == some 10 &&
    resultCell (read query republished.state) == resultCell (read query published.state))
  test "choice sees reached history only" (republished.state.auxiliary.choices == [0, 107] &&
    republished.state.auxiliary.wordCounts == [0, 1])
  let holder := publishM (choose none)
    {request with holderData := some ([88, 99] : List Nat)} initial
  test "holder fixes chosen word even when proposal differs"
    (resultCell (read query holder.state) == some 88)
  let malformed := publishM (choose none) {request with rows := 3} published.state
  test "duplicate publication refuses with actual attempted state and events"
    (stopped malformed .refused && malformed.state.words.length == 1 &&
      malformed.state.auxiliary.choices == [0, 0] && malformed.events == ["choose"])
  for replacement in [request, {request with receivers := [0, 1, 1]},
      {request with holder := 1}, {request with kind := .table .index (some 2)}] do
    let duplicate := publishM (choose none) replacement published.state
    test "rebinding with changed ordered metadata or shape refuses"
      (stopped duplicate .refused && resultCell (read query duplicate.state) == some 10)
  let typedRebind : Zkc.Source.Structured.OraclePublication.Request model :=
    ⟨.table (.field "bls12-381.fr") none, request.anchor, 2, 0, [1], location, none⟩
  let typedAttempt : PIR.Execution History String (List Int) := ⟨.returned [3, 4], {}, ["typed"]⟩
  let typedDuplicate := finish typedRebind published.state typedAttempt
  test "same anchor cannot rebind another nominal row sort" (stopped typedDuplicate .refused &&
    typedDuplicate.state.words.length == 1 && typedDuplicate.events == ["typed"])
  let badLength := publishM (choose none) {later with rows := 3} published.state
  test "wrong selected length refuses without installation" (stopped badLength .refused &&
    badLength.state.words.length == 1 && badLength.state.auxiliary.choices == [0, 0])
  let badHolder := publishM (choose none)
    {later with kind := kind, holderData := some ([1] : List Nat)} published.state
  test "malformed holder data refuses" (stopped badHolder .refused &&
    badHolder.state.words.length == 1)
  let badKey := publishM (choose none) {later with anchor := request.anchor} initial
  test "changed location order or key refuses"
    (stopped badKey .refused && badKey.state.words.isEmpty)
  let badFixed := publishM (choose none) {later with kind := .table .index (some 3)} initial
  test "wrong fixed shape refuses" (stopped badFixed .refused)
  test "unknown key refuses" (stopped (read (E := String)
    {query with anchor := later.anchor} published.state) .refused)
  let changedRoot : OracleAnchor :=
    {request.anchor with invocation := {request.anchor.invocation with root := 4}}
  test "complete anchor includes root identity" (stopped (read (E := String)
    {query with anchor := changedRoot} published.state) .refused)
  let reordered := publishM (choose none) {request with location := location [7, 2, 1]} initial
  test "reordered construction row is not the same key" (stopped reordered .refused)
  let corrupted : Store := ⟨[⟨.index, {stored with cells := [1]}⟩], {}⟩
  test "malformed stored length refuses" (stopped (read (E := String) query corrupted) .refused)
  test "out of range refuses" (stopped (read (E := String) (query 2) published.state) .refused)
  test "changed shape refuses" (stopped (read (E := String)
    {query with kind := .table .index (some 3)} published.state) .refused)
  let fixedWord := publishM (choose none) {request with kind := .table .index (some 2)} initial
  test "source shape forgetting reads the same installed word"
    (resultCell (read query fixedWord.state) == some 10)
  test "changed nominal type refuses" (stopped (read (E := String)
    {query with kind := .table (.field "bls12-381.fr") none} published.state) .refused)
  let fieldRequest : Zkc.Source.Structured.OraclePublication.Request model :=
    ⟨.table (.field "A") none, later.anchor, 2, 0, [1], later.location, none⟩
  let fieldPublished := finish fieldRequest initial typedAttempt
  test "same host carrier does not erase nominal field sort" (stopped (read (E := String)
    {query with anchor := later.anchor, kind := .table (.field "B") none}
    fieldPublished.state) .refused)
  for reason in [PIR.Stop.reject, .abort, .exhausted, .incomplete, .refused] do
    let failed := publishM (choose (some reason)) later published.state
    test ("publication keeps actual stop/poststate/events: " ++ reprStr reason)
      (stopped failed reason && failed.state.words.length == 1 &&
        failed.state.auxiliary.choices == [0, 0] && failed.events == ["choose"] &&
        resultCell (read query failed.state) == some 10)
    let failure : Table model → PIR.MonadHandler Id (participantInterfaceOn model.toCarriers)
        History String := fun _ _ aux ↦
      ⟨.stopped reason, {aux with seed := 999}, ["attempted-ordinary"]⟩
    let failedOrdinary := liftM failure draw published.state
    test ("ordinary stop cannot change words: " ++ reprStr reason)
      (stopped failedOrdinary reason && failedOrdinary.state.auxiliary.seed == 999 &&
        failedOrdinary.events == ["attempted-ordinary"] &&
        resultCell (read query failedOrdinary.state) == some 10)
  let outerFailure := publishM (m := Except String) (Aux := History) (E := String)
    (fun _ _ _ ↦ .error "outer") request initial
  test "outer failure remains an outer failure" (match outerFailure with
    | .error message => message == "outer" | _ => false)
  IO.println s!"published-words: {← count.get} controls passed"

private def replace {V : Ty → Type} {types : List Ty} {type : Ty} :
    Values V types → Var types type → V type → Values V types
  | .cons _ rest, .here, value => .cons value rest
  | .cons head rest, .there position, value => .cons head (replace rest position value)

private def field := "bls12-381.fr"
private def service : Ty := .service ("random." ++ field ++ "/0")

private def protocol (name : String) (inputs outputs : List Ty)
    (inputScopes outputScopes : List (List String)) (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, inputs, outputs,
    some ⟨["P", "V"], inputScopes, outputScopes⟩, [], some (.protocol ⟨name, []⟩), body⟩

/-- This is source grammar, admitted below; no hand-written Process substitutes for it. -/
private def child : Definition :=
  protocol "child" [.indices, service] [.index, .index, .index] [["P"], ["V"]]
    [["V"], ["V"], ["V"]]
    (.block [
      .instruction (.indexConstant "2") [] [.index] [] "",
      .instruction (.oracle (.send "P" ["V"] kind ["rows"] [("rows", 3)]))
        [1, 0] [.oracle kind] [] "first",
      .instruction (.draw "V" field) [3] [.field field] [] "challenge",
      .instruction (.indexConstant "0") [] [.index] [] "",
      .instruction (.oracle (.query (some "V") kind)) [2, 0] [.index] [] "read_first",
      .instruction (.oracle (.query (some "V") kind)) [3, 1] [.index] [] "read_again",
      .instruction (.oracle (.send "P" ["V"] kind ["rows"] [("rows", 3)]))
        [6, 5] [.oracle kind] [] "later",
      .instruction (.oracle (.query (some "V") kind)) [5, 3] [.index] [] "read_old"]
      (.ret [3, 2, 0]))

private def root : Definition :=
  protocol "main" [.indices, service] [.index, .index, .index] [["P"], ["V"]]
    [["V"], ["V"], ["V"]]
    (.block [
      .instruction (.indexConstant "2") [] [.index] [] "",
      .instruction (.indexConstant "0") [] [.index] [] "",
      .instruction (.protocolRepeat 3 2 ["P", "V"] [["V"], ["V"], ["V"]])
        [1, 0, 0, 0, 2, 3] [.index, .index, .index]
        [.region [.index, .index, .index, .index, .indices, service] [.index, .index, .index]
          (.block [.instruction (.protocolApply "child" ["P", "V"])
            [4, 5] [.index, .index, .index] [] "child"] (.yield [0, 1, 2]))] "round"]
      (.ret [0, 1, 2]))

def source : Snapshot :=
  {OracleProcessData.snapshot with
    definitions := [child, root]
    relations := []
    contracts := [⟨"child", []⟩, ⟨"main", []⟩]}

/-- Kernel-checked association with the exact source grammar above. -/
def sourceProgram : Program := (check source).toOption.get (by decide +kernel)

theorem source_checked : check source = .ok sourceProgram := by kernel_rfl

def sourceImported : Imported source := ⟨sourceProgram, source_checked⟩

def sourceSubject : OracleSubject source :=
  sourceImported.oracleSubject.toOption.get (by decide +kernel)

theorem source_selected : sourceImported.oracleSubject = .ok sourceSubject := by kernel_rfl

private def sourceControls : IO Unit := do
  let subject := sourceSubject
  for self in [0, 1] do
    let types := subject.imported.program.payload.entry.inputs
    let some data := Var.decode types .indices 0 | throw (IO.userError "data input")
    let some random := Var.decode types service 1 | throw (IO.userError "random input")
    let inputs := replace (replace (Values.absent model.Value types) data
      (if self == 0 then some [10, 20] else none)) random
      (if self == 1 then some (0 : Nat) else none)
    let start ← match subject.start model self inputs [] (⟨[], {}⟩ : Store) with
      | .error code => throw (IO.userError ("source ingress: " ++ code))
      | .ok start => pure start
    let result := Zkc.Source.Structured.PublishedWords.sourceRunM (m := Id) start
      (ordinary 7) (choose none)
    unless result.state.oracle.provider.words.length == 4 &&
        result.state.oracle.entries.length == 4 && result.state.parents.isEmpty &&
        (match result.outcome with | .returned _ => true | _ => false) do
      throw (IO.userError "nested source success")
    unless result.state.oracle.entries.all (fun entry ↦ match entry.2.payload with
        | .base data => data.isSome == (self == 0)
        | .virtual .. => false) do
      throw (IO.userError "ideal provider words must not fill receiver logical payloads")
    let aux := result.state.oracle.provider.auxiliary
    unless aux.choices == (if self == 0 then [0, 0, 0, 0] else [0, 107, 107, 214]) &&
        aux.wordCounts == [0, 1, 2, 3] do
      throw (IO.userError "reached publication histories")
    let words := result.state.oracle.provider.words
    unless words.all (fun entry ↦ entry.2.location.invocation.frames.length == 2) &&
        (words.map (·.2.anchor)).eraseDups.length == 4 do
      throw (IO.userError "complete nested anchors")
    if self == 1 then
      let .returned outputs := result.outcome | throw (IO.userError "source output")
      for port in [0, 1, 2] do
        let some output := Var.decode _ .index port | throw (IO.userError "output type")
        unless (outputs.get output).bind ProtocolValue.toConcrete == some 117 do
          throw (IO.userError "repeated source reads of old word after later publication")
      unless result.state.oracle.queries == 6 && aux.events ==
          ["choose", "challenge", "aux-update", "choose", "choose", "challenge", "aux-update",
            "choose"] do
        throw (IO.userError "source order")
      let alternative := Zkc.Source.Structured.PublishedWords.sourceRunM (m := Id) start
        (ordinary 99) (choose none)
      let first := words.getLast?
      let alternateFirst := alternative.state.oracle.provider.words.getLast?
      unless (first.bind fun entry ↦ (find words .index entry.2.anchor).map (·.cells)) ==
          some [10, 20] && (alternateFirst.bind fun entry ↦
            (find alternative.state.oracle.provider.words .index entry.2.anchor).map (·.cells)) ==
          some [10, 20] do
        throw (IO.userError "first selection sees no later challenge")
    for reason in [PIR.Stop.reject, .abort, .exhausted, .incomplete, .refused] do
      let failed := Zkc.Source.Structured.PublishedWords.sourceRunM (m := Id) start
        (ordinary 7) (choose (some reason))
      unless stopped failed reason && failed.state.parents.length == 2 &&
          failed.state.oracle.entries.isEmpty && failed.state.oracle.provider.words.isEmpty &&
          failed.state.oracle.provider.auxiliary.events == ["choose"] &&
          failed.state.oracle.queries == 0 &&
          failed.events == [.mark "", .mark "", .mark "round", .mark "child", .mark "",
            .mark "apply_5_child_first", .logical (.provider "choose")] do
        throw (IO.userError "publication stop retains exact source prefix with no suffix")
    for reason in [PIR.Stop.reject, .abort, .exhausted, .incomplete, .refused] do
      let failLater : Chooser Id model History String := fun publication words aux ↦
        choose (if words.length == 1 then some reason else none) publication words aux
      let failed := Zkc.Source.Structured.PublishedWords.sourceRunM (m := Id) start
        (ordinary 7) failLater
      let provider := failed.state.oracle.provider
      unless stopped failed reason && failed.state.parents.length == 2 &&
          failed.state.oracle.entries.length == 1 && provider.words.length == 1 &&
          provider.auxiliary.choices == (if self == 0 then [0, 0] else [0, 107]) &&
          provider.auxiliary.events == (if self == 0 then ["choose", "choose"] else
            ["choose", "challenge", "aux-update", "choose"]) &&
          failed.state.oracle.queries == (if self == 0 then 0 else 2) &&
          failed.events.getLast? == some (.logical (.provider "choose")) do
        throw (IO.userError "later publication stop retains old word and reached prefix")
      let some old := provider.words.head? | throw (IO.userError "missing old word")
      unless resultCell (read {query with anchor := old.2.anchor} provider) == some 10 do
        throw (IO.userError "old word changed on failed later publication")
  IO.println "published-words-source: checked nested source, both roles, all five stops passed"

#eval controls
#eval sourceControls

end Tests.PublishedWords
