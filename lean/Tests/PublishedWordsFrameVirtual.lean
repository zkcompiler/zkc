import Zkc.Source.Structured.PublishedWordsFrame
import Tests.OracleProviderFrame
import Tests.OracleProcessData

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
open Zkc.Source.Structured.PublishedWords
open Tests.OracleProcessData

namespace Tests.PublishedWordsFrameVirtual

private def stored : Word model .index :=
  ⟨kind, anchor 0, 2, 0, [1], location 0, [10, 20]⟩
private def provider : State model Nat := ⟨[⟨.index, stored⟩], 42⟩
private def initial : OracleProtocol.State model snapshot [] math (State model Nat) :=
  ⟨⟨0, runtime.entries, provider, 0⟩, state.frame, []⟩

private def ordinary : Table model →
    PIR.MonadHandler List (participantInterfaceOn model.toCarriers) Nat String :=
  fun words operation aux ↦ match operation with
    | .query _ (.sampleIndex _) _ =>
      [⟨.returned 0, aux + words.length, ["first"]⟩,
       ⟨.returned 1, aux + 10 * words.length, ["second"]⟩]
    | _ => [⟨.stopped .refused, aux + 100, ["unexpected"]⟩]
private def choose : Chooser List model Nat String :=
  fun _ _ aux ↦ [⟨.stopped .abort, aux + 1000, ["unexpected-publication"]⟩]

/-- The live nominal lookup is a theorem of the actual nested virtual interpreter. -/
theorem nested_live (result : PIR.Execution
    (OracleProtocol.State model snapshot [] math (State model Nat))
    (OracleProtocol.Event String) Nat)
    (member : result ∈ (process false).runM (actionM [checked] ordinary choose) initial) :
    find result.state.oracle.provider.words .index (anchor 0) = some stored := by
  apply Tests.OracleProviderFrame.list_post
    (process_live [checked] ordinary choose (process false) initial .index (anchor 0) stored ?_)
    result member
  simp [initial, provider, find, stored]

private def queries (events : List (OracleProtocol.Event String)) : List OracleRead :=
  events.filterMap fun event ↦ match event with | .logical (.query request) => some request | _ => none

private def controls : IO Unit := do
  let count ← IO.mkRef (0 : Nat)
  let test (name : String) (condition : Bool) : IO Unit := do
    unless condition do throw (IO.userError name)
    count.modify (· + 1)
  let results := (process false).runM (actionM [checked] ordinary choose) initial
  test "all nested virtual branches keep exact old words"
    (results.length == 4 && results.all fun result ↦
      result.outcome == .returned 17 && result.state.oracle.queries == 14 &&
      (find result.state.oracle.provider.words .index (anchor 0)).any (fun word ↦ word.cells == [10, 20]))
  test "auxiliary updates remain branch specific"
    (results.map (·.state.oracle.provider.auxiliary) == [44, 53, 53, 62])
  test "ordered complete event records and expansion ancestry"
    (results.all fun result ↦ (queries result.events).map (·.expansion.length) ==
      [0, 1, 2, 2, 1, 2, 2, 0, 1, 2, 2, 1, 2, 2])
  let adaptive := adaptiveProcess.runM (actionM [checked] ordinary choose) initial
  test "actual ordinary replies select virtual reads of immutable cells"
    (adaptive.map (·.outcome) == [.returned (some 10), .returned (some 20)])
  for reason in [PIR.Stop.reject, .abort, .exhausted, .incomplete, .refused] do
    let halt : PIR.Process (OracleProtocol.Interface model) Nat :=
      .call (.oracle (request 0)) fun _ ↦ .halt reason
    let stopped := halt.runM (actionM [checked] ordinary choose) initial
    test "every explicit halt keeps nested read counters, words, and query log"
      (stopped.length == 1 && stopped.all fun result ↦
        result.outcome == .stopped reason && result.state.oracle.queries == 7 &&
        result.state.oracle.provider.auxiliary == 42 && (queries result.events).length == 7)
  let absent := {initial with oracle.provider.words := []}
  let refused := adaptiveProcess.runM (actionM [checked] ordinary choose) absent
  test "missing stored word stops inside original nested virtual expansion"
    (refused.length == 2 && refused.all fun result ↦
      result.outcome == .stopped .refused && result.state.oracle.queries == 3 &&
      (queries result.events).length == 3 && result.state.oracle.provider.words.isEmpty)
  let request : OraclePublication.Request model :=
    ⟨kind, anchor 0, 2, 0, [1], location 0, none⟩
  let duplicateChooser : Chooser List model Nat String := fun request _ aux ↦
    match request with
    | ⟨.table .index _, _, _, _, _, _, _⟩ =>
      [⟨.returned ([99, 100] : List Nat), aux + 1, ["duplicate-a"]⟩,
       ⟨.returned ([7, 8] : List Nat), aux + 20, ["duplicate-b"]⟩]
    | _ => [⟨.stopped .refused, aux, []⟩]
  let duplicate := publishM duplicateChooser request provider
  test "duplicate keys refuse every proposal and retain attempted state/events"
    (duplicate.map (·.outcome) == [.stopped .refused, .stopped .refused] &&
      duplicate.map (·.state.auxiliary) == [43, 62] &&
      duplicate.map (·.events) == [["duplicate-a"], ["duplicate-b"]] &&
      duplicate.all fun result ↦ (find result.state.words .index (anchor 0)).any
        (fun word ↦ word.cells == [10, 20]))
  let send : OracleRequest model.toCarriers :=
    ⟨.send kind 0 [1] [], location 0, 1, id,
      .cons none (.cons (some (ProtocolValue.ofConcrete .index 2)) .nil)⟩
  let receiver : OracleProtocol.State model snapshot [] math (State model Nat) :=
    ⟨⟨1, [], provider, 0⟩,
      {invocation := (location 0).invocation, definition := 1, row := (location 0).row}, []⟩
  let duplicateSource := ((PIR.Process.call (.oracle send) fun _ ↦ .done ()) :
      PIR.Process (OracleProtocol.Interface model) Unit).runM
    (actionM [checked] ordinary duplicateChooser) receiver
  test "actual duplicate publication rolls back candidate logical delivery only"
    (duplicateSource.length == 2 &&
      duplicateSource.map (·.state.oracle.provider.auxiliary) == [43, 62] &&
      duplicateSource.map (·.events) ==
        [[.logical (.provider "duplicate-a")], [.logical (.provider "duplicate-b")]] &&
      duplicateSource.all fun result ↦ result.outcome == .stopped .refused &&
        result.state.oracle.entries.isEmpty && result.state.oracle.queries == 0 &&
        (find result.state.oracle.provider.words .index (anchor 0)).any
          (fun word ↦ word.cells == [10, 20]))
  let fresh := {send with location := location 9}
  let freshSource := ((PIR.Process.call (.oracle fresh) fun _ ↦ .done ()) :
      PIR.Process (OracleProtocol.Interface model) Unit).runM
    (actionM [checked] ordinary duplicateChooser)
    {receiver with frame.row := (location 9).row}
  test "successful actual publication retains provider events before logical delivery"
    (freshSource.length == 2 && freshSource.all fun result ↦
      result.outcome == .returned () && result.state.oracle.entries.length == 1 &&
      result.state.oracle.provider.words.length == 2 &&
      (find result.state.oracle.provider.words .index (anchor 0)).any
        (fun word ↦ word.cells == [10, 20]) &&
      (match result.events with
        | [.logical (.provider _), .logical (.delivery actual 0 1 key)] =>
          actual == location 9 && key == anchor 9
        | _ => false))
  let field : Word model (.field "A") :=
    ⟨.table (.field "A") none, anchor 0, 1, 0, [1], location 0, [3]⟩
  test "foreign nominal field sorts sharing a carrier cannot match"
    ((find [⟨.field "A", field⟩] (.field "B") (anchor 0)).isNone)
  let exception := (process false).runM
    (actionM (m := Except String) (E := String) [checked] (fun _ _ _ ↦ .error "outer")
      (fun _ _ _ ↦ .error "chooser")) initial
  test "outer failure remains an outer failure"
    (match exception with | .error "outer" => true | _ => false)
  IO.println s!"published-words-frame-virtual: {← count.get} controls passed"

#eval controls

end Tests.PublishedWordsFrameVirtual
