import Zkc.Source.Structured.PublishedWordsFrame
import Zkc.Source.Structured.RegisteredLifetime
import Tests.OracleProviderFrame
import Tests.PublishedWords

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
open Zkc.Source.Structured.PublishedWords
open Tests.OracleProcessData (model)

namespace Tests.PublishedWordsFrame

section
-- Two three-cell words agree on the first read and disagree on the last.
-- A second word at this anchor is impossible even if it has the right shape.
private def originalCell (i : Fin 3) : Nat := i.val
private def changedCell (i : Fin 3) : Nat := if i.val = 2 then 9 else i.val

example : originalCell 0 = changedCell 0 := rfl

example {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
    {entries : OracleEntries model snapshot domains math} {participant : Nat} {source : OracleAnchor}
    {state : State model Unit}
    (live : RegisteredWord (row := .index) entries participant source originalCell state) :
    ¬ Nonempty (RegisteredWord (row := .index) entries participant source changedCell state) := by
  rintro ⟨alternative⟩
  have last := congrFun (live.unique alternative) (2 : Fin 3)
  contradiction

-- A later chooser or an early refusal cannot rebind the same handle to
-- another word that agrees with every read except the last one.
example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment} {A E : Type}
    (oracles : List (CheckedOracle snapshot domains math))
    (network : Table model → PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Unit E)
    (choose : Chooser m model Unit E) (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math (State model Unit)) (anchor : OracleAnchor)
    (live : RegisteredWord (row := .index) state.oracle.entries state.oracle.self anchor originalCell state.oracle.provider) :
    Std.Do.Internal.Ensures (fun record ↦ ¬ Nonempty (RegisteredWord (row := .index)
      record.state.oracle.entries record.state.oracle.self anchor changedCell record.state.oracle.provider))
      (process.runM (actionM oracles network choose) state) := by
  apply (processPublicationFrame oracles network choose process state).weaken
  rintro record frame ⟨different⟩
  obtain ⟨original⟩ := live.transport frame
  have last := congrFun (original.unique different) (2 : Fin 3)
  contradiction

-- Even a preserved provider table cannot authorize a new logical entry
-- that shadows its dynamic anchor. The registry refuses this insertion.
example {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
    (entry : OracleStoredTable model snapshot domains math .index) :
    OracleStore.insert [⟨.index, entry⟩] {entry with rows := 3} = none := by
  apply OracleStore.insert_duplicate
  simp [OracleStore.hasAnchor]
end

/-- No whole-run frame premise: every branch of an arbitrary original Process. -/
theorem every_process_result {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {Aux E A : Type}
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : Table model →
      PIR.MonadHandler List (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser List model Aux E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (before : OracleProtocol.State model snapshot domains math (State model Aux))
    (result : PIR.Execution (OracleProtocol.State model snapshot domains math (State model Aux))
      (OracleProtocol.Event E) A)
    (member : result ∈ process.runM (actionM oracles ordinary choose) before) :
    Preserves before.oracle.provider.words result.state.oracle.provider.words :=
  OracleProviderFrame.list_post (process_frame oracles ordinary choose process before) result member

/-- Every reached record of an arbitrary admitted original source retains all old words. -/
theorem every_source_result {snapshot : Snapshot} {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self (State model Nat))
    (ordinary : Table model →
      PIR.MonadHandler List (participantInterfaceOn model.toCarriers) Nat String)
    (choose : Chooser List model Nat String) :
    ∀ result ∈ sourceRunM start ordinary choose,
      Preserves start.state.oracle.provider.words result.state.oracle.provider.words :=
  fun result member ↦
    OracleProviderFrame.list_post (sourceRunM_frame start ordinary choose) result member

private def oldAnchor : OracleAnchor := (⟨⟨999, []⟩, 888, [7, 1, 0]⟩ : OracleLocation).anchor
private def oldWord : Word model .index :=
  ⟨.table .index none, oldAnchor, 2, 17, [19, 19, 17], ⟨⟨999, []⟩, 888, [7, 1, 0]⟩, [900, 901]⟩
private def initial : State model Nat := ⟨[⟨.index, oldWord⟩], 0⟩

private def ordinary : Table model →
    PIR.MonadHandler List (participantInterfaceOn model.toCarriers) Nat String :=
  fun words operation auxiliary ↦ match operation with
    | .query _ (.draw _) _ =>
      [⟨.returned (Int.ofNat auxiliary), auxiliary + words.length + 3, ["draw-a"]⟩,
       ⟨.returned (Int.ofNat (auxiliary + 1)), auxiliary + words.length + 11, ["draw-b"]⟩]
    | .query _ (.sampleIndex _) _ =>
      [⟨.returned 0, auxiliary + 1, ["index-a"]⟩,
       ⟨.returned 1, auxiliary + 9, ["index-b"]⟩]
    | _ => [⟨.stopped .refused, auxiliary + 100, ["ordinary-refused"]⟩]

private def choose (failure : Option PIR.Stop := none) : Chooser List model Nat String :=
  fun request words auxiliary ↦
    let after := auxiliary + 2
    match failure with
    | some reason => [⟨.stopped reason, after, ["attempt-stopped"]⟩]
    | none => match request with
      | ⟨.table .index _, _, _, _, _, _, _⟩ =>
        [⟨.returned ([auxiliary + words.length, 31] : List Nat), after, ["choose-a"]⟩,
         ⟨.returned ([auxiliary + words.length + 20, 71] : List Nat), after + 7, ["choose-b"]⟩]
      | _ => [⟨.stopped .refused, after, ["nominal-refusal"]⟩]

private def replace {V : Ty → Type} {types : List Ty} {type : Ty} :
    Values V types → Var types type → V type → Values V types
  | .cons _ rest, .here, value => .cons value rest
  | .cons head rest, .there position, value => .cons head (replace rest position value)

private def stopped {S E A : Type} (result : PIR.Execution S E A) (reason : PIR.Stop) : Bool :=
  match result.outcome with | .stopped actual => actual == reason | _ => false

private def oldIntact (words : Table model) : Bool :=
  (find words .index oldAnchor).any fun stored ↦
    stored.cells == [900, 901] && stored.holder == 17 && stored.receivers == [19, 19, 17]

private def controls : IO Unit := do
  let count ← IO.mkRef (0 : Nat)
  let test (name : String) (condition : Bool) : IO Unit := do
    unless condition do throw (IO.userError name)
    count.modify (· + 1)
  let subject := Tests.PublishedWords.sourceSubject
  for self in [0, 1] do
    let types := subject.imported.program.payload.entry.inputs
    let some data := Var.decode types .indices 0 | throw (IO.userError "data input")
    let service : Ty := .service "random.bls12-381.fr/0"
    let some random := Var.decode types service 1 | throw (IO.userError "random input")
    let inputs := replace (replace (Values.absent model.Value types) data
      (if self == 0 then some [10, 20] else none)) random
      (if self == 1 then some (0 : Nat) else none)
    let start ← match subject.start model self inputs [] initial with
      | .error code => throw (IO.userError code)
      | .ok start => pure start
    let results := sourceRunM start ordinary (choose none)
    test "nested source branches and keeps every old word"
      (!results.isEmpty && results.all (fun result ↦ oldIntact result.state.oracle.provider.words &&
        result.state.oracle.provider.words.length == 5 && result.state.parents.isEmpty &&
        result.state.oracle.entries.length == 4 &&
        (match result.outcome with | .returned _ => true | _ => false)))
    test "every branch runs original source counters"
      (results.all fun result ↦ result.state.oracle.queries == (if self == 0 then 0 else 6))
    test "differing reached auxiliary histories"
      ((results.map (·.state.oracle.provider.auxiliary)).eraseDups.length > 1)
    for reason in [PIR.Stop.reject, .abort, .exhausted, .incomplete, .refused] do
      let failLater : Chooser List model Nat String := fun request words aux ↦
        choose (if words.length == 2 then some reason else none) request words aux
      let failed := sourceRunM start ordinary failLater
      test "every stopped publication branch keeps earlier words, actual state, and event"
        (!failed.isEmpty && failed.all fun result ↦
          stopped result reason && oldIntact result.state.oracle.provider.words &&
          result.state.oracle.provider.words.length == 2 && result.state.oracle.entries.length == 1 &&
          result.state.parents.length == 2 &&
          result.events.getLast? == some (.logical (.provider "attempt-stopped")))
      let ordinaryStop : Table model →
          PIR.MonadHandler List (participantInterfaceOn model.toCarriers) Nat String :=
        fun _ _ aux ↦ [⟨.stopped reason, aux + 111, ["ordinary-stop"]⟩,
          ⟨.stopped reason, aux + 222, ["ordinary-stop-other"]⟩]
      if self == 1 then
        let stoppedRuns := sourceRunM start ordinaryStop (choose none)
        test "ordinary stops retain attempted auxiliary updates and original prefix"
          (stoppedRuns.length == 4 && stoppedRuns.all fun result ↦
            stopped result reason && oldIntact result.state.oracle.provider.words &&
            result.state.oracle.provider.words.length == 2 && result.state.oracle.queries == 0 &&
            result.state.oracle.provider.auxiliary ≥ 113 &&
            (result.events.getLast? == some (.ordinary "ordinary-stop") ||
             result.events.getLast? == some (.ordinary "ordinary-stop-other")))
  IO.println s!"published-words-frame-source: {← count.get} controls passed"

#eval controls

end Tests.PublishedWordsFrame
