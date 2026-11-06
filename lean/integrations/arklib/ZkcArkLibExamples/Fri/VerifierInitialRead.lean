module

public import ZkcExamples.Structured.FriCheckPositions
public import ZkcArkLibExamples.Fri.StoredWord
public import Zkc.Source.Structured.MarkedPublication

@[expose] public section

/-! The actual Check iteration probes the first published word at its bound
position. Keep the original cursor checks, event order, reply and continuation. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierInitialRead
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (extension)
open FriCheckPositions (iteration initialRequest initialSite)

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {Aux E : Type}
abbrev State (model : DomainModel) (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) (Aux : Type) :=
  OracleProtocol.State model snapshot domains math (PublishedWords.State model Aux)

def response (context : ProtocolContext) (source : OracleAnchor) (position : Nat)
    (value : model.Field extension) (state : State model snapshot domains math Aux) :
    PIR.Execution (State model snapshot domains math Aux)
      (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply
      (initialRequest context source position)) :=
  if initialSite.definition = state.frame.definition ∧ initialSite.row = state.frame.row then
    ⟨.returned (.cons (OracleProtocol.concrete model (.field extension) value) .nil),
      {state with oracle.queries := state.oracle.queries + 1},
      [.logical (.query (Phases.publishedRequest extension source position
        {initialSite with invocation := state.frame.invocation} []))]⟩
  else ⟨.stopped .refused, state, []⟩

variable {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PublishedWords.Table model → PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser m model Aux E)

private theorem read (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (state : State model snapshot domains math Aux)
    (role : state.oracle.self = 1) (source : OracleAnchor) {n : Nat}
    (word : Fin (2 ^ n) → model.Field extension)
    (live : StoredWord.Base state.oracle.entries state.oracle.self source word state.oracle.provider)
    (index : Fin (2 ^ n)) :
    PublishedWords.actionM oracles ordinary choose (initialRequest context source index.val) state =
      pure (response context source index.val (word index) state) := by
  unfold response
  split
  · rename_i cursor
    exact live.sourceQuery oracles ordinary choose state index 1 1 context.roles initialSite
      role.symm cursor.1 cursor.2 (receiver.trans role.symm)
  · rename_i mismatch
    refine (OraclePublication.queryWithPureReads oracles (PublishedWords.liftM ordinary) PublishedWords.read
      (PublishedWords.publishM choose) (.table (.field extension) none) 1 initialSite 1 context.roles
      (.cons (OracleProtocol.concrete model (.oracle (.table (.field extension) none)) source)
        (.cons (OracleProtocol.concrete model .index index.val) .nil)) state).trans ?_
    simp only [OracleProtocol.handler]
    split
    · rfl
    · rename_i valid
      exact False.elim (mismatch (by simpa using valid))

/-- The mark prefix and the remaining callback are extracted from the admitted
tree. For any lawful prover/sampler, even partial ones, the first read can be
replaced by this exact cell response without changing the full computation.
The receiver must have a live, visible word and the bound position must lie inside it. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs) (ordinal : Fin xs.length)
    (source : OracleAnchor) (cap : FriCheckPositions.Captures model)
    (state : State model snapshot domains math Aux)
    (role : state.oracle.self = 1) {n : Nat} (word : Fin (2 ^ n) → model.Field extension)
    (live : StoredWord.Base state.oracle.entries state.oracle.self source word state.oracle.provider)
    (inside : xs[ordinal.val] < 2 ^ n) :
    let process := iteration context cap xs ordinal.val source
    let handler := PublishedWords.actionM oracles ordinary choose
    let op := initialRequest (model := model) context source xs[ordinal.val]
    ∃ marks next, process = OracleProtocol.withMarks marks (.call op next) ∧
      FriCheckPositions.rejectsMismatch (context := context) (source := source) (position := xs[ordinal.val]) cap ordinal.val next ∧
      process.runM handler state =
        ((OracleProtocol.withMarks marks (.done ())).runM handler state >>= fun record ↦
          record.followM fun () current ↦
            (response context source xs[ordinal.val] (word ⟨_, inside⟩) current).followM
              fun reply ↦ (next reply).runM handler) := by
  dsimp only
  obtain ⟨marks, next, equation, guard⟩ := FriCheckPositions.firstRead context receiver xs admitted ordinal source cap
  refine ⟨marks, next, equation, guard, ?_⟩
  rw [equation]
  apply OraclePublication.runMarked
  intro current same
  have active : current.oracle.self = 1 := by rw [same, role]
  have currentLive : StoredWord.Base current.oracle.entries current.oracle.self source word current.oracle.provider := by
    rw [same]; exact live
  have reply := read oracles ordinary choose context receiver current active source word currentLive ⟨_, inside⟩
  simp only [PublishedWords.actionM, Fin.val_mk] at reply
  rw [PIR.Process.runM, reply, pure_bind]
  rfl

/-- A wrong value claimed at this ordinal prevents every successful return
of the entire installed callback. Refusal at a source cursor is distinguished
from rejection at the equality guard. Other monadic failures may have no record. -/
theorem rejectsClaim (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs) (ordinal : Fin xs.length)
    (source : OracleAnchor) (cap : FriCheckPositions.Captures model)
    (state : State model snapshot domains math Aux) (role : state.oracle.self = 1)
    {n : Nat} (word : Fin (2 ^ n) → model.Field extension)
    (live : StoredWord.Base state.oracle.entries state.oracle.self source word state.oracle.provider)
    (inside : xs[ordinal.val] < 2 ^ n) (first : List (model.Field extension))
    (enabled : cap.associate = OracleProtocol.concrete model .boolean true)
    (vector : cap.first = OracleProtocol.concrete model (.vector extension) first)
    (size : first.length < indexLimit) (supplied : ordinal.val < first.length)
    (mismatch : word ⟨xs[ordinal.val], inside⟩ ≠ first[ordinal.val]) :
    Std.Do.Internal.Ensures (fun record ↦ record.outcome = .stopped .reject ∨ record.outcome = .stopped .refused)
      ((iteration context cap xs ordinal.val source).runM (PublishedWords.actionM oracles ordinary choose) state) := by
  obtain ⟨marks, next, eqn, guard⟩ := FriCheckPositions.firstRead context receiver xs admitted ordinal source cap
  rw [eqn]
  refine OraclePublication.markedOutcomes oracles (PublishedWords.liftM ordinary) PublishedWords.readM
    (PublishedWords.publishM choose) marks _ (fun out ↦ out = .stopped .reject ∨ out = .stopped .refused)
    (Or.inr rfl) state.oracle ?_ state rfl
  intro current same
  have active : current.oracle.self = 1 := by rw [same, role]
  have currentLive : StoredWord.Base current.oracle.entries current.oracle.self source word current.oracle.provider := by
    rw [same]; exact live
  have reply := read oracles ordinary choose context receiver current active source word currentLive ⟨_, inside⟩
  simp only [PublishedWords.actionM, Fin.val_mk] at reply
  rw [PIR.Process.runM, reply, pure_bind]
  unfold response
  split
  · obtain ⟨finalMarks, stopped⟩ := guard first (word ⟨_, inside⟩) enabled vector size supplied mismatch
    simp only [PIR.Execution.followM, stopped]
    apply Zkc.MonadicPostcondition.map
    · refine OraclePublication.markedOutcomes oracles (PublishedWords.liftM ordinary) PublishedWords.readM
        (PublishedWords.publishM choose) finalMarks (.halt .reject)
        (fun out ↦ out = .stopped .reject ∨ out = .stopped .refused) (Or.inr rfl) _ ?_ _ rfl
      intro s _
      exact Zkc.MonadicPostcondition.pure _ _ (Or.inl rfl)
    · exact fun _ valid ↦ valid
  · exact Zkc.MonadicPostcondition.pure _ _ (Or.inr rfl)

end ZkcSecurity.ArkLib.Fri.VerifierInitialRead
