module

public import Zkc.Source.Structured.RegisteredWord
public import ZkcArkLib.Fri.SourcePublication
public import ZkcExamples.Structured.FriCommitRound
public import Zkc.Source.Structured.PublishedWordsLaws

@[expose] public section

/-! The received layer at the beginning of a Commit round comes from the
actual publication chooser. Its whole word is fixed before the field draw,
with source validation, duplicate words, invalid proposals and aborted
choices preserving their original behavior. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitPublication
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
attribute [local implicit_reducible] OracleOp.arguments OracleOp.results OracleKind.data OracleKind.answer OracleKind.shape
open FriSource (extension)
open FriCommitRound (kind registrySite sendRequest)
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]

abbrev State (model : DomainModel) (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) (Aux : Type) :=
  OracleProtocol.State model snapshot domains math (PublishedWords.State model Aux)

def location (state : State model snapshot domains math Aux) : OracleLocation :=
  {registrySite 0 with invocation := state.frame.invocation}

def request (context : ProtocolContext) (rows : Nat) (site : OracleLocation) :
    OraclePublication.Request model :=
  ⟨kind, site.anchor, rows, context.roles 0, [context.roles 1], site, none⟩

def candidate (context : ProtocolContext) (rows : Nat) (state : State model snapshot domains math Aux) :
    PIR.Execution (State model snapshot domains math Aux) (OracleProtocol.Event E)
      ((OracleProtocol.Interface model).Reply (sendRequest context rows)) :=
  let site := location state
  let table : OracleStoredTable model snapshot domains math (.field extension) :=
    ⟨site.anchor, rows, context.roles 0, [context.roles 1], .base none⟩
  ⟨.returned (.cons (OracleProtocol.concrete model (.oracle kind) site.anchor) .nil),
    {state with oracle.entries := ⟨.field extension, table⟩ :: state.oracle.entries},
    [.logical (.delivery site (context.roles 0) (context.roles 1) site.anchor)]⟩

variable (oracles : List (CheckedOracle snapshot domains math))
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

private theorem localSend (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (rows : Nat) (bounded : rows ≤ 32)
    (state : State model snapshot domains math Aux) (role : state.oracle.self = 1)
    (atDef : (registrySite 0).definition = state.frame.definition) (atRow : (registrySite 0).row = state.frame.row)
    (fresh : OracleStore.hasAnchor state.oracle.entries (location state).anchor = false) :
    OracleProtocol.handler (E := E) model oracles OracleProcess.refusingOrdinary OracleProcess.refusingBase
      (sendRequest context rows) state = candidate context rows state := by
  have shape : OracleStore.validRows kind rows = true := by
    have small : rows < indexLimit := lt_of_le_of_lt bounded (by decide : 32 < indexLimit)
    simp [OracleStore.validRows, OracleKind.rows, small]
  have bounds : OracleStore.validBounds kind [("rows",32)] rows = true := by
    simpa [OracleStore.validBounds, OracleKind.rows] using And.intro (by decide : 32 < indexLimit) bounded
  simp only [location, atDef, atRow] at fresh
  simp [candidate, sendRequest, location, OracleProtocol.handler, atDef, atRow, OracleExecution.operation,
    OracleKind.shape,
    OracleProtocol.concrete, ProtocolValue.toConcrete_ofConcrete, role, receiver, OracleStore.visible,
    shape, bounds, separate, OracleStore.insert, fresh]

private theorem requestsWord (context : ProtocolContext) (rows : Nat) (state : State model snapshot domains math Aux) :
    OraclePublication.request? (sendRequest context rows) state (candidate (E := E) context rows state) =
      some (request context rows (location state)) := by
  simp [OraclePublication.request?, sendRequest, candidate, request, Values.get, OracleKind.answer, OracleProtocol.concrete,
    ProtocolValue.toConcrete_ofConcrete, OracleStore.find, location]

/-- Once the original receiver send passes its location, row and freshness
checks, the only external effect it performs is to choose the full new
word against the prior table. The old words and auxiliary state are those
from this occurrence. A failed installation prevents every later action. -/
theorem send (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (rows : Nat) (bounded : rows ≤ 32) (state : State model snapshot domains math Aux)
    (role : state.oracle.self = 1) (atDef : (registrySite 0).definition = state.frame.definition)
    (atRow : (registrySite 0).row = state.frame.row)
    (fresh : OracleStore.hasAnchor state.oracle.entries (location state).anchor = false) :
    let req := request context rows (location state)
    PublishedWords.actionM oracles network choose (sendRequest context rows) state =
      (choose req state.oracle.provider.words state.oracle.provider.auxiliary >>= fun attempt ↦
        pure (OraclePublication.complete state (candidate context rows state)
          (PublishedWords.finish req state.oracle.provider attempt))) := by
  dsimp only
  unfold PublishedWords.actionM OraclePublication.actionM
  have localAction := OraclePublication.send_actionM model oracles (PublishedWords.liftM network) PublishedWords.readM
    kind 0 [1] [("rows", 32)] (registrySite 0) 1 context.roles
    (.cons none (.cons (OracleProtocol.concrete model .index rows) .nil)) state
  change OracleProcess.actionM model oracles (PublishedWords.liftM network) PublishedWords.readM
    (sendRequest context rows) state = _ at localAction
  erw [localAction, pure_bind]
  erw [localSend oracles context receiver separate rows bounded state role atDef atRow fresh]
  rw [OraclePublication.afterM_some _ _ _ _ _ (requestsWord context rows state)]
  simp [PublishedWords.publishM, candidate]

/-- Every returned handle names exactly the word that the receiver's chooser
just supplied. No successful record can keep the old table alone or use a
different same-sort publication as this round's word. -/
theorem installedWord (context : ProtocolContext) (rows : Nat) (state : State model snapshot domains math Aux)
    (attempt : PIR.Execution Aux E (List (model.Field extension)))
    (reply : (OracleProtocol.Interface model).Reply (sendRequest context rows)) :
    let req := request context rows (location state)
    let result := OraclePublication.complete state (candidate context rows state)
      (PublishedWords.finish req state.oracle.provider attempt)
    result.outcome = .returned reply →
      reply = .cons (OracleProtocol.concrete model (.oracle kind) (location state).anchor) .nil ∧
      ∃ cells, attempt.outcome = .returned cells ∧ result.state.oracle.provider.words =
        ⟨.field extension, PublishedWords.word req cells⟩ :: state.oracle.provider.words := by
  dsimp only
  let req : OraclePublication.Request model := request context rows (location state)
  cases pub : PublishedWords.finish req state.oracle.provider attempt with
  | mk outcome after events =>
    cases outcome with
    | stopped reason =>
      intro impossible
      cases impossible
    | returned token =>
      cases token
      have accepted : (PublishedWords.finish req state.oracle.provider attempt).outcome = .returned () := by rw [pub]
      obtain ⟨cells, chosen, fixed⟩ := PublishedWords.finish_success req state.oracle.provider attempt accepted
      rw [pub] at fixed
      intro same
      exact ⟨(PIR.Outcome.returned.inj same).symm, cells, chosen, fixed⟩

/-- Every accepted receiver publication supplies the live base-word fact
used by the query proofs. The polynomial or proximity of that word is left
open: its finite coordinates are derived from the actual chooser reply. -/
theorem returnedBase (context : ProtocolContext) (receiver : context.roles 1 = 1) (n : Nat)
    (state : State model snapshot domains math Aux) (self : state.oracle.self = 1)
    (attempt : PIR.Execution Aux E (List (model.Field extension)))
    (reply : (OracleProtocol.Interface model).Reply (sendRequest context (2 ^ n))) :
    let site := location state
    let req := request context (2 ^ n) site
    let result := OraclePublication.complete state (candidate context (2 ^ n) state)
      (PublishedWords.finish req state.oracle.provider attempt)
    result.outcome = .returned reply →
      ∃ word : Fin (2 ^ n) → model.Field extension,
        attempt.outcome = .returned (List.ofFn word) ∧
        Nonempty (PublishedWords.RegisteredWord (row := .field extension) result.state.oracle.entries result.state.oracle.self site.anchor word
          result.state.oracle.provider) := by
  let site := location state
  let req : OraclePublication.Request model := request context (2 ^ n) site
  dsimp only
  rcases attempt with ⟨outcome, post, trace⟩
  cases outcome with
  | stopped why => intro impossible; cases impossible
  | returned cells =>
    let proposed : PIR.Execution Aux E (List (model.Field extension)) := ⟨.returned cells, post, trace⟩
    by_cases admitted : PublishedWords.hasAnchor state.oracle.provider.words site.anchor = false ∧
        PublishedWords.valid req cells = true
    · have installed := PublishedWords.finish_returned req state.oracle.provider cells post trace admitted.1 admitted.2
      have shape : OracleStore.validRows kind (2 ^ n) = true ∧ cells.length = 2 ^ n := by
        simpa [PublishedWords.valid, req, request] using admitted.2
      let word (i : Fin (2 ^ n)) := cells[i.val]'(shape.2.symm ▸ i.isLt)
      have canonical : List.ofFn word = cells := by
        apply List.ext_getElem (List.length_ofFn.trans shape.2.symm)
        intro i below within
        simp [word]
      intro _
      refine ⟨word, congrArg PIR.Outcome.returned canonical.symm, ?_⟩
      let Live (pub : PIR.Execution (PublishedWords.State model Aux) E Unit) : Prop :=
        let result := OraclePublication.complete state (candidate context (2 ^ n) state) pub
        Nonempty (PublishedWords.RegisteredWord (row := .field extension) result.state.oracle.entries result.state.oracle.self site.anchor word
          result.state.oracle.provider)
      change Live (PublishedWords.finish req state.oracle.provider proposed)
      apply (congrArg Live installed).mpr
      refine ⟨{ registry := ⟨site.anchor, 2 ^ n, context.roles 0, [context.roles 1], .base none⟩
                lookup := ?_, data := none, base := rfl, visible := ?_, registryRows := rfl,
                stored := PublishedWords.word req cells, found := ?_, answer := rfl,
                shape := shape.1, rows := rfl, cells := canonical.symm,
                holder := rfl, receivers := rfl, occurrence := rfl }⟩
      · simp [OraclePublication.complete, candidate, site, OracleStore.find]
      · simp [OraclePublication.complete, candidate, OracleStore.visible, self, receiver]
      · exact PublishedWords.find_word req cells _
    · have invalid : (PublishedWords.hasAnchor state.oracle.provider.words site.anchor ||
          !PublishedWords.valid req cells) = true := by
        cases fresh : PublishedWords.hasAnchor state.oracle.provider.words site.anchor <;>
          cases valid : PublishedWords.valid req cells <;> simp_all
      have refused : (PublishedWords.finish req state.oracle.provider proposed).outcome = .stopped .refused := by
        dsimp only [proposed, PublishedWords.finish]
        change (if PublishedWords.hasAnchor state.oracle.provider.words site.anchor || !PublishedWords.valid req cells
          then _ else _ : PIR.Execution (PublishedWords.State model Aux) E Unit).outcome = .stopped .refused
        rw [ite_eq_left invalid]
      intro impossible
      change (OraclePublication.complete state (candidate (E := E) context (2 ^ n) state)
        (PublishedWords.finish req state.oracle.provider proposed)).outcome = .returned reply at impossible
      cases publication : PublishedWords.finish req state.oracle.provider proposed with
      | mk outcome after events =>
        rw [publication] at refused impossible
        cases outcome with
        | stopped reason => cases impossible
        | returned token => cases refused

/-- On the actual receiver action, every successful choice returns the
dynamic anchor of the published word and installs the reusable provider
witness for that very word. Stops require no witness. -/
theorem sendRegisters (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (n : Nat) (bounded : 2 ^ n ≤ 32) (state : State model snapshot domains math Aux)
    (role : state.oracle.self = 1) (atDef : (registrySite 0).definition = state.frame.definition)
    (atRow : (registrySite 0).row = state.frame.row)
    (fresh : OracleStore.hasAnchor state.oracle.entries (location state).anchor = false) :
    let source := (location state).anchor
    Std.Do.Internal.Ensures (fun result ↦ ∀ reply, result.outcome = .returned reply →
      reply = .cons (OracleProtocol.concrete model (.oracle kind) source) .nil ∧
      ∃ word : Fin (2 ^ n) → model.Field extension, Nonempty
        (PublishedWords.RegisteredWord (row := .field extension) result.state.oracle.entries
          result.state.oracle.self source word result.state.oracle.provider))
      (PublishedWords.actionM oracles network choose (sendRequest context (2 ^ n)) state) := by
  dsimp only
  rw [send oracles network choose context receiver separate _ bounded state role atDef atRow fresh]
  apply Std.Do.Internal.Ensures.bind (P := fun _ ↦ True)
  · apply Zkc.MonadicPostcondition.of_refinement (do
      let attempt ← choose (request context (2 ^ n) (location state)) state.oracle.provider.words state.oracle.provider.auxiliary
      pure ⟨attempt, trivial⟩)
    simp
  · intro attempt _
    apply Zkc.MonadicPostcondition.pure
    intro reply returned
    have handle := (installedWord context _ state attempt reply returned).1
    obtain ⟨word, _, live⟩ := returnedBase context receiver n state role attempt reply returned
    exact ⟨handle, word, live⟩

/-- The first reached action in the source iteration runs the chooser on
its original table. Only a returned publication resumes the original append,
draw and delivery continuation. All marks before the send remain in place. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (step : Nat) (st : FriCommitRound.State model) (bounded : st.rows ≤ 32) :
    ∃ marks next, FriCommitRound.iteration model context step st =
        OracleProtocol.withMarks marks (.call (sendRequest context st.rows) next) ∧
      FriCommitRound.beforeDraw context step st next ∧
      ∀ current : State model snapshot domains math Aux,
        current.oracle.self = 1 →
        (registrySite 0).definition = current.frame.definition → (registrySite 0).row = current.frame.row →
        OracleStore.hasAnchor current.oracle.entries (location current).anchor = false →
        let req := request context st.rows (location current)
        let handler := PublishedWords.actionM oracles network choose
        (PIR.Process.call (sendRequest context st.rows) next).runM handler current =
          (choose req current.oracle.provider.words current.oracle.provider.auxiliary >>= fun attempt ↦
            (OraclePublication.complete current (candidate context st.rows current)
              (PublishedWords.finish req current.oracle.provider attempt)).followM fun reply ↦
                (next reply).runM handler) := by
  obtain ⟨marks, next, equation, after⟩ := FriCommitRound.beforeChallenge context receiver step st
  refine ⟨marks, next, equation, after, ?_⟩
  intro current role atDef atRow fresh
  dsimp only
  rw [PIR.Process.runM, send oracles network choose context receiver separate st.rows bounded current role atDef
    atRow fresh, bind_assoc]
  simp only [pure_bind]

end ZkcSecurity.ArkLib.Fri.CommitPublication
