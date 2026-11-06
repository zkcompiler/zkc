module

public import Zkc.Source.Structured.PublishedWords

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Structured.PublishedWords

variable {model : DomainModel} {Aux E A : Type}

/-- A participant action preserves the word table on every outcome. -/
theorem actionM_ordinary {m : Type → Type} [Monad m] [LawfulMonad m]
    {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PublishedWords.Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser m model Aux E)
    (op : (participantInterfaceOn model.toCarriers).Op)
    (state : OracleProtocol.State model snapshot domains math (PublishedWords.State model Aux)) :
    PublishedWords.actionM oracles ordinary choose (.ordinary op) state = (do
      let result ← ordinary state.oracle.provider.words op state.oracle.provider.auxiliary
      pure ⟨result.outcome, {state with oracle.provider := ⟨state.oracle.provider.words, result.state⟩},
        result.events.map OracleProtocol.Event.ordinary⟩) := by
  unfold PublishedWords.actionM OraclePublication.actionM
  rw [OracleProcess.actionM_ordinary]
  simp [PublishedWords.liftM, OraclePublication.afterM, OraclePublication.request?]

/-- Every successful publication prepends one record. Both the order of the old
publications and the answers at their anchors survive every subsequent source action. -/
structure Preserves (before after : Table model) : Prop where
  order : before <:+ after
  lookup : ∀ row anchor stored, find before row anchor = some stored → find after row anchor = some stored

theorem Preserves.refl (words : Table model) : Preserves words words :=
  ⟨List.suffix_refl words, fun _ _ _ found ↦ found⟩

theorem Preserves.trans {first second third : Table model}
    (left : Preserves first second) (right : Preserves second third) : Preserves first third :=
  ⟨left.order.trans right.order, fun row anchor stored found ↦
    right.lookup row anchor stored (left.lookup row anchor stored found)⟩

/-- The first actual publication, once present, remains the first even if a
subsequent action stops after publishing more words. Tables store the newest first. -/
theorem Preserves.first {before after : Table model} {initial}
    (frame : Preserves before after) (present : before.getLast? = some initial) :
    after.getLast? = some initial := by
  obtain ⟨later, rfl⟩ := frame.order
  simp [List.getLast?_append, present]

theorem find_none_of_fresh (words : Table model) (anchor : OracleAnchor)
    (fresh : hasAnchor words anchor = false) (row : Ty) : find words row anchor = none := by
  induction words with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨storedRow, stored⟩
    simp only [hasAnchor, List.any_cons, Bool.or_eq_false_iff] at fresh
    have different : stored.anchor ≠ anchor := by simpa using fresh.1
    simp only [find]
    split
    · simp [ih fresh.2]
    · exact ih fresh.2

theorem cons_preserves (words : Table model) {row : Ty} (stored : Word model row)
    (fresh : hasAnchor words stored.anchor = false) :
    Preserves words (⟨row, stored⟩ :: words) := by
  refine ⟨List.suffix_cons _ _, ?_⟩
  intro queryRow anchor old found
  have different : stored.anchor ≠ anchor := by
    intro same
    rw [← same, find_none_of_fresh words stored.anchor fresh queryRow] at found
    cases found
  simp only [find]
  split
  · simp [found]
  · exact found

theorem find_word (request : OraclePublication.Request model)
    (cells : List (model.Value request.kind.answer)) (older : Table model) :
    find (⟨request.kind.answer, word request cells⟩ :: older)
      request.kind.answer request.anchor = some (word request cells) := by
  simp [find, word]

theorem selected_holder (request : OraclePublication.Request model)
    (proposal data : List (model.Value request.kind.answer))
    (present : request.holderData = some data) : selected request proposal = data := by
  simp [selected, present]

theorem selected_receiver (request : OraclePublication.Request model)
    (proposal : List (model.Value request.kind.answer)) (absent : request.holderData = none) :
    selected request proposal = proposal := by simp [selected, absent]

theorem finish_stopped (request : OraclePublication.Request model) (before : State model Aux)
    (reason : PIR.Stop) (after : Aux) (events : List E) :
    finish request before ⟨.stopped reason, after, events⟩ =
      ⟨.stopped reason, ⟨before.words, after⟩, events⟩ := rfl

theorem finish_returned (request : OraclePublication.Request model) (before : State model Aux)
    (proposal : List (model.Value request.kind.answer)) (after : Aux) (events : List E)
    (fresh : hasAnchor before.words request.anchor = false)
    (admitted : valid request (selected request proposal) = true) :
    finish request before ⟨.returned proposal, after, events⟩ =
      ⟨.returned (), ⟨⟨request.kind.answer, word request (selected request proposal)⟩ ::
        before.words, after⟩, events⟩ := by
  simp [finish, fresh, admitted]

theorem finish_refused (request : OraclePublication.Request model) (before : State model Aux)
    (proposal : List (model.Value request.kind.answer)) (after : Aux) (events : List E)
    (invalid : (hasAnchor before.words request.anchor ||
      !valid request (selected request proposal)) = true) :
    finish request before ⟨.returned proposal, after, events⟩ =
      ⟨.stopped .refused, ⟨before.words, after⟩, events⟩ := by simp [finish, invalid]

/-- Full-record law, independent of the outer monad and of how choice was made. -/
theorem finish_frame (request : OraclePublication.Request model) (before : State model Aux)
    (attempt : PIR.Execution Aux E (List (model.Value request.kind.answer))) :
    Preserves before.words (finish request before attempt).state.words := by
  rcases attempt with ⟨outcome, after, events⟩
  cases outcome with
  | stopped reason => exact .refl _
  | returned proposal =>
    dsimp only [finish]
    split
    · exact .refl _
    · rename_i admitted
      have fresh : hasAnchor before.words request.anchor = false := by
        cases h : hasAnchor before.words request.anchor <;> simp_all
      exact cons_preserves before.words (word request (selected request proposal)) fresh

/-- Every returned Execution records the actual attempted auxiliary poststate and events,
even when validation refuses a returned proposal. -/
theorem finish_attempt (request : OraclePublication.Request model) (before : State model Aux)
    (attempt : PIR.Execution Aux E (List (model.Value request.kind.answer))) :
    (finish request before attempt).state.auxiliary = attempt.state ∧
      (finish request before attempt).events = attempt.events := by
  rcases attempt with ⟨outcome, after, events⟩
  cases outcome with
  | stopped reason => exact ⟨rfl, rfl⟩
  | returned proposal => dsimp only [finish]; split <;> exact ⟨rfl, rfl⟩

theorem finish_failed (request : OraclePublication.Request model) (before : State model Aux)
    (attempt : PIR.Execution Aux E (List (model.Value request.kind.answer))) (reason : PIR.Stop)
    (failed : (finish request before attempt).outcome = .stopped reason) :
    (finish request before attempt).state.words = before.words := by
  rcases attempt with ⟨outcome, after, events⟩
  cases outcome with
  | stopped why => rfl
  | returned proposal =>
    dsimp only [finish] at failed ⊢
    split at failed <;> simp_all

/-- A success forces this exact installation; the premise does not provide a word or an
unrelated whole-run consistency assertion. -/
theorem finish_success (request : OraclePublication.Request model) (before : State model Aux)
    (attempt : PIR.Execution Aux E (List (model.Value request.kind.answer)))
    (success : (finish request before attempt).outcome = .returned ()) :
    ∃ proposal, attempt.outcome = .returned proposal ∧
      (finish request before attempt).state.words =
        ⟨request.kind.answer, word request (selected request proposal)⟩ :: before.words := by
  rcases attempt with ⟨outcome, after, events⟩
  cases outcome with
  | stopped reason => cases success
  | returned proposal =>
    refine ⟨proposal, rfl, ?_⟩
    dsimp only [finish] at success ⊢
    split at success <;> simp_all

/-- A successful install is exactly the selected whole word, rather than a per-query oracle. -/
theorem installed (request : OraclePublication.Request model) (before : State model Aux)
    (proposal : List (model.Value request.kind.answer)) (after : Aux) (events : List E)
    (fresh : hasAnchor before.words request.anchor = false)
    (admitted : valid request (selected request proposal) = true) :
    find (finish request before ⟨.returned proposal, after, events⟩).state.words
      request.kind.answer request.anchor = some (word request (selected request proposal)) := by
  rw [finish_returned request before proposal after events fresh admitted]
  exact find_word _ _ _

theorem read_state (request : OracleRead) (state : State model Aux) :
    (read (E := E) request state).state = state := rfl

/-- The precise outcome equation includes unknown keys, type/shape mismatch, malformed
stored lengths, and out-of-range positions, all refused without state changes or events. -/
theorem read_found (request : OracleRead) (state : State model Aux)
    (stored : Word model request.kind.answer)
    (found : find state.words request.kind.answer request.anchor = some stored) :
    read (E := E) request state =
      ⟨if stored.kind.answer != request.kind.answer ||
          !OracleStore.validRows stored.kind stored.rows ||
          !OracleStore.validRows request.kind stored.rows ||
          stored.cells.length != stored.rows || request.position ≥ stored.rows then
        .stopped .refused
      else match stored.cells[request.position]? with
        | none => .stopped .refused
        | some cell => .returned cell, state, []⟩ := by
  simp only [read, found]
  rfl

/-- An installed table can be read through a handle with a different shape annotation.
Both shapes must admit the same stored length, and the nominal answer sort must agree.
This is the compatibility used when a fixed-size table is exposed by an unsized handle. -/
theorem read_compatible_cell (request : OracleRead) (state : State model Aux)
    (stored : Word model request.kind.answer) (cell : model.Value request.kind.answer)
    (found : find state.words request.kind.answer request.anchor = some stored)
    (answer : stored.kind.answer = request.kind.answer)
    (storedShape : OracleStore.validRows stored.kind stored.rows = true)
    (requestedShape : OracleStore.validRows request.kind stored.rows = true)
    (length : stored.cells.length = stored.rows) (within : request.position < stored.rows)
    (selectedCell : stored.cells[request.position]? = some cell) :
    read (E := E) request state = ⟨.returned cell, state, []⟩ := by
  simp [read, found, answer, storedShape, requestedShape, length,
    Nat.not_le_of_gt within, selectedCell]

/-- A valid installed word returns the selected cell, with a complete unchanged record. -/
theorem read_cell (request : OracleRead) (state : State model Aux)
    (stored : Word model request.kind.answer) (cell : model.Value request.kind.answer)
    (found : find state.words request.kind.answer request.anchor = some stored)
    (kind : stored.kind = request.kind)
    (shape : OracleStore.validRows request.kind stored.rows = true)
    (length : stored.cells.length = stored.rows) (within : request.position < stored.rows)
    (selectedCell : stored.cells[request.position]? = some cell) :
    read (E := E) request state = ⟨.returned cell, state, []⟩ := by
  simp [read, found, kind, shape, length, Nat.not_le_of_gt within, selectedCell]

theorem read_out_of_range (request : OracleRead) (state : State model Aux)
    (stored : Word model request.kind.answer)
    (found : find state.words request.kind.answer request.anchor = some stored)
    (outside : request.position ≥ stored.rows) :
    read (E := E) request state = ⟨.stopped .refused, state, []⟩ := by
  simp [read, found, outside]

theorem read_unknown (request : OracleRead) (state : State model Aux)
    (unknown : find state.words request.kind.answer request.anchor = none) :
    read (E := E) request state = ⟨.stopped .refused, state, []⟩ := by simp [read, unknown]

variable {m : Type → Type} [Monad m]

/-- The equality retains the outer effect (which need not return an Execution). -/
theorem publishM_equation (choose : Chooser m model Aux E)
    (request : OraclePublication.Request model) (state : State model Aux) :
    publishM choose request state =
      (choose request state.words state.auxiliary >>= fun attempt ↦
        pure (finish request state attempt)) := rfl

/-- Construct the local preservation witness inside the same outer computation. There
is no support/totality assumption on `m`, and no whole-run word supplied by the caller. -/
theorem publishM_framed (choose : Chooser m model Aux E)
    (request : OraclePublication.Request model) (state : State model Aux) [LawfulMonad m] :
    ∃ checked : m {result : PIR.Execution (State model Aux) E Unit //
        Preserves state.words result.state.words},
      publishM choose request state = (checked >>= fun result ↦ pure result.val) := by
  refine ⟨(do
    let attempt ← choose request state.words state.auxiliary
    pure ⟨finish request state attempt, finish_frame request state attempt⟩), ?_⟩
  simp [publishM]

variable [LawfulMonad m]

/-- Ordinary calls keep the exact old table on every returned or stopped record. -/
theorem liftM_frame {I : PIR.Signature}
    (ordinary : Table model → PIR.MonadHandler m I Aux E)
    (operation : I.Op) (state : State model Aux) :
    (liftM ordinary operation state >>= fun result ↦ pure (result, result.state.words)) =
      (liftM ordinary operation state >>= fun result ↦ pure (result, state.words)) := by
  simp [liftM]

/-- Local frame for the existing publication transaction, including rollback of logical
metadata on a stop. Compose this with the ordinary/base action laws and `finish_frame`;
no protocol case or whole-run consistency hypothesis is required. -/
theorem complete_frame {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment}
    (before : OracleProtocol.State model snapshot domains math (State model Aux))
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math (State model Aux))
      (OracleProtocol.Event E) A)
    (publication : PIR.Execution (State model Aux) E Unit)
    (candidateFrame : Preserves before.oracle.provider.words candidate.state.oracle.provider.words)
    (publicationFrame : Preserves candidate.state.oracle.provider.words publication.state.words) :
    Preserves before.oracle.provider.words
      (OraclePublication.complete before candidate publication).state.oracle.provider.words := by
  rcases publication with ⟨outcome, after, events⟩
  cases outcome <;> exact candidateFrame.trans publicationFrame

/-- Reuse the generic monadic execution theorem for a proof-carrying invariant restriction.
A client supplies a local handler commuting with erasure (including failed records), not
an equation for a complete run. This applies directly to `OraclePublication.actionM`
and to the Process selected by `OraclePublication.sourceRunM`. -/
theorem runM_frame {I : PIR.Signature} {S : Type}
    (invariant : S → Prop) (handler : PIR.MonadHandler m I S E)
    (framed : PIR.MonadHandler m I {s // invariant s} E)
    (localFrame : ∀ operation state,
      framed operation state >>= PIR.Execution.expand (fun s ↦ pure s.val) =
        handler operation state.val)
    (process : PIR.Process I A) (state : {s // invariant s}) :
    (process.runM framed state >>= PIR.Execution.expand (fun s ↦ pure s.val)) =
      process.runM handler state.val := by
  symm
  simpa using PIR.runM_expand (fun s : {s // invariant s} ↦ pure s.val)
    framed handler (fun operation state ↦ by simpa using (localFrame operation state).symm)
    process state

end Zkc.Source.Structured.PublishedWords
