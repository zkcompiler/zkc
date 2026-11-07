module

public import Zkc.Source.Structured.OraclePublication

@[expose] public section

/-! An ideal finite-word provider for the explicit publication profile.

Only publication selects a word. A holder's supplied payload fixes that selection;
otherwise the adversary selects it from the reached provider history and auxiliary state.
Ordinary effects may inspect that history but can only return auxiliary state. This is an
ideal policy, not cryptographic binding or a law of independence for future randomness.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.PublishedWords

structure Word (model : DomainModel) (row : Ty) where
  kind : OracleKind
  anchor : OracleAnchor
  rows : Nat
  holder : Nat
  receivers : List Nat
  location : OracleLocation
  cells : List (model.Value row)

abbrev Table (model : DomainModel) := List ((row : Ty) × Word model row)

structure State (model : DomainModel) (Aux : Type) where
  words : Table model := []
  auxiliary : Aux

variable {model : DomainModel} {Aux E A : Type}

def find : Table model → (row : Ty) → OracleAnchor → Option (Word model row)
  | [], _, _ => none
  | ⟨storedRow, word⟩ :: rest, row, anchor =>
    if equal : storedRow = row then
      if word.anchor = anchor then some (equal ▸ word) else find rest row anchor
    else find rest row anchor

def hasAnchor (words : Table model) (anchor : OracleAnchor) : Bool :=
  words.any (fun entry ↦ entry.2.anchor == anchor)

/-- Preserve the full nominal kind and ordered metadata, without copying holder payload
into the role-local logical store. `cells` live only in this independent provider table. -/
def word (request : OraclePublication.Request model)
    (cells : List (model.Value request.kind.answer)) : Word model request.kind.answer :=
  ⟨request.kind, request.anchor, request.rows, request.holder, request.receivers,
    request.location, cells⟩

/-- With holder data, the policy selects that exact word. A receiver has no such data,
so its ideal word is the arbitrary proposed finite string. No equality oracle is needed. -/
def selected (request : OraclePublication.Request model)
    (proposal : List (model.Value request.kind.answer)) : List (model.Value request.kind.answer) :=
  request.holderData.getD proposal

/-- Source construction identities are checked here as provider policy too. Root input
publication needs a separate adapter; this profile publishes source sends only. -/
def valid (request : OraclePublication.Request model)
    (cells : List (model.Value request.kind.answer)) : Bool :=
  request.anchor == request.location.anchor && OracleStore.validRows request.kind request.rows &&
    cells.length == request.rows

/-- Complete postprocessing of the attempted choice. Every stop retains its auxiliary
poststate and events. Rejected proposals never install any part of a word. -/
def finish (request : OraclePublication.Request model) (before : State model Aux)
    (attempt : PIR.Execution Aux E (List (model.Value request.kind.answer))) :
    PIR.Execution (State model Aux) E Unit :=
  let unchanged : State model Aux := ⟨before.words, attempt.state⟩
  match attempt.outcome with
  | .stopped reason => ⟨.stopped reason, unchanged, attempt.events⟩
  | .returned proposal =>
    let cells := selected request proposal
    if hasAnchor before.words request.anchor || !valid request cells then
      ⟨.stopped .refused, unchanged, attempt.events⟩
    else ⟨.returned (), ⟨⟨request.kind.answer, word request cells⟩ :: before.words,
      attempt.state⟩, attempt.events⟩

variable {m : Type → Type} [Monad m]

/-- The adversary sees exactly the reached publication request and old finite words.
It cannot return or replace the table. Selection runs once before the source continuation. -/
abbrev Chooser (m : Type → Type) (model : DomainModel) (Aux E : Type) :=
  (request : OraclePublication.Request model) → Table model → Aux →
    m (PIR.Execution Aux E (List (model.Value request.kind.answer)))

def publishM (choose : Chooser m model Aux E) :
    PIR.MonadHandler m (OraclePublication.Interface model) (State model Aux) E :=
  fun request before ↦ do
    let attempt ← choose request before.words before.auxiliary
    pure (finish request before attempt)

/-- Read-only access to old words, with arbitrary auxiliary effects and all original stops. -/
def liftM {I : PIR.Signature}
    (ordinary : Table model → PIR.MonadHandler m I Aux E) :
    PIR.MonadHandler m I (State model Aux) E :=
  fun operation before ↦ do
    let attempt ← ordinary before.words operation before.auxiliary
    pure ⟨attempt.outcome, ⟨before.words, attempt.state⟩, attempt.events⟩

/-- Reads have no chooser. The logical store owns role visibility and virtual expansion;
this base provider checks the full nominal row sort, shape, key, and finite position. Read
locations/expansion paths are query sites, so are not compared to publication locations. -/
def read (request : OracleRead) (state : State model Aux) :
    PIR.Execution (State model Aux) E (model.Value request.kind.answer) :=
  let outcome := match find state.words request.kind.answer request.anchor with
    | none => .stopped .refused
    | some stored =>
      if stored.kind.answer != request.kind.answer ||
          !OracleStore.validRows stored.kind stored.rows ||
          !OracleStore.validRows request.kind stored.rows ||
          stored.cells.length != stored.rows || request.position ≥ stored.rows then
        .stopped .refused
      else match stored.cells[request.position]? with
        | none => .stopped .refused
        | some cell => .returned cell
  ⟨outcome, state, []⟩

def readM : PIR.MonadHandler m (oracleReadInterface model.toCarriers) (State model Aux) E :=
  fun request state ↦ pure (read request state)

/-- Concrete clients use these constructed handlers with the existing source profile. -/
def actionM {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E) [LawfulMonad m] :=
  OraclePublication.actionM model oracles (liftM ordinary) readM (publishM choose)

/-- The actual admitted source, with the three constructed provider handlers fixed here. -/
def sourceRunM {snapshot : Snapshot} {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self (State model Aux))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E) [LawfulMonad m] :=
  OraclePublication.sourceRunM start (liftM ordinary) readM (publishM choose)

end Zkc.Source.Structured.PublishedWords
