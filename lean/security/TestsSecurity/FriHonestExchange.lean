import ZkcExamples.Structured.FriSource
import ZkcSecurity.Bindings.Models.KoalaBearModel
import Zkc.Construction.DomainTranscript

/-! Replay both actual parties on one draw schedule. Only the holder's
source supplies the three words and the terminal vector. Check messages in
send order, with their nominal types, sites, and oracle identities. -/
namespace TestsSecurity.FriHonestExchange
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSource
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open Zkc.Construction.Domain (Payload)

private inductive Transfer where
  | word (row : Ty) (stored : PublishedWords.Word model row)
  | toHolder (site : String) (payload : Payload model.toCarriers)
  | toVerifier (site : String) (payload : Payload model.toCarriers)

private structure Traffic where
  messages : List Transfer := []
  fields : List Nat := []
  positions : List Nat := []

private abbrev refuse {A : Type} (state : Traffic) : PIR.Execution Traffic String A :=
  ⟨.stopped .refused, state, []⟩

private def holder : PublishedWords.Table model →
    PIR.MonadHandler Id (participantInterfaceOn model.toCarriers) Traffic String := fun _ op s ↦
  match op with
  | .receive (.field d) site 1 => match s.fields with
    | beta :: rest => ⟨.returned (beta : model.Field d),
        {s with fields := rest, messages := s.messages ++ [.toHolder site (.field d beta)]}, []⟩
    | [] => refuse s
  | .receive .index site 1 => match s.positions with
    | pos :: rest => ⟨.returned pos, {s with positions := rest, messages := s.messages ++ [.toHolder site (.index pos)]}, []⟩
    | [] => refuse s
  | .send (ty := .vector d) site 1 xs =>
    ⟨.returned (), {s with messages := s.messages ++ [.toVerifier site (.vector d xs)]}, []⟩
  | _ => refuse s

private def publish : PublishedWords.Chooser Id model Traffic String := fun req _ s ↦
  match req.holderData with
  | none => refuse s
  | some xs => ⟨.returned xs, {s with messages := s.messages ++ [.word req.kind.answer (PublishedWords.word req xs)]}, []⟩

private def replay : PublishedWords.Table model →
    PIR.MonadHandler Id (participantInterfaceOn model.toCarriers) Traffic String := fun _ op s ↦
  match op, s.messages with
  | .query _ (.draw d) (.cons 0 .nil), .toHolder _ p :: _ =>
    match p.value (.field d) with
    | some beta => ⟨.returned beta, s, []⟩
    | none => refuse s
  | .query _ (.sampleIndex _) (.cons 0 (.cons 32 .nil)), .toHolder _ p :: _ =>
    match p.value .index with
    | some pos => if pos < 32 then ⟨.returned pos, s, []⟩ else refuse s
    | none => refuse s
  | .send (ty := .field d) site 0 beta, .toHolder expected p :: rest =>
    if site == expected && p.value (.field d) == some beta then ⟨.returned (), {s with messages := rest}, []⟩ else refuse s
  | .send (ty := .index) site 0 pos, .toHolder expected p :: rest =>
    if site == expected && p.value .index == some pos then ⟨.returned (), {s with messages := rest}, []⟩ else refuse s
  | .receive ty site 0, .toVerifier expected p :: rest =>
    match p.value ty with
    | some value => if site == expected then ⟨.returned value, {s with messages := rest}, []⟩ else refuse s
    | none => refuse s
  | _, _ => refuse s

private def receive : PublishedWords.Chooser Id model Traffic String := fun req _ s ↦
  match s.messages with
  | .word row stored :: rest =>
    if same : row = req.kind.answer then
      if stored.kind == req.kind && stored.anchor == req.anchor && stored.location == req.location &&
          stored.rows == req.rows && stored.holder == req.holder && stored.receivers == req.receivers && req.holderData.isNone then
        ⟨.returned (same ▸ stored.cells), {s with messages := rest}, []⟩
      else refuse s
    else refuse s
  | _ => refuse s

private def check (shift : Octic) (polynomial : Octic → Octic) (fields positions : List Nat) : IO Unit := do
  let .ok points := Numerical.points model.toFieldModel extension shift 32 | throw (IO.userError "coset")
  let initial : Traffic := {fields, positions}
  let prover := PublishedWords.sourceRunM (start 0 (points.map polynomial) shift 3 8 0 initial) holder publish
  let traffic := prover.state.oracle.provider.auxiliary
  let holderReturned := match prover.outcome with | .returned _ => true | .stopped _ => false
  unless holderReturned && traffic.fields.isEmpty && traffic.positions.isEmpty && prover.state.parents.isEmpty do
    throw (IO.userError "holder failed or consumed the wrong draws")
  let run := fun (messages : List Transfer) ↦ verifier (model := model) (m := Id) shift 3 8 0 {messages} replay receive
  let checked := run traffic.messages
  let verifierAccepted := match checked.outcome with
    | .returned values => (values.get .here).bind ProtocolValue.toConcrete == some true
    | .stopped _ => false
  unless verifierAccepted && checked.state.oracle.queries == 96 && checked.state.parents.isEmpty &&
      checked.state.oracle.provider.auxiliary.messages.isEmpty do
    throw (IO.userError "honest exchange failed or left messages unread")
  -- Same-typed publication, different occurrence. Detect the swap before a
  -- later field or query draw could conceal it.
  let .word row first :: challenge :: .word nextRow next :: rest := traffic.messages
    | throw (IO.userError "initial exchange order")
  let wrong := run (.word nextRow next :: challenge :: .word row first :: rest)
  let refused := match wrong.outcome with | .stopped .refused => true | _ => false
  unless refused && wrong.state.oracle.provider.words.isEmpty do
    throw (IO.userError "a later publication occupied the first source send")

#eval do
  check 3 (fun x ↦ x^7 + 3*x^4 + 11*x + 1) [0, 5, 9] [31, 0, 0, 16, 27, 1, 3, 31]
  check 7 (fun _ ↦ 0) [9, 0, 9] [0, 0, 0, 0, 0, 0, 0, 0]
  IO.println "FRI-HONEST-EXCHANGE-PASS two paired runs and two misordered publication controls"

end TestsSecurity.FriHonestExchange
