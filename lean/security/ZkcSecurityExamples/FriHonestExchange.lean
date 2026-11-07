module

public import ZkcExamples.Structured.FriSource
public import ZkcSecurity.Bindings.Models.KoalaBearModel
public import Zkc.Construction.DomainTranscript

@[expose] public section

/-! Replay both actual parties on one draw schedule. Only the holder's
source supplies the three words and the terminal vector. Check messages in
send order, with their nominal types, sites, and oracle identities. -/
set_option autoImplicit false
namespace ZkcSecurity.Examples.FriHonestExchange
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSource
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open Zkc.Construction.Domain (Payload)

inductive Transfer where
  | word (row : Ty) (stored : PublishedWords.Word model row)
  | toHolder (site : String) (payload : Payload model.toCarriers)
  | toVerifier (site : String) (payload : Payload model.toCarriers)

structure Traffic where
  messages : List Transfer := []
  fields : List Octic := []
  positions : List Nat := []

abbrev refuse {A : Type} (state : Traffic) : PIR.Execution Traffic String A :=
  ⟨.stopped .refused, state, []⟩

def holder : PublishedWords.Table model →
    PIR.MonadHandler Id (participantInterfaceOn model.toCarriers) Traffic String := fun _ op s ↦
  match op with
  | .receive (.field d) site 1 => match s.fields with
    | beta :: rest =>
      let payload : Payload model.toCarriers := .field extension beta
      match payload.value (.field d) with
      | some value => ⟨.returned value,
          {s with fields := rest, messages := s.messages ++ [.toHolder site payload]}, []⟩
      | none => refuse s
    | [] => refuse s
  | .receive .index site 1 => match s.positions with
    | pos :: rest => ⟨.returned pos, {s with positions := rest, messages := s.messages ++ [.toHolder site (.index pos)]}, []⟩
    | [] => refuse s
  | .send (ty := .vector d) site 1 xs =>
    ⟨.returned (), {s with messages := s.messages ++ [.toVerifier site (.vector d xs)]}, []⟩
  | _ => refuse s

def publish : PublishedWords.Chooser Id model Traffic String := fun req _ s ↦
  match req.holderData with
  | none => refuse s
  | some xs => ⟨.returned xs, {s with messages := s.messages ++ [.word req.kind.answer (PublishedWords.word req xs)]}, []⟩

def replay : PublishedWords.Table model →
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

def receive : PublishedWords.Chooser Id model Traffic String := fun req _ s ↦
  match s.messages with
  | .word row stored :: rest =>
    if same : row = req.kind.answer then
      if stored.kind == req.kind && stored.anchor == req.anchor && stored.location == req.location &&
          stored.rows == req.rows && stored.holder == req.holder && stored.receivers == req.receivers && req.holderData.isNone then
        ⟨.returned (same ▸ stored.cells), {s with messages := rest}, []⟩
      else refuse s
    else refuse s
  | _ => refuse s


/-- The two roles consume the same chronological traffic. The holder alone
starts with the private vector. Any stop or unconsumed message remains
visible in the two complete execution records. -/
def exchange (shift : Octic) (word : List Octic) (fields : List Octic) (positions : List Nat) :
    Execution model Traffic String × Execution model Traffic String :=
  let prover := PublishedWords.sourceRunM (start 0 word shift 3 8 0 {fields, positions}) holder publish
  let traffic := prover.state.oracle.provider.auxiliary
  (prover, verifier (model := model) (m := Id) shift 3 8 0 {messages := traffic.messages} replay receive)

/-- A receiving role has no private payload. Matching the original occurrence
delivers the exact cells and consumes one publication from the shared wire. -/
theorem receiveMatching (request : OraclePublication.Request model)
    (cells : List (model.Value request.kind.answer)) (tail : Traffic) (words : PublishedWords.Table model) :
    receive {request with holderData := none} words
      {tail with messages := .word _ (PublishedWords.word request cells) :: tail.messages} =
        ⟨.returned cells, tail, []⟩ := by
  simp [receive, PublishedWords.word]

theorem publishPrivate (request : OraclePublication.Request model)
    (cells : List (model.Value request.kind.answer)) (supplied : request.holderData = some cells)
    (before : Traffic) (words : PublishedWords.Table model) :
    publish request words before = ⟨.returned cells,
      {before with messages := before.messages ++ [.word _ (PublishedWords.word request cells)]}, []⟩ := by
  simp [publish, supplied]

end ZkcSecurity.Examples.FriHonestExchange
