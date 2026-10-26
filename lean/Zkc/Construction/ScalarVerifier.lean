module

public import Zkc.Construction.OriginProjection
public import Zkc.Construction.Compiled
public import Zkc.Construction.Uniform.SourceProcess

@[expose] public section

/-! Actual Domain execution at the retained scalar ABI. The oracle mapping is
fixed by the artifact's repetition profile, before the caller's oracle/cache.
The initial scalar history is an opaque prefix, never a nominal input row. -/
set_option autoImplicit false
namespace Zkc.Construction.ScalarVerifier
open Zkc.Source Zkc.Source.Structured
open Zkc.Construction.Uniform.DomainAdapter

/-- Repetition coordinates are absent from the retained scalar oracle ABI.
Finite artifacts use their literal static origins. This choice is derived from
artifact syntax, never supplied by security evidence. -/
def origin (artifact : Participant) (value : Origin) : Origin :=
  if artifact.instructions.any (fun instruction => match instruction.operation with
      | .loop .. => true | _ => false) then
    value.withoutCoordinates
  else value

variable {F G : Type}

def sourceValue (handle : Nat) (published : List (Value F G)) :
    Slot → (ty : Ty) → Option (assignment F G ty)
  | .held reference, ty => (published[reference]?).bind (Value.decode ty)
  | .service, .service _ => some handle
  | _, _ => none

/-- Exact policy-selected source inputs, including absent private components. -/
def sourceInputs (handle : Nat) (published : List (Value F G)) :
    List Slot → (types : List Ty) → Values (Component (assignment F G)) types
  | _, [] => .nil
  | slots, ty :: rest => .cons (sourceValue handle published (slots.headD .absent) ty)
      (sourceInputs handle published slots.tail rest)

def inputs (context : Context) (published : List (Value F G)) :
    Option (Domain.Environment (uniformCarriers F G)) :=
  (embedValues published).map (· ++ [.transcript context.suite []])

def acceptance (position : Nat) (result : Domain.Result (uniformCarriers F G)) : Option Bool :=
  match result.values[position]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- Read the entire scalar suffix or refuse; never drop an unrepresentable
nominal message from an otherwise valid proof. -/
def proof (unread : Domain.Proof (uniformCarriers F G)) : Option (Proof F G) :=
  unread.mapM readbackPayload

@[simp] theorem proof_embed (unread : Proof F G) : proof (embedProof unread) = some unread := by
  induction unread with
  | nil => rfl
  | cons head tail ih =>
      simp only [proof, embedProof] at ih ⊢
      simp only [List.map_cons, List.mapM_cons, readbackPayload_embed, ih]
      rfl

/-- A failed ABI readback explicitly refuses. Its caller's original proof is
retained because the nominal suffix has no scalar representation. The installed
runner's embedding law proves this branch unreachable for its scalar inputs. -/
def observation (position : Nat) (original : Proof F G)
    (outcome : PIR.Outcome (Domain.Result (uniformCarriers F G)))
    (unread : Domain.Proof (uniformCarriers F G)) : PIR.Outcome (Option Bool) × Proof F G :=
  match proof unread with
  | some suffix => (mapOutcome (acceptance position) outcome, suffix)
  | none => (.stopped .refused, original)

@[simp] theorem observation_embed (position : Nat) (original unread : Proof F G)
    (outcome : PIR.Outcome (Domain.Result (uniformCarriers F G))) :
    observation position original outcome (embedProof unread) =
      (mapOutcome (acceptance position) outcome, unread) := by
  simp [observation]

/-- An unsupported message refuses even when surrounded by scalar messages. -/
theorem proof_refuses_index (earlier later : Proof F G) (index : Nat) :
    proof (embedProof earlier ++ .index index :: embedProof later) = none := by
  simp [proof, List.mapM_append, List.mapM_cons, readbackPayload]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual installed validator, selected at its checked Boolean output.
No relation/shape assumption restricts public values, proofs or oracle replies. -/
def verify {m : Type → Type} [Monad m] (program : Structured.Program) (context : Context)
    (artifact : Participant) (position : Nat) (challenge : History F G → m F)
    (published : List (Value F G)) (initial : History F G) (messages : Proof F G) :
    m (PIR.Outcome (Option Bool) × Proof F G) :=
  match inputs context published with
  | none => pure (.stopped .refused, messages)
  | some frame =>
      (fun result => observation position messages result.outcome result.state.proof) <$>
        Domain.run .validator (oracle (origin artifact) initial challenge)
          (Domain.participant (ringModel F G) program context artifact frame)
          ⟨frame, embedProof messages, ()⟩

/-- Eliminate the actual runner to its all-reply Process handler. -/
theorem verify_eq_runK {m : Type → Type} [Monad m] [LawfulMonad m]
    (program : Structured.Program) (context : Context) (artifact : Participant) (position : Nat)
    (challenge : History F G → m F) (published : List (Value F G))
    (frame : Domain.Environment (uniformCarriers F G)) (encoded : inputs context published = some frame)
    (initial : History F G) (messages : Proof F G) :
    verify program context artifact position challenge published initial messages =
      runK (origin artifact) initial challenge
        (Domain.participant (ringModel F G) program context artifact frame) messages
        (fun result unread => pure (.returned (acceptance position result), unread)) := by
  simp only [verify, encoded]
  have installed := congrArg (fun action =>
    (fun result => observation position messages result.1 result.2) <$> action)
    (run_actual (origin artifact) initial challenge
      (Domain.participant (ringModel F G) program context artifact frame) frame messages)
  simp only [Functor.map_map, observation_embed] at installed
  rw [installed]
  exact Zkc.Construction.Uniform.SourceProcess.run_map (origin artifact) initial challenge _ (acceptance position) messages

end Zkc.Construction.ScalarVerifier
