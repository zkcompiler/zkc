module

public import Zkc.Source.Structured.LogicalContext

@[expose] public section

/-! Admission of exported logical-context metadata against one signature.

An export names binder sorts and predicates only by identity (declaration and
normalized static arguments), binders by position and observations by
direction, port and role. A library resolution turns identities into typed
codes; checking then builds intrinsically typed terms. Nothing is defaulted:
an unknown identity, an unbound or wrongly sorted binder, an observation of the
wrong type or scope, and a wrong number of arguments are refused by name. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

/-- An exported sort: a native type or a library identity. -/
inductive RawSort where
  | native (type : Ty)
  | library (identity : Identity)
  deriving DecidableEq, Repr

/-- An exported argument: a binder position or a boundary observation. -/
inductive RawTerm where
  | binder (position : Nat)
  | observed (direction : ContractDirection) (port role : Nat)
  deriving DecidableEq, Repr

structure RawAtom where
  predicate : Identity
  arguments : List RawTerm
  deriving DecidableEq, Repr

structure RawContext where
  binders : List RawSort
  atoms : List RawAtom
  deriving DecidableEq, Repr

/-- A library's resolution of exported identities. Each answer is sound for the
identity it was asked about, so a resolved code carries exactly that identity. -/
structure Resolution (V : Vocabulary) where
  sort : Identity → Option V.Sorts
  predicate : Identity → Option V.Predicates
  sort_sound : ∀ identity code, sort identity = some code → V.sortIdentity code = identity
  predicate_sound : ∀ identity code, predicate identity = some code →
    V.predicateIdentity code = identity

/-- A sound resolution from candidate codes: a candidate is accepted only when
its own identity is exactly the exported one. -/
def Resolution.ofCandidates (V : Vocabulary) (sortCandidate : Identity → Option V.Sorts)
    (predicateCandidate : Identity → Option V.Predicates) : Resolution V where
  sort identity := (sortCandidate identity).bind fun code =>
    if V.sortIdentity code = identity then some code else none
  predicate identity := (predicateCandidate identity).bind fun code =>
    if V.predicateIdentity code = identity then some code else none
  sort_sound identity code resolved := by
    cases candidate : sortCandidate identity with
    | none => rw [candidate] at resolved; cases resolved
    | some found =>
      rw [candidate] at resolved
      change (if V.sortIdentity found = identity then some found else none) = some code at resolved
      split at resolved
      · cases resolved; assumption
      · cases resolved
  predicate_sound identity code resolved := by
    cases candidate : predicateCandidate identity with
    | none => rw [candidate] at resolved; cases resolved
    | some found =>
      rw [candidate] at resolved
      change (if V.predicateIdentity found = identity then some found else none) = some code at resolved
      split at resolved
      · cases resolved; assumption
      · cases resolved

inductive Refusal where
  | unknownSort (identity : Identity)
  | unknownPredicate (identity : Identity)
  | unboundBinder (position : Nat)
  | sortMismatch (position : Nat)
  | observationMismatch (direction : ContractDirection) (port role : Nat)
  | arityMismatch (identity : Identity)
  deriving DecidableEq, Repr

variable {V : Vocabulary} [DecidableEq V.Sorts] (resolution : Resolution V)

def checkSort : RawSort → Except Refusal (LogicalType V.Sorts)
  | .native type => .ok (.native type)
  | .library identity => match resolution.sort identity with
    | some code => .ok (.sort code)
    | none => .error (.unknownSort identity)

def checkSorts : List RawSort → Except Refusal (List (LogicalType V.Sorts))
  | [] => .ok []
  | first :: rest => do
    let head ← checkSort resolution first
    let tail ← checkSorts rest
    pure (head :: tail)

/-- Resolve an exported observation against the signature's typed ports, role
list and participant scopes. -/
def decodeSelector (signature : ProtocolSignature) (type : Ty) (direction : ContractDirection)
    (port role : Nat) : Option (BoundarySelector signature type) :=
  let typed : Option (BoundaryPort signature.inputs signature.outputs type) :=
    match direction with
    | .input => (Var.decode signature.inputs type port).map .input
    | .output => (Var.decode signature.outputs type port).map .output
  match typed with
  | none => none
  | some typedPort =>
    if bound : role < signature.roles.length then
      if inScope : ((match typedPort with
          | .input _ => signature.inputScopes
          | .output _ => signature.outputScopes)[typedPort.index]?.getD []).contains role = true then
        some ⟨typedPort, ⟨role, bound⟩, inScope⟩
      else none
    else none

variable {Value : Ty → Type} (signature : ProtocolSignature)

def checkTerm (context : List (LogicalType V.Sorts)) (expected : LogicalType V.Sorts) :
    RawTerm → Except Refusal (Term V Value signature context expected)
  | .binder position => match Var.decode context expected position with
    | some ref => .ok (.key (.binder ref))
    | none => if position < context.length then .error (.sortMismatch position)
      else .error (.unboundBinder position)
  | .observed direction port role => match expected with
    | .native type => match decodeSelector signature type direction port role with
      | some selector => .ok (.observed selector)
      | none => .error (.observationMismatch direction port role)
    | .sort _ => .error (.observationMismatch direction port role)

def checkTerms (identity : Identity) (context : List (LogicalType V.Sorts)) :
    (types : List (LogicalType V.Sorts)) → List RawTerm →
      Except Refusal (Values (Term V Value signature context) types)
  | [], [] => .ok .nil
  | type :: types, term :: terms => do
    let head ← checkTerm signature context type term
    let tail ← checkTerms identity context types terms
    pure (.cons head tail)
  | _, _ => .error (.arityMismatch identity)

def checkAtom (context : List (LogicalType V.Sorts)) (raw : RawAtom) :
    Except Refusal (Atom V Value signature context) :=
  match resolution.predicate raw.predicate with
  | none => .error (.unknownPredicate raw.predicate)
  | some code => do
    let arguments ← checkTerms signature raw.predicate context (V.arguments code) raw.arguments
    pure ⟨code, arguments⟩

def checkAtoms (context : List (LogicalType V.Sorts)) :
    List RawAtom → Except Refusal (List (Atom V Value signature context))
  | [] => .ok []
  | first :: rest => do
    let head ← checkAtom resolution signature context first
    let tail ← checkAtoms context rest
    pure (head :: tail)

/-- Check binder sorts first, then every atom in that context. -/
def checkContext (raw : RawContext) :
    Except Refusal ((context : List (LogicalType V.Sorts)) × List (Atom V Value signature context)) := do
  let context ← checkSorts resolution raw.binders
  let atoms ← checkAtoms resolution signature context raw.atoms
  pure ⟨context, atoms⟩

/-- The first binder of a context decodes at position zero, for any decision
procedure on sorts; this lets checks over symbolic static arguments compute. -/
theorem decode_first_binder {T : Type} [DecidableEq T] (head : T) (rest : List T) :
    Var.decode (head :: rest) head 0 = some .here :=
  Var.decode_index (Γ := head :: rest) Var.here

/-- A checked atom's predicate carries exactly the exported identity. -/
theorem checkAtom_identity {context : List (LogicalType V.Sorts)} {raw : RawAtom}
    {atom : Atom V Value signature context}
    (checked : checkAtom resolution signature context raw = .ok atom) :
    V.predicateIdentity atom.predicate = raw.predicate := by
  unfold checkAtom at checked
  split at checked
  · cases checked
  · rename_i code resolved
    cases arguments : checkTerms signature raw.predicate context (V.arguments code) raw.arguments with
    | error refusal =>
      rw [arguments] at checked
      cases checked
    | ok values =>
      rw [arguments] at checked
      cases checked
      exact resolution.predicate_sound _ _ resolved

/-- Exported aliases name one identity, so they check to one predicate code
and therefore read one meaning under every interpretation. -/
theorem checkAtom_alias {context : List (LogicalType V.Sorts)} {first second : RawAtom}
    {left right : Atom V Value signature context}
    (leftChecked : checkAtom resolution signature context first = .ok left)
    (rightChecked : checkAtom resolution signature context second = .ok right)
    (same : first.predicate = second.predicate) : left.predicate = right.predicate := by
  unfold checkAtom at leftChecked rightChecked
  rw [same] at leftChecked
  split at leftChecked
  · cases leftChecked
  · rename_i code resolved
    rw [resolved] at rightChecked
    dsimp only at rightChecked
    cases leftArguments : checkTerms signature second.predicate context (V.arguments code) first.arguments with
    | error refusal => rw [leftArguments] at leftChecked; cases leftChecked
    | ok leftValues =>
      cases rightArguments : checkTerms signature second.predicate context (V.arguments code)
          second.arguments with
      | error refusal => rw [rightArguments] at rightChecked; cases rightChecked
      | ok rightValues =>
        rw [leftArguments] at leftChecked
        rw [rightArguments] at rightChecked
        cases leftChecked
        cases rightChecked
        rfl

end Zkc.Source.Structured.Logical
