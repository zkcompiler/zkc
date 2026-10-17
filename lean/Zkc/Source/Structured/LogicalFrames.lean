module

public import Zkc.Source.Structured.LogicalChecking
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Loop frames: internal observations of a retained repeat.

An owner's boundary does not show the values a repeat carries between its
iterations. A loop frame is the masked state that enters one iteration of one
repeat occurrence at one participant, together with the iteration index. Frame
terms read an owner binder, a carried slot, the index, a supplied constant or a
view; frame atoms apply vocabulary predicates with the vocabulary's meanings. A
frame invariant is a list of frame atoms. Binders stay the owner's: a loop never
chooses or changes them.

Execution records actions, not frames, so a frame invariant is established by a
proof rule rather than read from a trace. `Repeat.loop_frames` turns a step
obligation on the actual callback, quantified over every reply, into the
invariant at the frames the loop reaches. The export form names the repeat
occurrence by its site in the owner body, the observed participant and carried
slots by position; `checkFrame` admits it against the repeat's typed state and
scopes. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

/-- Arguments of a frame atom. A carried slot is read from the frame, never from
the owner's boundary or store; a binder is read from the owner's binders. -/
inductive FrameTerm (V : Vocabulary) (Value : Ty → Type) (state : List Ty)
    (context : List (LogicalType V.Sorts)) : LogicalType V.Sorts → Type where
  | binder {type : LogicalType V.Sorts} (ref : Var context type) :
      FrameTerm V Value state context type
  | carried {type : Ty} (slot : Var state type) : FrameTerm V Value state context (.native type)
  | iteration : FrameTerm V Value state context (.native .index)
  | supplied {type : Ty} (value : Value type) : FrameTerm V Value state context (.native type)
  | view (view : V.Views) (argument : FrameTerm V Value state context (V.viewInput view)) :
      FrameTerm V Value state context (V.viewOutput view)

structure FrameAtom (V : Vocabulary) (Value : Ty → Type) (state : List Ty)
    (context : List (LogicalType V.Sorts)) where
  predicate : V.Predicates
  arguments : Values (FrameTerm V Value state context) (V.arguments predicate)

/-- The masked state entering iteration `index` at one participant. -/
structure Frame (Value : Ty → Type) (state : List Ty) where
  index : Nat
  carried : Values (Component Value) state

section Reading
variable {V : Vocabulary} {Value : Ty → Type} (interpretation : Interpretation V Value)
  (indexValue : Nat → Value .index) {state : List Ty} {context : List (LogicalType V.Sorts)}
  (binders : Values interpretation.Denote context) (frame : Frame Value state)

def FrameTerm.read : {type : LogicalType V.Sorts} →
    FrameTerm V Value state context type → Option (interpretation.Denote type)
  | _, .binder ref => some (binders.get ref)
  | _, .carried slot => frame.carried.get slot
  | _, .iteration => some (indexValue frame.index)
  | _, .supplied value => some value
  | _, .view code argument => (argument.read) >>= interpretation.view code

def readFrameTerms : {types : List (LogicalType V.Sorts)} →
    Values (FrameTerm V Value state context) types → Option (Values interpretation.Denote types)
  | _, .nil => some .nil
  | _, .cons term rest =>
    match term.read interpretation indexValue binders frame, readFrameTerms rest with
    | some value, some values => some (.cons value values)
    | _, _ => none

/-- An atom holds when every argument reads and the meaning holds; an absent
carried slot makes it false rather than choosing a value. -/
def FrameAtom.Holds (atom : FrameAtom V Value state context) : Prop :=
  ∃ arguments, readFrameTerms interpretation indexValue binders frame atom.arguments = some arguments ∧
    interpretation.holds atom.predicate arguments

abbrev FrameInvariant (V : Vocabulary) (Value : Ty → Type) (state : List Ty)
    (context : List (LogicalType V.Sorts)) := List (FrameAtom V Value state context)

def FrameInvariant.Holds (invariant : FrameInvariant V Value state context) : Prop :=
  ∀ atom ∈ invariant, atom.Holds interpretation indexValue binders frame

end Reading

section Laws
variable {V : Vocabulary} {Value : Ty → Type} {interpretation : Interpretation V Value}
  {indexValue : Nat → Value .index} {state : List Ty} {context : List (LogicalType V.Sorts)}

/-- A binder reads the owner's value at every frame. -/
theorem frame_binder_independent {type : LogicalType V.Sorts} (ref : Var context type)
    (binders : Values interpretation.Denote context) (first second : Frame Value state) :
    (FrameTerm.binder (Value := Value) (state := state) ref).read interpretation indexValue binders first =
      (FrameTerm.binder (Value := Value) (state := state) ref).read interpretation indexValue binders second :=
  rfl

/-- A carried slot reads the frame, never the binders. -/
theorem carried_binder_independent {type : Ty} (slot : Var state type)
    (left right : Values interpretation.Denote context) (frame : Frame Value state) :
    (FrameTerm.carried (V := V) (context := context) slot).read interpretation indexValue left frame =
      (FrameTerm.carried (V := V) (context := context) slot).read interpretation indexValue right frame :=
  rfl

/-- A masked-away slot never satisfies an atom that reads it. -/
theorem frame_absent_argument (atom : FrameAtom V Value state context)
    (binders : Values interpretation.Denote context) (frame : Frame Value state)
    (absent : readFrameTerms interpretation indexValue binders frame atom.arguments = none) :
    ¬ atom.Holds interpretation indexValue binders frame := by
  rintro ⟨arguments, present, _⟩
  rw [absent] at present
  cases present

end Laws

/-! ### The loop rule -/

end Zkc.Source.Structured.Logical

namespace Zkc.Source.Structured.Repeat

variable {F G : Type} {I : PIR.Signature}

/-- A step obligation on the actual masked callback step, for every reply,
establishes the invariant at the frame reached after any number of iterations.
Stops need no invariant; the frame index advances with each returned iteration. -/
theorem loop_frames (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (interaction : PIR.Interaction I)
    (valid : Nat → Values (Component (assignment F G)) spec.state → interaction.Phase → Prop)
    (preserved : ∀ index state phase, valid index state phase →
      PIR.Boundary.Returns interaction (fun result next => valid (index + 1) result next)
        (step spec context self captures body state index) phase)
    (start count : Nat) (state : Values (Component (assignment F G)) spec.state)
    (phase : interaction.Phase) (initial : valid start state phase) :
    PIR.Boundary.Returns interaction (fun result next => valid (start + count) result next)
      (loop spec context self captures body start count state) phase := by
  induction count generalizing start state phase with
  | zero =>
    rw [loop_zero]
    exact initial
  | succ count ih =>
    rw [loop_succ]
    apply PIR.Boundary.returns_bind interaction _ _
      (fun result next => valid (start + 1) result next)
    · exact preserved start state phase initial
    · intro result next reached
      have later := ih (start + 1) _ next reached
      simpa only [Nat.add_assoc, Nat.add_comm 1 count] using later

end Zkc.Source.Structured.Repeat

namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

/-! ### Export form -/

/-- An exported frame argument: an owner binder, a carried slot or the index. -/
inductive RawFrameTerm where
  | binder (position : Nat)
  | carried (slot : Nat)
  | iteration
  deriving DecidableEq, Repr

structure RawFrameAtom where
  predicate : Identity
  arguments : List RawFrameTerm
  deriving DecidableEq, Repr

/-- The repeat occurrence is named by its site in the owner body; the observed
participant by its local role. -/
structure RawFrame where
  site : String
  role : Nat
  atoms : List RawFrameAtom
  deriving DecidableEq, Repr

inductive FrameRefusal where
  | unknownRepeat (site : String)
  | unknownPredicate (identity : Identity)
  | unboundBinder (position : Nat)
  | sortMismatch (position : Nat)
  | carriedMismatch (slot role : Nat)
  | iterationMismatch
  | arityMismatch (identity : Identity)
  deriving DecidableEq, Repr

variable {V : Vocabulary} [DecidableEq V.Sorts] (resolution : Resolution V) {Value : Ty → Type}

/-- A carried slot must exist with the expected type, and its scope must
contain the observed role: a slot hidden from that participant is refused
rather than read as always absent. -/
def checkFrameTerm (spec : RepeatSpec) (role : Nat) (context : List (LogicalType V.Sorts))
    (expected : LogicalType V.Sorts) :
    RawFrameTerm → Except FrameRefusal (FrameTerm V Value spec.state context expected)
  | .binder position => match Var.decode context expected position with
    | some ref => .ok (.binder ref)
    | none => if position < context.length then .error (.sortMismatch position)
      else .error (.unboundBinder position)
  | .carried slot => match expected with
    | .native type => match Var.decode spec.state type slot with
      | some ref =>
        if (spec.stateScopes[slot]?.getD []).contains role then .ok (.carried ref)
        else .error (.carriedMismatch slot role)
      | none => .error (.carriedMismatch slot role)
    | .sort _ => .error (.carriedMismatch slot role)
  | .iteration => match expected with
    | .native .index => .ok .iteration
    | _ => .error .iterationMismatch

def checkFrameTerms (spec : RepeatSpec) (role : Nat) (identity : Identity)
    (context : List (LogicalType V.Sorts)) :
    (types : List (LogicalType V.Sorts)) → List RawFrameTerm →
      Except FrameRefusal (Values (FrameTerm V Value spec.state context) types)
  | [], [] => .ok .nil
  | type :: types, term :: terms => do
    let head ← checkFrameTerm spec role context type term
    let tail ← checkFrameTerms spec role identity context types terms
    pure (.cons head tail)
  | _, _ => .error (.arityMismatch identity)

def checkFrameAtom (spec : RepeatSpec) (role : Nat) (context : List (LogicalType V.Sorts))
    (raw : RawFrameAtom) : Except FrameRefusal (FrameAtom V Value spec.state context) :=
  match resolution.predicate raw.predicate with
  | none => .error (.unknownPredicate raw.predicate)
  | some code => do
    let arguments ← checkFrameTerms spec role raw.predicate context (V.arguments code) raw.arguments
    pure ⟨code, arguments⟩

def checkFrameAtoms (spec : RepeatSpec) (role : Nat) (context : List (LogicalType V.Sorts)) :
    List RawFrameAtom → Except FrameRefusal (FrameInvariant V Value spec.state context)
  | [] => .ok []
  | first :: rest => do
    let head ← checkFrameAtom resolution spec role context first
    let tail ← checkFrameAtoms spec role context rest
    pure (head :: tail)

/-- Admit an exported frame invariant against the repeat occurrences of the
owner body, resolved by site, within the owner's checked binder context. -/
def checkFrame (repeats : String → Option RepeatSpec) (context : List (LogicalType V.Sorts))
    (raw : RawFrame) : Except FrameRefusal ((spec : RepeatSpec) × FrameInvariant V Value spec.state context) :=
  match repeats raw.site with
  | none => .error (.unknownRepeat raw.site)
  | some spec => do
    let atoms ← checkFrameAtoms (Value := Value) resolution spec raw.role context raw.atoms
    pure ⟨spec, atoms⟩

end Zkc.Source.Structured.Logical
