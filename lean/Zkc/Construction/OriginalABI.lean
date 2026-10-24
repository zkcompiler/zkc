module

public import Zkc.Construction.OriginalSimulation

@[expose] public section

/-! Explicit live-value relations between the full original optional ABI and
physical nominal frames. No unconstrained/free location is permitted. Service
capabilities are retained as capabilities, never decoded from proof payloads.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source

inductive Location where
  | absent
  | data (reference : Nat)
  | capability (handle : Nat)
  deriving DecidableEq, Repr

variable {carriers : Structured.Carriers}

def ComponentHolds (frame : Domain.Environment carriers) :
    Location → (ty : Structured.Ty) → Option (carriers.Value ty) → Prop
  | .absent, _, value => value = none
  | .data reference, ty, value =>
      ∃ actual, value = some actual ∧ (frame[reference]?).bind (Domain.Value.decode ty) = some actual
  | .capability handle, .service _, value => value = some handle
  | .capability _, _, _ => False

/-- Both tuple lengths must agree. Every source output, including an absent
role component or a private capability, is accounted for. -/
def ValuesHolds (frame : Domain.Environment carriers) :
    List Location → {types : List Structured.Ty} → Values (Component carriers.Value) types → Prop
  | [], [], .nil => True
  | location :: locations, _ :: _, .cons value rest =>
      ComponentHolds frame location _ value ∧ ValuesHolds frame locations rest
  | _, _, _ => False

/-- Input decoding distinguishes a hidden optional component from a malformed
physical value. Runtime service handles are supplied by the checked ABI map. -/
def readComponent (frame : Domain.Environment carriers) :
    Location → (ty : Structured.Ty) → Option (Component carriers.Value ty)
  | .absent, _ => some none
  | .data reference, ty => ((frame[reference]?).bind (Domain.Value.decode ty)).map some
  | .capability handle, .service _ => some (some handle)
  | .capability _, _ => none

/-- Read the entire original input tuple. Both layout-length mismatches and
nominal data-decoding failures refuse; neither fabricates an absent component. -/
def readComponents (frame : Domain.Environment carriers) :
    (types : List Structured.Ty) → List Location → Option (Values (Component carriers.Value) types)
  | [], [] => some .nil
  | ty :: types, location :: locations => do
      let value ← readComponent frame location ty
      let rest ← readComponents frame types locations
      return .cons value rest
  | _, _ => none

theorem readComponent_iff (frame : Domain.Environment carriers) (location : Location)
    (ty : Structured.Ty) (value : Component carriers.Value ty) :
    readComponent frame location ty = some value ↔ ComponentHolds frame location ty value := by
  cases location with
  | absent => simp [readComponent, ComponentHolds, eq_comm]
  | data reference =>
      cases decoded : (frame[reference]?).bind (Domain.Value.decode ty) <;>
        simp [readComponent, ComponentHolds, decoded, eq_comm]
  | capability handle => cases ty <;> simp [readComponent, ComponentHolds, eq_comm]

/-- Executable input decoding and the full ABI relation have exactly the same
meaning, including capabilities, absent components and nominal field sorts. -/
theorem readComponents_iff (frame : Domain.Environment carriers) (types : List Structured.Ty)
    (locations : List Location) (values : Values (Component carriers.Value) types) :
    readComponents frame types locations = some values ↔ ValuesHolds frame locations values := by
  induction types generalizing locations with
  | nil => cases locations <;> cases values <;> simp [readComponents, ValuesHolds]
  | cons ty types ih =>
      cases values with
      | cons value rest =>
        cases locations with
        | nil => simp [readComponents, ValuesHolds]
        | cons location locations =>
          constructor
          · intro found
            cases head : readComponent frame location ty with
            | none => simp [readComponents, head] at found
            | some actual =>
              cases tail : readComponents frame types locations with
              | none => simp [readComponents, head, tail] at found
              | some remaining =>
                simp only [readComponents, head, tail] at found
                cases found
                exact ⟨(readComponent_iff _ _ _ _).mp head, (ih _ _).mp tail⟩
          · intro related
            have head := (readComponent_iff _ _ _ _).mpr related.1
            have tail := (ih _ _).mpr related.2
            simp only [readComponents, head, tail]
            rfl

/-- The artifact input declaration and source input layout are independent
metadata; neither reads or reconstructs the original body from instructions. -/
structure InputABI where
  sorts : List ValueSort
  locations : List Location

/-- Every original component agrees at its selected return and frame locations.
This helper does not constrain extra artifact slots, return arity, transcript
history or source frames. A complete root contract must fix those separately. -/
def Returns {types : List Structured.Ty} (outputs live : List Location)
    (original : Values (Component carriers.Value) types × State carriers)
    (constructed : Domain.Result carriers) : Prop :=
  ValuesHolds constructed.values outputs original.1 ∧
    ValuesHolds constructed.environment live original.1

/-- A matching data coordinate recovers precisely its original nominal value. -/
theorem ComponentHolds.data {frame : Domain.Environment carriers} {reference : Nat}
    {ty : Structured.Ty} {value : Option (carriers.Value ty)}
    (related : ComponentHolds frame (.data reference) ty value) :
    ∃ actual, value = some actual ∧ (frame[reference]?).bind (Domain.Value.decode ty) = some actual :=
  related

/-- A hidden source component cannot be related to a fabricated physical value. -/
theorem ComponentHolds.absent {frame : Domain.Environment carriers} {ty : Structured.Ty}
    {value : Option (carriers.Value ty)} (related : ComponentHolds frame .absent ty value) :
    value = none := related

end Zkc.Construction.Original
