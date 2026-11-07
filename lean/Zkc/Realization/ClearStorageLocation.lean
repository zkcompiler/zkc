module

public import Zkc.Source.Structured.OracleOperations

@[expose] public section

/-! Recovering a logical publication location from its static construction path
and the actual enclosing iteration coordinates. An allocation ordinal is not a
source coordinate, especially when nested trip counts vary. -/

set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source.Structured

/-- Keep the complete call/loop path, erasing only dynamic iteration indices. -/
def staticFrames : List InvocationFrame → List InvocationFrame
  | [] => []
  | .application caller position :: rest => .application caller position :: staticFrames rest
  | .iteration owner position _ :: rest => .iteration owner position 0 :: staticFrames rest

def coordinates : List InvocationFrame → List Nat
  | [] => []
  | .application _ _ :: rest => coordinates rest
  | .iteration _ _ index :: rest => index :: coordinates rest

def staticLocation (location : OracleLocation) : OracleLocation :=
  { location with invocation.frames := staticFrames location.invocation.frames }

/-- Static paths plus ordered coordinates identify the entire invocation. -/
theorem frames_unique {left right : List InvocationFrame}
    (shape : staticFrames left = staticFrames right)
    (indices : coordinates left = coordinates right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons other tail => cases other <;> simp [staticFrames] at shape
  | cons frame rest ih =>
    cases right with
    | nil => cases frame <;> simp [staticFrames] at shape
    | cons other tail =>
      cases frame with
      | application caller position =>
        cases other with
        | application otherCaller otherPosition =>
          simp only [staticFrames, List.cons.injEq, InvocationFrame.application.injEq] at shape
          obtain ⟨⟨rfl, rfl⟩, shape⟩ := shape
          exact congrArg (List.cons _) (ih shape indices)
        | iteration => simp [staticFrames] at shape
      | iteration owner position index =>
        cases other with
        | application => simp [staticFrames] at shape
        | iteration otherOwner otherPosition otherIndex =>
          simp only [staticFrames, List.cons.injEq, InvocationFrame.iteration.injEq] at shape
          obtain ⟨⟨rfl, rfl, _⟩, shape⟩ := shape
          simp only [coordinates, List.cons.injEq] at indices
          obtain ⟨rfl, indices⟩ := indices
          exact congrArg (List.cons _) (ih shape indices)

theorem location_unique {left right : OracleLocation}
    (shape : staticLocation left = staticLocation right)
    (indices : coordinates left.invocation.frames = coordinates right.invocation.frames) :
    left = right := by
  rcases left with ⟨⟨root, frames⟩, definition, row⟩
  rcases right with ⟨⟨otherRoot, otherFrames⟩, otherDefinition, otherRow⟩
  simp only [staticLocation, OracleLocation.mk.injEq, InvocationCoordinate.mk.injEq] at shape
  rcases shape with ⟨⟨rfl, path⟩, rfl, rfl⟩
  cases frames_unique path indices
  rfl

/-- Erasing the index does not erase a repeat or change its nesting depth. -/
theorem coordinates_length_static (frames : List InvocationFrame) :
    (coordinates (staticFrames frames)).length = (coordinates frames).length := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => cases frame <;> simp [staticFrames, coordinates, ih]

theorem coordinates_length_of_static {left right : List InvocationFrame}
    (shape : staticFrames left = staticFrames right) :
    (coordinates left).length = (coordinates right).length := by
  simpa only [coordinates_length_static] using congrArg (fun frames ↦ (coordinates frames).length) shape

end Zkc.Realization.ClearStorage
