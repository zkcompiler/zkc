module

@[expose] public section

set_option autoImplicit false

/-!
# Breaking a logical line (FM1)

A logical line is a sequence of atoms: text, the opening and closing of a bracket, and the comma
that separates the items of a bracket. Flat, a comma is `, `. A logical line longer than 100
characters is broken inside a bracket, after its commas, with each item on its own line four
spaces deeper and the closing bracket on its own line.

FM1 says "inside its outermost bracket", and a line has several brackets at the outermost
level. The bracket chosen is the widest of the shallowest brackets that hold a comma; a tie goes
to the first. The lines that the break makes are broken again by the same rule when they are
still too long. A line without a bracket that holds a comma stays as it is.
-/

namespace Zkc.Frontend.Syntax.Layout

inductive Atom where
  | text (text : String)
  | opening (text : String)
  | closing (text : String)
  | comma
  deriving Inhabited, BEq

def Atom.flat : Atom → String
  | .text value | .opening value | .closing value => value
  | .comma => ", "

def Atom.width (atom : Atom) : Nat := atom.flat.length

def maxWidth : Nat := 100

def flatten (atoms : Array Atom) : String :=
  atoms.foldl (fun acc atom => acc ++ atom.flat) ""

def widthOf (atoms : Array Atom) (first last : Nat) : Nat := Id.run do
  let mut width := 0
  for i in [first:last] do
    width := width + atoms[i]!.width
  return width

/-- A bracket that may be broken: where it opens and closes, and its depth. -/
structure Candidate where
  opening : Nat
  closing : Nat
  depth : Nat
  width : Nat

/-- The brackets that hold a comma among their own items. -/
def candidates (atoms : Array Atom) : Array Candidate := Id.run do
  -- the open brackets: position, and whether a comma was seen at their level
  let mut stack : Array (Nat × Bool) := #[]
  let mut found : Array Candidate := #[]
  for i in [0:atoms.size] do
    match atoms[i]! with
    | .opening _ => stack := stack.push (i, false)
    | .closing _ =>
      match stack.back? with
      | some (opening, hasComma) =>
        stack := stack.pop
        if hasComma then
          found := found.push
            { opening, closing := i, depth := stack.size, width := widthOf atoms opening (i + 1) }
      | none => pure ()
    | .comma =>
      match stack.back? with
      | some (opening, _) => stack := stack.set! (stack.size - 1) (opening, true)
      | none => pure ()
    | .text _ => pure ()
  return found

def choose (found : Array Candidate) : Option Candidate := Id.run do
  let mut best : Option Candidate := none
  for candidate in found do
    match best with
    | none => best := some candidate
    | some current =>
      if candidate.depth < current.depth
          ∨ (candidate.depth == current.depth ∧ candidate.width > current.width)
          ∨ (candidate.depth == current.depth ∧ candidate.width == current.width
            ∧ candidate.opening < current.opening) then
        best := some candidate
  return best

/-- The items of the bracket opened at `opening`: the atoms between its commas. -/
def items (atoms : Array Atom) (opening closing : Nat) : Array (Array Atom) := Id.run do
  let mut result : Array (Array Atom) := #[]
  let mut current : Array Atom := #[]
  let mut depth := 0
  for i in [opening + 1:closing] do
    let atom := atoms[i]!
    match atom with
    | .opening _ => depth := depth + 1; current := current.push atom
    | .closing _ => depth := depth - 1; current := current.push atom
    | .comma =>
      if depth == 0 then
        result := result.push current
        current := #[]
      else current := current.push atom
    | .text _ => current := current.push atom
  result := result.push current
  return result

/-- The lines of a logical line at indentation `indent`. -/
partial def layout (indent : Nat) (atoms : Array Atom) : Array String :=
  let flat := flatten atoms
  if indent + flat.length ≤ maxWidth then #["".pushn ' ' indent ++ flat]
  else
    match choose (candidates atoms) with
    | none => #["".pushn ' ' indent ++ flat]
    | some candidate =>
      let head := atoms.extract 0 (candidate.opening + 1)
      let tail := atoms.extract candidate.closing atoms.size
      let parts := items atoms candidate.opening candidate.closing
      let itemLines := (parts.mapIdx fun index part =>
        let withComma := if index + 1 < parts.size then part.push (.text ",") else part
        layout (indent + 4) withComma).flatten
      layout indent head ++ itemLines ++ layout indent tail

end Zkc.Frontend.Syntax.Layout
