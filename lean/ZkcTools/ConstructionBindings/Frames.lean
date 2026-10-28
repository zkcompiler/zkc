module

public import ZkcTools.ConstructionBindings.Common

@[expose] public section

/-! Structural SSA descriptors for recursive construction bindings. This is a
syntax traversal, not an evaluator. Descriptors propose local instantiations;
the emitted correspondence and simulation proofs remain the authority. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Frames
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Repeat where
  path : List Nat
  offset : Nat
  site : String
  maximum : Nat
  count : Nat
  initial : List Nat
  yielded : List Nat
  sorts : List ValueSort
  body : List Zkc.Construction.Instruction
  deriving Repr, DecidableEq

/-- The selector naming convention is shared with the constructed-view printer.
It depends on the actual recursive path, not on a family callback name. -/
def selector (path : List Nat) : String :=
  path.foldl (fun name index => name ++ "Step" ++ toString index ++ "Body") "body"

def loopSelector (path : List Nat) : String :=
  selector path.dropLast ++ "Step" ++ toString (path.getLast?.getD 0)

def collect : Nat → List Zkc.Construction.Instruction → Nat → List Nat → Except String (List Repeat)
  | 0, _, _, _ => .error "construction-binding-frame-depth"
  | fuel + 1, instructions, start, path => do
    let mut offset := start
    let mut repeats := []
    for (instruction, index) in instructions.zipIdx do
      unless instruction.operands.all (· < offset) do
        throw "construction-binding-frame-forward-reference"
      match instruction.operation with
      | .loop site maximum yielded =>
        let count :: initial := instruction.operands
          | throw "construction-binding-frame-loop-operands"
        let here := path ++ [index]
        let children ← collect fuel instruction.body
          (offset + 1 + instruction.results.length) here
        let arity := instruction.body.foldl (fun size step => size + step.results.length)
          (offset + 1 + instruction.results.length)
        unless yielded.length == instruction.results.length && yielded.all (· < arity) do
          throw "construction-binding-frame-yield"
        repeats := repeats ++ [⟨here, offset, site, maximum, count, initial,
          yielded, instruction.results, instruction.body⟩] ++ children
      | _ =>
        unless instruction.body.isEmpty do throw "construction-binding-frame-region"
      offset := offset + instruction.results.length
    return repeats

def analyze (artifact : Participant) : Except String (List Repeat) := do
  let repeats ← collect 1024 artifact.instructions artifact.inputs.length []
  let arity := artifact.instructions.foldl (fun size step => size + step.results.length)
    artifact.inputs.length
  unless artifact.returned.all (· < arity) do throw "construction-binding-frame-return"
  return repeats

/-- Match a full qualified source occurrence. Ambiguity is always a refusal. -/
def select (repeats : List Repeat) (site : String) : Except String Repeat :=
  unique "frame-occurrence" (repeats.filter (·.site == site))

/-- Read a local slot from the selected instruction's operands. This supplies
captures whose identity is fixed by an installed primitive law, not a number. -/
def callOperands (descriptor : Repeat) (helper : String) : Except String (List Nat) := do
  let instruction ← unique "frame-helper" (descriptor.body.filter fun step =>
    step.operation == .call helper)
  return instruction.operands

end ZkcTools.ConstructionBindings.Frames
