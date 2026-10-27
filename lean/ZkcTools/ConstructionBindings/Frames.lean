module

public import ZkcTools.ConstructionBindings.Common
public import Mathlib.Data.List.Perm.Basic

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

/-- A formal layout perturbation: rename input references throughout the
recursive SSA tree, including loop yields. Newly allocated slots retain their
indices. The caller supplies a permutation, and separate structural checks and
full simulations check the resulting participant. No byte identity is made. -/
def reindexInstructions (rename : Nat → Nat) : Nat → List Zkc.Construction.Instruction → List Zkc.Construction.Instruction
  | 0, instructions => instructions
  | fuel + 1, instructions => instructions.map fun instruction =>
      { instruction with
        operands := instruction.operands.map rename
        operation := match instruction.operation with
          | .loop site maximum yielded => .loop site maximum (yielded.map rename)
          | .localService port request template coordinates =>
              .localService port { request with operands := request.operands.map rename }
                template (coordinates.map rename)
          | operation => operation
        body := reindexInstructions rename fuel instruction.body }

/-- Insert a pure index-coordinate allocation before the root. Every allocated
SSA reference (including nested induction/carry slots) shifts, while input
references keep their identities. Structural admission and full connection
checking remain separate obligations for this syntax transformation. -/
def prependCoordinates (artifact : Participant) : Participant :=
  let rename := fun reference =>
    if reference < artifact.inputs.length then reference else reference + 1
  { artifact with
    instructions := ⟨.indicesEmpty, [], [.indices], []⟩ ::
      reindexInstructions rename 1024 artifact.instructions
    returned := artifact.returned.map rename }

def permuteInputs (artifact : Participant) (order : List Nat) : Except String Participant := do
  unless order.length == artifact.inputs.length && decide (order.Perm (List.range order.length)) do
    throw "construction-binding-input-permutation"
  let inputs ← order.mapM fun reference =>
    match artifact.inputs[reference]? with
    | some sort => .ok sort
    | none => .error "construction-binding-input-permutation"
  let rename := fun reference =>
    if reference < order.length then order.idxOf reference else reference
  return { artifact with
    inputs := inputs
    instructions := reindexInstructions rename 1024 artifact.instructions
    returned := artifact.returned.map rename }

end ZkcTools.ConstructionBindings.Frames
