module

public import Zkc.Construction.Participant
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-! Pure participant layout transformations. These transform syntax only;
structural admission and source correspondence remain separate obligations. -/
set_option autoImplicit false
namespace Zkc.Construction.LayoutPermutation

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


end Zkc.Construction.LayoutPermutation
