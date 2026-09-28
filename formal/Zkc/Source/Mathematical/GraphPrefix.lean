import Zkc.Source.Mathematical.Graph

/-! Checked prefixes for iterative graph construction.

A prefix connects the original context to the current context. Frames are
stored in reverse source order. Closing a prefix wraps the accumulated region
before visiting the preceding frame, so flat graphs need no recursive return
stack. Nested map/fold bodies retain their ordinary intrinsic representation.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Graph

variable {Role : Type} [DecidableEq Role] {parties : List Role} {algebra : Algebra}

inductive Prefix (parties : List Role) (algebra : Algebra) :
    List (Port Role algebra.Ty) → List (Port Role algebra.Ty) → Type where
  | nil {Γ} : Prefix parties algebra Γ Γ
  | operation {Γ Δ roles} (previous : Prefix parties algebra Γ Δ)
      (op : algebra.Op) (args : Inputs Δ (algebra.arguments op))
      (availability : roles = Inputs.available parties args) :
      Prefix parties algebra Γ (⟨roles, algebra.result op⟩ :: Δ)
  | tuple {Γ Δ types roles} (previous : Prefix parties algebra Γ Δ)
      (args : Inputs Δ types) (availability : roles = Inputs.available parties args) :
      Prefix parties algebra Γ (⟨roles, algebra.product types⟩ :: Δ)
  | project {Γ Δ types ty} (previous : Prefix parties algebra Γ Δ)
      (value : Input Δ (algebra.product types)) (component : Var types ty) :
      Prefix parties algebra Γ (⟨value.1, ty⟩ :: Δ)
  | map {Γ Δ captures outputs} (previous : Prefix parties algebra Γ Δ)
      (count : algebra.Count) (capture : Operands Δ captures)
      (body : Region parties algebra (⟨parties, algebra.index count⟩ :: captures) outputs) :
      Prefix parties algebra Γ (vectorPorts count outputs ++ Δ)
  | fold {Γ Δ captures carried} (previous : Prefix parties algebra Γ Δ)
      (count : algebra.Count) (initial : Operands Δ carried) (capture : Operands Δ captures)
      (body : Region parties algebra
        (⟨parties, algebra.index count⟩ :: (carried ++ captures)) carried) :
      Prefix parties algebra Γ (carried ++ Δ)

def Prefix.close {Γ Δ ports : List (Port Role algebra.Ty)}
    (frames : Prefix parties algebra Γ Δ) (tail : Region parties algebra Δ ports) :
    Region parties algebra Γ ports :=
  match frames with
  | .nil => tail
  | .operation previous op args availability => previous.close (.operation op args availability tail)
  | .tuple previous args availability => previous.close (.tuple args availability tail)
  | .project previous value component => previous.close (.project value component tail)
  | .map previous count capture body => previous.close (.map count capture body tail)
  | .fold previous count initial capture body => previous.close (.fold count initial capture body tail)

end Zkc.Source.Mathematical.Graph
