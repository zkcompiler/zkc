import Zkc.Source.Region
import Zkc.Source.Decoding

/-! Compact region data and checked binding. The shared suffix remains explicit
through erasure and elaboration; neither operation expands it into source trees. -/

set_option autoImplicit false
namespace Zkc.Source

inductive RawRegion (Ty Op : Type) where
  | ret (index : Nat)
  | stop (reason : PIR.Stop)
  | letOp (op : Op) (arguments : List Nat) (next : RawRegion Ty Op)
  | branch (condition : Nat) (yes no : RawRegion Ty Op)
  | iterate (count : Nat) (accumulator : Ty) (initial : Nat) (body next : RawRegion Ty Op)
  | bind (result : Ty) (body next : RawRegion Ty Op)
  deriving DecidableEq, Repr

variable {language : Language} [DecidableEq language.Ty]

def RawRegion.elaborate (Γ : List language.Ty) (ty : language.Ty) :
    RawRegion language.Ty language.Op →
      Except (FormationError language.Ty) (Region language Γ ty)
  | .ret index => return .ret (← decodeVariable Γ ty index)
  | .stop reason => .ok (.stop reason)
  | .letOp op indices next => do
    let arguments ← decodeOperands Γ (language.arguments op) indices
    let next ← next.elaborate (language.result op :: Γ) ty
    pure (.letOp op arguments next)
  | .branch index yes no => do
    let condition ← decodeVariable Γ language.condition index
    let yes ← yes.elaborate Γ ty
    let no ← no.elaborate Γ ty
    pure (.branch condition yes no)
  | .iterate count acc index body next => do
    let initial ← decodeVariable Γ acc index
    let body ← body.elaborate (acc :: Γ) acc
    let next ← next.elaborate (acc :: Γ) ty
    pure (.iterate count initial body next)
  | .bind result body next => do
    let body ← body.elaborate Γ result
    let next ← next.elaborate (result :: Γ) ty
    pure (.bind body next)

def Region.erase {Γ ty} : Region language Γ ty → RawRegion language.Ty language.Op
  | .ret value => .ret value.index
  | .stop reason => .stop reason
  | .letOp op arguments next => .letOp op (Operands.indices arguments) next.erase
  | .branch condition yes no => .branch condition.index yes.erase no.erase
  | .iterate (acc := acc) count initial body next =>
    .iterate count acc initial.index body.erase next.erase
  | .bind (a := a) body next => .bind a body.erase next.erase

@[simp] theorem Region.elaborate_erase {Γ ty} (region : Region language Γ ty) :
    region.erase.elaborate Γ ty = .ok region := by
  induction region with
  | ret value => simp [erase, RawRegion.elaborate]; rfl
  | stop reason => rfl
  | letOp op arguments next ih => simp [erase, RawRegion.elaborate, ih]; rfl
  | branch condition yes no yesIH noIH => simp [erase, RawRegion.elaborate, yesIH, noIH]; rfl
  | iterate count initial body next bodyIH nextIH =>
    simp [erase, RawRegion.elaborate, bodyIH, nextIH]; rfl
  | bind body next bodyIH nextIH => simp [erase, RawRegion.elaborate, bodyIH, nextIH]; rfl

def RawRegion.nodeCount {Ty Op : Type} : RawRegion Ty Op → Nat
  | .ret _ | .stop _ => 1
  | .letOp _ _ next => 1 + next.nodeCount
  | .branch _ yes no => 1 + yes.nodeCount + no.nodeCount
  | .iterate _ _ _ body next | .bind _ body next => 1 + body.nodeCount + next.nodeCount

/-- Interpreter work excludes operation-internal cost, which belongs to the library. -/
def RawRegion.workBound {Ty Op : Type} : RawRegion Ty Op → Nat
  | .ret _ | .stop _ => 1
  | .letOp _ _ next => 1 + next.workBound
  | .branch _ yes no => 1 + max yes.workBound no.workBound
  | .iterate count _ _ body next => 1 + count * (1 + body.workBound) + next.workBound
  | .bind _ body next => 1 + body.workBound + next.workBound

end Zkc.Source
