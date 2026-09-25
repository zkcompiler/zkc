import Zkc.Source.Decoding
import Zkc.Compiler.Plan

/-! The direct plan's typed decoding boundary.

Source and direct plans currently share a finite control grammar. Their typed
representations and evaluators are distinct. The enclosing format must identify
the realization kind; this grammar does not encode native buffer plans or code.
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

variable {language : Language} [DecidableEq language.Ty]

def decodePlan (Γ : List language.Ty) (ty : language.Ty) :
    RawProgram language.Ty language.Op →
      Except (FormationError language.Ty) (Plan language Γ ty)
  | .ret index => return .yield (← decodeVariable Γ ty index)
  | .stop reason => .ok (.stop reason)
  | .letOp op indices next => do
    let arguments ← decodeOperands Γ (language.arguments op) indices
    let next ← decodePlan (language.result op :: Γ) ty next
    pure (.execute op arguments next)
  | .branch index yes no => do
    let condition ← decodeVariable Γ language.condition index
    let yes ← decodePlan Γ ty yes
    let no ← decodePlan Γ ty no
    pure (.select condition yes no)
  | .iterate count acc index body next => do
    let initial ← decodeVariable Γ acc index
    let body ← decodePlan (acc :: Γ) acc body
    let next ← decodePlan (acc :: Γ) ty next
    pure (.loop count initial body next)

def Plan.erase {Γ ty} : Plan language Γ ty → RawProgram language.Ty language.Op
  | .yield value => .ret value.index
  | .stop reason => .stop reason
  | .execute op arguments next => .letOp op (Operands.indices arguments) next.erase
  | .select condition yes no => .branch condition.index yes.erase no.erase
  | .loop (acc := acc) count initial body next =>
    .iterate count acc initial.index body.erase next.erase

@[simp] theorem Plan.decode_erase {Γ ty} (plan : Plan language Γ ty) :
    decodePlan Γ ty plan.erase = .ok plan := by
  induction plan with
  | yield value => simp [erase, decodePlan]; rfl
  | stop reason => rfl
  | execute op arguments next ih => simp [erase, decodePlan, ih]; rfl
  | select condition yes no yesIH noIH => simp [erase, decodePlan, yesIH, noIH]; rfl
  | loop count initial body next bodyIH nextIH =>
    simp [erase, decodePlan, bodyIH, nextIH]; rfl

end Zkc.Compiler
