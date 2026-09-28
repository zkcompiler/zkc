import Zkc.Source.Mathematical.TypeAdmission
import Tests.MathematicalTypes
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalTypeExpansion
open Zkc.Source.Mathematical

def closed (raw : List Raw.TypeTemplate) (request : Raw.TypeUse) (budget : Nat := 1000000) :
    Except TypeAdmission.Error (TypeExpansion.Shape 0 0) :=
  (do
    let declarations ← TypeAdmission.declarations MathematicalTypes.emptyMeaning (fun _ => false) raw
    let result ← TypeAdmission.use MathematicalTypes.emptyMeaning declarations 0 request
    return result.expanded.shape).run' (min budget 1000000)

def seven : Raw.TypeUse := ⟨⟨1⟩, [.literal 4, .literal 7]⟩

-- The certificate itself, rather than a finite execution test, establishes
-- equality to the selected type's meaning for every assignment.
example {scope arity} (source : TypeSyntax.Templates 0 scope)
    (request : TypeSyntax.Use scope arity)
    (result : TypeExpansion.Expanded MathematicalTypes.emptyMeaning (fun _ => false)
      (request.denote (source.denote MathematicalTypes.emptyMeaning))) (values : Fin arity → Nat) :
    TypeExpansion.denote MathematicalTypes.emptyMeaning result.shape values =
      request.denote (source.denote MathematicalTypes.emptyMeaning) values := result.sound values

def atomMeaning : TypeSyntax.Interpretation 1 where
  nominal := fun _ _ _ => Nat
  polynomial := fun _ _ _ _ => Nat
  residual := fun _ _ _ => Nat

def nominal : TypeSyntax.Templates 1 [0] :=
  .snoc .nil 0 (.nominal ⟨0, by decide⟩ "Unknown" [])

def sharedBudget (budget : Nat) : Except TypeExpansion.Error Unit :=
  (do
    let _ ← TypeExpansion.normalize (.literal ⟨2, by decide⟩ : Static.Expression 0)
    let _ ← TypeExpansion.normalize (.literal ⟨2, by decide⟩ : Static.Expression 0)
    pure ()).run' budget

-- Execute the elaborator with proofs erased. Kernel reduction of its complete
-- dependent computation is not used as a performance test or as a substitute
-- for the general semantic certificate above.
def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (closed MathematicalTypes.templates seven).isOk "earlier template expansion"
  let equalTypes := [⟨0, .fin (.add (.literal 2) (.literal 3))⟩, ⟨0, .fin (.literal 5)⟩]
  checks.holds (match closed equalTypes ⟨⟨0⟩, []⟩, closed equalTypes ⟨⟨1⟩, []⟩ with
    | .ok left, .ok right => decide (left = right)
    | _, _ => false)
    "normalized equality across authored templates"
  checks.holds (!(closed [⟨1, .fin (.literal 2)⟩] ⟨⟨0⟩, [.pow2 (.literal 64)]⟩).isOk)
    "unused overflowing argument"
  checks.holds (!(closed [⟨0, .fin (.multiply (.literal 0) (.pow2 (.literal 64)))⟩] ⟨⟨0⟩, []⟩).isOk)
    "overflow before annihilation"
  checks.holds (!(closed MathematicalTypes.templates seven 0).isOk) "shared work refusal"
  checks.holds (!(closed [⟨0, .fin (.literal 2)⟩, ⟨0, .fin (.pow2 (.literal 64))⟩]
    ⟨⟨0⟩, []⟩).isOk) "unused declaration still checked"
  checks.holds (!(closed [⟨0, .fin (.literal 2)⟩, ⟨1000000000, .fin (.literal 2)⟩]
    ⟨⟨0⟩, []⟩).isOk) "static arity charged before scope construction"
  checks.holds (match closed [⟨0, .fin (.literal 2)⟩, ⟨0, .fin (.literal 2)⟩] ⟨⟨0⟩, []⟩ with
    | .error .duplicate => true
    | _ => false) "duplicate authored type declaration"
  checks.holds (!(TypeExpansion.instantiate (meaning := atomMeaning) (arity := 0) (fun _ => false)
    nominal ⟨0, .here, [], rfl⟩).isOk) "uninstalled domain type"
  checks.holds (!(sharedBudget 3).isOk) "normalizations share allowance"
  checks.holds (sharedBudget 4).isOk "closed normalizations succeed at their combined traversal allowance"
  checks.finish "mathematical type expansion"

#eval run
end Tests.MathematicalTypeExpansion
