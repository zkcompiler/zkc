import Zkc.Source.Mathematical.TypeMeaning

set_option autoImplicit false
namespace Tests.MathematicalTypes
open Zkc.Source.Mathematical

def templates : List Raw.TypeTemplate :=
  [⟨1, .fin (.parameter 0)⟩,
   ⟨2, .vector ⟨⟨0⟩, [.add (.parameter 0) (.literal 1)]⟩ (.parameter 1)⟩,
   ⟨1, .product [⟨⟨0⟩, [.parameter 0]⟩, ⟨⟨1⟩, [.parameter 0, .literal 7]⟩]⟩]

example : (TypeSyntax.declarations 0 templates).isOk = true := rfl
example : ((TypeSyntax.declarations 0 templates).map fun result => result.arities) = .ok [1, 2, 1] := rfl

example : (TypeSyntax.declarations 0 [⟨0, .product [⟨⟨0⟩, []⟩]⟩]).isOk = false := rfl
example : (TypeSyntax.declarations 0
    [⟨0, .product [⟨⟨1⟩, []⟩]⟩, ⟨0, .fin (.literal 2)⟩]).isOk = false := rfl
example : (TypeSyntax.declarations 0 [⟨0, .fin (.parameter 0)⟩]).isOk = false := rfl
example : (TypeSyntax.declarations 0
    [⟨1, .fin (.parameter 0)⟩, ⟨0, .vector ⟨⟨0⟩, []⟩ (.literal 2)⟩]).isOk = false := rfl
example : (TypeSyntax.declarations 0 [⟨0, .nominal ⟨0⟩ "Field" []⟩]).isOk = false := rfl
example : (TypeSyntax.declarations 1
    [⟨0, .polynomial ⟨0⟩ (.literal 3) (.literal 2) .individual⟩,
     ⟨0, .residual ⟨0⟩ (.literal 3) (.literal 2)⟩]).isOk = true := rfl

-- Scope formation retains the raw arithmetic. Registry/type expansion must
-- separately normalize and check overflow; this phase does not erase it.
example : ((TypeSyntax.declarations 0
    [⟨0, .fin (.multiply (.literal 0) (.pow2 (.literal 64)))⟩]).map
      fun result => result.templates.erase) =
    .ok [⟨0, .fin (.multiply (.literal 0) (.pow2 (.literal 64)))⟩] := rfl

example {domains raw result} (accepted : TypeSyntax.declarations domains raw = .ok result) :
    result.templates.erase = raw := TypeSyntax.declarations_erases domains accepted

def emptyMeaning : TypeSyntax.Interpretation 0 where
  nominal := fun domain => nomatch domain
  polynomial := fun domain => nomatch domain
  residual := fun domain => nomatch domain

def first : TypeSyntax.Templates 0 [1] :=
  .snoc .nil 1 (.fin (.parameter ⟨0, by decide⟩))

def second : TypeSyntax.Templates 0 [1, 2] :=
  .snoc first 2 (.vector
    ⟨1, .here, [.add (.parameter ⟨0, by decide⟩) (.literal ⟨1, by decide⟩)], rfl⟩
    (.parameter ⟨1, by decide⟩))

-- Earlier type templates are instantiated with the authored static tuple.
-- The vector has seven elements, each in Fin (four plus one).
example : second.denote emptyMeaning (.there .here)
    (fun index => if index.val = 0 then 4 else 7) = (Fin 7 → Fin 5) := rfl

end Tests.MathematicalTypes
