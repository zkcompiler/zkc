module

public import Zkc.Source.Structured.Algebra

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Structured

/-! Domain models.

A `FieldModel` adds to carriers (`Algebra`) the structures field operations
use, and a `DomainModel` adds those of group operations: a commutative ring and
decidable equality per field identity, an optional computable inverse,
embeddings between field identities, an additive group and decidable equality
per group identity, and the scalar actions between them. Nothing here assumes a
characteristic, a prime field or a particular identity; which identities exist,
how they are related and which laws a theorem may assume are said by the
catalogue rows that admission checks.

The interpretation by one commutative ring `F` for every field identity and one
module `G` over it for every group identity is `uniformCarriers F G` with
`ringModel F G`; its values are `assignment F G`. -/

/-- The structures field operations use, on top of the carriers. The inverse
is data, so that inversion stays computable; a model built from a commutative
ring alone leaves it absent. `embed extension base` maps the elements of a base
identity into an extension identity. -/
structure FieldModel extends Carriers where
  fieldRing : ∀ d, CommRing (Field d)
  fieldDecEq : ∀ d, DecidableEq (Field d)
  inverse : ∀ d, Option (Field d → Field d)
  embed : (extension base : String) → Field base → Field extension

/-- The structures group operations use, on top of a field model. `smul g f`
is the action of the elements of the field identity `f` on those of the group
identity `g`. -/
structure DomainModel extends FieldModel where
  groupAdd : ∀ g, AddCommGroup (Group g)
  groupDecEq : ∀ g, DecidableEq (Group g)
  smul : (g f : String) → Field f → Group g → Group g

instance (model : FieldModel) (d : String) : CommRing (model.Field d) := model.fieldRing d
instance (model : FieldModel) (d : String) : DecidableEq (model.Field d) := model.fieldDecEq d
instance (model : DomainModel) (g : String) : AddCommGroup (model.Group g) := model.groupAdd g
instance (model : DomainModel) (g : String) : DecidableEq (model.Group g) := model.groupDecEq g

/-- The field structures of the uniform interpretation, from a commutative ring
with decidable equality. It has no inverse, and every embedding is the
identity of `F`. -/
abbrev ringFieldModel (F G : Type) [CommRing F] [DecidableEq F] : FieldModel where
  toCarriers := uniformCarriers F G
  fieldRing := fun _ => inferInstanceAs (CommRing F)
  fieldDecEq := fun _ => inferInstanceAs (DecidableEq F)
  inverse := fun _ => none
  embed := fun _ _ value => value

/-- The uniform interpretation with the structures of the instance arguments:
`F` acts on `G` by its module action, for every pair of identities. -/
abbrev ringModel (F G : Type) [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F]
    [DecidableEq G] : DomainModel where
  toFieldModel := ringFieldModel F G
  groupAdd := fun _ => inferInstanceAs (AddCommGroup G)
  groupDecEq := fun _ => inferInstanceAs (DecidableEq G)
  smul := fun _ _ (scalar : F) (point : G) => scalar • point

end Zkc.Source.Structured
