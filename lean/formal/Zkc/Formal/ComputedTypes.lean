module

public import Zkc.Core.Meaning.Role
public meta import Lean

public meta section

/-!
The types of a statement, computed.

A value of a type of the vocabulary is written with a type that only computation makes the
field, the group or the natural numbers (`Model.Val M ty`, `RV M role lty`). A statement that a
text reads is stated with those types computed, so that it is about the same terms as a lemma
about the carrier. The walk reads a reply and a value with this, and `claim_intro` an input of
a generated proposition; a module of statements that has no walk needs only this module.
-/

open Lean Meta

namespace Zkc.Formal.Walk

/-- The type of a variable that a step introduces, computed: the carrier of a type of the
vocabulary, and for a sequence the list of the carrier of its items. -/
partial def readType (type : Expr) : MetaM Expr := do
  let computed ← whnfD type
  if computed.isAppOfArity ``List 1 then return mkApp computed.appFn! (← readType computed.appArg!)
  else return computed

/-- Whether a term mentions the type of the values of a type of the vocabulary. -/
def mentionsValues (e : Expr) : Bool :=
  (e.find? fun s => s.isConstOf ``Zkc.Core.Model.Val || s.isConstOf ``Zkc.Core.Ty.Val ||
    s.isConstOf ``Zkc.Core.Tys.Val || s.isConstOf ``Zkc.Core.Tys.Choice ||
    s.isConstOf ``Zkc.Core.Semantics.Val || s.isConstOf ``Zkc.Core.RV ||
    s.isConstOf ``Zkc.Core.LVal).isSome

/-- A statement with the types in it computed: a type that is written as the values of a type of
the vocabulary is replaced by its carrier, also where it is an implicit argument, so that the
statement is about the same terms as a lemma about the carrier. The result is definitionally
the statement given. A reply and an input of a statement are read with it: a part of a tuple,
an item of a sequence and an alternative of a variant are then values of the field, the group
or the natural numbers, and not of a type that only computation makes one of those. -/
def computedTypes (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun sub => do
    if sub.hasLooseBVars || !mentionsValues sub then return .continue
    if !(← Meta.isType sub) then return .continue
    let computed ← whnfD sub
    return if computed == sub then .continue else .visit computed)

end Zkc.Formal.Walk
