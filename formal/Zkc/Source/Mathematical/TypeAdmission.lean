import Zkc.Source.Mathematical.TypeExpansion

/-! Type-declaration admission from the raw carrier.

All declarations are expanded in their own static scope, including declarations
unused by an entry. A use is checked again after substitution. The decoded
object retains the exact authored declarations and arguments beside the
expanded mathematical type and its semantic certificate.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.TypeAdmission

inductive Error where
  | duplicate
  | scope (reason : TypeSyntax.Error)
  | expansion (reason : TypeExpansion.Error)
  deriving DecidableEq, Repr

variable {domains : Nat} (meaning : TypeSyntax.Interpretation domains)

private def chargeStatic : Nat → Static.Raw → TypeExpansion.Admission Unit
  | 0, _ => throw .resource
  | depth + 1, value => do
      TypeExpansion.consume
      match value with
      | .literal _ | .parameter _ => pure ()
      | .add a b | .multiply a b => chargeStatic depth a; chargeStatic depth b
      | .pow2 exponent => chargeStatic depth exponent

private def chargeUse (source : Raw.TypeUse) : TypeExpansion.Admission Unit := do
  TypeExpansion.consume
  source.statics.forM (chargeStatic 65)

private def chargeType (source : Raw.TypeExpression) : TypeExpansion.Admission Unit := do
  TypeExpansion.consume
  match source with
  | .nominal _ name arguments =>
      TypeExpansion.consume name.utf8ByteSize
      arguments.forM (chargeStatic 65)
  | .product elements => elements.forM chargeUse
  | .fin count => chargeStatic 65 count
  | .vector element count => chargeUse element; chargeStatic 65 count
  | .polynomial _ variables degree _ | .residual _ variables degree =>
      chargeStatic 65 variables; chargeStatic 65 degree

private def liftAdmission {α : Type} (action : TypeExpansion.Admission α) : StateT Nat (Except Error) α :=
  fun available => (action available).mapError Error.expansion

/-- Normalized bodies are retained for every declaration. Their interpretations
are those of the corresponding scoped body over its actual earlier table. -/
inductive Templates (check : TypeExpansion.DomainCheck domains) : {scope : List Nat} → TypeSyntax.Templates domains scope → Type where
  | nil : Templates (@check) .nil
  | snoc {scope arity} {previous : TypeSyntax.Templates domains scope}
      {body : TypeSyntax.Expression domains scope arity}
      (earlier : Templates (@check) previous)
      (expanded : TypeExpansion.Expanded meaning check
        (fun values => body.denote meaning (previous.denote meaning) values)) :
      Templates (@check) (.snoc previous arity body)

def validate (check : TypeExpansion.DomainCheck domains) : {scope : List Nat} →
    (source : TypeSyntax.Templates domains scope) → TypeExpansion.Admission (Templates meaning check source)
  | _, .nil => return .nil
  | _, .snoc previous _ body => do
      let earlier ← validate check previous
      let expanded ← TypeExpansion.expression check (TypeExpansion.templates check previous) 65 body
      return .snoc earlier expanded

structure Table (raw : List Raw.TypeTemplate) where
  domainCheck : TypeExpansion.DomainCheck domains
  unique : raw.Nodup
  arities : List Nat
  source : TypeSyntax.Templates domains arities
  erasure : source.erase = raw
  formed : Templates meaning domainCheck source

/-- Keep the checker identity in the result so module admission can connect
domain formation to the actual manifest-selected packages. -/
def declarationsChecked (check : TypeExpansion.DomainCheck domains) (raw : List Raw.TypeTemplate) :
    StateT Nat (Except Error) { result : Table meaning raw // @result.domainCheck = @check } := do
  if raw.length > 4096 then throw (.expansion .resource)
  let available ← get
  if raw.length > available then throw (.expansion .resource)
  set (available - raw.length)
  liftAdmission (raw.forM fun declaration => do
    TypeExpansion.consume declaration.statics
    chargeType declaration.body)
  -- This reference consumer uses structural equality. Charge its worst case
  -- before checking uniqueness; the native carrier uses ordered byte keys.
  liftAdmission (TypeExpansion.consume (raw.length * (available - (← get))))
  if unique : raw.Nodup then
    let decoded ← (TypeSyntax.declarations domains raw).mapError Error.scope
    let formed ← liftAdmission (validate meaning check decoded.templates)
    return ⟨⟨check, unique, decoded.arities, decoded.templates, decoded.erasure, formed⟩, rfl⟩
  else throw .duplicate

def declarations (check : TypeExpansion.DomainCheck domains) (raw : List Raw.TypeTemplate) :
    StateT Nat (Except Error) (Table meaning raw) := do
  return (← declarationsChecked meaning check raw).val

structure Decoded {raw : List Raw.TypeTemplate} (table : Table meaning raw)
    (arity : Nat) (source : Raw.TypeUse) where
  use : TypeSyntax.Use table.arities arity
  erasure : use.erase = source
  expanded : TypeExpansion.Expanded meaning table.domainCheck (use.denote (table.source.denote meaning))

def use {raw : List Raw.TypeTemplate} (table : Table meaning raw) (arity : Nat) (source : Raw.TypeUse) :
    StateT Nat (Except Error) (Decoded meaning table arity source) := do
  liftAdmission (chargeUse source)
  let decoded ← (TypeSyntax.use table.arities arity source).mapError Error.scope
  let expanded ← liftAdmission (TypeExpansion.use
    (TypeExpansion.templates table.domainCheck table.source) 65 decoded.val)
  return ⟨decoded.val, decoded.property, expanded⟩

theorem Decoded.denotes {raw arity source} {table : Table meaning raw}
    (result : Decoded meaning table arity source) (parameters : Fin arity → Nat) :
    TypeExpansion.denote meaning result.expanded.shape parameters =
      result.use.denote (table.source.denote meaning) parameters := result.expanded.sound parameters

structure Instantiated {raw : List Raw.TypeTemplate} (table : Table meaning raw)
    {arity target : Nat} (parameters : Fin arity → Static.Expression target) (source : Raw.TypeUse) where
  use : TypeSyntax.Use table.arities arity
  erasure : use.erase = source
  expanded : TypeExpansion.Expanded meaning table.domainCheck (fun values =>
    use.denote (table.source.denote meaning) (fun index => (parameters index).eval values))

/-- Resolve a use written in a declaration's static scope under the selected
call tuple. The authored use and its arity are retained independently of the
target scope (which is zero for a closed instance). -/
def instantiate {raw : List Raw.TypeTemplate} (table : Table meaning raw)
    {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (source : Raw.TypeUse) : StateT Nat (Except Error) (Instantiated meaning table parameters source) := do
  liftAdmission (chargeUse source)
  let decoded ← (TypeSyntax.use table.arities arity source).mapError Error.scope
  let expanded ← liftAdmission (TypeExpansion.use (TypeExpansion.templates table.domainCheck table.source) 65
    (decoded.val.substitute parameters))
  return ⟨decoded.val, decoded.property, ⟨expanded.shape, fun values =>
    (expanded.sound values).trans (TypeSyntax.Use.denote_substitute _ decoded.val parameters values), expanded.formed, expanded.measured⟩⟩

end Zkc.Source.Mathematical.TypeAdmission
