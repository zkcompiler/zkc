import Zkc.Source.DefinitionRenaming

/-! Small laws at the resolved source-project boundary.

Owners are exact identities supplied by the project adapter, never aliases,
file paths or hashes. This model does not check visibility, alias cycles,
duplicate declaration contents or the native resolver.
-/

set_option autoImplicit false

namespace Zkc.Source.ProjectResolution

/-- A logical declaration key; relocating its source file does not change it. -/
structure DeclarationId (Owner : Type) where
  owner : Owner
  modulePath : List String
  name : String
  deriving DecidableEq, Repr

variable {Key Target Value Name : Type}

/-- Exact lookup, without a short-name fallback. Coherence of duplicate keys is
a separate admission obligation. -/
def lookup [DecidableEq Key] (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | (candidate, value) :: rest =>
      if candidate = key then some value else lookup key rest

/-- The alias environment is already resolved, including re-exports. `Name`
may include the importing scope; it is not the declaration's owner. -/
def resolve [DecidableEq Key] (aliases : Name → Option Key)
    (declarations : List (Key × Value)) (name : Name) : Option Value :=
  (aliases name).bind (fun key => lookup key declarations)

theorem resolve_same_declaration [DecidableEq Key]
    (aliases : Name → Option Key) (declarations : List (Key × Value))
    (left right : Name) (key : Key)
    (hl : aliases left = some key) (hr : aliases right = some key) :
    resolve aliases declarations left = resolve aliases declarations right := by
  simp [resolve, hl, hr]

/-- Distinct owners cannot match even when module and declaration names agree. -/
theorem lookup_other_owner {Owner : Type} [DecidableEq Owner]
    (wanted candidate : DeclarationId Owner) (value : Value)
    (rest : List (DeclarationId Owner × Value))
    (different : candidate.owner ≠ wanted.owner) :
    lookup wanted ((candidate, value) :: rest) = lookup wanted rest := by
  have distinct : candidate ≠ wanted := fun same => different (congrArg (·.owner) same)
  simp [lookup, distinct]

/-- A collision-free output-name allocation preserves both success and failure
of exact lookup. Injectivity is required on keys, not just printed short names. -/
theorem lookup_rename [DecidableEq Key] [DecidableEq Target]
    (rename : Key → Target) (injective : ∀ a b, rename a = rename b → a = b)
    (key : Key) (declarations : List (Key × Value)) :
    lookup (rename key) (declarations.map (fun entry => (rename entry.1, entry.2))) =
      lookup key declarations := by
  induction declarations with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, value⟩
      have same : rename candidate = rename key ↔ candidate = key :=
        ⟨injective candidate key, congrArg rename⟩
      simp [lookup, same, ih]

theorem resolve_rename [DecidableEq Key] [DecidableEq Target]
    (rename : Key → Target) (injective : ∀ a b, rename a = rename b → a = b)
    (aliases : Name → Option Key) (declarations : List (Key × Value)) (name : Name) :
    resolve (fun name => (aliases name).map rename)
        (declarations.map (fun entry => (rename entry.1, entry.2))) name =
      resolve aliases declarations name := by
  cases found : aliases name with
  | none => simp [resolve, found]
  | some key => simpa [resolve, found] using lookup_rename rename injective key declarations

variable {language : Language} {interface : PIR.Signature}
variable {scope target : List (DefinitionSignature language.Ty)}

/-- Preserving exact, unique declaration keys prevents typed references from
being merged during definition-scope renaming. -/
theorem references_injective
    (sourceKey : {signature : DefinitionSignature language.Ty} → Var scope signature → Key)
    (targetKey : {signature : DefinitionSignature language.Ty} → Var target signature → Key)
    (unique : ∀ {signature} (a b : Var scope signature), sourceKey a = sourceKey b → a = b)
    (references : Renaming scope target)
    (preserves : ∀ {signature} (ref : Var scope signature),
      targetKey (references ref) = sourceKey ref)
    {signature : DefinitionSignature language.Ty} (a b : Var scope signature)
    (same : references a = references b) : a = b := by
  apply unique a b
  rw [← preserves a, ← preserves b, same]

/-- Exact identity connects to execution only when both actual definition
tables implement the same keyed meaning. Identity or matching signatures alone
are not evidence of body equivalence. Reuse the existing region transport law. -/
theorem denote_rename_of_keyed_meaning
    (base : Interpretation language interface)
    (sourceDefinitions : Definitions language scope)
    (targetDefinitions : Definitions language target)
    (sourceKey : {signature : DefinitionSignature language.Ty} → Var scope signature → Key)
    (targetKey : {signature : DefinitionSignature language.Ty} → Var target signature → Key)
    (meaning : Key → (signature : DefinitionSignature language.Ty) →
      Values base.Value signature.arguments → PIR.Proc interface (base.Value signature.result))
    (sourceLaw : ∀ {signature} (ref : Var scope signature) args,
      sourceDefinitions.operation base (.call ref) args = meaning (sourceKey ref) signature args)
    (targetLaw : ∀ {signature} (ref : Var target signature) args,
      targetDefinitions.operation base (.call ref) args = meaning (targetKey ref) signature args)
    (references : Renaming scope target)
    (preserves : ∀ {signature} (ref : Var scope signature),
      targetKey (references ref) = sourceKey ref)
    {Γ : List language.Ty} {ty : language.Ty}
    (body : Region (language.withDefinitions scope) Γ ty) (env : Environment base.Value Γ) :
    (body.renameDefinitions references).denote (targetDefinitions.meaning base) env =
      body.denote (sourceDefinitions.meaning base) env := by
  apply Region.denote_renameDefinitions base sourceDefinitions targetDefinitions references
  intro signature ref args
  rw [targetLaw, sourceLaw, preserves]

end Zkc.Source.ProjectResolution
