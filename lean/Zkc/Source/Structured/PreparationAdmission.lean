module

public import Zkc.Source.Structured.Admission
public import Zkc.Source.Structured.CheckedData

@[expose] public section

/-! Independent preparation profiles over the retained unit and shared raw
carrier. These predicates describe admitted structure, not semantic totality. -/

namespace Zkc.Source.Structured

inductive PreparationProfile where
  | realization | map
  deriving DecidableEq, Repr

def PreparationProfile.error : PreparationProfile → String
  | .realization => "structured-realization"
  | .map => "structured-map"

/-- Map closures stay in scalar fields; realizations exclude services. The
identities are admitted against the unit's catalogue rows. -/
def PreparationProfile.typeAllowed (profile : PreparationProfile) (type : Ty) : Bool :=
  match profile, type with
  | .realization, type => !type.isService
  | .map, .field _ => true
  | .map, _ => false

/-- Every port is checked, even an unused input or a discarded result. -/
def PreparationProfile.typesAllowed (profile : PreparationProfile) (types : List Ty) : Bool :=
  validTypes types && types.all profile.typeAllowed

/-- Check empty source preconditions at each reachable original function once.
The bound counts unique definitions, not call expansion or dependency depth.
Operations, types and exact nested call edges are checked by ordinary formation;
the selected checked closure supplies the sole preparation profile authority. -/
def checkPreparationPreconditions (snapshot : Snapshot) (profile : PreparationProfile) :
    Nat → List String → List String → Except String Unit
  | _, [], _ => .ok ()
  | 0, _ :: _, _ => .error "structured-reference-limit"
  | remaining + 1, name :: pending, visited => do
    let .function function ← lookupDefinition snapshot name | throw profile.error
    if !function.preconditions.isEmpty then throw profile.error
    let visited := name :: visited
    let discovered := function.identityDependencies.eraseDups.filter fun dependency =>
      !pending.contains dependency && !visited.contains dependency
    checkPreparationPreconditions snapshot profile remaining (pending ++ discovered) visited

/-- Resolve the exact private Math root and ABI, then check source preconditions.
The existing definition ordering and availability checks own dependency depth. -/
def checkPreparationClosure (snapshot : Snapshot) (profile : PreparationProfile)
    (helper : Helper) : Except String Unit := do
  let root ← lookupDefinition snapshot helper.name
  if !root.acceptsEdge .call || helper.kind != .math ||
      root.inputs != helper.inputs || root.outputs != helper.outputs then throw profile.error
  checkPreparationPreconditions snapshot profile snapshot.definitions.length [helper.name] []

def RealizationDeclaration.helperSpec (declaration : RealizationDeclaration) : Helper :=
  ⟨declaration.helper, .math, declaration.inputs, declaration.outputs⟩

def RealizationDeclaration.raw (declaration : RealizationDeclaration) : RawRegion Ty Op :=
  .letOp (.invoke declaration.helperSpec) (List.range declaration.inputs.length)
    declaration.outputs .nil (.ret (List.range declaration.outputs.length))

/-- The field a map lifts: the field of its one vector result. -/
def MapDeclaration.field (declaration : MapDeclaration) : String :=
  match declaration.outputs with
  | [.vector field] => field
  | _ => ""

def MapDeclaration.spec (declaration : MapDeclaration) : MapSpec :=
  ⟨declaration.helper, declaration.field, declaration.rowwise⟩

def MapDeclaration.raw (declaration : MapDeclaration) : RawRegion Ty Op :=
  .letOp (.map declaration.spec) (List.range declaration.inputs.length)
    declaration.outputs .nil (.ret [0])

def RealizationDeclaration.validate (snapshot : Snapshot)
    (declaration : RealizationDeclaration) : Except String Unit := do
  if !(Definition.realization declaration).headerValid then throw "structured-realization"
  checkPreparationClosure snapshot .realization declaration.helperSpec

def MapDeclaration.validate (snapshot : Snapshot)
    (declaration : MapDeclaration) : Except String Unit := do
  if !(Definition.map declaration).headerValid ||
      declaration.inputs != declaration.spec.arguments ||
      declaration.outputs != [.vector declaration.field] then throw "structured-map"
  snapshot.catalogue.require declaration.field .field "Field"
  checkPreparationClosure snapshot .map declaration.spec.helper

/-- Structural counterpart for semantic proofs over the existing checked
carrier. No theorem about return behavior follows merely from this definition. -/
def Op.preparationAllowed (profile : PreparationProfile) : Op → Bool
  | .fieldEmbed .. | .fieldConstant .. | .fieldAdd _ | .fieldSubtract _ | .fieldMultiply _ => true
  | .invoke helper => helper.kind == .math && validString helper.name &&
      profile.typesAllowed helper.inputs && profile.typesAllowed helper.outputs
  | .fieldEqual _ | .groupIdentity _ | .groupAdd _ | .groupEqual _ | .groupScale _ _ =>
    profile == .realization
  | .indexConstant n => profile == .realization && n < indexLimit
  | .indexEqual | .booleanConstant _ | .booleanAnd | .booleanOr |
      .booleanXor | .booleanEqual | .booleanNotEqual => profile == .realization
  | .select type => profile == .realization && profile.typeAllowed type
  | _ => false

end Zkc.Source.Structured

namespace Zkc.Source.RawRegion
open Structured

/-- Return and region-free total-profile operations only. Typed formation and
full-signature helper linking remain separate explicit evidence. -/
def preparationAllowed (profile : PreparationProfile) : RawRegion Ty Op → Bool
  | .ret _ => true
  | .letOp op _ results .nil next =>
    op.preparationAllowed profile && profile.typesAllowed results && next.preparationAllowed profile
  | _ => false

end Zkc.Source.RawRegion

namespace Zkc.Source.Structured

/-- Compute a selected Math closure inside the existing declaration order.
An unrelated Local body or partial Math helper is never given a total profile. -/
def preparationHelpers (profile : PreparationProfile) (definitions : List CheckedDefinition) :
    List Helper :=
  definitions.foldl (fun selected definition =>
    if definition.kind == .math && profile.typesAllowed definition.inputs &&
        profile.typesAllowed definition.outputs && definition.raw.preparationAllowed profile &&
        definition.helpers.all selected.contains then definition.helper :: selected
    else selected) []

/-- Structural closure evidence over the original checked table. The semantic
implication is a separate theorem; this proposition makes no execution claim. -/
def PreparationClosed (profile : PreparationProfile) (definitions : List CheckedDefinition)
    (selected : List Helper) : Prop :=
  (∀ helper ∈ selected, helper ∈ definitions.map CheckedDefinition.helper) ∧
  ∀ definition ∈ definitions, definition.helper ∈ selected →
    definition.kind = .math ∧ definition.raw.preparationAllowed profile = true ∧
    ∀ helper ∈ definition.helpers, helper ∈ selected

instance preparationClosedDecidable (profile : PreparationProfile)
    (definitions : List CheckedDefinition) (selected : List Helper) :
    Decidable (PreparationClosed profile definitions selected) :=
  inferInstanceAs (Decidable
    ((∀ helper ∈ selected, helper ∈ definitions.map CheckedDefinition.helper) ∧
    ∀ definition ∈ definitions, definition.helper ∈ selected →
      definition.kind = .math ∧ definition.raw.preparationAllowed profile = true ∧
      ∀ helper ∈ definition.helpers, helper ∈ selected))

end Zkc.Source.Structured
