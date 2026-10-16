module

public import Zkc.Source.Structured.Admission

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

def PreparationProfile.typeAllowed (profile : PreparationProfile) (type : Ty) : Bool :=
  match profile with
  | .realization => validType type && !type.isService
  | .map => type == .field scalarDomain

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

def MapDeclaration.spec (declaration : MapDeclaration) : MapSpec :=
  ⟨declaration.helper, scalarDomain, declaration.rowwise⟩

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
      declaration.outputs != [.vector scalarDomain] then throw "structured-map"
  checkPreparationClosure snapshot .map declaration.spec.helper

/-- Structural counterpart for semantic proofs over the existing checked
carrier. No theorem about return behavior follows merely from this definition. -/
def Op.preparationAllowed (profile : PreparationProfile) : Op → Bool
  | .fieldConstant d n => d == scalarDomain && n < scalarModulus
  | .fieldAdd d | .fieldSubtract d | .fieldMultiply d => d == scalarDomain
  | .invoke helper => helper.kind == .math && validString helper.name &&
      profile.typesAllowed helper.inputs && profile.typesAllowed helper.outputs
  | .fieldEqual d => profile == .realization && d == scalarDomain
  | .groupIdentity d | .groupAdd d | .groupEqual d =>
    profile == .realization && d == groupDomain
  | .groupScale g f => profile == .realization && g == groupDomain && f == scalarDomain
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
