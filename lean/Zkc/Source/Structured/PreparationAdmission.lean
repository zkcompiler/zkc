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

/-- Resolve the exact private Math root and ABI. A realization has no external
premises; ordinary formation discharges internal call and callback premises.
Scalar maps additionally require an empty-premise transitive closure. -/
def checkPreparationClosure (snapshot : Snapshot) (profile : PreparationProfile)
    (helper : Helper) : Except String Unit := do
  let root ← lookupDefinition snapshot helper.name
  if !root.acceptsEdge .call || helper.kind != .math ||
      root.inputs != helper.inputs || root.outputs != helper.outputs then throw profile.error
  if profile == .map then
    checkPreparationPreconditions snapshot profile snapshot.definitions.length [helper.name] []
  else
    let .function function := root | throw profile.error
    if !function.preconditions.isEmpty then throw profile.error

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
  | .makeProduct .. | .getProduct .. => profile == .realization
  | .select type => profile == .realization && profile.typeAllowed type
  | _ => false

/-- Finite computation admission retains reached domain exhaustion and checked
reads. It does not establish the immediate-return law of preparationAllowed. -/
def Op.computationAllowed : Op → Bool
  | .boundedAt _ => true
  | .fold spec => spec.kind == .math
  | op => op.preparationAllowed .realization

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

/-- A named finite fold carries its checked callbacks in the shared helper
inventory. Arbitrary nested regions and Local control remain outside Math. -/
def computationAllowed : RawRegion Ty Op → Bool
  | .ret _ => true
  | .letOp op _ results .nil next =>
    op.computationAllowed && PreparationProfile.realization.typesAllowed results &&
      next.computationAllowed
  | _ => false

/-- Every intermediate scalar belongs to the selected map field, including
discarded results. Helper port and dependency checks are supplied by selection. -/
def mapFieldAllowed (field : String) : RawRegion Ty Op → Bool
  | .ret _ => true
  | .letOp _ _ results .nil next =>
    results.all (· == .field field) && next.mapFieldAllowed field
  | _ => false

end Zkc.Source.RawRegion

namespace Zkc.Source.Structured

/-- One closure selector over the actual checked dependency inventory. Calls,
steps and predicates all require exact earlier signatures, even when dormant. -/
def selectMathHelpers (typesAllowed : List Ty → Bool)
    (bodyAllowed : RawRegion Ty Op → Bool) (definitions : List CheckedDefinition) : List Helper :=
  definitions.foldl (fun selected definition =>
    if definition.kind == .math && typesAllowed definition.inputs &&
        typesAllowed definition.outputs && bodyAllowed definition.raw &&
        definition.helpers.all selected.contains then definition.helper :: selected
    else selected) []

/-- The narrow region-free closure used by immediate-return proofs. -/
def preparationHelpers (profile : PreparationProfile) : List CheckedDefinition → List Helper :=
  selectMathHelpers profile.typesAllowed (·.preparationAllowed profile)

/-- A scalar map uses one exact field throughout its complete checked closure.
The generic preparation profile remains the independent return certificate. -/
def mapHelpers (field : String) : List CheckedDefinition → List Helper :=
  selectMathHelpers
    (fun types => PreparationProfile.map.typesAllowed types && types.all (· == .field field))
    (fun body => body.preparationAllowed .map && body.mapFieldAllowed field)

theorem selectMathHelpers_mono
    {types₁ types₂ : List Ty → Bool} {body₁ body₂ : RawRegion Ty Op → Bool}
    (types : ∀ ts, types₁ ts = true → types₂ ts = true)
    (bodies : ∀ raw, body₁ raw = true → body₂ raw = true)
    (definitions : List CheckedDefinition) :
    selectMathHelpers types₁ body₁ definitions ⊆ selectMathHelpers types₂ body₂ definitions := by
  unfold selectMathHelpers
  suffices monotone : ∀ (left right : List Helper), left ⊆ right →
      definitions.foldl (fun selected definition =>
        if definition.kind == .math && types₁ definition.inputs && types₁ definition.outputs &&
            body₁ definition.raw && definition.helpers.all selected.contains then
          definition.helper :: selected else selected) left ⊆
      definitions.foldl (fun selected definition =>
        if definition.kind == .math && types₂ definition.inputs && types₂ definition.outputs &&
            body₂ definition.raw && definition.helpers.all selected.contains then
          definition.helper :: selected else selected) right from
    monotone [] [] (by intro _ h; exact h)
  induction definitions with
  | nil => intro left right subset; exact subset
  | cons definition rest ih =>
    intro left right subset
    simp only [List.foldl_cons]
    apply ih
    split
    · rename_i selected
      have parts := Bool.and_eq_true_iff.mp selected
      have deps : definition.helpers.all right.contains = true := by
        have used := parts.2
        rw [List.all_eq_true] at used ⊢
        intro helper member
        exact List.contains_iff_mem.mpr (subset (List.contains_iff_mem.mp (used helper member)))
      have facts : definition.kind == .math ∧ types₁ definition.inputs = true ∧
          types₁ definition.outputs = true ∧ body₁ definition.raw = true := by
        simpa only [Bool.and_eq_true, and_assoc] using parts.1
      have selected₂ : (definition.kind == .math && types₂ definition.inputs &&
          types₂ definition.outputs && body₂ definition.raw &&
          definition.helpers.all right.contains) = true := by
        simp only [Bool.and_eq_true]
        exact ⟨⟨⟨⟨facts.1, types _ facts.2.1⟩, types _ facts.2.2.1⟩, bodies _ facts.2.2.2⟩, deps⟩
      simp only [selected₂, ↓reduceIte]
      exact List.cons_subset_cons _ subset
    · split
      · exact fun _ member => List.mem_cons_of_mem _ (subset member)
      · exact subset

theorem mapHelpers_subset (field : String) (definitions : List CheckedDefinition) :
    mapHelpers field definitions ⊆ preparationHelpers .map definitions :=
  selectMathHelpers_mono (fun _ accepted => (Bool.and_eq_true_iff.mp accepted).1)
    (fun _ accepted => (Bool.and_eq_true_iff.mp accepted).1) definitions

/-- General Math computations may stop at reached finite-domain admission.
Selection supplies structural closure, never an unconditional return theorem. -/
def computationHelpers : List CheckedDefinition → List Helper :=
  selectMathHelpers PreparationProfile.realization.typesAllowed (·.computationAllowed)

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
