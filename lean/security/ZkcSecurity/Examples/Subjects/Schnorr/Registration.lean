module

public import ZkcSecurity.Examples.Subjects.Schnorr.Endpoints
public import ZkcSecurity.Tools.ClaimConstruction
public import ZkcSecurity.Claims.Methods.Knowledge
public import ZkcExamples.Structured.SchnorrBinding

@[expose] public section

/-! Typed author-library registration. The retained target and admitted artifacts
are fixed before source requests are resolved. Existing evidence only witnesses
the registered extraction experiment; it never supplies a request's meaning. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr.Registration
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Endpoint
open ZkcSecurity.Tools.ClaimConstruction

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
  [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- Registered transcript and scalar-coordinate interpretation, fixed independently of evidence. -/
def extractionProfile : ExtractionProfile compiled F G where
  target := Contract.retained
  formula := ZkcExamples.Construction.SchnorrProofBinding.formulaBinding
  layout := .scalar 2
  domain := "bls12-381.fr"
  coordinates := by decide +kernel
  Commit := G
  decidableCommit := inferInstance
  shape := ZkcSecurity.Families.Schnorr.shape compiled.context ZkcExamples.Construction.SchnorrProof.wiring
  native := ZkcExamples.Construction.SchnorrProof.wiring.challengeSite
  delivery := "label_64656c6976657279_0"
  selected := by decide +kernel
  request := .draw ZkcExamples.Construction.SchnorrProof.wiring.fieldDomain
  requestSelected := rfl
  scalarChallenge := rfl
  challenge := rfl

def subject (endpoint : Semantics) : Subject F G artifacts endpoint where
  reference := sourceReference (stage endpoint)
  stageMatched := rfl
  compiled := compiled
  connection := sourceConnection
  target := .retained Contract.retained ZkcExamples.Construction.SchnorrProofBinding.formulaBinding
  importedRegistered := by intro declaration impossible; cases impossible
  sites := sourceSites
  sitesUnique := by decide +kernel
  sitesNativeUnique := by decide +kernel
  lowering := match endpoint with
    | .idealMeaning => PUnit.unit
    | .executableBytes => lowering
  extractors := extractionProfile.registry (.retained Contract.retained ZkcExamples.Construction.SchnorrProofBinding.formulaBinding) rfl

def subjectIdeal := subject (F := F) (G := G) .idealMeaning

def subjectBytes := subject (F := F) (G := G) .executableBytes

def modelRegistry (endpoint : Semantics) (application : String) :=
  models (ModelContext.parameter "application" application) endpoint

noncomputable def builtinProperties (endpoint : Semantics) (application : String) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := endpoint)
    (modelRegistry endpoint application)

/- This extension concerns only the return occurrence in the actual retained
formula. It makes no claim to generate whole-protocol derivations (the later
source derivation workstream). The occurrence and its surrounding operations
are pinned to the generated body below. -/
open Zkc.Source Zkc.Source.Structured

abbrev viewContext : List Ty := [.boolean, .group "bls12-381.g1",
  .group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr"]

def returnView : Region dialect viewContext [.boolean] := .ret (.cons .here .nil)

def viewEnvironment : Environment (assignment F G) viewContext :=
  (Values.cons false (.cons (0 : G) (.cons 0 (.cons 0 (.cons (0 : F) .nil))))).get

abbrev identityOperations : PIR.OperationInterpretation closedInterface closedInterface :=
  fun operation => .call operation .done

def viewMeaning := meaning F G (Zkc.Construction.helperTable ZkcExamples.Construction.SchnorrProof.imported.program F G)

def ViewEqual : Prop :=
  ZkcExamples.Construction.SchnorrProofBodies.formulaBody =
    .letOp (.groupScale "bls12-381.g1" "bls12-381.fr")
      (.cons .here (.cons (.there (.there .here)) .nil)) .nil
      (.letOp (.groupEqual "bls12-381.g1")
        (.cons (.there (.there .here)) (.cons .here .nil)) .nil returnView) ∧
  (returnView.denote (viewMeaning (F := F) (G := G)) viewEnvironment).interpret identityOperations =
    .done (.cons false .nil)

omit [Fintype F] [Inhabited F] [SampleableType F] [SampleableType G] in
theorem proveView (_application : String) : ViewEqual (F := F) (G := G) := ⟨rfl, rfl⟩

noncomputable def viewProperty (endpoint : Semantics) (application : String) :
    PropertyExport (Subject F G artifacts endpoint) where
  Arguments _ := Unit
  elaborate request admitted := do
    admitted.check request
    let model ← resolveModel (modelRegistry endpoint application) F artifacts.original endpoint request.model
    match model with
    | .error missing => throw (.schema (String.intercalate ", " missing.definitions))
    | .ok _ =>
      if request.parameters.isSome || !request.capabilities.isEmpty then
        throw (.schema "local return view has no parameters or capabilities")
      match request.quantity with
      | .scalar (.natural 0) => pure ()
      | _ => throw (.schema "local return view requires zero quantity")
      return ()
  meaning _ _ := .ok (ViewEqual (F := F) (G := G))
  requiredLinks admitted _ := admitted.stageLinks

/-- Typed registry extension only; no native grammar or Python branch. -/
noncomputable def propertyRegistry (endpoint : Semantics) (application : String) :
    Registry (PropertyExport (Subject F G artifacts endpoint)) :=
  { exports := (builtinProperties (F := F) (G := G) endpoint application).exports ++
      [⟨⟨"user.view_equal", 0⟩, "zkc.property.local-return-view/0", some (viewProperty endpoint application)⟩] }

omit [Fintype F] [Inhabited F] [SampleableType F] [SampleableType G] in
/-- Named implication consumed by the existing derivation route and proof audit. -/
theorem viewOfReturn {proposition : Prop} (same : proposition = ViewEqual (F := F) (G := G))
    (equation : (returnView.denote (viewMeaning (F := F) (G := G)) viewEnvironment).interpret
      identityOperations = .done (.cons false .nil)) : proposition :=
  same.mpr ⟨rfl, equation⟩

/-- Existing occurrence-local derivation consumer at the same evaluated index. -/
noncomputable def proveDerived
    {registry : Registry (PropertyExport (Subject F G artifacts .idealMeaning))}
    {wire : Wire.Request}
    {resolved : Resolved registry Subject.reference (subjectIdeal (F := F) (G := G)) wire}
    (evaluated : Evaluated resolved) (same : evaluated.proposition = ViewEqual (F := F) (G := G))
    (links : (index : Fin resolved.requiredLinks.length) →
      Option (PLift (resolved.requiredLinks.get index).goal)) : Receipt evaluated :=
  Receipt.ofDerivation
    (Region.Derivation.ret (meaning := viewMeaning (F := F) (G := G))
      (operations := identityOperations) (.cons .here .nil) viewEnvironment)
    (viewOfReturn same)
    ⟨.derivation, "ZkcSecurity.Examples.Subjects.Schnorr.Registration.viewOfReturn",
      ⟨"user.view_derivation", 0⟩, [], []⟩ links

/-- The Sigma method must match the registered recovery function. -/
def justification (endpoint : Semantics) : SigmaJustification (subject (F := F) (G := G) endpoint) (extractionProfile (F := F) (G := G)) where
  Stmt := G
  PrvState := F
  handle := 0
  family := family
  model := model
  relation statement witness := by
    have pinned := (Contract.holds_pinned statement witness).symm.trans (relation statement witness)
    exact pinned
  shape := rfl
  recovery := by
    intro statement first response₁ second response₂
    simp only [family, ZkcSecurity.Families.Schnorr.family, _root_.Schnorr.sigma, extractionProfile,
      Extraction.Layout.recover_scalar, div_eq_mul_inv]

/-- A proof of the request-fixed experiment; the method cannot replace its profile. -/
theorem proveKnowledge {endpoint : Semantics}
    (request : KnowledgeRequest (subject (F := F) (G := G) endpoint)) : request.meaning := by
  have same := request.profile_eq (extractionProfile (F := F) (G := G)) rfl rfl
  apply knowledgeEndpoint request
  rw [same]
  exact justification endpoint

/-- The independent interactive Entry retains the actual target and selector. -/
def interactiveSubject : InteractiveSubject where
  reference := interactiveReference
  interactive := rfl
  noArtifacts := rfl
  snapshot := ZkcExamples.Structured.SchnorrInteractiveData.snapshot
  imported := ZkcExamples.Structured.SchnorrInteractive.imported
  owner := ZkcExamples.Structured.SchnorrBinding.owner
  entry := ZkcExamples.Structured.SchnorrBinding.owner_is_entry
  clauseIndex := ZkcExamples.Structured.SchnorrBinding.clauseIndex
  target := ZkcExamples.Structured.SchnorrBinding.exact_clause.1
  acceptancePort := ⟨0, by decide +kernel⟩
  acceptanceRole := ⟨1, by decide +kernel⟩
  boolean := rfl
  decision := rfl

def interactiveModels : Registry Unit :=
  ⟨[⟨⟨"models.interactive", 0⟩, "zkc.model.interactive/0", none⟩]⟩

@[simp] theorem admittedField : artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field := rfl

def library : Library where
  subject := ``subjectIdeal
  bytesSubject := some ``subjectBytes
  properties := ``propertyRegistry
  models := ``modelRegistry
  normalization := [``propertyRegistry, ``modelRegistry, ``subject, ``subjectIdeal,
    ``viewProperty, ``builtinProperties, ``admittedField, ``sourceReference, ``ZkcSecurity.Claims.stage, ``subjectBytes]
  interactiveSubject := some ``interactiveSubject
  interactiveModels := some ``interactiveModels
  methods := [(⟨"fs.forking", 0⟩, ``proveKnowledge)]
  theoremMethods := [(⟨"user.view_theorem", 0⟩, ``proveView)]
  receiptMethods := [(⟨"user.view_derivation", 0⟩, ``proveDerived)]

end ZkcSecurity.Examples.Subjects.Schnorr.Registration
