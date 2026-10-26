module

public import ZkcSecurity.Examples.Subjects.ChaumPedersen.Endpoints
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Typed author-library registration. The retained target and admitted artifacts
are fixed before source requests are resolved. Existing evidence only witnesses
the registered extraction experiment; it never supplies a request's meaning. -/

namespace ZkcSecurity.Examples.Subjects.ChaumPedersen.Registration
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Endpoint
open ZkcSecurity.Tools.ClaimConstruction

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
  [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- Registered transcript and scalar-coordinate interpretation, fixed independently of evidence. -/
def extractionProfile : ExtractionProfile compiled F G where
  target := Contract.retained
  layout := .scalar 4
  domain := "bls12-381.fr"
  coordinates := by decide +kernel
  Commit := G × G
  decidableCommit := inferInstance
  shape := ZkcSecurity.Families.SchnorrVariants.equalityShape compiled.context ZkcExamples.Construction.ChaumPedersenProof.wiring
  native := ZkcExamples.Construction.ChaumPedersenProof.wiring.challengeSite
  delivery := "label_64656c6976657279_0"
  selected := by decide +kernel
  request := .draw ZkcExamples.Construction.ChaumPedersenProof.wiring.fieldDomain
  requestSelected := rfl
  scalarChallenge := rfl
  challenge := rfl

def subject : Subject F G artifacts .idealMeaning where
  reference := sourceReference (stage .idealMeaning)
  stageMatched := rfl
  compiled := compiled
  connection := sourceConnection
  target := .retained Contract.retained
  importedRegistered := by intro declaration impossible; cases impossible
  sites := sourceSites
  sitesUnique := by decide +kernel
  sitesNativeUnique := by decide +kernel
  lowering := PUnit.unit
  extractors := extractionProfile.registry (.retained Contract.retained) rfl

def subjectIdeal := subject (F := F) (G := G)

def modelRegistry (endpoint : Semantics) (application : String) :=
  models (ModelContext.parameter "application" application) endpoint

noncomputable def propertyRegistry (endpoint : Semantics) (application : String) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := endpoint)
    (modelRegistry endpoint application)

/-- The Sigma method must match the registered recovery function. -/
def justification : SigmaJustification (subject (F := F) (G := G)) (extractionProfile (F := F) (G := G)) where
  Stmt := G × G
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
    simp only [family, ZkcSecurity.Families.SchnorrVariants.equalityFamily, ZkcSecurity.Families.SchnorrVariants.equalitySigma, _root_.Schnorr.sigma, extractionProfile,
      Extraction.Layout.recover_scalar, div_eq_mul_inv]

/-- A proof of the request-fixed experiment; the method cannot replace its profile. -/
theorem proveKnowledge
    (request : KnowledgeRequest (subject (F := F) (G := G))) : request.meaning := by
  have same := request.profile_eq (extractionProfile (F := F) (G := G)) rfl rfl
  apply knowledgeEndpoint request
  rw [same]
  exact justification (F := F) (G := G)

@[simp] theorem admittedField : artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field := rfl

def library : Library where
  subject := ``subjectIdeal
  bytesSubject := none
  properties := ``propertyRegistry
  models := ``modelRegistry
  normalization := [``propertyRegistry, ``modelRegistry, ``subject, ``subjectIdeal,
    ``admittedField, ``sourceReference, ``ZkcSecurity.Claims.stage]
  methods := [(⟨"fs.forking", 0⟩, ``proveKnowledge)]

end ZkcSecurity.Examples.Subjects.ChaumPedersen.Registration
