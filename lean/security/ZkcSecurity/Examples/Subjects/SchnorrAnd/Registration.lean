module

public import ZkcSecurity.Examples.Subjects.SchnorrAnd.Endpoints
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Typed author-library registration. The retained target and admitted artifacts
are fixed before source requests are resolved. Existing evidence only witnesses
the registered extraction experiment; it never supplies a request's meaning. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Endpoint
open ZkcSecurity.Tools.ClaimConstruction

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
  [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- Registered transcript and scalar-coordinate interpretation, fixed independently of evidence. -/
def extractionProfile : ExtractionProfile compiled F G where
  target := Contract.retained
  layout := .pair (.scalar 4) (.scalar 5)
  domain := "bls12-381.fr"
  coordinates := by decide +kernel
  Commit := G × G
  decidableCommit := inferInstance
  shape := ZkcSecurity.Families.SchnorrVariants.conjunctionShape compiled.context ZkcExamples.Construction.SchnorrAndProof.wiring
  native := ZkcExamples.Construction.SchnorrAndProof.wiring.challengeSite
  delivery := "label_64656c6976657279_0"
  selected := by decide +kernel
  request := .draw ZkcExamples.Construction.SchnorrAndProof.wiring.fieldDomain
  requestSelected := rfl
  scalarChallenge := rfl
  challenge := rfl

def subject : Subject F G artifacts .idealMeaning where
  reference := sourceReference (stage .idealMeaning)
  stageMatched := rfl
  compiled := compiled
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
  PrvState := F × F
  handle := 0
  family := family
  model := model
  relation statement witness := by
    have pinned := (Contract.holds_pinned statement witness).symm.trans (relation statement witness)
    have embed : extractionProfile.embed witness = Contract.embed witness := by
      funext type selector
      cases type <;> try rfl
      by_cases coordinate : selector.port.index = 4 <;>
        simp [ExtractionProfile.embed, Extraction.Layout.embed, Extraction.Layout.read_pair, Extraction.Layout.read_scalar,
          extractionProfile, Contract.embed, coordinate]
    change Contract.retained.Holds statement (extractionProfile.embed witness) ↔ _
    rw [embed]
    exact pinned
  shape := rfl
  recovery := by
    intro statement first response₁ second response₂
    simp only [family, ZkcSecurity.Families.SchnorrVariants.conjunctionFamily, ZkcSecurity.VCVio.SigmaAndSchnorr.sigma, ZkcSecurity.VCVio.SigmaAnd.and, _root_.Schnorr.sigma, extractionProfile,
      Extraction.Layout.recover_pair, Extraction.Layout.recover_scalar, div_eq_mul_inv, pure_bind]

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

end ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration
