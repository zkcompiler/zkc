module

public import ZkcSecurity.Examples.Subjects.SchnorrAnd.Endpoints
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Typed author-library registration. The retained target and admitted artifacts
are fixed before source requests are resolved. Existing evidence only witnesses
the generic replay class; it never supplies a request's meaning. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Endpoint
open ZkcSecurity.Tools.ClaimConstruction

set_option smartUnfolding false
set_option linter.unusedSectionVars false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
  [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

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

def subjectIdeal := subject (F := F) (G := G)

def modelRegistry (endpoint : Semantics) (application : String) :=
  models (ModelContext.parameter "application" application) endpoint

noncomputable def propertyRegistry (endpoint : Semantics) (application : String) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := endpoint)
    (modelRegistry endpoint application)

/-- One shared route for all pinned Sigma subjects and both supported stages. -/
theorem proveKnowledge (request : KnowledgeRequest (subject (F := F) (G := G))) :
    request.meaning :=
  knowledgeEndpointOfEvidence request (knowledge .idealMeaning PUnit.unit)
    (by trivial) rfl HEq.rfl

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
