module

public import Zkc.Claims.Registry
public import ZkcSecurity.Claims.Extractor

@[expose] public section

/-! An admitted subject fixes the actual artifacts, compilation, application
meaning and selected stage before proof evidence is chosen. Digest attribution
and source label attribution are frontend links, explicitly distinct from the
kernel checked artifact, target, policy and occurrence selections below. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Endpoint

def stage : Semantics → Stage
  | .idealMeaning => .compiledIdeal
  | .executableBytes => .executableBytes

/-- A proposed static challenge occurrence, checked against the actual selected
construction context. Source-to-native label correspondence remains IR-relative. -/
structure Site (context : Context) where
  label : String
  native : String
  delivery : String
  selected : (native, delivery) ∈ context.draws
  request : Zkc.Construction.Request
  requestSelected : context.request = some request

def Site.event {context : Context} {F G : Type} (site : Site context) : Event F G :=
  .challenge (context.query site.native site.request)

structure Subject (F G : Type) [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (art : Artifacts) (endpoint : Semantics) where
  reference : SubjectRef
  stageMatched : reference.stage = stage endpoint
  compiled : Compiled art
  connection : compiled.SourceConnection (F := F) (G := G)
  target : SoundnessTarget compiled F G
  /-- A selected imported language must be exported under this versioned key.
  Retained targets do not consult this field. -/
  importedVersion : Nat := 0
  importedRegistry : Registry (ImportedLanguage compiled F G) := ⟨[]⟩
  importedRegistered : ∀ declaration, target = .importedLanguage declaration →
    ∃ entry, importedRegistry.lookup ⟨declaration.identifier, importedVersion⟩ = .ok entry ∧
      entry.definition = some declaration
  sites : List (Site compiled.context) := []
  sitesUnique : (sites.map Site.label).Nodup
  sitesNativeUnique : (sites.map Site.native).Nodup
  lowering : LoweringRequirement art compiled F G endpoint
  /-- Registered extraction semantics are fixed before proof-method selection. -/
  extractors : Registry { profile : ExtractionProfile compiled F G // target = .retained profile.target profile.formula } := ⟨[]⟩

namespace Subject
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  {art : Artifacts} {endpoint : Semantics} (subject : Subject F G art endpoint)

def targetReference : Wire.TargetRef :=
  match subject.target with
  | .retained target _ => .retained target.owner.contract.owner target.clauseIndex.val
      (target.owner.clause target.clauseIndex).name
  | .importedLanguage declaration => .importedLanguage art.original.entry
      ⟨⟨declaration.identifier, subject.importedVersion⟩, []⟩

def acceptance : Wire.Acceptance :=
  ⟨true, art.participant.policy.acceptance, subject.compiled.context.validator, []⟩

def falseStatement : art.Statement F G → Prop := subject.target.FalseStatement

/-- Exact matching is independent of evidence and display attachments. -/
def check (request : Wire.Request) : Except ResolutionError Unit := do
  if request.subject != subject.reference then throw .subjectMismatch
  if !request.target.matches subject.targetReference then throw .targetMismatch
  if request.accept != subject.acceptance then throw .acceptanceMismatch

end Subject
end ZkcSecurity.Claims
