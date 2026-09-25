import Zkc.Compiler.Checking
import Zkc.Source.InputBinding

/-! Consumer-bound metadata for the direct logical-plan checker.

References identify definitions that the consumer must resolve. Matching them
does not prove an external implementation or cryptographic assumption. The only
implemented rule introduces no requirements and preserves complete logical
execution for all inputs and handlers under the same interpretation.
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

structure DefinitionRef where
  name : String
  revision : String
  deriving DecidableEq, Repr

structure CompilationContext (Ty : Type) where
  role : String
  inputs : List (InputDeclaration Ty)
  resultType : Ty
  dependencies : List DefinitionRef
  deriving DecidableEq, Repr

structure Claim where
  relation : String
  observation : String
  scope : String
  deriving DecidableEq, Repr

def completeExecution : Claim :=
  ⟨"equality", "logical-outcome-state-events", "all-inputs-and-handlers"⟩

def formatVersion : Nat := 1
def semanticsVersion : String := "finite-source-1"

structure Request (Ty Op : Type) where
  context : CompilationContext Ty
  permittedRequirements : List DefinitionRef
  source : RawProgram Ty Op
  deriving DecidableEq, Repr

structure Candidate (Ty Op : Type) where
  format : Nat
  semantics : String
  capabilities : List String
  realization : String
  rule : String
  claim : Claim
  context : CompilationContext Ty
  requirements : List DefinitionRef
  body : RawProgram Ty Op
  deriving DecidableEq, Repr

inductive CheckError where
  | formatVersion
  | semanticsVersion
  | unsupportedCapability
  | unsupportedRealization
  | unsupportedRule
  | unsupportedClaim
  | contextMismatch
  | invalidContext
  | unapprovedRequirement
  | unsupportedRequirement
  | malformedSource
  | uncheckedPlan
  deriving DecidableEq, Repr

def CheckError.code : CheckError → String
  | .formatVersion => "unsupported-format-version"
  | .semanticsVersion => "unsupported-semantics-version"
  | .unsupportedCapability => "unsupported-capability"
  | .unsupportedRealization => "unsupported-realization"
  | .unsupportedRule => "unsupported-rule"
  | .unsupportedClaim => "unsupported-claim"
  | .contextMismatch => "context-mismatch"
  | .invalidContext => "invalid-context"
  | .unapprovedRequirement => "unapproved-requirement"
  | .unsupportedRequirement => "unsupported-requirement"
  | .malformedSource => "malformed-source"
  | .uncheckedPlan => "unchecked-plan"

variable {Ty Op : Type} [DecidableEq Ty]

def validContext (context : CompilationContext Ty) : Bool :=
  !context.role.isEmpty &&
    decide ((context.inputs.map (·.name)).Nodup) &&
    context.inputs.all (fun input => !input.name.isEmpty &&
      (input.access == .shared || input.access == .privateTo context.role)) &&
    decide ((context.dependencies.map (·.name)).Nodup) &&
    context.dependencies.all (fun ref => !ref.name.isEmpty && !ref.revision.isEmpty)

/-- Carrier-independent metadata. Bodies are checked separately against their
consumer-selected grammar and transformation rule. -/
structure PlanMetadata (Ty : Type) where
  format : Nat
  semantics : String
  capabilities : List String
  realization : String
  rule : String
  claim : Claim
  context : CompilationContext Ty
  requirements : List DefinitionRef
  deriving DecidableEq, Repr

def Candidate.metadata (candidate : Candidate Ty Op) : PlanMetadata Ty :=
  ⟨candidate.format, candidate.semantics, candidate.capabilities, candidate.realization,
    candidate.rule, candidate.claim, candidate.context, candidate.requirements⟩

/-- Capabilities describe additional mandatory facilities; each direct grammar
is selected explicitly. Sharing policy never converts or ignores a body. -/
def directMetadataError (semantics : String) (context : CompilationContext Ty)
    (permitted : List DefinitionRef) (candidate : PlanMetadata Ty) : Option CheckError :=
  if candidate.format != formatVersion then some .formatVersion
  else if candidate.semantics != semantics then some .semanticsVersion
  else if !candidate.capabilities.isEmpty then some .unsupportedCapability
  else if candidate.realization != "direct-logical-plan" then some .unsupportedRealization
  else if candidate.rule != "direct-lowering" then some .unsupportedRule
  else if candidate.claim != completeExecution then some .unsupportedClaim
  else if candidate.context != context then some .contextMismatch
  else if !validContext context then some .invalidContext
  else if candidate.requirements.any (fun ref => !permitted.contains ref) then
    some .unapprovedRequirement
  else if !candidate.requirements.isEmpty then some .unsupportedRequirement
  else none

def metadataError (request : Request Ty Op) (candidate : Candidate Ty Op) : Option CheckError :=
  directMetadataError semanticsVersion request.context request.permittedRequirements candidate.metadata

variable {language : Language} [DecidableEq language.Ty]

structure CheckedArtifact (request : Request language.Ty language.Op)
    (candidate : Candidate language.Ty language.Op) where
  metadata : metadataError request candidate = none
  source : Program language (request.context.inputs.map (·.type)) request.context.resultType
  elaborated : request.source.elaborate _ _ = .ok source
  checked : CheckedPlan source candidate.body

def checkCandidate [DecidableEq language.Op] (request : Request language.Ty language.Op)
    (candidate : Candidate language.Ty language.Op) :
    Except CheckError (CheckedArtifact (language := language) request candidate) :=
  match metadata : metadataError request candidate with
  | some error => .error error
  | none =>
    match elaborated : request.source.elaborate
        (request.context.inputs.map (·.type)) request.context.resultType with
    | .error _ => .error .malformedSource
    | .ok source =>
      match checkDirect source candidate.body with
      | none => .error .uncheckedPlan
      | some checked => .ok ⟨metadata, source, elaborated, checked⟩

end Zkc.Compiler
