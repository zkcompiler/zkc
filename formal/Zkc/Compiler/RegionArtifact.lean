import Zkc.Compiler.ArtifactFormat
import Zkc.Source.RegionFormat

/-! Source-relative checking for compact regions. Metadata policy is shared with
the finite direct path; body admission remains specific to this explicit grammar.
Neither decoding nor checking calls the potentially expanding `Region.flatten`.
-/

set_option autoImplicit false
namespace Zkc.Compiler.RegionArtifact
open Lean Source Source.Format

def semanticsVersion : String := "region-source-1"

structure Request (Ty Op : Type) where
  context : CompilationContext Ty
  permittedRequirements : List DefinitionRef
  source : RawRegion Ty Op
  deriving DecidableEq, Repr

structure Candidate (Ty Op : Type) where
  metadata : PlanMetadata Ty
  body : RawRegion Ty Op
  deriving DecidableEq, Repr

variable {Ty Op : Type}

def request (types : Codec Ty) (operations : Codec Op) (depth : Nat) : Codec (Request Ty Op) where
  encode value := .arr #[.str "zkc-request", toJson formatVersion, .str semanticsVersion,
    (ArtifactFormat.context types).encode value.context,
    .arr (value.permittedRequirements.map ArtifactFormat.reference.encode).toArray,
    RegionFormat.encode types operations value.source]
  decode json := do
    match ← array json with
    | [.str "zkc-request", version, semantics, ctx, permitted, source] =>
      if (← natural version) != formatVersion || (← string semantics) != semanticsVersion then
        throw .shape
      return ⟨← (ArtifactFormat.context types).decode ctx,
        ← (← array permitted).mapM ArtifactFormat.reference.decode,
        ← RegionFormat.decode types operations depth source⟩
    | _ => throw .shape

def candidate (types : Codec Ty) (operations : Codec Op) (depth : Nat) : Codec (Candidate Ty Op) where
  encode value := .arr #[.str "zkc-plan", toJson value.metadata.format, .str value.metadata.semantics,
    toJson value.metadata.capabilities, .str value.metadata.realization, .str value.metadata.rule,
    ArtifactFormat.claim.encode value.metadata.claim,
    (ArtifactFormat.context types).encode value.metadata.context,
    .arr (value.metadata.requirements.map ArtifactFormat.reference.encode).toArray,
    RegionFormat.encode types operations value.body]
  decode json := do
    match ← array json with
    | [.str "zkc-plan", version, semantics, capabilities, realization, rule, property, ctx,
        requirements, body] =>
      return ⟨⟨← natural version, ← string semantics, ← (← array capabilities).mapM string,
        ← string realization, ← string rule, ← ArtifactFormat.claim.decode property,
        ← (ArtifactFormat.context types).decode ctx,
        ← (← array requirements).mapM ArtifactFormat.reference.decode⟩,
        ← RegionFormat.decode types operations depth body⟩
    | _ => throw .shape

variable {language : Language} [DecidableEq language.Ty]

structure Checked (request : Request language.Ty language.Op)
    (candidate : Candidate language.Ty language.Op) where
  metadata : directMetadataError semanticsVersion request.context request.permittedRequirements
    candidate.metadata = none
  region : Region language (request.context.inputs.map (·.type)) request.context.resultType
  sourceDecoded : request.source.elaborate _ _ = .ok region
  candidateDecoded : candidate.body.elaborate _ _ = .ok region

def check [DecidableEq language.Op] (request : Request language.Ty language.Op)
    (candidate : Candidate language.Ty language.Op) :
    Except CheckError (Checked (language := language) request candidate) :=
  match metadata : directMetadataError semanticsVersion request.context
      request.permittedRequirements candidate.metadata with
  | some error => .error error
  | none =>
    match decoded : request.source.elaborate
        (request.context.inputs.map (·.type)) request.context.resultType with
    | .error _ => .error .malformedSource
    | .ok region =>
      if same : region.erase = candidate.body then
        .ok ⟨metadata, region, decoded, same ▸ region.elaborate_erase⟩
      else .error .uncheckedPlan

/-- Any typed interpretation of the submitted candidate has the same complete
execution as the checked source, for every environment, handler and state. -/
theorem Checked.correct {request : Request language.Ty language.Op}
    {candidate : Candidate language.Ty language.Op} (checked : Checked request candidate)
    (plan : Region language (request.context.inputs.map (·.type)) request.context.resultType)
    (decoded : candidate.body.elaborate _ _ = .ok plan)
    {interface : PIR.Signature} {S E : Type}
    (meaning : Interpretation language interface) (handler : PIR.Handler interface S E)
    (env : Environment meaning.Value (request.context.inputs.map (·.type))) (state : S) :
    (plan.denote meaning env).run handler state =
      (checked.region.denote meaning env).run handler state := by
  have same : checked.region = plan := Except.ok.inj (checked.candidateDecoded.symm.trans decoded)
  rw [same]

end Zkc.Compiler.RegionArtifact
