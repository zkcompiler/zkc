module

public import ZkcSecurity.VCVio.UniformChallenge
public import ZkcSecurity.Claims.Soundness

@[expose] public section

open scoped ZkcSecurity.VCVio.UniformChallenge

/-! Knowledge meaning is the concrete registered extraction experiment against
the actual verifier and public-input adversary interface. Sigma families and
special soundness justify that meaning only in the endpoint proof method. -/

set_option autoImplicit false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Claims
open OracleComp OracleSpec
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint

section
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [Fintype F] {art : Artifacts} {endpoint : Semantics}

/-- Resolve semantic data only from the admitted subject's registry. The small
request stores a proof of availability, never a second copy of that data. -/
def Subject.extractionProfile (subject : Subject F G art endpoint) :
    Option { profile : ExtractionProfile subject.compiled F G // subject.target = .retained profile.target profile.formula } := do
  let entry ← (subject.extractors.lookup responseDifference).toOption
  if entry.identifier = responseDifference ∧ entry.schema = "zkc.extractor.response-difference/0" then
    entry.definition
  else none

structure KnowledgeRequest (subject : Subject F G art endpoint) where
  registered : subject.extractionProfile.isSome = true
  model : Model
  fixed : model.form = .fixed

namespace KnowledgeRequest
variable {subject : Subject F G art endpoint} (request : KnowledgeRequest subject)

abbrev profile : ExtractionProfile subject.compiled F G :=
  (subject.extractionProfile.get request.registered).val

omit [SampleableType F] [Fintype F] in
theorem selected : subject.target = .retained request.profile.target request.profile.formula :=
  (subject.extractionProfile.get request.registered).property

omit [SampleableType F] [Fintype F] in
/-- A singleton standard registration fixes the whole interface, not just the
name of its recovery arithmetic. -/
theorem profile_eq (profile : ExtractionProfile subject.compiled F G)
    (selected : subject.target = .retained profile.target profile.formula)
    (registered : subject.extractors = profile.registry subject.target selected) : request.profile = profile := by
  have lookup : subject.extractionProfile = some ⟨profile, selected⟩ := by
    unfold Subject.extractionProfile
    rw [registered]
    rfl
  unfold KnowledgeRequest.profile
  simp only [lookup, Option.get_some]

/-- Public-input prover followed by the actual compiled verifier, in one cache. -/
def typedRun (_request : KnowledgeRequest subject) (statement : art.Statement F G) (initial : History F G)
    (prover : TypedProver F G (art.Statement F G)) :
    OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Bool :=
  StateT.run' (simulateQ (Sigma.forwardUniform (F := F) (G := G) + Sigma.historyOracle (F := F) (G := G)) (do
    let proof ← prover statement initial
    verdict <$> subject.compiled.verifier Sigma.historyChallenge statement initial proof)) (∅ : Sigma.Cache F G)

noncomputable def typedAcceptance (request : KnowledgeRequest subject) (statement : art.Statement F G) (initial : History F G)
    (prover : TypedProver F G (art.Statement F G)) : ENNReal :=
  Pr{let accepted ← request.typedRun statement initial prover}[accepted = true]

def bytesRun {subject : Subject F G art .executableBytes} (_request : KnowledgeRequest subject)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (statement : art.Statement F G) (initial : History F G)
    (prover : BytesProver F G (art.Statement F G)) :
    OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Bool :=
  StateT.run' (simulateQ (Sigma.forwardUniform (F := F) (G := G) + Sigma.historyOracle (F := F) (G := G)) (do
    let bytes ← prover statement initial
    subject.lowering.validate Sigma.historyChallenge codec budget binding statement initial bytes)) (∅ : Sigma.Cache F G)

noncomputable def bytesAcceptance {subject : Subject F G art .executableBytes} (request : KnowledgeRequest subject)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (statement : art.Statement F G) (initial : History F G)
    (prover : BytesProver F G (art.Statement F G)) : ENNReal :=
  Pr{let accepted ← request.bytesRun codec budget binding statement initial prover}[accepted = true]

def IdealGuarantee {subject : Subject F G art .idealMeaning} (request : KnowledgeRequest subject) : Prop :=
  ∀ (statement : art.Statement F G) (initial : History F G)
    (prover : TypedProver F G (art.Statement F G)) (queries : Nat),
    request.model.queries.allows queries →
    IsQueryBoundP (prover statement initial) (· matches .inr _) queries →
    let accepting := request.typedAcceptance statement initial prover
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let extracted ← request.profile.extract statement initial prover queries}[
        request.profile.target.Holds request.profile.formula statement (request.profile.embed extracted)]

def BytesGuarantee {subject : Subject F G art .executableBytes} (request : KnowledgeRequest subject) : Prop :=
  ∀ codec budget binding (statement : art.Statement F G) (initial : History F G)
    (prover : BytesProver F G (art.Statement F G)) (queries : Nat),
    request.model.queries.allows queries →
    IsQueryBoundP (prover statement initial) (· matches .inr _) queries →
    let accepting := request.bytesAcceptance codec budget binding statement initial prover
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let extracted ← request.profile.extract statement initial
          (fun published history => subject.lowering.decoded codec published <$> prover published history) queries}[
        request.profile.target.Holds request.profile.formula statement (request.profile.embed extracted)]

/-- No existential family, extractor, prover key, or witness map occurs here. -/
def meaning : Prop :=
  match endpoint with
  | .idealMeaning => request.IdealGuarantee
  | .executableBytes => request.BytesGuarantee

end KnowledgeRequest

end
end ZkcSecurity.Claims
