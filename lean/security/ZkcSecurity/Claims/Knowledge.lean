module

public import ZkcSecurity.VCVio.UniformChallenge
public import ZkcSecurity.Claims.Soundness
public import ZkcSecurity.Claims.EndpointHypotheses

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
    Option { profile : ExtractionProfile subject.compiled F G // subject.target = .retained profile.target } := do
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
theorem selected : subject.target = .retained request.profile.target :=
  (subject.extractionProfile.get request.registered).property

omit [SampleableType F] [Fintype F] in
/-- A singleton standard registration fixes the whole interface, not just the
name of its recovery arithmetic. -/
theorem profile_eq (profile : ExtractionProfile subject.compiled F G)
    (selected : subject.target = .retained profile.target)
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
        request.profile.target.Holds statement (request.profile.embed extracted)]

def BytesGuarantee {subject : Subject F G art .executableBytes} (request : KnowledgeRequest subject) : Prop :=
  ∀ codec budget binding (statement : art.Statement F G) (initial : History F G)
    (prover : BytesProver F G (art.Statement F G)) (queries : Nat),
    request.model.queries.allows queries →
    IsQueryBoundP (prover statement initial) (· matches .inr _) queries →
    let accepting := request.bytesAcceptance codec budget binding statement initial prover
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let extracted ← request.profile.extract statement initial
          (fun published history => subject.lowering.decoded codec published <$> prover published history) queries}[
        request.profile.target.Holds statement (request.profile.embed extracted)]

/-- No existential family, extractor, prover key, or witness map occurs here. -/
def meaning : Prop :=
  match endpoint with
  | .idealMeaning => request.IdealGuarantee
  | .executableBytes => request.BytesGuarantee

end KnowledgeRequest

/-- Method data only. Its recovery equality rules out substituting witness
search for the request's registered response-difference function. -/
structure SigmaJustification (subject : Subject F G art endpoint)
    (profile : ExtractionProfile subject.compiled F G) where
  Stmt : Type
  PrvState : Type
  handle : Nat
  family : SigmaFamily (F := F) (G := G) subject.compiled.context (art.Statement F G)
    Stmt profile.Witness profile.Commit PrvState profile.Witness
  model : ∀ statement, subject.compiled.original statement handle = family.validator statement
  relation : ∀ statement witness,
    profile.target.Holds statement (profile.embed witness) ↔ family.rel statement (family.key statement) witness = true
  shape : family.shape = profile.shape
  recovery : ∀ statement first left second right,
    (family.sigma statement).extract first left second right =
      pure (profile.layout.recover first left second right)

namespace SigmaJustification
variable {subject : Subject F G art endpoint} {profile : ExtractionProfile subject.compiled F G}
  (justification : SigmaJustification subject profile)

def evidence : KnowledgeEvidence art endpoint justification.Stmt profile.Witness profile.Commit
    justification.PrvState profile.Witness (fun statement witness => profile.target.Holds statement (profile.embed witness)) where
  compiled := subject.compiled
  connection := subject.connection
  target := profile.target
  witness := profile.embed
  relationPinned _ _ := Iff.rfl
  handle := justification.handle
  family := justification.family
  model := justification.model
  relation := justification.relation
  lowering := subject.lowering
  hypotheses := []

omit [SampleableType F] [Fintype F] in
/-- The actual cached verifier has the family's verification result at the
registered challenge. No constant challenge is supplied at unrelated sites. -/
theorem verify_eq (statement : art.Statement F G) (initial : History F G)
    (cache : (Sigma.Key F G profile.Commit →ₒ F).QueryCache)
    (commitment : profile.Commit) (response : profile.Witness) :
    profile.verify statement initial cache commitment response =
      match cache (.inl initial, commitment) with
      | some challenge => (justification.family.sigma statement).verify
          (justification.family.key statement) commitment challenge response
      | none => false := by
  unfold ExtractionProfile.verify
  rw [← justification.shape, Compiled.transform_eq _ subject.connection _ statement justification.handle, justification.model,
    justification.family.transform_shape, justification.shape, profile.shape.route_append]
  cases cache (.inl initial, commitment) <;> rfl

omit [Fintype F] in
/-- The registered experiment equals the existing endpoint's replay algorithm
only after checking shape and recovery correspondence. -/
theorem extract_eq (statement : art.Statement F G) (initial : History F G)
    (prover : TypedProver F G (art.Statement F G)) (queries : Nat) :
    profile.extract statement initial prover queries =
      _root_.FiatShamir.knowledgeExtractor (justification.family.sigma statement)
        (justification.family.generable statement) (History F G ⊕ History F G)
        (justification.family.shape.reduce
          (justification.evidence.readProver (fun _ history => prover statement history)))
        (.inl initial) queries (justification.family.key statement) := by
  unfold ExtractionProfile.extract
  have verifies := funext fun cache => funext fun commitment => funext fun response =>
    justification.verify_eq statement initial cache commitment response
  rw [verifies]
  have recovery := funext fun first => funext fun left => funext fun second => funext fun right =>
    justification.recovery statement first left second right
  rw [← recovery]
  rw [← Extraction.replay_eq (justification.family.sigma statement)
    (justification.family.generable statement)
    (justification.family.shape.reduce (justification.evidence.readProver (fun _ history => prover statement history)))
    (justification.family.key statement) (.inl initial) queries]
  congr 1
  funext message
  change simulateQ profile.shape.routeQueries (profile.shape.read <$> prover statement (message.elim id id)) =
    simulateQ justification.family.shape.routeQueries
      (justification.family.shape.read <$> prover statement (message.elim id id))
  rw [justification.shape]

end SigmaJustification

/-- The endpoint is a proof method for the independently fixed request. -/
theorem knowledgeEndpoint [Inhabited F] {subject : Subject F G art endpoint} (request : KnowledgeRequest subject)
    (justification : SigmaJustification subject request.profile) : request.meaning := by
  cases endpoint with
  | idealMeaning =>
    intro statement initial prover queries _ bounded
    rw [justification.extract_eq]
    exact knowledge_soundness justification.evidence statement initial
      (fun _ history => prover statement history) queries bounded
  | executableBytes =>
    intro codec budget binding statement initial prover queries _ bounded
    rw [justification.extract_eq]
    have decoded : justification.evidence.decodedProver codec statement (fun _ history => prover statement history) =
        justification.evidence.readProver (fun _ history => subject.lowering.decoded codec statement <$> prover statement history) := by
      funext key history
      change (fun bytes => justification.family.shape.read (subject.lowering.decoded codec statement bytes)) <$>
          prover statement history = justification.family.shape.read <$> (subject.lowering.decoded codec statement <$> prover statement history)
      rw [Functor.map_map]
    rw [← decoded]
    exact knowledge_soundness_bytes justification.evidence codec budget binding statement initial
      (fun _ history => prover statement history) queries bounded

end
end ZkcSecurity.Claims
