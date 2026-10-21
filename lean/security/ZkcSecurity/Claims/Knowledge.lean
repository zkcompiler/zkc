module

public import ZkcSecurity.Claims.Soundness
public import ZkcSecurity.Claims.EndpointHypotheses
public import ZkcSecurity.Endpoint.Knowledge

@[expose] public section

/-! K3 fixes an existential replay-extractor class. Its quantified witnesses
are a special-sound Sigma protocol, transcript shape and actual compiled
correspondence. The extractor is always VCVio's replay extractor on injectively
routed proofs; neither an arbitrary extractor nor an arbitrary relation can be
supplied by evidence. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open OracleComp OracleSpec
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Endpoint

section
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [Fintype F] [Inhabited F] {art : Artifacts} {endpoint : Semantics}
  (subject : Subject F G art endpoint)

/-- The existential data and checked correspondence of the registered class.
The relation of the eventual experiment is always the selected retained
formula, applied to its actual published values and logical witnesses. -/
structure ReplayClass (target : RetainedTarget subject.compiled.imported art.participant.policy art.publics) where
  Stmt : Type
  Wit : Type
  Commit : Type
  PrvState : Type
  Resp : Type
  decidableCommit : DecidableEq Commit
  sampleableWitness : SampleableType Wit
  handle : Nat
  family : SigmaFamily (F := F) (G := G) subject.compiled.context (art.Statement F G)
    Stmt Wit Commit PrvState Resp
  witness : Wit → target.Witness F G
  model : ∀ statement, subject.compiled.original statement handle = family.validator statement
  relation : ∀ statement extracted,
    target.Holds statement (witness extracted) ↔ family.rel statement (family.key statement) extracted = true

attribute [instance] ReplayClass.decidableCommit ReplayClass.sampleableWitness

/-- Reuse any existing pinned endpoint package. Compiled equality and the
dependent target equality are checked before its family can witness the fixed
request class. No relation, extractor or guarantee is selected by this adapter.
`HEq` compares the retained targets across the two compiled indices; after
`compiled` it is ordinary equality. -/
def ReplayClass.ofEvidence
    (target : RetainedTarget subject.compiled.imported art.participant.policy art.publics)
    {Stmt Wit Commit PrvState Resp : Type} [DecidableEq Commit] [SampleableType Wit]
    {holds : art.Statement F G → Wit → Prop}
    (evidence : KnowledgeEvidence art endpoint Stmt Wit Commit PrvState Resp holds)
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (compiled : evidence.compiled = subject.compiled) (selected : HEq evidence.target target) :
    ReplayClass subject target := by
  rcases subject with ⟨reference, stageMatched, subjectCompiled, subjectTarget, version, registry,
    registered, sites, unique, nativeUnique, lowering⟩
  dsimp only at compiled selected target ⊢
  cases compiled
  cases eq_of_heq selected
  exact {
    Stmt := Stmt, Wit := Wit, Commit := Commit, PrvState := PrvState, Resp := Resp
    decidableCommit := inferInstance
    sampleableWitness := inferInstance
    handle := evidence.handle
    family := evidence.family
    witness := evidence.witness
    model := evidence.model
    relation := fun statement extracted =>
      (evidence.relationPinned statement extracted).symm.trans (evidence.relation statement extracted) }

namespace ReplayClass
variable {subject}
  {target : RetainedTarget subject.compiled.imported art.participant.policy art.publics}

/-- An internal application of the preserved endpoint API. This function does
not accept a predicate: `holds` is definitionally the selected retained formula. -/
def evidence (replay : ReplayClass subject target) :
    KnowledgeEvidence art endpoint replay.Stmt replay.Wit replay.Commit replay.PrvState replay.Resp
      (fun statement extracted => target.Holds statement (replay.witness extracted)) where
  compiled := subject.compiled
  target := target
  witness := replay.witness
  relationPinned _ _ := Iff.rfl
  handle := replay.handle
  family := replay.family
  model := replay.model
  relation := replay.relation
  lowering := subject.lowering
  hypotheses := []

omit [SampleableType F] [Fintype F] [Inhabited F] in
/-- Explicit class laws: verifier correspondence and globally injective
routing, using the existing Sigma model. -/
theorem corresponds (replay : ReplayClass subject target) (statement : art.Statement F G) (initial : History F G) :
    Sigma.Corresponds replay.family.shape (replay.family.sigma statement) (replay.family.key statement)
      initial (replay.evidence.verify statement initial) := replay.evidence.corresponds statement initial

omit [SampleableType F] [Fintype F] [Inhabited F] in
theorem routing_injective (replay : ReplayClass subject target) :
    Function.Injective replay.family.shape.route := replay.family.shape.route_injective

/-- The exact registered forking form. The model's natural query symbol stays
universally quantified. In particular the endpoint's general Q is retained. -/
def IdealGuarantee {subject : Subject F G art .idealMeaning}
    {target : RetainedTarget subject.compiled.imported art.participant.policy art.publics}
    (replay : ReplayClass subject target) (limit : QueryLimit) : Prop :=
  ∀ (statement : art.Statement F G) (initial : History F G)
    (prover : TypedProver F G replay.Stmt) (queries : Nat),
    limit.allows queries → IsQueryBoundP (prover (replay.family.key statement) initial) (· matches .inr _) queries →
    let accepting := replay.evidence.typedAcceptance prover statement initial
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let extracted ← _root_.FiatShamir.knowledgeExtractor (replay.family.sigma statement)
          (replay.family.generable statement) (History F G ⊕ History F G)
          (replay.family.shape.reduce (replay.evidence.readProver prover)) (.inl initial) queries
          (replay.family.key statement)}[target.Holds statement (replay.witness extracted)]

def BytesGuarantee {subject : Subject F G art .executableBytes}
    {target : RetainedTarget subject.compiled.imported art.participant.policy art.publics}
    (replay : ReplayClass subject target) (limit : QueryLimit) : Prop :=
  ∀ codec budget binding (statement : art.Statement F G) (initial : History F G)
    (prover : BytesProver F G replay.Stmt) (queries : Nat),
    limit.allows queries → IsQueryBoundP (prover (replay.family.key statement) initial) (· matches .inr _) queries →
    let accepting := replay.evidence.bytesAcceptance codec budget binding prover statement initial
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let extracted ← _root_.FiatShamir.knowledgeExtractor (replay.family.sigma statement)
          (replay.family.generable statement) (History F G ⊕ History F G)
          (replay.family.shape.reduce (replay.evidence.decodedProver codec statement prover)) (.inl initial) queries
          (replay.family.key statement)}[target.Holds statement (replay.witness extracted)]

def guarantee (replay : ReplayClass subject target) (limit : QueryLimit) : Prop :=
  match endpoint with
  | .idealMeaning => replay.IdealGuarantee limit
  | .executableBytes => replay.BytesGuarantee limit

/-- The checked endpoint implication, preserving the actual compiled verifier,
special soundness, model equation, exact replay algorithm and forking formula. -/
theorem proveGuarantee (replay : ReplayClass subject target) (limit : QueryLimit) : replay.guarantee limit := by
  cases endpoint with
  | idealMeaning =>
    intro statement initial prover queries _ bounded
    exact knowledge_soundness replay.evidence statement initial prover queries bounded
  | executableBytes =>
    intro codec budget binding statement initial prover queries _ bounded
    exact knowledge_soundness_bytes replay.evidence codec budget binding statement initial prover queries bounded

end ReplayClass

structure KnowledgeRequest where
  target : RetainedTarget subject.compiled.imported art.participant.policy art.publics
  selected : subject.target = .retained target
  model : Model
  fixed : model.form = .fixed

/-- The protocol and transcript shape are existentially quantified before the
statements, histories, provers and query counts in the guarantee. Evidence
witnesses this fixed Sigma replay class, not an arbitrary extractor theory or a
canonical family representation. The guarantee is a probability inequality;
it does not state a running-time bound. -/
def KnowledgeRequest.meaning {subject : Subject F G art endpoint} (request : KnowledgeRequest subject) : Prop :=
  ∃ replay : ReplayClass subject request.target, replay.guarantee request.model.queries

theorem knowledgeEndpoint {subject : Subject F G art endpoint} (request : KnowledgeRequest subject)
    (replay : ReplayClass subject request.target) : request.meaning :=
  ⟨replay, replay.proveGuarantee request.model.queries⟩

/-- Reuse a pinned endpoint package for a request about the same admitted subject
and selected target. The method supplies evidence, never the request's meaning.
The target selection transport is shared by all Sigma registrations. -/
theorem knowledgeEndpointOfEvidence {subject : Subject F G art endpoint}
    (request : KnowledgeRequest subject)
    {Stmt Wit Commit PrvState Resp : Type} [DecidableEq Commit] [SampleableType Wit]
    {holds : art.Statement F G → Wit → Prop}
    (evidence : KnowledgeEvidence art endpoint Stmt Wit Commit PrvState Resp holds)
    (hypotheses : HypothesesProved evidence.hypotheses)
    (compiled : evidence.compiled = subject.compiled)
    (target : HEq (SoundnessTarget.retained (F := F) (G := G) evidence.target) subject.target) :
    request.meaning := by
  apply knowledgeEndpoint request
  apply ReplayClass.ofEvidence subject request.target evidence hypotheses compiled
  cases subject with
  | mk reference stageMatched subjectCompiled subjectTarget version registry registered sites unique nativeUnique lowering =>
    dsimp only at compiled target request ⊢
    cases compiled
    exact heq_of_eq (SoundnessTarget.retained.inj ((eq_of_heq target).trans request.selected))

end
end ZkcSecurity.Claims
