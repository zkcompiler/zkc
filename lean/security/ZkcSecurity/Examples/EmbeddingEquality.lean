module

public import ZkcExamples.Construction.EmbeddingEqualityBinding
public import ZkcSecurity.Endpoint.DomainCompiled
public import ZkcSecurity.Endpoint.DomainSafety
public import ZkcSecurity.Domains.KoalaBearModel
public import Zkc.Source.Structured.DomainContract
public import ZkcSecurity.Endpoint.DomainExecutionProjection

@[expose] public section

/-! The mixed-domain compiled-ideal equality endpoint. All carriers below are
the actual KoalaBear base and degree-eight binomial quotient realization.
The verifier binding is an equation about the actual admitted export, including
arbitrary incoming messages. Canonical receipt association is a separate gate. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option smartUnfolding true

noncomputable section

namespace ZkcSecurity.Examples.EmbeddingEquality
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Domains.KoalaBearModel (model baseIdentity octicIdentity)
open ZkcExamples.Construction.EmbeddingEqualityBinding

set_option backward.isDefEq.respectTransparency false

abbrev Base := model.Field baseIdentity
abbrev Octic := model.Field octicIdentity

local instance : Field Base := ZkcSecurity.Domains.KoalaBearModel.laws.fieldInstance baseIdentity (by decide)
local instance : Field Octic := ZkcSecurity.Domains.KoalaBearModel.laws.fieldInstance octicIdentity (by decide)
local instance : DecidableEq Base := model.fieldDecEq baseIdentity
local instance : DecidableEq Octic := model.fieldDecEq octicIdentity

def embedBase (value : Base) : Octic := model.embed octicIdentity baseIdentity value

def artifacts : Endpoint.Domain.Artifacts := ⟨snapshot, artifact, [.field baseIdentity, .field baseIdentity]⟩

def checked : Endpoint.Domain.Compiled artifacts :=
  ⟨imported, compiled, selection, selected, selection_checked, public_shape, source_occurrences⟩

abbrev Statement := artifacts.Statement model
abbrev Payload := Construction.Domain.Payload model.toCarriers
abbrev Event := Construction.Domain.Event model.toCarriers
abbrev History := Construction.Domain.History model.toCarriers
abbrev Proof := Construction.Domain.Proof model.toCarriers

def statement (a b : Base) : Statement := .cons a (.cons b .nil)

/-- The request fixes exactly two public base scalars; there is no truth or
honest-message premise on a soundness input. -/
theorem statement_shape (input : Statement) : ∃ a b, input = statement a b := by
  cases input with
  | cons a rest =>
    cases rest with
    | cons b rest =>
      cases rest
      exact ⟨a, b, rfl⟩

def target (a b : Base) : Prop :=
  formula.invokeRelationOn model (.cons a (.cons b .nil)) = .done (.cons true .nil)

theorem target_iff (a b : Base) : target a b ↔ a = b := by
  change (PIR.Process.done (I := closedInterface)
    (.cons (decide (a = b)) .nil : Values model.Value [.boolean]) =
      .done (.cons true .nil)) ↔ a = b
  simp

def decision (a b : Base) (u c : Octic) : Bool :=
  decide (u + c = embedBase a + c) &&
    decide (u + c = embedBase b + c)

/-- Both checks are essential, and u is the arbitrary malicious reply. -/
theorem decision_sound (a b : Base) (u c : Octic) (accepted : decision a b u c = true) :
    a = b := by
  obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp accepted
  have ha := of_decide_eq_true left
  have hb := of_decide_eq_true right
  exact ZkcSecurity.Domains.KoalaBearModel.embed_injective
    (add_right_cancel (ha.symm.trans hb))

def messageSite : String := "label_6d657373616765_0"
def challengeSite : String := "label_6368616c6c656e6765"
def deliverySite : String := "label_64656c6976657279_0"

/-- A readable open process. Its receive continuation quantifies every octic
value; no equality to the honest producer expression is assumed. -/
def verifierView (a b : Base) : PIR.Process (Construction.Domain.Actions model.toCarriers) (Option Bool) :=
  .call (.receive (.field octicIdentity) messageSite context.producer) fun u =>
    .call (.query challengeSite octicIdentity (.cons 0 .nil)) fun c =>
      .call (.send (ty := .field octicIdentity) deliverySite context.producer c) fun _ =>
        .done (some (decision a b u c))

def verifier {m : Type → Type} [Monad m]
    (query : History → (event : Event) → m (Construction.Domain.Raw event)) (a b : Base)
    (initial : History) (proof : Proof) :=
  checked.verifier model query (statement a b) initial proof

theorem encode_statement (a b : Base) :
    Construction.Domain.encodeValues (statement a b) = some
      [.data (.field baseIdentity a), .data (.field baseIdentity b)] := rfl

theorem embedding_call (a : Base) :
    Construction.Domain.callHelper model imported.program "s7h6578616d706c655h656d626564"
      [.data (.field "koala-bear.ext8-binomial3")] [.data (.field "koala-bear" a)] =
      .returned [.data (.field "koala-bear.ext8-binomial3" (embedBase a))] := by
  rfl

theorem addition_calculation (x y : Octic) :
    Construction.Domain.calculate model (.fieldAdd "koala-bear.ext8-binomial3")
      [.data (.field "koala-bear.ext8-binomial3" x), .data (.field "koala-bear.ext8-binomial3" y)] =
      .returned [.data (.field "koala-bear.ext8-binomial3" (x + y))] := rfl

theorem equality_calculation (x y : Octic) :
    Construction.Domain.calculate model (.fieldEqual "koala-bear.ext8-binomial3")
      [.data (.field "koala-bear.ext8-binomial3" x), .data (.field "koala-bear.ext8-binomial3" y)] =
      .returned [.data (.boolean (decide (x = y)))] := rfl

theorem conjunction_calculation (x y : Bool) :
    Construction.Domain.calculate model .booleanAnd [.data (.boolean x), .data (.boolean y)] =
      .returned [.data (.boolean (x && y))] := rfl

set_option maxHeartbeats 2000000 in
/-- Full interpreted compiled-artifact equality, for every monad, oracle,
initial transcript and proof (including malformed and unread payloads). -/
theorem compiled_verifier_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (query : History → (event : Event) → m (Construction.Domain.Raw event)) (a b : Base)
    (initial : History) (proof : Proof) :
    verifier query a b initial proof =
      Construction.Domain.transform context query (verifierView a b) initial proof := by
  unfold verifier
  rw [Endpoint.Domain.Compiled.verifier_readExecution, encode_statement]
  dsimp only
  cases proof with
  | nil =>
    change (fun (result : PIR.Outcome (Construction.Domain.Result model.toCarriers) × Proof) =>
      (Zkc.Transcript.mapOutcome checked.acceptance result.1, result.2)) <$>
      pure (.stopped .refused, []) = pure (.stopped .refused, [])
    simp only [map_pure]
    rfl
  | cons payload unread =>
    cases decoded : payload.value (.field octicIdentity) with
    | none =>
      change (fun (result : PIR.Outcome (Construction.Domain.Result model.toCarriers) × Proof) =>
        (Zkc.Transcript.mapOutcome checked.acceptance result.1, result.2)) <$>
        Endpoint.Domain.readExecution query
          (.call (.receive (.field octicIdentity) messageSite messageSite "role00000000") _)
          (payload :: unread) = _
      simp only [Endpoint.Domain.readExecution, decoded]
      simp only [map_pure]
      change (pure (PIR.Outcome.stopped (A := Option Bool) .refused, payload :: unread) : m _) = _
      simp [Construction.Domain.transform, Zkc.Transcript.transform, verifierView,
        Construction.Domain.interface, Construction.Domain.receivedValue, decoded]
    | some u =>
      have payloadEq := Construction.Domain.Payload.ofValue_value decoded
      simp only [Construction.Domain.Payload.ofValue, Option.some.injEq] at payloadEq
      subst payload
      change (fun (result : PIR.Outcome (Construction.Domain.Result model.toCarriers) × Proof) =>
        (Zkc.Transcript.mapOutcome checked.acceptance result.1, result.2)) <$>
        (query (initial ++ [.message (context.message messageSite context.producer context.validator)
          (.field octicIdentity u)]) (.challenge (context.query challengeSite (.draw octicIdentity)))
          >>= _) =
        (query (initial ++ [.message (context.message messageSite context.producer context.validator)
          (.field octicIdentity u)]) (.challenge (context.query challengeSite (.draw octicIdentity)))
          >>= fun c => pure (.returned (some (decision a b u c)), unread))
      rw [map_bind]
      congr 1
      funext c
      have sourceEntry : snapshot.entry = "s7h6578616d706c6517h456d62656464696e67457175616c697479" := rfl
      simp [Construction.Domain.evaluate, Construction.Domain.step,
        Construction.Domain.read, Construction.Domain.sortsMatch,
        Construction.Domain.Value.sort, Construction.Domain.Payload.ty,
        Construction.Domain.templateOrigin, Construction.Domain.atCoordinates,
        Template.origin, Template.qualify, Template.repeats, Template.applicationPrefix,
        qualifyProtocolSite, checked, artifacts, selection,
        sourceEntry, Origin.message, baseIdentity, octicIdentity,
        ZkcExamples.Construction.EmbeddingEqualityParticipant.participant,
        addition_calculation, embedding_call, equality_calculation, conjunction_calculation,
        Endpoint.Domain.readExecution, PIR.Process.bind,
        Endpoint.Domain.Compiled.acceptance, Zkc.Transcript.mapOutcome, decision]

end ZkcSecurity.Examples.EmbeddingEquality
