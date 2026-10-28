module

public import TestsSecurity.RootConnectionPublicDraw
public import TestsSecurity.RootConnectionControls
public import ZkcSecurity.FiatShamir.RootConnectionLossless

@[expose] public section

/-! End-to-end lossless installation on the admitted Aggregate/public-draw roots.
These are the existing disclosed finite constructed fixtures, not native compiler
or retained-claim receipts. Arbitrary histories, recursive values, oracle replies
and unread suffixes are preserved by the actual full-result reader. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.RootConnectionLossless
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir
open TestsSecurity.SourceReading

/-- Both source admission and finite data support are independently checked. -/
theorem aggregate_data : PublicSourceSupport.check Aggregate.program = true := by kernel_rfl
theorem draw_data : PublicSourceSupport.check RootConnectionPublicDraw.program = true := by kernel_rfl

/-- The check includes captured components and repeat callbacks, with no bound
unrolling and no restriction on the actual TwoSums arguments or private handles. -/
theorem twoSums_data : PublicSourceSupport.check ZkcExamples.Structured.OriginalArtifacts.TwoSums.program = true := by
  kernel_rfl

theorem twoSums_supported (model : DomainModel) (role : Nat)
    (inputs : Values (Component model.Value) ZkcExamples.Structured.OriginalArtifacts.TwoSums.program.payload.entry.inputs) :
    OperationSupport DomainSourceReading.DataOperation
      (Occurrence.participant model ZkcExamples.Structured.OriginalArtifacts.TwoSums.program role inputs) :=
  PublicSourceSupport.participant _ twoSums_data model role inputs

def aggregate (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  RootConnection.losslessPresentation RootConnectionFixture.root aggregate_data _ rfl rfl model physical

def draw (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  RootConnection.losslessPresentation RootConnectionPublicDraw.root draw_data _ rfl rfl model physical

def producerDraw (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  RootConnection.losslessPresentation RootConnectionPublicDraw.producerRoot draw_data _ rfl rfl model physical

/-- The adapter has the full Domain.Result return type, including the physical
SSA environment, rather than a chosen encoding from source returns. -/
theorem aggregate_full_read (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m]
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → m (Domain.Raw event))
    (proof : Domain.Proof model.toCarriers) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Domain.participant model Aggregate.program Aggregate.context RootConnectionFixture.artifact physical) proof =
      transform NominalDomain.interface oracle (aggregate model physical)
        (RootConnectionFixture.root.inputs.initial physical).history proof :=
  RootConnection.losslessRead RootConnectionFixture.root aggregate_data _ rfl rfl model physical oracle proof

theorem draw_full_read (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m]
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → m (Domain.Raw event))
    (proof : Domain.Proof model.toCarriers) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Domain.participant model RootConnectionPublicDraw.program RootConnectionPublicDraw.context
        RootConnectionPublicDraw.artifact physical) proof =
      transform NominalDomain.interface oracle (draw model physical)
        (RootConnectionPublicDraw.root.inputs.initial physical).history proof :=
  RootConnection.losslessRead RootConnectionPublicDraw.root draw_data _ rfl rfl model physical oracle proof

theorem producer_draw_full_read (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m]
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → m (Domain.Raw event))
    (proof : Domain.Proof model.toCarriers) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Domain.participant model RootConnectionPublicDraw.program RootConnectionPublicDraw.context
        RootConnectionPublicDraw.producerArtifact physical) proof =
      transform NominalDomain.interface oracle (producerDraw model physical)
        (RootConnectionPublicDraw.producerRoot.inputs.initial physical).history proof :=
  RootConnection.losslessRead RootConnectionPublicDraw.producerRoot draw_data _ rfl rfl model physical oracle proof

/-- Successful recursive messages retain both visible outputs and every cell
of the actual physical environment, for arbitrary values and unread suffixes. -/
theorem aggregate_full_return (model : DomainModel) (value : model.Value Aggregate.packet)
    (history : Domain.History model.toCarriers) (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → Id (Domain.Raw event)) :
    let payload : Domain.Payload model.toCarriers := ⟨Aggregate.packet, rfl, value⟩
    let reached := history ++ [.message Aggregate.origin payload]
    transform NominalDomain.interface oracle (aggregate model [.transcript "suite" history]) history (payload :: suffix) =
      (.returned ⟨[.data payload, .transcript "suite" reached],
        [.transcript "suite" history, .indices [], .data payload, .transcript "suite" reached]⟩, suffix) := by
  dsimp only
  exact (aggregate_full_read model [.transcript "suite" history] oracle
    (⟨Aggregate.packet, rfl, value⟩ :: suffix)).symm.trans (by kernel_rfl)

/-- The public-draw reconstruction retains the arbitrary oracle reply as a
non-Boolean residual and keeps the query/delivery histories in the full frame. -/
theorem draw_full_return (model : DomainModel) (history : Domain.History model.toCarriers)
    (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → Id (Domain.Raw event)) :
    let challenge := RootConnectionPublicDraw.context.query "challenge" (.draw "bls12-381.fr")
    let answer := oracle history (.challenge challenge)
    let queried := history ++ [.challenge challenge]
    let reached := queried ++ [.message (RootConnectionPublicDraw.context.message "delivery" 1 0)
      (.field "bls12-381.fr" answer)]
    transform NominalDomain.interface oracle (draw model [.transcript "suite" history]) history suffix =
      (.returned ⟨[.data (.boolean true), .data (.field "bls12-381.fr" answer), .transcript "suite" reached],
        [.transcript "suite" history, .indices [], .data (.field "bls12-381.fr" answer),
          .transcript "suite" queried, .transcript "suite" reached, .data (.boolean true)]⟩, suffix) := by
  dsimp only
  exact (draw_full_read model [.transcript "suite" history] oracle suffix).symm.trans (by kernel_rfl)

/-- Malformed messages retain their entire head and suffix under the new
reconstruction, exactly as under the actual endpoint. -/
theorem malformed_receive (model : DomainModel) (history : Domain.History model.toCarriers)
    (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → Id (Domain.Raw event)) :
    transform NominalDomain.interface oracle (aggregate model [.transcript "suite" history]) history
      (.boolean true :: suffix) = (.stopped .refused, .boolean true :: suffix) := by
  exact (aggregate_full_read model [.transcript "suite" history] oracle (.boolean true :: suffix)).symm.trans
    (RootConnectionFixture.wrong_message_type model history suffix oracle)

theorem wrong_nominal_receive (model : DomainModel) (history : Domain.History model.toCarriers)
    (value : model.Value RootConnectionFixture.otherPacket) (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → Id (Domain.Raw event)) :
    transform NominalDomain.interface oracle (aggregate model [.transcript "suite" history]) history
      (⟨RootConnectionFixture.otherPacket, rfl, value⟩ :: suffix) =
      (.stopped .refused, ⟨RootConnectionFixture.otherPacket, rfl, value⟩ :: suffix) := by
  exact (aggregate_full_read model [.transcript "suite" history] oracle
    (⟨RootConnectionFixture.otherPacket, rfl, value⟩ :: suffix)).symm.trans
    (RootConnectionFixture.wrong_nominal_message model value history suffix oracle)

/-- A malformed physical row stops without creating any return or consuming
proof data; operation-local authority does not repair input decoding. -/
theorem malformed_input (model : DomainModel) (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → Id (Domain.Raw event)) :
    transform NominalDomain.interface oracle (aggregate model []) [] suffix = (.stopped .refused, suffix) := by
  exact (aggregate_full_read model [] oracle suffix).symm.trans
    (RootConnectionFixture.malformed_input model suffix oracle)

/-- Actual Aggregate receives and deliveries make no charged query. -/
theorem aggregate_cost (model : DomainModel) (history : Domain.History model.toCarriers)
    (charge : Domain.History model.toCarriers → Domain.Event model.toCarriers → ENNReal) :
    Typed.ChargedCostBound NominalDomain.interface charge (aggregate model [.transcript "suite" history]) history 0 := by
  apply (RootConnection.losslessAlignment RootConnectionFixture.root aggregate_data _ rfl rfl model
    [.transcript "suite" history]).cost
  change ∀ message value, NominalDomain.received Aggregate.packet Aggregate.origin
    (.message Aggregate.origin message) = some value → True
  intro _ _ _
  trivial

/-- The genuine public draw charges once at its exact initial history/key.
All replies, the delivery observation and non-Boolean residual are retained. -/
theorem draw_cost (model : DomainModel) (history : Domain.History model.toCarriers)
    (charge : Domain.History model.toCarriers → Domain.Event model.toCarriers → ENNReal) :
    Typed.ChargedCostBound NominalDomain.interface charge (draw model [.transcript "suite" history]) history
      (charge history (.challenge (RootConnectionPublicDraw.context.query "challenge" (.draw "bls12-381.fr")))) := by
  apply (RootConnection.losslessAlignment RootConnectionPublicDraw.root draw_data _ rfl rfl model
    [.transcript "suite" history]).cost
  change ∃ remaining, charge history (.challenge (RootConnectionPublicDraw.context.query "challenge" (.draw "bls12-381.fr"))) +
      remaining ≤ charge history (.challenge (RootConnectionPublicDraw.context.query "challenge" (.draw "bls12-381.fr"))) ∧
      ∀ _answer : model.Field "bls12-381.fr", True
  exact ⟨0, by simp, fun _ => trivial⟩

/-- Existing abstract escape derivations transfer on this actual root. The
caller must prove each local exceptional set and its own terminal property. -/
theorem draw_derivation (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    (escape : EscapeJudgment (Domain.Event model.toCarriers) Domain.Raw)
    (Post : Domain.History model.toCarriers →
      (Values (Component model.Value) RootConnectionPublicDraw.program.payload.entry.outputs × Original.State model.toCarriers) → Prop)
    (Next : Domain.History model.toCarriers → Domain.Result model.toCarriers → Prop)
    (proof : Zkc.Obligations.Derivation NominalDomain.interface escape Post
      (RootConnectionPublicDraw.root.inputs.initial physical).history
      (RootConnection.publicPresentation RootConnectionPublicDraw.root model physical))
    (terminal : ∀ reached source target,
      Original.CompleteReturns RootConnectionPublicDraw.program.payload.entry.signature RootConnectionPublicDraw.context 1
        RootConnectionPublicDraw.artifact source target → Post reached source → Next reached target) :
    Nonempty (Zkc.Obligations.Derivation NominalDomain.interface escape Next
      (RootConnectionPublicDraw.root.inputs.initial physical).history (draw model physical)) :=
  (RootConnection.losslessAlignment RootConnectionPublicDraw.root draw_data _ rfl rfl model physical).derivation proof terminal

section Claims
variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- This has precisely the existing request-owned export type. There is no
instance source equation, target reading, encoder or chosen return relation. -/
example (subject : ZkcSecurity.Claims.Domain.Subject model art) (routing : Original.Routing)
    (context : routing.context = subject.compiled.selection.context)
    (root : ConnectionRoot.RootCertificate subject.compiled.imported.program routing
      subject.compiled.selection.context.validator art.participant)
    (data : PublicSourceSupport.check subject.compiled.imported.program = true)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = [])
    (schedule : ZkcSecurity.Claims.Domain.ChargeSchedule subject) (queries : Nat) (budget : ENNReal)
    (rejects : let installation := RootConnection.claimsInstallation subject routing context root replacement profile noLocal
      ∀ statement, subject.FalseStatement statement → ∀ initial,
        Zkc.Obligations.Derivation installation.absorb
          (ZkcSecurity.Obligations.boundedEscape (schedule.charge queries))
          (fun _ result => installation.acceptance result ≠ some true) initial (installation.presented statement initial))
    (costs : let installation := RootConnection.claimsInstallation subject routing context root replacement profile noLocal
      ∀ statement initial, Typed.ChargedCostBound installation.absorb (schedule.charge queries)
        (installation.presented statement initial) initial budget) :
    ZkcSecurity.Claims.Domain.ChargedExport subject schedule queries budget :=
  RootConnection.losslessChargedExport subject routing context root data replacement profile noLocal
    schedule queries budget rejects costs

end Claims

#print axioms aggregate_data
#print axioms draw_data
#print axioms twoSums_supported
#print axioms aggregate_full_return
#print axioms draw_full_return
#print axioms aggregate_full_read
#print axioms draw_full_read
#print axioms producer_draw_full_read
#print axioms malformed_receive
#print axioms wrong_nominal_receive
#print axioms malformed_input
#print axioms aggregate_cost
#print axioms draw_cost
#print axioms draw_derivation
#print axioms RootConnection.publicLossless
#print axioms RootConnection.losslessBridge
#print axioms RootConnection.claimsLossless
#print axioms RootConnection.losslessChargedExport

end TestsSecurity.RootConnectionLossless
