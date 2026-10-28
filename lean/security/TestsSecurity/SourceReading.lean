module

public import ZkcSecurity.FiatShamir.DomainSourceReading
public import ZkcExamples.Structured.OriginalArtifacts.TwoSums
public import Zkc.Source.KernelRfl
public import Mathlib.Data.ZMod.Basic

public section

/-! Actual TwoSums source integration, an admitted aggregate source, and exact
nominal/refusal controls. No old per-source routing witness is used by these
readings. The small aggregate is a disclosed synthetic source, not a native
compiler correspondence claim.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.SourceReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.FiatShamir
open ZkcSecurity.FiatShamir.DomainReduction

section TwoSums
open ZkcExamples.Structured.OriginalArtifacts.TwoSums
variable {F G : Type} [CommRing F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Two real component applications with arbitrary symbolic repeat count and
inputs. Source operation installation replaces all instance reading plumbing. -/
theorem twoSums_reading (left right : List F) (leftClaim rightClaim : F)
    (count handle : Nat) (history : Domain.History (uniformCarriers F G)) :
    let source := Occurrence.participant (ringModel F G) program 1
      (.cons (some left) (.cons (some right) (.cons (some leftClaim) (.cons (some rightClaim)
        (.cons (some count) (.cons (some handle) .nil))))))
    Bridge NominalDomain.interface SourceReading.Post history
      (Original.fold (routing handle) source ⟨[], history⟩)
      (DomainSourceReading.presentation (routing handle) source ⟨[], history⟩) := by
  dsimp only
  exact DomainSourceReading.reading (routing handle) _ rfl rfl _ ⟨[], history⟩

/-- The actual producer source has the same automatic endpoint projection.
This deliberately makes no producer runtime/completeness assertion. -/
theorem twoSums_producer_endpoint_reading (left right : List F) (leftClaim rightClaim : F)
    (count handle : Nat) (history : Domain.History (uniformCarriers F G)) :
    let source := Occurrence.participant (ringModel F G) program 0
      (.cons (some left) (.cons (some right) (.cons (some leftClaim) (.cons (some rightClaim)
        (.cons (some count) (.cons (some handle) .nil))))))
    Bridge NominalDomain.interface SourceReading.Post history
      (Original.fold (ProducerCall0.routing handle) source ⟨[], history⟩)
      (DomainSourceReading.presentation (ProducerCall0.routing handle) source ⟨[], history⟩) := by
  dsimp only
  exact DomainSourceReading.reading (ProducerCall0.routing handle) _ rfl rfl _ ⟨[], history⟩

end TwoSums

namespace Aggregate

@[expose] def item : Ty := .product "source-reading-record" "value"
  (.cons .boolean (.cons (.field "bls12-381.fr") .nil))
@[expose] def packet : Ty := .sequence item

@[expose] def snapshot : Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "Aggregate"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"Aggregate", .protocol, .publicDef, [packet], [packet],
    some ⟨["P", "V"], [["P"]], [["V"]]⟩, [], some (.protocol ⟨"Aggregate", []⟩),
    .block [.instruction (.exchange "P" "V") [0] [packet] [] "packet"] (.ret [0])⟩]
  contracts := [⟨"Aggregate", []⟩]
  catalogue := blsRows

@[expose] def body : Region protocolDialect [packet] [packet] :=
  .letOp (.mark "packet") .nil .nil <|
  .letOp (.exchange packet 0 1 "packet") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

@[expose] def definition : CheckedProtocol :=
  ⟨⟨"Aggregate", ["P", "V"], [packet], [packet], [[0]], [[1]]⟩,
    body.erase, body, body.elaborate_erase⟩

@[expose] def payload : UnitPayload where
  definitions := []
  protocols := [definition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := by kernel_rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

@[expose] def program : Program := ⟨snapshot, payload⟩
theorem admitted : check snapshot = .ok program := by kernel_rfl

@[expose] def context : Context := Context.fiatShamir "Aggregate" ["P", "V"] 0 1 0
  "random.bls12-381.fr/0" none "suite" []
@[expose] def message : Template := ⟨"Aggregate", [], ["message", "Aggregate", "packet", "packet", "P", "V"]⟩
@[expose] def routing (mode : Domain.Mode) : Original.Routing := ⟨snapshot, context, mode, 0, [message], [], [], []⟩

theorem route : (routing .validator).message [] "packet" 0 1 =
    some (context.message "packet" 0 1) := by decide +kernel

/-- The admitted source is interpreted at the real validator role. The returned
aggregate, optional component and full construction state are preserved. -/
theorem reading (model : DomainModel) (history : Domain.History model.toCarriers) :
    let source := Occurrence.participant model program 1 (.cons none .nil)
    Bridge NominalDomain.interface SourceReading.Post history
      (Original.fold (routing .validator) source ⟨[], history⟩)
      (DomainSourceReading.presentation (routing .validator) source ⟨[], history⟩) := by
  dsimp only
  exact DomainSourceReading.reading (routing .validator) _ rfl rfl _ ⟨[], history⟩

@[expose] def model : DomainModel := ringModel (ZMod 5) (ZMod 5)
@[expose] def value : model.Value packet := [(true, 3, ()), (false, 4, ())]
@[expose] def encoded : Domain.Payload model.toCarriers := ⟨packet, rfl, value⟩
@[expose] def origin : Origin := context.message "packet" 0 1

/-- Successful aggregate reading is non-vacuous and retains the unread suffix,
the nonempty initial history and the complete optional source return. -/
theorem readback (history : Domain.History model.toCarriers)
    (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Original.fold (routing .validator)
        (Occurrence.participant model program 1 (.cons none .nil)) ⟨[], history⟩)
      (encoded :: suffix) =
      (PIR.Outcome.returned (.cons (some value) .nil,
        (⟨[], history ++ [.message origin encoded]⟩ : Original.State model.toCarriers)), suffix) := by
  kernel_rfl

/-- Wrong proof sorts and exhaustion keep the existing refusal and unread
suffix. In particular they do not fabricate an aggregate observation. -/
theorem malformed (history : Domain.History model.toCarriers)
    (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Original.fold (routing .validator)
        (Occurrence.participant model program 1 (.cons none .nil)) ⟨[], history⟩)
      (.boolean true :: suffix) = (.stopped .refused, .boolean true :: suffix) := by
  kernel_rfl

theorem exhausted (history : Domain.History model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Original.fold (routing .validator)
        (Occurrence.participant model program 1 (.cons none .nil)) ⟨[], history⟩)
      [] = (.stopped .refused, []) := by
  kernel_rfl

/-- A reading does not certify route coverage: deleting a required route is
faithfully refused by the actual fold, before consuming a proof message. -/
theorem missing_route (history : Domain.History model.toCarriers) :
    Original.fold { routing .validator with messages := [] }
      (Occurrence.participant model program 1 (.cons none .nil)) ⟨[], history⟩ = .halt .refused := by
  kernel_rfl

end Aggregate

namespace ComponentLoops
variable {carriers : Carriers}

@[expose] def actual (origin : Origin) (payload : Domain.Payload carriers) (state : Original.State carriers) :=
  (Original.record state origin payload).bind fun result => .done result.2

@[expose] def presented (origin : Origin) (payload : Domain.Payload carriers) (state : Original.State carriers) :=
  (DomainSourceReading.record state origin payload).bind fun result => .done result.2

theorem step (origin : Origin) (payload : Domain.Payload carriers)
    (history : Domain.History carriers) (state : Original.State carriers) (agrees : state.history = history) :
    Bridge NominalDomain.interface (fun reached state => state.history = reached) history
      (actual origin payload state) (presented origin payload state) := by
  subst history
  apply (DomainSourceReading.record_reading state origin payload).bind
  intro reached final holds
  exact .done _ _ holds

/-- Installed component bridges compose over two symbolic loop bounds, with
the exact reached history passed from each inner loop to the next outer step. -/
theorem nested (origin : Origin) (payload : Domain.Payload carriers)
    (outer inner : Nat) (state : Original.State carriers) :
    Bridge NominalDomain.interface (fun reached state => state.history = reached) state.history
      (PIR.repeatN outer (PIR.repeatN inner (actual origin payload)) state)
      (PIR.repeatN outer (PIR.repeatN inner (presented origin payload)) state) := by
  apply Bridge.repeatN (fun reached _ (state : Original.State carriers) => state.history = reached)
  · intro reached _ state holds
    apply Bridge.repeatN (fun reached _ (state : Original.State carriers) => state.history = reached)
    · intro reached _ state holds
      exact step origin payload reached state holds
    · exact holds
  · rfl

end ComponentLoops

/-- Operation-level reading retains the complete return, even when an
acceptance Boolean alone would not distinguish the values. -/
theorem changed_return (history : Domain.History Aggregate.model.toCarriers) :
    ¬ Bridge NominalDomain.interface SourceReading.Post history
      (.done ((true, (0 : Nat)), (⟨[], history⟩ : Original.State Aggregate.model.toCarriers)))
      (.done ((true, (1 : Nat)), (⟨[], history⟩ : Original.State Aggregate.model.toCarriers))) := by
  intro bridge
  cases bridge.reading

theorem changed_frames (history : Domain.History Aggregate.model.toCarriers) :
    ¬ Bridge NominalDomain.interface SourceReading.Post history
      (.done (true, (⟨[], history⟩ : Original.State Aggregate.model.toCarriers)))
      (.done (true, (⟨[⟨"invented", 0⟩], history⟩ : Original.State Aggregate.model.toCarriers))) := by
  intro bridge
  cases bridge.reading

/-- A failed close keeps the source refusal instead of silently dropping an
unmatched frame in the nominal presentation. -/
example (history : Domain.History Aggregate.model.toCarriers) :
    DomainSourceReading.presentation (Aggregate.routing .validator)
      (.call (.leave ⟨"missing", 0⟩) (fun _ => .done true)) ⟨[], history⟩ = .halt .refused := by
  kernel_rfl

/-- Equal host carriers cannot authorize a different nominal field. -/
example (value : Bool) (origin : Origin) :
    NominalDomain.received (carriers := uniformCarriers Bool Unit) (.field "left") origin
      (.message origin (.field "right" value)) = none := by
  apply NominalDomain.received_wrong_type
  change Ty.field "right" ≠ Ty.field "left"
  decide

/-- Ordered aggregate fields and constructor identity remain part of decoding. -/
example : NominalDomain.received Aggregate.packet Aggregate.origin
    (.message Aggregate.origin
      (⟨.sequence (.product "source-reading-record" "other"
        (.cons .boolean (.cons (.field "bls12-381.fr") .nil))), rfl, []⟩ :
        Domain.Payload Aggregate.model.toCarriers)) = none := by
  apply NominalDomain.received_wrong_type
  decide

/-- The current endpoint relation has no private-service case. Such an adapter
must use an appropriate private-service consumer, rather than public absorption. -/
theorem private_requires_adapter {carriers : Carriers} {I : PIR.Signature} {A : Type}
    (absorb : Zkc.Transcript.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
    (Post : Domain.History carriers → A → Prop) (history : Domain.History carriers)
    (port : ServicePort) (origin : Origin)
    (next : Domain.Raw (.challenge origin : Domain.Event carriers) → PIR.Process (Domain.effects carriers) A)
    (presented : PIR.Process I A) :
    ¬ Bridge absorb Post history (.call (.localService port origin) next) presented := by
  intro bridge
  cases bridge.coherent

#print axioms twoSums_reading
#print axioms twoSums_producer_endpoint_reading
#print axioms Aggregate.reading
#print axioms Aggregate.readback
#print axioms ComponentLoops.nested
#print axioms DomainSourceReading.reading
#print axioms SourceReading.Interpretation.reading
#print axioms Bridge.repeatN

end TestsSecurity.SourceReading
