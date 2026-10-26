module

public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Construction.Generated.SmallSumcheckPair
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates
public import ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingLoop
public import ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerReduce
public import Zkc.Source.Structured.BodyBindings

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

abbrev program := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported.program
abbrev validatorArtifact := ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant
abbrev producerArtifact := ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant
abbrev context : Zkc.Construction.Context := ({ toContextIdentity := { entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",                          roles := ["role00000000", "role00000001"],                          producer := 0,                          validator := 1 },   profile := Zkc.Construction.Profile.fiatShamir                { service := 3,                  contract := "random.bls12-381.fr/0",                  request := some { method := "draw",                               operands := [],                               sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" },                  suite := "merlin3.bls12-381.fr64be/0",                  draws := [("apply_18_label_726564756365_label_6368616c6c656e6765",                             "apply_18_label_726564756365_label_64656c6976657279_0")] } })
theorem context_checked : exportContext program.snapshot validatorArtifact = some context := by decide +kernel
theorem policy_checked : producerArtifact.policy = validatorArtifact.policy := by decide +kernel

abbrev occurrence0 : Occurrence := ⟨context.entry, "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726564756365"⟩
theorem occurrence0_decimal : protocolSiteDecimal "label_726564756365".utf8ByteSize = "18" := by decide +kernel
theorem occurrence0_low_valid : SourceOccurrences.valid program.snapshot context occurrence0.low = true := by decide +kernel
theorem occurrence0_high_valid : SourceOccurrences.valid program.snapshot context occurrence0.high = true := by decide +kernel
theorem occurrence0_draw_valid : SourceOccurrences.valid program.snapshot context occurrence0.draw = true := by decide +kernel
theorem occurrence0_delivery_valid : SourceOccurrences.valid program.snapshot context occurrence0.delivery = true := by decide +kernel
theorem occurrence0_delivery_checked : SourceDelivery.checked program.snapshot context occurrence0.draw occurrence0.delivery = true := by decide +kernel
theorem occurrence0_query : occurrence0.draw = ({ entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",   steps := [{ kind := "apply",               protocol := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",               site := "label_726564756365" },             { kind := "repeat",               protocol := "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5",               site := "s15" }],   event := ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765",             "input_5", "random.bls12-381.fr/0", "draw", "role00000001"] }) := by kernel_rfl
theorem occurrence0_messages : occurrence0.messages = ([{ entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",    steps := [{ kind := "apply",                protocol := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",                site := "label_726564756365" },              { kind := "repeat",                protocol := "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5",                site := "s15" }],    event := ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0",              "label_726f756e64_0", "role00000000", "role00000001"] },  { entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",    steps := [{ kind := "apply",                protocol := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",                site := "label_726564756365" },              { kind := "repeat",                protocol := "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5",                site := "s15" }],    event := ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1",              "label_726f756e64_1", "role00000000", "role00000001"] },  { entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",    steps := [{ kind := "apply",                protocol := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071",                site := "label_726564756365" },              { kind := "repeat",                protocol := "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5",                site := "s15" }],    event := ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5",              "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"] }]) := by kernel_rfl
theorem occurrence0_origins :
    ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.OriginLaws context occurrence0 := by
  constructor <;> intro index <;> kernel_rfl


abbrev routing (handle : Nat) : Original.Routing :=
  ⟨program.snapshot, context, .validator, handle, occurrence0.messages, [occurrence0.draw], [⟨occurrence0.draw, occurrence0.delivery⟩], []⟩

theorem occurrence0_routes (handle index : Nat) :
    Routes (routing handle) occurrence0.protocol
      [⟨qualifyProtocolSite occurrence0.protocol.applicationPrefix "s15", index⟩]
      handle (occurrence0.origins context index) := by
  constructor
  · rfl
  all_goals
    simp only [Original.Routing.message, Original.Routing.draw, Occurrence.messages,
      Occurrence.origins, OccurrenceResolution.resolve, List.filter_cons, List.filter_nil]
    simp only [OccurrenceResolution.matchesOccurrence, occurrence0_low_valid, occurrence0_high_valid, occurrence0_draw_valid, occurrence0_delivery_valid]
    simp [occurrence0_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Context.service, Context.request, Context.contract, Context.replacement?, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw, Occurrence.round_label, Occurrence.challenge_label, Occurrence.delivery_label]

theorem helper_bodies : ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.Bodies program := by bind_structured_bodies
theorem verifier_bodies : SumcheckVerifierHelpers.Bodies program.payload.definitions :=
  ⟨helper_bodies.sumcheck.empty, helper_bodies.sumcheck.append, helper_bodies.sumcheck.width, helper_bodies.sumcheck.«variables», helper_bodies.sumcheck.values⟩

namespace ValidatorCall0
abbrev occurrence := occurrence0
def outputs : VerifierOutputs context.suite := ({ point := { index := 26 }, scalar := { index := 31 }, transcript := { index := 25 } })
theorem outputs_derived : ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.verifierOutputs context.suite validatorArtifact 1 = .ok outputs := by decide +kernel
theorem output_references : outputs.references = [26, 31, 25] := by kernel_rfl
theorem capture_size : ((validatorArtifact.instructions.take 1).foldl (fun size instruction => size + instruction.results.length) validatorArtifact.inputs.length) = 5 := by kernel_rfl
theorem loop_operands : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).operands = [2, 4, 1, 3] := by kernel_rfl
theorem loop_operation : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).operation = (Zkc.Construction.Operation.loop "apply_18_label_726564756365_s15" 2 [26, 31, 25]) := by kernel_rfl
abbrev routes := occurrence0_routes
theorem body_syntax : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).body =
    ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorInstructions context occurrence 5 := by kernel_rfl
theorem loop_sorts : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).results = VerifierOutputs.sorts context.suite := by kernel_rfl
theorem loop_site : "apply_18_label_726564756365_s15" = qualifyProtocolSite occurrence.protocol.applicationPrefix "s15" := by kernel_rfl
theorem body_instance : ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep1Body (ringModel F G) program context =
    ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorBody (ringModel F G) program context occurrence 5 := by kernel_rfl
theorem output_instance : outputs = ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.verifierOutputs context 5 := by kernel_rfl
noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 5) (index handle : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (VerifierReturns (F := F) (G := G) context outputs
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩])
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle)
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol
          (occurrence.protocol.roles 1)
          (.cons (some index) ((SumcheckVerifierLaws.embedV (some point, some scalar)).append
            (.cons (some handle) .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩], history⟩)
      (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep1Body (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" point),
          .data (.field "bls12-381.fr" scalar), .transcript context.suite history])) := by
  rw [body_instance, output_instance]
  exact ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorRound
    program helper_bodies.sumcheck verifier_bodies (routing handle) context rfl occurrence
    (by decide +kernel) occurrence0_origins 5 captured size index handle point scalar history
    (routes handle index)

def callback (handle : Nat) : VerifierCallback program (routing handle) occurrence context outputs 5 handle
  (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep1Body (ringModel F G) program context) :=
  ⟨fun captured size index point scalar history => round captured size index handle point scalar history⟩
end ValidatorCall0

namespace ProducerCall0
abbrev occurrence := occurrence0
def outputs : ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.Outputs context.suite := ({ raw := { index := 34 },   dimension := { index := 35 },   width := { index := 36 },   point := { index := 37 },   transcript := { index := 33 } })
theorem outputs_derived : ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.producerOutputs context.suite producerArtifact 10 = .ok outputs := by decide +kernel
theorem output_references : outputs.references = [34, 35, 36, 37, 33] := by kernel_rfl
theorem capture_size : ((producerArtifact.instructions.take 10).foldl (fun size instruction => size + instruction.results.length) producerArtifact.inputs.length) = 13 := by kernel_rfl
theorem loop_operands : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).operands = [1, 4, 5, 6, 12, 2] := by kernel_rfl
theorem loop_operation : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).operation = (Zkc.Construction.Operation.loop "apply_18_label_726564756365_s15" 2 [34, 35, 36, 37, 33]) := by kernel_rfl
open ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer
abbrev routing (handle : Nat) : Original.Routing := { ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.routing handle with mode := .producer }
theorem routes (handle index : Nat) :
    Routes (routing handle) occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
      (occurrence.origins context index) := by
  constructor
  · rfl
  · exact (occurrence0_routes handle index).low
  · exact (occurrence0_routes handle index).high
  · have policy :
        (!(context.draws.map Prod.fst).Nodup || !(context.draws.map Prod.snd).Nodup) = false := by
      decide +kernel
    have candidates : (([⟨occurrence0.draw, occurrence0.delivery⟩] : List Original.Delivery).filter fun candidate =>
        Original.deliveryValid program.snapshot context
          candidate.draw candidate.message &&
        candidate.message.qualify (candidate.message.event[2]?.getD "") ==
          SumcheckVerifierLaws.deliverySite occurrence.protocol &&
        (context.draws.contains
          (candidate.draw.qualify (candidate.draw.event[2]?.getD ""),
            SumcheckVerifierLaws.deliverySite occurrence.protocol))) =
        [⟨occurrence.draw, occurrence.delivery⟩] := by
      decide +kernel
    have drawSite : occurrence.draw.qualify (occurrence.draw.event[2]?.getD "") =
        SumcheckVerifierLaws.challengeSite occurrence.protocol := by decide +kernel
    simp only [Original.Routing.delivery,
      policy, Bool.false_eq_true, ↓reduceIte, candidates, drawSite]
    change ((OccurrenceResolution.resolve program.snapshot context
      (context.message (SumcheckVerifierLaws.deliverySite occurrence.protocol) 1 0)
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
      [occurrence.delivery]).bind fun message =>
      (OccurrenceResolution.resolve program.snapshot context
        (context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol)
          (.draw "bls12-381.fr"))
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.draw]).bind fun draw => some (draw, message)) = _
    have messageSingleton : OccurrenceResolution.resolve program.snapshot context
        (context.message (SumcheckVerifierLaws.deliverySite occurrence.protocol) 1 0)
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.delivery] = some (occurrence.origins context index).delivery := by
      simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence,
        occurrence0_delivery_valid]
      simp [occurrence0_decimal,
        Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite,
        SumcheckVerifierLaws.deliverySite, Occurrence.origins, Context.message,
        Context.role, Origin.message, Domain.atCoordinates]
      kernel_rfl
    have drawSingleton : OccurrenceResolution.resolve program.snapshot context
        (context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol) (.draw "bls12-381.fr"))
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.draw] = some (occurrence.origins context index).draw := by
      simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence, occurrence0_draw_valid]
      simp [occurrence0_decimal,
        Occurrence.draw, Occurrence.steps, Occurrence.protocol,
        Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite,
        SumcheckVerifierLaws.challengeSite, Occurrence.origins, Context.query,
        Context.role, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw]
      kernel_rfl
    rw [messageSingleton, Option.bind_some, drawSingleton]
    rfl
  · exact Original.Routing.draw_request (occurrence0_routes handle index).draw

theorem body_syntax : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).body =
    ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerInstructions context occurrence 13 := by kernel_rfl
theorem loop_sorts : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).results = ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.Outputs.sorts context.suite := by kernel_rfl
theorem loop_site : "apply_18_label_726564756365_s15" = qualifyProtocolSite occurrence.protocol.applicationPrefix "s15" := by kernel_rfl
theorem body_instance : ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep10Body (ringModel F G) program context =
    ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerBody (ringModel F G) program context occurrence 13 := by kernel_rfl
theorem output_instance : outputs = ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerOutputs context 13 := by kernel_rfl
noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 13) (index handle : Nat)
    (raw : List F) (dimension width : Nat) (point : List F)
    (shape : PrimitiveLibrary.HasShape raw dimension width)
    (bounded : raw.length < indexLimit) (positive : 0 < dimension)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (RoundReturns (F := F) (G := G) context outputs
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        raw dimension width point)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle)
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol
          (occurrence.protocol.roles 0)
          (.cons (some index) ((SumcheckProverLaws.embedP (raw, dimension, width, point)).append
            (.cons none .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩], history⟩)
      (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep10Body (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" raw),
          .data (.index dimension), .data (.index width),
          .data (.vector "bls12-381.fr" point), .transcript context.suite history])) := by
  rw [body_instance, output_instance]
  exact ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerRound
    program helper_bodies.sumcheck (routing handle) context rfl occurrence
    (by decide +kernel) occurrence0_origins 13 captured size index raw dimension width point
    shape bounded positive history (routes handle index)

def callback (handle : Nat) : ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.ProducerCallback program (routing handle) occurrence context outputs 13 handle
  (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep10Body (ringModel F G) program context) :=
  ⟨fun captured size index raw dimension width point shape bounded positive history => round captured size index handle raw dimension width point shape bounded positive history⟩
end ProducerCall0

end ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck
