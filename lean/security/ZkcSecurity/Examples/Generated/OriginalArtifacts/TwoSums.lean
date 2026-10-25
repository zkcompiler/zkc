module

public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
public import ZkcExamples.Construction.Generated.TwoSumsPair
public import ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator
public import ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer
public import ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs
public import ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates
public import ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates
public import ZkcSecurity.Realizations.Sumcheck.ArtifactBindingLoop
public import ZkcSecurity.Realizations.Sumcheck.OriginalProducerReduce
public import Zkc.Source.Structured.BodyBindings

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

abbrev program := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported.program
abbrev validatorArtifact := ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant
abbrev producerArtifact := ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant
abbrev context : Zkc.Construction.Context := ({ entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",   roles := ["role00000000", "role00000001"],   producer := 0,   validator := 1,   service := 5,   contract := "random.bls12-381.fr/0",   request := some { method := "draw", operands := [], sort := Zkc.Source.Structured.Ty.field "bls12-381.fr" },   suite := "merlin3.bls12-381.fr64be/0",   draws := [("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"),             ("apply_16_label_7269676874_label_6368616c6c656e6765",              "apply_16_label_7269676874_label_64656c6976657279_0")] })
theorem context_checked : exportContext program.snapshot validatorArtifact = some context := by decide +kernel
theorem policy_checked : producerArtifact.policy = validatorArtifact.policy := by decide +kernel

abbrev occurrence0 : Occurrence := ⟨context.entry, "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6c656674"⟩
theorem occurrence0_decimal : protocolSiteDecimal "label_6c656674".utf8ByteSize = "14" := by decide +kernel
theorem occurrence0_low_valid : SourceOccurrences.valid program.snapshot context occurrence0.low = true := by decide +kernel
theorem occurrence0_high_valid : SourceOccurrences.valid program.snapshot context occurrence0.high = true := by decide +kernel
theorem occurrence0_draw_valid : SourceOccurrences.valid program.snapshot context occurrence0.draw = true := by decide +kernel
theorem occurrence0_delivery_valid : SourceOccurrences.valid program.snapshot context occurrence0.delivery = true := by decide +kernel
theorem occurrence0_delivery_checked : SourceDelivery.checked program.snapshot context occurrence0.draw occurrence0.delivery = true := by decide +kernel
theorem occurrence0_query : occurrence0.draw = ({ entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",   steps := [{ kind := "apply",               protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",               site := "label_6c656674" },             { kind := "repeat",               protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",               site := "s15" }],   event := ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765",             "input_5", "random.bls12-381.fr/0", "draw", "role00000001"] }) := by kernel_rfl
theorem occurrence0_messages : occurrence0.messages = ([{ entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",    steps := [{ kind := "apply",                protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",                site := "label_6c656674" },              { kind := "repeat",                protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",                site := "s15" }],    event := ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0",              "label_726f756e64_0", "role00000000", "role00000001"] },  { entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",    steps := [{ kind := "apply",                protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",                site := "label_6c656674" },              { kind := "repeat",                protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",                site := "s15" }],    event := ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1",              "label_726f756e64_1", "role00000000", "role00000001"] },  { entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",    steps := [{ kind := "apply",                protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",                site := "label_6c656674" },              { kind := "repeat",                protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",                site := "s15" }],    event := ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",              "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"] }]) := by kernel_rfl
abbrev occurrence1 : Occurrence := ⟨context.entry, "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_7269676874"⟩
theorem occurrence1_decimal : protocolSiteDecimal "label_7269676874".utf8ByteSize = "16" := by decide +kernel
theorem occurrence1_low_valid : SourceOccurrences.valid program.snapshot context occurrence1.low = true := by decide +kernel
theorem occurrence1_high_valid : SourceOccurrences.valid program.snapshot context occurrence1.high = true := by decide +kernel
theorem occurrence1_draw_valid : SourceOccurrences.valid program.snapshot context occurrence1.draw = true := by decide +kernel
theorem occurrence1_delivery_valid : SourceOccurrences.valid program.snapshot context occurrence1.delivery = true := by decide +kernel
theorem occurrence1_delivery_checked : SourceDelivery.checked program.snapshot context occurrence1.draw occurrence1.delivery = true := by decide +kernel
theorem occurrence1_query : occurrence1.draw = ({ entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",   steps := [{ kind := "apply",               protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",               site := "label_7269676874" },             { kind := "repeat",               protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",               site := "s15" }],   event := ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765",             "input_5", "random.bls12-381.fr/0", "draw", "role00000001"] }) := by kernel_rfl
theorem occurrence1_messages : occurrence1.messages = ([{ entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",    steps := [{ kind := "apply",                protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",                site := "label_7269676874" },              { kind := "repeat",                protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",                site := "s15" }],    event := ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0",              "label_726f756e64_0", "role00000000", "role00000001"] },  { entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",    steps := [{ kind := "apply",                protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",                site := "label_7269676874" },              { kind := "repeat",                protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",                site := "s15" }],    event := ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1",              "label_726f756e64_1", "role00000000", "role00000001"] },  { entry := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",    steps := [{ kind := "apply",                protocol := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d",                site := "label_7269676874" },              { kind := "repeat",                protocol := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",                site := "s15" }],    event := ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d",              "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"] }]) := by kernel_rfl
theorem occurrence0_origins :
    ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.OriginLaws context occurrence0 := by
  constructor <;> intro index <;>
    simp [Domain.queryOrigin, Occurrence.origins, occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw]

theorem occurrence1_origins :
    ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.OriginLaws context occurrence1 := by
  constructor <;> intro index <;>
    simp [Domain.queryOrigin, Occurrence.origins, occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw]


abbrev routing (handle : Nat) : Original.Routing :=
  ⟨program.snapshot, context, .validator, handle, occurrence0.messages ++ occurrence1.messages, [occurrence0.draw, occurrence1.draw], [⟨occurrence0.draw, occurrence0.delivery⟩, ⟨occurrence1.draw, occurrence1.delivery⟩], []⟩

theorem occurrence0_routes (handle index : Nat) :
    Routes (routing handle) occurrence0.protocol
      [⟨qualifyProtocolSite occurrence0.protocol.applicationPrefix "s15", index⟩]
      handle (occurrence0.origins context index) := by
  constructor
  · rfl
  all_goals
    simp only [Original.Routing.message, Original.Routing.draw, routing, Occurrence.messages,
      Occurrence.origins, OccurrenceResolution.resolve, List.cons_append, List.nil_append,
      List.filter_cons, List.filter_nil, ite_eq_left rfl]
    simp only [OccurrenceResolution.matchesOccurrence, occurrence0_low_valid, occurrence0_high_valid, occurrence0_draw_valid, occurrence0_delivery_valid, occurrence1_low_valid, occurrence1_high_valid, occurrence1_draw_valid, occurrence1_delivery_valid]
    simp [occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw]

theorem occurrence1_routes (handle index : Nat) :
    Routes (routing handle) occurrence1.protocol
      [⟨qualifyProtocolSite occurrence1.protocol.applicationPrefix "s15", index⟩]
      handle (occurrence1.origins context index) := by
  constructor
  · rfl
  all_goals
    simp only [Original.Routing.message, Original.Routing.draw, routing, Occurrence.messages,
      Occurrence.origins, OccurrenceResolution.resolve, List.cons_append, List.nil_append,
      List.filter_cons, List.filter_nil, ite_eq_left rfl]
    simp only [OccurrenceResolution.matchesOccurrence, occurrence0_low_valid, occurrence0_high_valid, occurrence0_draw_valid, occurrence0_delivery_valid, occurrence1_low_valid, occurrence1_high_valid, occurrence1_draw_valid, occurrence1_delivery_valid]
    simp [occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw]

theorem helper_bodies : ZkcSecurity.Realizations.Sumcheck.DomainHelpers.Bodies program := by bind_structured_bodies
theorem verifier_bodies : SumcheckVerifierHelpers.Bodies program.payload.definitions :=
  ⟨helper_bodies.sumcheck.empty, helper_bodies.sumcheck.append, helper_bodies.sumcheck.width, helper_bodies.sumcheck.«variables», helper_bodies.sumcheck.values⟩

namespace ValidatorCall0
abbrev occurrence := occurrence0
def outputs : VerifierOutputs context.suite := ({ point := { index := 28 }, scalar := { index := 33 }, transcript := { index := 27 } })
theorem outputs_derived : ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.verifierOutputs context.suite validatorArtifact 1 = .ok outputs := by decide +kernel
theorem output_references : outputs.references = [28, 33, 27] := by kernel_rfl
theorem capture_size : ((validatorArtifact.instructions.take 1).foldl (fun size instruction => size + instruction.results.length) validatorArtifact.inputs.length) = 7 := by kernel_rfl
theorem loop_operands : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).operands = [4, 6, 2, 5] := by kernel_rfl
theorem loop_operation : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).operation = (Zkc.Construction.Operation.loop "apply_14_label_6c656674_s15" 4 [28, 33, 27]) := by kernel_rfl
abbrev routes := occurrence0_routes
theorem body_syntax : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).body =
    ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.validatorInstructions context occurrence 7 := by kernel_rfl
theorem loop_sorts : (validatorArtifact.instructions.get ⟨1, by decide +kernel⟩).results = VerifierOutputs.sorts context.suite := by kernel_rfl
theorem loop_site : "apply_14_label_6c656674_s15" = qualifyProtocolSite occurrence.protocol.applicationPrefix "s15" := by kernel_rfl
theorem body_instance : ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep1Body (ringModel F G) program context =
    ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.validatorBody (ringModel F G) program context occurrence 7 := by kernel_rfl
theorem output_instance : outputs = ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.verifierOutputs context 7 := by kernel_rfl
noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 7) (index handle : Nat) (point : List F) (scalar : F)
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
      (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep1Body (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" point),
          .data (.field "bls12-381.fr" scalar), .transcript context.suite history])) := by
  rw [body_instance, output_instance]
  exact ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.validatorRound
    program helper_bodies.sumcheck verifier_bodies (routing handle) context rfl occurrence
    (by decide +kernel) occurrence0_origins 7 captured size index handle point scalar history
    (routes handle index)

def callback (handle : Nat) : VerifierCallback program (routing handle) occurrence context outputs 7 handle
  (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep1Body (ringModel F G) program context) :=
  ⟨fun captured size index point scalar history => round captured size index handle point scalar history⟩
end ValidatorCall0

namespace ValidatorCall1
abbrev occurrence := occurrence1
def outputs : VerifierOutputs context.suite := ({ point := { index := 33 }, scalar := { index := 38 }, transcript := { index := 32 } })
theorem outputs_derived : ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.verifierOutputs context.suite validatorArtifact 4 = .ok outputs := by decide +kernel
theorem output_references : outputs.references = [33, 38, 32] := by kernel_rfl
theorem capture_size : ((validatorArtifact.instructions.take 4).foldl (fun size instruction => size + instruction.results.length) validatorArtifact.inputs.length) = 12 := by kernel_rfl
theorem loop_operands : (validatorArtifact.instructions.get ⟨4, by decide +kernel⟩).operands = [4, 11, 3, 9] := by kernel_rfl
theorem loop_operation : (validatorArtifact.instructions.get ⟨4, by decide +kernel⟩).operation = (Zkc.Construction.Operation.loop "apply_16_label_7269676874_s15" 4 [33, 38, 32]) := by kernel_rfl
abbrev routes := occurrence1_routes
theorem body_syntax : (validatorArtifact.instructions.get ⟨4, by decide +kernel⟩).body =
    ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.validatorInstructions context occurrence 12 := by kernel_rfl
theorem loop_sorts : (validatorArtifact.instructions.get ⟨4, by decide +kernel⟩).results = VerifierOutputs.sorts context.suite := by kernel_rfl
theorem loop_site : "apply_16_label_7269676874_s15" = qualifyProtocolSite occurrence.protocol.applicationPrefix "s15" := by kernel_rfl
theorem body_instance : ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep4Body (ringModel F G) program context =
    ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.validatorBody (ringModel F G) program context occurrence 12 := by kernel_rfl
theorem output_instance : outputs = ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.verifierOutputs context 12 := by kernel_rfl
noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 12) (index handle : Nat) (point : List F) (scalar : F)
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
      (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep4Body (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" point),
          .data (.field "bls12-381.fr" scalar), .transcript context.suite history])) := by
  rw [body_instance, output_instance]
  exact ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates.validatorRound
    program helper_bodies.sumcheck verifier_bodies (routing handle) context rfl occurrence
    (by decide +kernel) occurrence1_origins 12 captured size index handle point scalar history
    (routes handle index)

def callback (handle : Nat) : VerifierCallback program (routing handle) occurrence context outputs 12 handle
  (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep4Body (ringModel F G) program context) :=
  ⟨fun captured size index point scalar history => round captured size index handle point scalar history⟩
end ValidatorCall1

namespace ProducerCall0
abbrev occurrence := occurrence0
def outputs : ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Outputs context.suite := ({ raw := { index := 35 },   dimension := { index := 36 },   width := { index := 37 },   point := { index := 38 },   transcript := { index := 34 } })
theorem outputs_derived : ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.producerOutputs context.suite producerArtifact 10 = .ok outputs := by decide +kernel
theorem output_references : outputs.references = [35, 36, 37, 38, 34] := by kernel_rfl
theorem capture_size : ((producerArtifact.instructions.take 10).foldl (fun size instruction => size + instruction.results.length) producerArtifact.inputs.length) = 14 := by kernel_rfl
theorem loop_operands : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).operands = [2, 5, 6, 7, 13, 3] := by kernel_rfl
theorem loop_operation : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).operation = (Zkc.Construction.Operation.loop "apply_14_label_6c656674_s15" 4 [35, 36, 37, 38, 34]) := by kernel_rfl
open ZkcSecurity.Realizations.Sumcheck.OriginalProducer
abbrev routing (handle : Nat) : Original.Routing := { ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.routing handle with mode := .producer }
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
    have candidates : (([⟨occurrence0.draw, occurrence0.delivery⟩, ⟨occurrence1.draw, occurrence1.delivery⟩] : List Original.Delivery).filter fun candidate =>
        Original.deliveryValid program.snapshot context
          candidate.draw candidate.message &&
        candidate.message.qualify (candidate.message.event[2]?.getD "") ==
          SumcheckVerifierLaws.deliverySite occurrence.protocol &&
        (context.draws.contains
          (candidate.draw.qualify (candidate.draw.event[2]?.getD ""),
            SumcheckVerifierLaws.deliverySite occurrence.protocol))) =
        [⟨occurrence.draw, occurrence.delivery⟩] := by
      decide +kernel
    have deliverySite : occurrence.delivery.qualify
        (occurrence.delivery.event[2]?.getD "") =
        SumcheckVerifierLaws.deliverySite occurrence.protocol := by decide +kernel
    have drawSite : occurrence.draw.qualify (occurrence.draw.event[2]?.getD "") =
        SumcheckVerifierLaws.challengeSite occurrence.protocol := by decide +kernel
    simp only [Original.Routing.delivery, show (routing handle).context = context from rfl,
      policy, Bool.false_eq_true, ↓reduceIte, candidates, deliverySite, drawSite]
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
      simp [occurrence, context, occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw,
        Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite, roleSubstitution,
        SumcheckVerifierLaws.deliverySite, Occurrence.origins, Context.message,
        Context.role, Origin.message, Domain.atCoordinates, decimal, decimalDigit]
    have drawSingleton : OccurrenceResolution.resolve program.snapshot context
        (context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol) (.draw "bls12-381.fr"))
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.draw] = some (occurrence.origins context index).draw := by
      simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence, occurrence0_draw_valid]
      simp [occurrence, context, occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw,
        Occurrence.draw, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite, roleSubstitution,
        SumcheckVerifierLaws.challengeSite, Occurrence.origins, Context.query,
        Context.role, Origin.query, Domain.atCoordinates, decimal, decimalDigit]
    rw [messageSingleton, Option.bind_some, drawSingleton]
    rfl
  · exact Original.Routing.draw_request (occurrence0_routes handle index).draw

theorem body_syntax : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).body =
    ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerInstructions context occurrence 14 := by kernel_rfl
theorem loop_sorts : (producerArtifact.instructions.get ⟨10, by decide +kernel⟩).results = ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Outputs.sorts context.suite := by kernel_rfl
theorem loop_site : "apply_14_label_6c656674_s15" = qualifyProtocolSite occurrence.protocol.applicationPrefix "s15" := by kernel_rfl
theorem body_instance : ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep10Body (ringModel F G) program context =
    ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerBody (ringModel F G) program context occurrence 14 := by kernel_rfl
theorem output_instance : outputs = ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerOutputs context 14 := by kernel_rfl
noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 14) (index handle : Nat)
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
      (ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep10Body (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" raw),
          .data (.index dimension), .data (.index width),
          .data (.vector "bls12-381.fr" point), .transcript context.suite history])) := by
  rw [body_instance, output_instance]
  exact ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerRound
    program helper_bodies.sumcheck (routing handle) context rfl occurrence
    (by decide +kernel) occurrence0_origins 14 captured size index raw dimension width point
    shape bounded positive history (routes handle index)

def callback (handle : Nat) : ZkcSecurity.Realizations.Sumcheck.OriginalProducer.ProducerCallback program (routing handle) occurrence context outputs 14 handle
  (ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep10Body (ringModel F G) program context) :=
  ⟨fun captured size index raw dimension width point shape bounded positive history => round captured size index handle raw dimension width point shape bounded positive history⟩
end ProducerCall0

namespace ProducerCall1
abbrev occurrence := occurrence1
def outputs : ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Outputs context.suite := ({ raw := { index := 50 },   dimension := { index := 51 },   width := { index := 52 },   point := { index := 53 },   transcript := { index := 49 } })
theorem outputs_derived : ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.producerOutputs context.suite producerArtifact 21 = .ok outputs := by decide +kernel
theorem output_references : outputs.references = [50, 51, 52, 53, 49] := by kernel_rfl
theorem capture_size : ((producerArtifact.instructions.take 21).foldl (fun size instruction => size + instruction.results.length) producerArtifact.inputs.length) = 29 := by kernel_rfl
theorem loop_operands : (producerArtifact.instructions.get ⟨21, by decide +kernel⟩).operands = [2, 20, 21, 22, 28, 18] := by kernel_rfl
theorem loop_operation : (producerArtifact.instructions.get ⟨21, by decide +kernel⟩).operation = (Zkc.Construction.Operation.loop "apply_16_label_7269676874_s15" 4 [50, 51, 52, 53, 49]) := by kernel_rfl
open ZkcSecurity.Realizations.Sumcheck.OriginalProducer
abbrev routing (handle : Nat) : Original.Routing := { ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.routing handle with mode := .producer }
theorem routes (handle index : Nat) :
    Routes (routing handle) occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
      (occurrence.origins context index) := by
  constructor
  · rfl
  · exact (occurrence1_routes handle index).low
  · exact (occurrence1_routes handle index).high
  · have policy :
        (!(context.draws.map Prod.fst).Nodup || !(context.draws.map Prod.snd).Nodup) = false := by
      decide +kernel
    have candidates : (([⟨occurrence0.draw, occurrence0.delivery⟩, ⟨occurrence1.draw, occurrence1.delivery⟩] : List Original.Delivery).filter fun candidate =>
        Original.deliveryValid program.snapshot context
          candidate.draw candidate.message &&
        candidate.message.qualify (candidate.message.event[2]?.getD "") ==
          SumcheckVerifierLaws.deliverySite occurrence.protocol &&
        (context.draws.contains
          (candidate.draw.qualify (candidate.draw.event[2]?.getD ""),
            SumcheckVerifierLaws.deliverySite occurrence.protocol))) =
        [⟨occurrence.draw, occurrence.delivery⟩] := by
      decide +kernel
    have deliverySite : occurrence.delivery.qualify
        (occurrence.delivery.event[2]?.getD "") =
        SumcheckVerifierLaws.deliverySite occurrence.protocol := by decide +kernel
    have drawSite : occurrence.draw.qualify (occurrence.draw.event[2]?.getD "") =
        SumcheckVerifierLaws.challengeSite occurrence.protocol := by decide +kernel
    simp only [Original.Routing.delivery, show (routing handle).context = context from rfl,
      policy, Bool.false_eq_true, ↓reduceIte, candidates, deliverySite, drawSite]
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
        occurrence1_delivery_valid]
      simp [occurrence, context, occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw,
        Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite, roleSubstitution,
        SumcheckVerifierLaws.deliverySite, Occurrence.origins, Context.message,
        Context.role, Origin.message, Domain.atCoordinates, decimal, decimalDigit]
    have drawSingleton : OccurrenceResolution.resolve program.snapshot context
        (context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol) (.draw "bls12-381.fr"))
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.draw] = some (occurrence.origins context index).draw := by
      simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence, occurrence1_draw_valid]
      simp [occurrence, context, occurrence0, occurrence1, occurrence0_decimal, occurrence1_decimal, Occurrence.low, Occurrence.high, Occurrence.draw, Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol, SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin, Template.repeats, Template.qualify, Template.applicationPrefix, context, ProtocolContext.enter, qualifyProtocolSite, roleSubstitution, SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite, SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite, Context.message, Context.query, Context.role, Origin.message, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw,
        Occurrence.draw, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite, roleSubstitution,
        SumcheckVerifierLaws.challengeSite, Occurrence.origins, Context.query,
        Context.role, Origin.query, Domain.atCoordinates, decimal, decimalDigit]
    rw [messageSingleton, Option.bind_some, drawSingleton]
    rfl
  · exact Original.Routing.draw_request (occurrence1_routes handle index).draw

theorem body_syntax : (producerArtifact.instructions.get ⟨21, by decide +kernel⟩).body =
    ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerInstructions context occurrence 29 := by kernel_rfl
theorem loop_sorts : (producerArtifact.instructions.get ⟨21, by decide +kernel⟩).results = ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Outputs.sorts context.suite := by kernel_rfl
theorem loop_site : "apply_16_label_7269676874_s15" = qualifyProtocolSite occurrence.protocol.applicationPrefix "s15" := by kernel_rfl
theorem body_instance : ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep21Body (ringModel F G) program context =
    ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerBody (ringModel F G) program context occurrence 29 := by kernel_rfl
theorem output_instance : outputs = ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerOutputs context 29 := by kernel_rfl
noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 29) (index handle : Nat)
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
      (ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep21Body (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" raw),
          .data (.index dimension), .data (.index width),
          .data (.vector "bls12-381.fr" point), .transcript context.suite history])) := by
  rw [body_instance, output_instance]
  exact ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates.producerRound
    program helper_bodies.sumcheck (routing handle) context rfl occurrence
    (by decide +kernel) occurrence1_origins 29 captured size index raw dimension width point
    shape bounded positive history (routes handle index)

def callback (handle : Nat) : ZkcSecurity.Realizations.Sumcheck.OriginalProducer.ProducerCallback program (routing handle) occurrence context outputs 29 handle
  (ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep21Body (ringModel F G) program context) :=
  ⟨fun captured size index raw dimension width point shape bounded positive history => round captured size index handle raw dimension width point shape bounded positive history⟩
end ProducerCall1

end ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums
