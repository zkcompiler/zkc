module
public import ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates
public import ZkcSecurity.Realizations.Sumcheck.OriginalProducerLoop
public meta import Zkc.Construction.ArtifactBindingTactic
/-! Shared producer callback certificate with all source optional slots, five physical
outputs, shape update and captured-prefix checkpoints retained. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]


open ZkcSecurity.Realizations.Sumcheck.OriginalProducer
open ZkcSecurity.Realizations.Sumcheck.ArtifactBindingTemplates

def producerOutputs (context : Zkc.Construction.Context) (offset : Nat) : Outputs context.suite :=
  ⟨⟨offset + 21⟩, ⟨offset + 22⟩, ⟨offset + 23⟩, ⟨offset + 24⟩, ⟨offset + 20⟩⟩

def producerBody (model : Structured.DomainModel) (program : Structured.Program)
    (context : Zkc.Construction.Context) (occurrence : Occurrence) (offset : Nat) : Domain.View.Block model.toCarriers :=
  (Domain.View.sequence (Domain.View.helper model program (SumcheckHelperBodies.sumsHelper.name) ([(offset + 1), (offset + 2), (offset + 3)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),  Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.send ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 1))) (offset + 6) ([]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 8) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.observe context (context.suite) occurrence.low (offset + 5) (offset + 6) (offset + 9) ([Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.send ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 1))) (offset + 7) ([]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 11) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.observe context (context.suite) occurrence.high (offset + 10) (offset + 7) (offset + 12) ([Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 14) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.challenge context (context.suite) ("bls12-381.fr") occurrence.draw (offset + 13) (offset + 15) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),  Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 18) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.observe context (context.suite) occurrence.delivery (offset + 17) (offset + 16) (offset + 19) ([Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.helper model program (MapFirstBodies.firstHelper.name) ([(offset + 1), (offset + 2), (offset + 3), (offset + 16)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.vector "bls12-381.fr"),  Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.index),  Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.index)]))
  (Domain.View.sequence (Domain.View.helper model program (SumcheckHelperBodies.appendHelper.name) ([(offset + 4), (offset + 16)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.vector "bls12-381.fr")]))
  Domain.View.empty)))))))))))))))))

/-- Exact syntax of the installed producer callback. -/
def producerInstructions (context : Zkc.Construction.Context) (occurrence : Occurrence)
    (offset : Nat) : List Zkc.Construction.Instruction :=
  [⟨.call (SumcheckHelperBodies.sumsHelper.name), ([(offset + 1), (offset + 2), (offset + 3)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),  Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.send ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 1))), [(offset + 6)], ([]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 8), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.observe (context.suite) occurrence.low, [(offset + 5), (offset + 6), (offset + 9)], ([Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.send ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 1))), [(offset + 7)], ([]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 11), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.observe (context.suite) occurrence.high, [(offset + 10), (offset + 7), (offset + 12)], ([Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 14), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.challenge (context.suite) ("bls12-381.fr") occurrence.draw, [(offset + 13), (offset + 15)], ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),  Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 18), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.observe (context.suite) occurrence.delivery, [(offset + 17), (offset + 16), (offset + 19)], ([Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.call (MapFirstBodies.firstHelper.name), ([(offset + 1), (offset + 2), (offset + 3), (offset + 16)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.vector "bls12-381.fr"),  Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.index),  Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.index)]), []⟩,
   ⟨.call (SumcheckHelperBodies.appendHelper.name), ([(offset + 4), (offset + 16)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.vector "bls12-381.fr")]), []⟩]

/-- One symbolic full simulation for the installed producer layout. -/
def producerRound (program : Structured.Program)
    (helpers : SumcheckUnitContracts.Bodies program.payload.definitions)
    (routing : Original.Routing) (context : Zkc.Construction.Context)
    (contextEq : routing.context = context) (occurrence : Occurrence)
    (separate : occurrence.protocol.roles 1 ≠ occurrence.protocol.roles 0)
    (origins : OriginLaws context occurrence) (offset : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (index : Nat) (raw : List F) (dimension width : Nat) (point : List F)
    (shape : PrimitiveLibrary.HasShape raw dimension width)
    (bounded : raw.length < indexLimit) (positive : 0 < dimension)
    (history : Domain.History (uniformCarriers F G))
    (routes : ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Routes routing occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
      (occurrence.origins context index)) :
    Original.Simulation
      (RoundReturns (F := F) (G := G) context (producerOutputs context offset)
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        raw dimension width point)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol (occurrence.protocol.roles 0)
          (.cons (some index) ((SumcheckProverLaws.embedP (raw, dimension, width, point)).append
            (.cons none .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩], history⟩)
      (producerBody (ringModel F G) program context occurrence offset
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" raw),
          .data (.index dimension), .data (.index width),
          .data (.vector "bls12-381.fr" point), .transcript context.suite history])) := by
  subst context
  rw [ZkcSecurity.Realizations.Sumcheck.OriginalProducer.original_round program.payload helpers
    routing occurrence.protocol separate index none
    (occurrence.origins routing.context index) raw dimension width point shape bounded positive _ routes]
  have sumsEq := ZkcSecurity.Realizations.Sumcheck.DomainHelpers.sums (F := F) (G := G) program helpers
    raw dimension width (lt_trans shape.2.1 (by decide +kernel)) positive (shape.split_valid positive)
  have firstEq (challenge : F) := ZkcSecurity.Realizations.Sumcheck.DomainHelpers.first (F := F) (G := G)
    program helpers raw dimension width challenge shape bounded positive
  have appendEq := ZkcSecurity.Realizations.Sumcheck.DomainHelpers.append (F := F) (G := G) program helpers
  simp only [producerBody, Domain.View.sequence]
  derive_artifact_binding
    normalizing (
      try normalize_artifact_operations
        [sumsEq, firstEq, appendEq, origins.low, origins.high, origins.draw, origins.delivery]
        unfolding [producer, Original.queryField,
          Occurrence.origins, OccurrenceResolution.atCoordinates_request,
          Context.message, Origin.message, Context.query, Origin.query, Request.draw]
      try simp (disch := omega) only [PIR.Process.bind, List.append_assoc, List.cons_append, List.nil_append,
        List.getElem?_append_right, size, Nat.add_sub_cancel_left,
        List.getElem?_cons_zero, List.getElem?_cons_succ]
      change Original.Simulation _ _ _ _)
    solving (first
      | solve | simp [Zkc.Construction.ArtifactBinding.Captures, List.append_assoc]
      | (unfold RoundReturns
         constructor
         · unfold ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Returns
           refine ⟨_, _, _, _, rfl, ?_⟩
           simp (disch := omega) [producerOutputs, List.getElem?_append_right, size, List.getElem?_cons_zero, List.getElem?_cons_succ]
         · exact ⟨_, rfl⟩))
end ZkcSecurity.Realizations.Sumcheck.OriginalProducerTemplates
