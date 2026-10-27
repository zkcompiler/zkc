module
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingLoop
public meta import Zkc.Construction.ArtifactBindingTactic
/-! Shared validator callback certificate. Actual occurrences check their complete
instruction syntax, View body and typed output association before applying this proof. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

def verifierOutputs (context : Zkc.Construction.Context) (offset : Nat) : VerifierOutputs context.suite :=
  ⟨⟨offset + 21⟩, ⟨offset + 26⟩, ⟨offset + 20⟩⟩

/-- Local origin resolution at every dynamic repeat coordinate. -/
structure OriginLaws (context : Zkc.Construction.Context) (occurrence : Occurrence) : Prop where
  low : ∀ index, Domain.templateOrigin context occurrence.low [index] = some (occurrence.origins context index).low
  high : ∀ index, Domain.templateOrigin context occurrence.high [index] = some (occurrence.origins context index).high
  draw : ∀ index, Domain.queryOrigin context context.suite "bls12-381.fr" occurrence.draw [index] = some (occurrence.origins context index).draw
  delivery : ∀ index, Domain.templateOrigin context occurrence.delivery [index] = some (occurrence.origins context index).delivery

/-- The installed validator layout, with absolute references embedded after a captured prefix.
Every sequence retains the existing Domain View checkpoints. -/
def validatorBody (model : Structured.DomainModel) (program : Structured.Program)
    (context : Zkc.Construction.Context) (occurrence : Occurrence) (offset : Nat) : Domain.View.Block model.toCarriers :=
  (Domain.View.sequence (Domain.View.receive ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 0))) (Zkc.Source.Structured.Ty.field "bls12-381.fr") ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 5) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.observe context (context.suite) occurrence.low (offset + 3) (offset + 4) (offset + 6) ([Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.receive ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 0))) (Zkc.Source.Structured.Ty.field "bls12-381.fr") ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 9) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.observe context (context.suite) occurrence.high (offset + 7) (offset + 8) (offset + 10) ([Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.calculation model (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr") ([(offset + 4), (offset + 8)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.calculation model (Zkc.Construction.Calculation.fieldEqual "bls12-381.fr") ([(offset + 2), (offset + 12)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.boolean)]))
  (Domain.View.sequence (Domain.View.guard (offset + 13) ([]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 14) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.challenge context (context.suite) ("bls12-381.fr") occurrence.draw (offset + 11) (offset + 15) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),  Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 18) (offset + 0) ([Zkc.Construction.ValueSort.indices]))
  (Domain.View.sequence (Domain.View.observe context (context.suite) occurrence.delivery (offset + 17) (offset + 16) (offset + 19) ([Zkc.Construction.ValueSort.transcript context.suite]))
  (Domain.View.sequence (Domain.View.helper model program (SumcheckHelperBodies.appendHelper.name) ([(offset + 1), (offset + 16)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.vector "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.calculation model (Zkc.Construction.Calculation.fieldConstant "bls12-381.fr" 1) ([]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.calculation model (Zkc.Construction.Calculation.fieldSubtract "bls12-381.fr") ([(offset + 22), (offset + 16)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.calculation model (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([(offset + 23), (offset + 4)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.calculation model (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([(offset + 16), (offset + 8)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  (Domain.View.sequence (Domain.View.calculation model (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr") ([(offset + 24), (offset + 25)]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
  Domain.View.empty)))))))))))))))))))))))

/-- Exact syntax of the installed layout, including the diagnostic guard site. -/
def validatorInstructions (context : Zkc.Construction.Context) (occurrence : Occurrence) (offset : Nat) : List Zkc.Construction.Instruction :=
  [⟨.receive ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((SumcheckVerifierLaws.lowSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 0))) (Zkc.Source.Structured.Ty.field "bls12-381.fr"), [], ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 5), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.observe (context.suite) occurrence.low, [(offset + 3), (offset + 4), (offset + 6)], ([Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.receive ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((SumcheckVerifierLaws.highSite occurrence.protocol)) ((context.role (occurrence.protocol.roles 0))) (Zkc.Source.Structured.Ty.field "bls12-381.fr"), [], ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 9), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.observe (context.suite) occurrence.high, [(offset + 7), (offset + 8), (offset + 10)], ([Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.calculate (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr"), ([(offset + 4), (offset + 8)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.calculate (Zkc.Construction.Calculation.fieldEqual "bls12-381.fr"), ([(offset + 2), (offset + 12)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.boolean)]), []⟩,
   ⟨.guard (qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.roundGuardSite0), [(offset + 13)], ([]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 14), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.challenge (context.suite) ("bls12-381.fr") occurrence.draw, [(offset + 11), (offset + 15)], ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),  Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.indicesEmpty, [], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.indicesAppend, [(offset + 18), (offset + 0)], ([Zkc.Construction.ValueSort.indices]), []⟩,
   ⟨.observe (context.suite) occurrence.delivery, [(offset + 17), (offset + 16), (offset + 19)], ([Zkc.Construction.ValueSort.transcript context.suite]), []⟩,
   ⟨.call (SumcheckHelperBodies.appendHelper.name), ([(offset + 1), (offset + 16)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.vector "bls12-381.fr")]), []⟩,
   ⟨.calculate (Zkc.Construction.Calculation.fieldConstant "bls12-381.fr" 1), ([]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.calculate (Zkc.Construction.Calculation.fieldSubtract "bls12-381.fr"), ([(offset + 22), (offset + 16)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.calculate (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr"), ([(offset + 23), (offset + 4)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.calculate (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr"), ([(offset + 16), (offset + 8)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩,
   ⟨.calculate (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr"), ([(offset + 24), (offset + 25)]), ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]), []⟩]

/-- One symbolic full simulation for the installed validator layout. -/
def validatorRound (program : Structured.Program)
    (helpers : SumcheckUnitContracts.Bodies program.payload.definitions)
    (verifierBodies : SumcheckVerifierHelpers.Bodies program.payload.definitions)
    (routing : Original.Routing) (context : Zkc.Construction.Context)
    (contextEq : routing.context = context) (occurrence : Occurrence)
    (separate : occurrence.protocol.roles 0 ≠ occurrence.protocol.roles 1)
    (origins : OriginLaws context occurrence) (offset : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (index handle : Nat) (point : List F) (scalar : F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes routing occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩]
      handle (occurrence.origins context index)) :
    Original.Simulation
      (VerifierReturns (F := F) (G := G) context (verifierOutputs context offset)
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩])
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol (occurrence.protocol.roles 1)
          (.cons (some index) ((SumcheckVerifierLaws.embedV (some point, some scalar)).append
            (.cons (some handle) .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩], history⟩)
      (validatorBody (ringModel F G) program context occurrence offset
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" point),
          .data (.field "bls12-381.fr" scalar), .transcript context.suite history])) := by
  subst context
  rw [original_round program.payload verifierBodies routing occurrence.protocol separate index handle
    (occurrence.origins routing.context index) point scalar _ routes]
  simp only [validatorBody, Domain.View.sequence]
  derive_artifact_binding
    normalizing (saturate_artifact (
      try normalize_artifact_operations
        [ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.append program helpers,
          origins.low, origins.high, origins.draw, origins.delivery]
        unfolding [verifier, Original.queryField,
          Occurrence.origins, OccurrenceResolution.atCoordinates_request,
          Context.message, Origin.message, Context.query, Origin.query, Request.draw]
      try simp (disch := omega) only [PIR.Process.bind, List.append_assoc, List.cons_append, List.nil_append,
        List.getElem?_append_right, size,
        Nat.add_sub_cancel_left, List.getElem?_cons_zero, List.getElem?_cons_succ]))
    solving (first
      | solve | simp [Zkc.Construction.ArtifactBinding.Captures, List.append_assoc]
      | (unfold VerifierReturns
         refine ⟨_, _, rfl, ?_⟩
         simp (disch := omega) [verifierOutputs, List.getElem?_append_right, size, List.getElem?_cons_zero, List.getElem?_cons_succ]))
end ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates
