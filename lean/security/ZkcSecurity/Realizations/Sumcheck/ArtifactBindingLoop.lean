module

public import ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
public import ZkcExamples.Structured.OriginalSumcheckReduce

@[expose] public section

/-! Reusable source-repeat composition. Iteration indices and occurrence frames
come from the original repeat, independently of the artifact instruction list. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open SumcheckVerifierBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev VerifierSource (F G : Type) :=
  Values (Component (assignment F G)) repeatState × Original.State (uniformCarriers F G)

def carried (context : Zkc.Construction.Context) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" scalar),
    .transcript context.suite history]

def LoopReturns (context : Zkc.Construction.Context)
    (source : VerifierSource F G) (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point scalar history,
    source = (SumcheckVerifierLaws.embedV (some point, some scalar), ⟨[], history⟩) ∧
    frame = carried context point scalar history

/-- A local callback certificate, fixed to the actual original library and the
actual compiled callback. There is no assumed whole-region process equality. -/
structure VerifierCallback (program : Structured.Program)
    (routing : Original.Routing) (occurrence : Occurrence)
    (context : Zkc.Construction.Context) (outputs : VerifierOutputs context.suite) (offset handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G)) where
  round : ∀ captured : Domain.Environment (uniformCarriers F G), captured.length = offset →
    ∀ index point scalar history,
    Original.Simulation
      (VerifierReturns context outputs
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩])
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol
          (occurrence.protocol.roles 1)
          (.cons (some index) ((SumcheckVerifierLaws.embedV (some point, some scalar)).append
            (.cons (some handle) .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩], history⟩)
      (body (captured ++ .data (.index index) :: carried context point scalar history))

/-- One real source iteration, including opening/closing its source frame,
role masking, all callback effects, and the compiled yield/type checks. -/
def VerifierCallback.step (program : Structured.Program)
    (routing : Original.Routing) (occurrence : Occurrence)
    (context : Zkc.Construction.Context) (outputs : VerifierOutputs context.suite) (offset maximum handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G))
    (certificate : VerifierCallback program routing occurrence context outputs offset handle body)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (source : VerifierSource F G) (frame : Domain.Environment (uniformCarriers F G))
    (index : Nat) (related : LoopReturns context source frame) :
    Original.Simulation (LoopReturns context)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) occurrence.protocol (occurrence.protocol.roles 1)
          (.cons (some handle) .nil)
          (OriginalSumcheckLibrary.round program.payload occurrence.protocol
            (occurrence.protocol.roles 1)) source.1 index Occurrence.iterations "s15") source.2)
      ((body (captured ++ .data (.index index) :: frame)).bind fun final =>
        match Domain.read final outputs.references with
        | none => .halt .refused
        | some next => if Domain.sortsMatch
            [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
              .transcript context.suite] next then .done next else .halt .refused) := by
  apply Classical.choice
  obtain ⟨point, scalar, history, rfl, rfl⟩ := related
  refine ⟨?_⟩
  simp only [Repeat.stepOn, SumcheckVerifierLaws.mask_embedV _ _ rfl maximum,
    Original.fold_bind, Original.fold_within, List.nil_append, PIR.Process.bind_assoc]
  apply (certificate.round captured size index point scalar history).bind
    (fun _ _ related => related)
  intro result final returned
  apply Classical.choice
  obtain ⟨nextPoint, nextScalar, output, pointRead, scalarRead, historyRead, frames⟩ := returned
  refine ⟨?_⟩
  cases result with
  | mk values state =>
    dsimp only at output frames
    subst values
    simp only [Original.fold, PIR.Process.interpretState, frames, List.getLast?_singleton, ↓reduceIte,
      List.dropLast_singleton, PIR.Process.bind, SumcheckVerifierLaws.mask_embedV _ _ rfl maximum]
    simp only [VerifierOutputs.references, Domain.read, List.mapM_cons, List.mapM_nil, pointRead, scalarRead, historyRead,
      Bind.bind, Pure.pure, Option.bind]
    simp only [Domain.sortsMatch, Domain.Value.sort, List.map_cons,
      List.map_nil, beq_self_eq_true, ↓reduceIte]
    exact .done ⟨nextPoint, nextScalar, state.history, rfl, rfl⟩

/-- Arbitrarily many admitted source iterations reuse the one callback proof.
No instruction count or root name controls the loop. -/
def VerifierCallback.loop (program : Structured.Program)
    (routing : Original.Routing) (occurrence : Occurrence)
    (context : Zkc.Construction.Context) (outputs : VerifierOutputs context.suite) (offset maximum handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G))
    (certificate : VerifierCallback program routing occurrence context outputs offset handle body)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (indices : List Nat) (source : VerifierSource F G)
    (frame : Domain.Environment (uniformCarriers F G))
    (related : LoopReturns context source frame) :
    Original.Simulation (LoopReturns context)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Finite.fold (fun (value, state) index => Original.fold routing
        (Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) occurrence.protocol (occurrence.protocol.roles 1)
          (.cons (some handle) .nil)
          (OriginalSumcheckLibrary.round program.payload occurrence.protocol
            (occurrence.protocol.roles 1)) value index Occurrence.iterations "s15") state)
        indices source)
      (Domain.iterate body captured outputs.references
        [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
          .transcript context.suite] indices frame) := by
  apply Original.Simulation.iterate
  · intro source frame index related
    rcases source with ⟨value, state⟩
    refine Zkc.Construction.ArtifactBinding.transport rfl ?_
      (certificate.step program routing occurrence context outputs offset maximum handle body
        captured size (value, state) frame index related)
    congr 1
    funext final
    cases Domain.read final outputs.references <;> rfl
  · exact fun _ _ _ related => related
  · exact related

/-- Full original Reduce outputs and the complete appended compiled frame. -/
def ReduceReturns (context : Zkc.Construction.Context)
    (captured : Domain.Environment (uniformCarriers F G))
    (source : Values (Component (assignment F G)) reduceOutputs ×
      Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point scalar history,
    source = (reduceReturnValues (SumcheckVerifierLaws.embedV (some point, some scalar)),
      ⟨[], history⟩) ∧ frame = captured ++ carried context point scalar history

/-- Shared original-to-compiled Reduce construction, including rejection of an
excessive count before any iteration. The actual source chooses the repeat;
the independent callback certificate proves its actual compiled realization. -/
def VerifierCallback.reduce (program : Structured.Program)
    (bodies : SumcheckVerifierHelpers.Bodies program.payload.definitions)
    (routing : Original.Routing) (occurrence : Occurrence)
    (separate : occurrence.protocol.roles 0 ≠ occurrence.protocol.roles 1)
    (context : Zkc.Construction.Context) (outputs : VerifierOutputs context.suite) (offset maximum handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G))
    (certificate : VerifierCallback program routing occurrence context outputs offset handle body)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (count countRef : Nat) (initialRefs : List Nat) (scalar : F)
    (history : Domain.History (uniformCarriers F G))
    (countRead : captured[countRef]? = some (.data (.index count)))
    (initialRead : Domain.read captured initialRefs = some (carried context [] scalar history)) :
    Original.Simulation (ReduceReturns context captured)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (OriginalSumcheckLibrary.reduce program.payload maximum occurrence.protocol
          (occurrence.protocol.roles 1) []
          (.cons none (.cons none (.cons none (.cons (some scalar)
            (.cons (some count) (.cons (some handle) .nil))))))) ⟨[], history⟩)
      (Domain.View.loop maximum outputs.references
        countRef initialRefs
        [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
          .transcript context.suite] body captured) := by
  rw [OriginalSumcheckLibrary.reduce_verifier program.payload bodies maximum occurrence.protocol separate]
  rw [Original.fold_bind, Original.fold_repeat]
  have active : (((repeatSpec maximum).roles.map occurrence.protocol.roles).contains
      (occurrence.protocol.roles 1)) = true := by
    simp []
  simp only [active, ↓reduceIte, SumcheckVerifierLaws.mask_embedV _ _ rfl maximum]
  simp only [Domain.View.loop, countRead, initialRead, carried, Domain.sortsMatch,
    Domain.Value.sort, List.map_cons, List.map_nil,
    beq_self_eq_true, and_true]
  by_cases admitted : count ≤ maximum
  · simp only [admitted, ↓reduceIte]
    apply (certificate.loop program routing occurrence context outputs offset maximum handle body
      captured size (List.range count)
      (SumcheckVerifierLaws.embedV (some [], some scalar), ⟨[], history⟩)
      (carried context [] scalar history) ⟨[], scalar, history, rfl, rfl⟩).bind
      (fun _ _ related => related)
    intro result final returned
    apply Classical.choice
    obtain ⟨point, scalar, history, rfl, rfl⟩ := returned
    refine ⟨?_⟩
    simp only [Original.fold, PIR.Process.interpretState, Domain.View.append, carried,
      Domain.sortsMatch, Domain.Value.sort, List.map_cons, List.map_nil,
      beq_self_eq_true, ↓reduceIte]
    exact .done ⟨point, scalar, history, rfl, rfl⟩
  · simp only [admitted, ↓reduceIte, PIR.Process.bind]
    exact .halt .refused

end ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
