module

public import ZkcSecurity.Realizations.Sumcheck.OriginalProducer
public import ZkcExamples.Structured.OriginalSumcheckReduce

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.OriginalProducer
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open SumcheckVerifierBodies ZkcSecurity.Realizations.Sumcheck.ArtifactBinding

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev ProducerSource (F G : Type) :=
  Values (Component (assignment F G)) repeatState × Original.State (uniformCarriers F G)

def carried (context : Zkc.Construction.Context) (raw : List F) (dimension width : Nat)
    (point : List F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" raw), .data (.index dimension), .data (.index width),
    .data (.vector "bls12-381.fr" point), .transcript context.suite history]

/-- Loop composition fixes all five physical values and all six optional
source slots, with the shape invariant required by the next actual callback. -/
def LoopReturns (context : Zkc.Construction.Context) (dimension : Nat)
    (source : ProducerSource F G) (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ raw width point history,
    source = (SumcheckProverLaws.embedP (raw, dimension, width, point), ⟨[], history⟩) ∧
    frame = carried context raw dimension width point history ∧
    PrimitiveLibrary.HasShape raw dimension width ∧ raw.length < indexLimit

structure ProducerCallback (program : Structured.Program)
    (routing : Original.Routing) (occurrence : Occurrence)
    (context : Zkc.Construction.Context) (outputs : Outputs context.suite) (offset handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G)) where
  round : ∀ captured : Domain.Environment (uniformCarriers F G), captured.length = offset →
    ∀ index raw dimension width point,
    PrimitiveLibrary.HasShape raw dimension width → raw.length < indexLimit → 0 < dimension →
    ∀ history,
    Original.Simulation
      (RoundReturns context outputs
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        raw dimension width point)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol
          (occurrence.protocol.roles 0)
          (.cons (some index) ((SumcheckProverLaws.embedP (raw, dimension, width, point)).append
            (.cons none .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩], history⟩)
      (body (captured ++ .data (.index index) :: carried context raw dimension width point history))

/-- The compiled callback followed by its exact physical yield and sort check. -/
def iteration (context : Zkc.Construction.Context) (outputs : Outputs context.suite)
    (body : Domain.View.Block (uniformCarriers F G))
    (captured frame : Domain.Environment (uniformCarriers F G)) (index : Nat) :
    PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G)) :=
  (body (captured ++ .data (.index index) :: frame)).bind fun final =>
    match Domain.read final outputs.references with
    | none => .halt .refused
    | some next => if Domain.sortsMatch
        [.data (.vector "bls12-381.fr"), .data .index, .data .index,
          .data (.vector "bls12-381.fr"), .transcript context.suite] next then
        .done next else .halt .refused

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem iterate_iteration (context : Zkc.Construction.Context) (outputs : Outputs context.suite)
    (body : Domain.View.Block (uniformCarriers F G))
    (captured frame : Domain.Environment (uniformCarriers F G)) (indices : List Nat) :
    Domain.iterate body captured outputs.references
      [.data (.vector "bls12-381.fr"), .data .index, .data .index,
        .data (.vector "bls12-381.fr"), .transcript context.suite] indices frame =
      Finite.fold (iteration context outputs body captured) indices frame := by
  rw [Original.iterate_eq_fold]
  congr 1
  funext frame index
  unfold iteration
  congr 1
  funext final
  cases Domain.read final outputs.references <;> rfl

def ProducerCallback.step (program : Structured.Program)
    (routing : Original.Routing) (occurrence : Occurrence)
    (context : Zkc.Construction.Context) (outputs : Outputs context.suite) (offset maximum handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G))
    (certificate : ProducerCallback program routing occurrence context outputs offset handle body)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (source : ProducerSource F G) (frame : Domain.Environment (uniformCarriers F G))
    (index dimension : Nat) (positive : 0 < dimension)
    (related : LoopReturns context dimension source frame) :
    Original.Simulation (LoopReturns context (dimension - 1))
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) occurrence.protocol
          (occurrence.protocol.roles 0) (.cons none .nil)
          (OriginalSumcheckLibrary.round program.payload occurrence.protocol
            (occurrence.protocol.roles 0)) source.1 index Occurrence.iterations "s15") source.2)
      (iteration context outputs body captured frame index) := by
  unfold iteration
  apply Classical.choice
  obtain ⟨raw, width, point, history, rfl, rfl, shape, bounded⟩ := related
  refine ⟨?_⟩
  simp only [Repeat.stepOn, SumcheckProverLaws.mask_embedP _ _ rfl maximum,
    Original.fold_bind, Original.fold_within, List.nil_append, PIR.Process.bind_assoc]
  apply (certificate.round captured size index raw dimension width point shape bounded positive history).bind
    (fun _ _ related => related)
  intro result final returned
  apply Classical.choice
  obtain ⟨returned, challenge, update⟩ := returned
  obtain ⟨nextRaw, nextDimension, nextWidth, nextPoint, output,
    rawRead, dimensionRead, widthRead, pointRead, historyRead, frames⟩ := returned
  have values := output.symm.trans update
  have equal : (nextRaw, nextDimension, nextWidth, nextPoint) =
      (Zkc.Polynomial.Multilinear.restrictValues raw challenge, dimension - 1, width,
        point ++ [challenge]) := by
    simpa only [SumcheckProverLaws.embedP, SumcheckRoundNormalForms.proverState,
      Values.cons.injEq, Option.some.injEq, and_true, Prod.mk.injEq] using values
  cases equal
  refine ⟨?_⟩
  cases result with
  | mk values state =>
    dsimp only at output frames
    subst values
    simp only [Original.fold, PIR.Process.interpretState, frames, List.getLast?_singleton,
      ↓reduceIte, List.dropLast_singleton, PIR.Process.bind,
      SumcheckProverLaws.mask_embedP _ _ rfl maximum]
    simp only [Outputs.references, Domain.read, List.mapM_cons, List.mapM_nil, rawRead, dimensionRead,
      widthRead, pointRead, historyRead, Bind.bind, Pure.pure, Option.bind]
    simp only [Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, List.map_cons,
      List.map_nil, beq_self_eq_true, ↓reduceIte]
    exact .done ⟨_, _, _, _, rfl, rfl,
      MapFirstLaws.restrict_shape raw dimension width challenge shape positive,
      MapFirstLaws.restrict_length_bound raw challenge bounded⟩

/-- A remaining-dimension invariant composes all admitted rounds, including
zero trips. The reached indices are the original range, and compiled yield
and sort checks are discharged at each actual callback return. -/
def ProducerCallback.loop (program : Structured.Program)
    (routing : Original.Routing) (occurrence : Occurrence)
    (context : Zkc.Construction.Context) (outputs : Outputs context.suite) (offset maximum handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G))
    (certificate : ProducerCallback program routing occurrence context outputs offset handle body)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (start count dimension : Nat) (enough : count ≤ dimension)
    (source : ProducerSource F G) (frame : Domain.Environment (uniformCarriers F G))
    (related : LoopReturns context dimension source frame) :
    Original.Simulation (LoopReturns context (dimension - count))
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Finite.fold (fun source index => Original.fold routing
        (Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) occurrence.protocol
          (occurrence.protocol.roles 0) (.cons none .nil)
          (OriginalSumcheckLibrary.round program.payload occurrence.protocol
            (occurrence.protocol.roles 0)) source.1 index Occurrence.iterations "s15") source.2)
        (List.range' start count) source)
      (Domain.iterate body captured
        outputs.references
        [.data (.vector "bls12-381.fr"), .data .index, .data .index,
          .data (.vector "bls12-381.fr"), .transcript context.suite]
        (List.range' start count) frame) := by
  rw [iterate_iteration]
  induction count generalizing start dimension source frame with
  | zero =>
    simpa only [Nat.sub_zero, List.range'_zero, Finite.fold, Domain.iterate] using
      (Original.Simulation.done related)
  | succ count ih =>
    rcases source with ⟨value, state⟩
    simp only [List.range'_succ, Finite.fold]
    have composed := (certificate.step program routing occurrence context outputs offset maximum handle body
      captured size (value, state) frame start dimension (by omega) related).bind
      (sourceNext := Finite.fold (fun source index => Original.fold routing
        (Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) occurrence.protocol
          (occurrence.protocol.roles 0) (.cons none .nil)
          (OriginalSumcheckLibrary.round program.payload occurrence.protocol
            (occurrence.protocol.roles 0)) source.1 index Occurrence.iterations "s15") source.2)
        (List.range' (start + 1) count))
      (targetNext := Finite.fold (iteration context outputs body captured)
        (List.range' (start + 1) count))
      (returnRelation := LoopReturns context (dimension - (count + 1)))
      (nextLive := fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (fun _ _ related => related) (fun next nextFrame nextRelated => by
        simpa only [Nat.sub_sub, Nat.add_comm count 1] using
          ih (start + 1) (dimension - 1) (by omega) next nextFrame nextRelated)
    simpa only using composed

end ZkcSecurity.Realizations.Sumcheck.OriginalProducer
