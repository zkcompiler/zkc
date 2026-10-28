module

public import ZkcSecurity.Families.Sumcheck.SourceHonestIteration
public import ZkcExamples.Structured.SumcheckSourceSelections
public import Zkc.Obligations.FrameComposition

@[expose] public section

/-! Mathematical consumers of the complete nominal reduction. Source masks and
reached induction values are retained by a symbolic finite-fold equation. No
source/artifact correspondence or canonical receipt is constructed here. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Families.Sumcheck.SourceIteration
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E : Type}
variable (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
  (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
  (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
  (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2) (handle : Nat)

def callback : RegionFunction (Component model.Value) (Occurrence.signature model.toCarriers)
    (.index :: (SumcheckVerifierBodies.repeatState ++ [.service "random.bls12-381.fr/0"]),
      SumcheckVerifierBodies.repeatState) := fun args => SumcheckVerifierBodies.roundBody.denote
  (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
    (ctx.roles 1) protocols ctx Occurrence.iterations) args.get

def maskedStep (maximum : Nat) :=
  Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) ctx (ctx.roles 1)
    (.cons (some handle) .nil) (callback model definitions protocols ctx)
    (iterations := Occurrence.iterations) (site := SumcheckVerifierBodies.repeatSite)

omit fieldLaw in
theorem mask_state (maximum : Nat) (point : Option (List (model.Field field)))
    (scalar : Option (model.Field field)) :
    maskValues (ctx.roles 1) (ctx.mapScopes (SumcheckVerifierBodies.repeatSpec maximum).stateScopes)
      (state model point scalar) = state model point scalar := by
  unfold state
  iterate 7 unfold maskValues
  simp [ProtocolContext.mapScopes, Participant.restrict]

include linked bodies distinct

theorem masked_step {n : Nat} (maximum index : Nat)
    (reference : PrefixState (model.Field field) Frame (n+1)) :
    maskedStep model definitions protocols ctx handle maximum (encode model index reference).slots index =
      (step model definitions protocols ctx handle (encode model index reference)).bind
        (fun returned => .done returned.slots) := by
  unfold maskedStep Repeat.stepOn
  rw [show (encode model index reference).slots = state model (some reference.point) (some reference.scalar) from rfl,
    mask_state model ctx]
  have round : callback model definitions protocols ctx
      (Values.cons (some index)
        ((state model (some reference.point) (some reference.scalar)).append (.cons (some handle) .nil))) =
      SumcheckReferenceInstallation.reference model ctx (some handle) (some reference.point) (some reference.scalar) :=
    body_reference model definitions linked bodies protocols ctx distinct index
      (some reference.point) (some reference.scalar) (some handle)
  rw [round]
  simp only [step, Occurrence.iterations, IterationObservations.within, PIR.Process.bind]
  rw [round_reference model definitions linked bodies protocols ctx distinct handle]
  simp only [SumcheckReferenceInstallation.reference, PIR.Process.bind_assoc, PIR.Process.bind,
    encode, repeatSite]
  congr 1
  funext _
  congr 1
  funext lo
  congr 1
  funext hi
  by_cases checked : reference.scalar = lo+hi
  · simp only [checked, ↓reduceIte, PIR.Process.bind]
    congr 1
    funext r
    congr 1
    funext _
    congr 1
    funext _
    exact congrArg PIR.Process.done (mask_state model ctx maximum _ _)
  · simp only [checked, ↓reduceIte, PIR.Process.bind]

omit fieldLaw linked bodies distinct in
theorem step_index (runtime : Runtime model Frame) :
    PIR.Yields (fun returned => returned.index = runtime.index+1)
      (step model definitions protocols ctx handle runtime) := by
  have all {A : Type} (process : PIR.Process (Occurrence.signature model.toCarriers) A) :
      PIR.Yields (fun _ => True) process := by
    induction process with
    | done => trivial
    | halt => trivial
    | call _ _ ih => exact ih
  have roundIndex : PIR.Yields (fun returned => returned.index = runtime.index+1)
      (roundStep model definitions protocols ctx handle runtime) := by
    unfold roundStep
    exact (all _).bind (fun _ _ => rfl)
  unfold step
  simp only [Occurrence.iterations, IterationObservations.within, PIR.Process.bind]
  intro _
  exact roundIndex.bind (fun _ same => fun _ => same)

omit linked bodies distinct in
theorem encode_index {n : Nat} (index : Nat) (reference : PrefixState (model.Field field) Frame n) :
    (encode model index reference).index = index := rfl

/-- The source range and carried counter advance together. The induction uses
an independent all-replies shape/frame law, including attacker endpoints. -/
theorem loop_equation (original : List (model.Field field)) (callerFrame : Frame) (maximum : Nat) :
    ∀ count (runtime : Runtime model Frame), represented model original callerFrame count runtime →
      Finite.fold (maskedStep model definitions protocols ctx handle maximum)
        (List.range' runtime.index count) runtime.slots =
        (PIR.repeatN count (step model definitions protocols ctx handle) runtime).bind
          (fun returned => .done returned.slots) := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro runtime valid
    obtain ⟨reference, same, retained, encoded⟩ := valid
    rw [encoded]
    simp only [encode_index, List.range'_succ, Finite.fold, PIR.repeatN]
    rw [masked_step model definitions linked bodies protocols ctx distinct handle maximum runtime.index reference]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    have preserved := frame_contract (E := Unit) model definitions linked bodies protocols ctx distinct handle
      original callerFrame count (encode model runtime.index reference) ⟨reference, same, retained, rfl⟩
    have indices := step_index model definitions protocols ctx handle (encode model runtime.index reference)
    have framed := preserved.conj indices
    apply framed.bind_congr
    intro next valid
    simpa only [valid.2, encode] using ih next valid.1

/-- Actual complete reduction, with arbitrary caller frame returned alongside
all six source outputs. The source still owns count admission and terminal reads. -/
def reduction {n : Nat} (maximum count : Nat)
    (reference : PrefixState (model.Field field) Frame n) :=
  ((SumcheckVerifierBodies.reduceBody maximum).denote
    (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
      (ctx.roles 1) protocols ctx Occurrence.iterations)
    (SumcheckReductionReference.pattern.environment model
      (SumcheckReductionReference.inputs model (some reference.point) (some reference.scalar)
        (some count) (some handle))).get).bind fun returned => .done (returned, reference.frame)

theorem reduction_equation (reductionBodies : SumcheckReductionReference.Bodies model definitions)
    (maximum count : Nat) (bounded : count ≤ maximum)
    (reference : PrefixState (model.Field field) Frame count) :
    reduction model definitions protocols ctx handle maximum count reference =
      (PIR.repeatN count (step model definitions protocols ctx handle) (encode model 0 reference)).bind
        (fun returned => .done (SumcheckVerifierBodies.reduceReturnValues returned.slots, reference.frame)) := by
  unfold reduction
  rw [SumcheckReductionReference.body_reference model definitions linked reductionBodies protocols
    maximum ctx distinct]
  have admitted : denoteRepeatOn (SumcheckVerifierBodies.repeatSpec maximum) ctx (ctx.roles 1)
      (some count) (state model (some reference.point) (some reference.scalar)) (.cons (some handle) .nil)
      (callback model definitions protocols ctx) Occurrence.iterations SumcheckVerifierBodies.repeatSite =
      Finite.fold (maskedStep model definitions protocols ctx handle maximum)
        (List.range' 0 count) (state model (some reference.point) (some reference.scalar)) := by
    have active : ((SumcheckVerifierBodies.repeatSpec maximum).roles.map ctx.roles).contains (ctx.roles 1) = true := by
      simp
    rw [denoteRepeatOn, ite_eq_left active]
    simp only [bounded, ↓reduceIte]
    change Finite.fold _ (List.range count)
      (maskValues _ _ (state model (some reference.point) (some reference.scalar))) = _
    rw [mask_state model ctx maximum, List.range_eq_range']
    rfl
  change ((denoteRepeatOn (SumcheckVerifierBodies.repeatSpec maximum) ctx (ctx.roles 1)
    (some count) (state model (some reference.point) (some reference.scalar)) (.cons (some handle) .nil)
    (callback model definitions protocols ctx) Occurrence.iterations SumcheckVerifierBodies.repeatSite).bind
    (SumcheckReductionReference.terminal model)).bind _ = _
  rw [admitted]
  have loop := loop_equation model definitions linked bodies protocols ctx distinct handle
    reference.original reference.frame maximum count (encode model 0 reference) ⟨reference,rfl,rfl,rfl⟩
  change Finite.fold _ (List.range' 0 count) (state model (some reference.point) (some reference.scalar)) = _ at loop
  rw [loop]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  apply (RepeatedComponent.frame_repeatN (component (E := Unit) model definitions protocols ctx handle)
    (frame_contract model definitions linked bodies protocols ctx distinct handle reference.original reference.frame)
    count (encode model 0 reference) ⟨reference,rfl,rfl,rfl⟩).bind_congr
  intro returned valid
  obtain ⟨next, same, retained, encoded⟩ := valid
  rw [encoded]
  rfl

/-- An independent all-replies frame for the complete source reduction.
It is available on either branch of a larger conjunction, without a No premise. -/
theorem reduction_frame (reductionBodies : SumcheckReductionReference.Bodies model definitions)
    (maximum count : Nat) (bounded : count ≤ maximum)
    (reference : PrefixState (model.Field field) Frame count) :
    PIR.Yields (fun out => ∃ next : PrefixState (model.Field field) Frame 0,
      next.original = reference.original ∧ next.frame = reference.frame ∧
      out = (SumcheckVerifierBodies.reduceReturnValues (encode model 0 next).slots, reference.frame))
      (reduction model definitions protocols ctx handle maximum count reference) := by
  rw [reduction_equation model definitions linked bodies protocols ctx distinct handle reductionBodies
    maximum count bounded]
  exact (RepeatedComponent.frame_repeatN (component (E := Unit) model definitions protocols ctx handle)
    (frame_contract model definitions linked bodies protocols ctx distinct handle reference.original reference.frame)
    count (encode model 0 reference) ⟨reference,rfl,rfl,rfl⟩).bind (by
      intro returned valid
      obtain ⟨next,same,retained,encoded⟩ := valid
      refine ⟨next,same,retained,?_⟩
      rw [encoded]
      rfl)

/-- The terminal predicate retains the complete returned source tuple and the
private frame. It is precisely the family's No, not a new target predicate. -/
def reductionNo (original : List (model.Field field)) (callerFrame : Frame)
    (_history : List E)
    (out : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs × Frame) : Prop :=
  ∃ reference : PrefixState (model.Field field) Frame 0,
    reference.original = original ∧ reference.frame = callerFrame ∧
      out = (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots, callerFrame) ∧
      (layout model).representation.No reference

def reduction_no {P : Type} {Raw : E → Type}
    (reductionBodies : SumcheckReductionReference.Bodies model definitions)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw) (escape : EscapeJudgment E Raw)
    (original : List (model.Field field)) (callerFrame : Frame)
    (steps : RepeatedComponent.NoContract (component model definitions protocols ctx handle)
      absorb escape (no model (Frame := Frame) original callerFrame))
    (maximum count : Nat) (bounded : count ≤ maximum)
    (reference : PrefixState (model.Field field) Frame count)
    (same : reference.original = original) (retained : reference.frame = callerFrame)
    (wrong : (layout model).representation.No reference) (history : List E) :
    Derivation absorb escape (reductionNo model original callerFrame) history
      (reduction model definitions protocols ctx handle maximum count reference) := by
  rw [reduction_equation model definitions linked bodies protocols ctx distinct handle reductionBodies maximum count bounded]
  exact (no_repeat model definitions protocols ctx handle original callerFrame absorb escape steps
    count history (encode model 0 reference) ⟨reference,same,retained,rfl,wrong⟩).bind _ (by
      intro reached returned valid
      apply Derivation.done
      obtain ⟨next, sameNext, retainedNext, encoded, wrongNext⟩ := valid
      refine ⟨next,sameNext,retainedNext,?_,wrongNext⟩
      rw [encoded, retained]
      rfl)

/-- Successful reduction returns the same complete tuple and private frame,
and the terminal reference is true. Rejection cannot discharge this predicate. -/
def reductionYes (original : List (model.Field field)) (callerFrame : Frame)
    (out : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs × Frame) : Prop :=
  ∃ reference : PrefixState (model.Field field) Frame 0,
    reference.original = original ∧ reference.frame = callerFrame ∧
      out = (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots, callerFrame) ∧
      (layout model).representation.Yes reference

/-- A caller can retain its handler synchronization predicate through the final
pure source return. The continuation sees the complete runtime and history. -/
theorem reduction_honest_preserving {H : Type}
    (reductionBodies : SumcheckReductionReference.Bodies model definitions)
    (original : List (model.Field field)) (callerFrame : Frame)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract (component model definitions protocols ctx handle) handler
      (honest model good original callerFrame))
    (maximum count : Nat) (bounded : count ≤ maximum)
    (reference : PrefixState (model.Field field) Frame count) (history : List E) (h : H)
    (initial : honest model good original callerFrame history count (encode model 0 reference) h)
    (post : (Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs × Frame) → H → List E → Prop)
    (finish : ∀ reached runtime final, honest model good original callerFrame reached 0 runtime final →
      post (SumcheckVerifierBodies.reduceReturnValues runtime.slots, reference.frame) final reached) :
    PIR.WeakestPrecondition.satisfies
      ((reduction model definitions protocols ctx handle maximum count reference).run handler h)
      post (fun _ _ _ => False) history := by
  rw [reduction_equation model definitions linked bodies protocols ctx distinct handle reductionBodies maximum count bounded]
  apply PIR.WeakestPrecondition.successful_bind _ _ _ _ _ _ _
    (honest_repeat model definitions protocols ctx handle original callerFrame handler good steps
      count history (encode model 0 reference) h initial)
  intro runtime final reached valid
  simpa only [PIR.Process.run, PIR.WeakestPrecondition.satisfies, List.append_nil] using
    finish reached runtime final valid

theorem reduction_honest {H : Type}
    (reductionBodies : SumcheckReductionReference.Bodies model definitions)
    (original : List (model.Field field)) (callerFrame : Frame)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract (component model definitions protocols ctx handle) handler
      (honest model good original callerFrame))
    (maximum count : Nat) (bounded : count ≤ maximum)
    (reference : PrefixState (model.Field field) Frame count) (history : List E) (h : H)
    (initial : honest model good original callerFrame history count (encode model 0 reference) h) :
    PIR.WeakestPrecondition.satisfies
      ((reduction model definitions protocols ctx handle maximum count reference).run handler h)
      (fun returned _ _ => reductionYes model original callerFrame returned)
      (fun _ _ _ => False) history := by
  rw [reduction_equation model definitions linked bodies protocols ctx distinct handle reductionBodies maximum count bounded]
  have returned := honest_repeat model definitions protocols ctx handle original callerFrame handler good steps
    count history (encode model 0 reference) h initial
  rw [PIR.run_bind]
  cases execution : (PIR.repeatN count (step model definitions protocols ctx handle)
      (encode model 0 reference)).run handler h with
  | mk outcome final events =>
    rw [execution] at returned
    cases outcome with
    | stopped reason => exact returned
    | returned value =>
      change honest model good original callerFrame _ 0 value final at returned
      obtain ⟨next,same,retained,encoded,yes,_⟩ := returned
      change reductionYes model original callerFrame _
      obtain ⟨start,startSame,startRetained,startEncoded,_,_⟩ := initial
      have frameEq : reference.frame = callerFrame := by
        have := congrArg Runtime.callerFrame startEncoded
        exact this.trans startRetained
      refine ⟨next,same,retained,?_,yes⟩
      rw [encoded,frameEq]
      rfl

theorem reduction_cost {P : Type} {Raw : E → Type}
    (reductionBodies : SumcheckReductionReference.Bodies model definitions)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (charge : List E → E → ENNReal) (cuts : SourceRound.Cuts model absorb ctx handle)
    (boundaries : Boundaries model absorb ctx) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error)
    (maximum count : Nat) (bounded : count ≤ maximum)
    (reference : PrefixState (model.Field field) Frame count) (history : List E) :
    ZkcSecurity.FiatShamir.Typed.ChargedCostBound absorb charge
      (reduction model definitions protocols ctx handle maximum count reference) history (count • error) := by
  rw [reduction_equation model definitions linked bodies protocols ctx distinct handle reductionBodies maximum count bounded]
  apply (ZkcSecurity.FiatShamir.CostComposition.map_iff _ _ _).mpr
  exact cost_repeat model definitions linked bodies protocols ctx distinct handle reference.original reference.frame
    absorb charge cuts boundaries error price count history (encode model 0 reference) ⟨reference,rfl,rfl,rfl⟩

end ZkcSecurity.Families.Sumcheck.SourceIteration
