module

public import ZkcSecurity.Bindings.Sumcheck.SourcePairRound
public import ZkcSecurity.Bindings.Sumcheck.SourceProducerReduction
public import ZkcSecurity.Bindings.Sumcheck.SourceReduction

@[expose] public section

/-! Full paired source repetition with a shared mathematical prefix state.
The relation retains every source slot and an arbitrary caller frame. This
establishes successful interaction, rather than a validator-handler WP fact.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourcePair
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent
open ZkcSecurity.Source

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

def producerSlots {n : Nat} (state : PrefixState (model.Field field) Frame n) :=
  Prover.state model state.entries n 1 state.point

def validatorSlots {n : Nat} (state : PrefixState (model.Field field) Frame n) :=
  SumcheckReferenceInstallation.state model (some state.point) (some state.scalar)

def invariant (original : List (model.Field field)) (callerFrame : Frame) (n : Nat)
    (p v : Values (Component model.Value) SumcheckVerifierBodies.repeatState) : Prop :=
  ∃ state : PrefixState (model.Field field) Frame n,
    state.original = original ∧ state.frame = callerFrame ∧
    state.scalar = state.entries.sum ∧ state.entries.length < indexLimit ∧ n < 64 ∧
    p = producerSlots model state ∧ v = validatorSlots model state

omit fieldLaw in
theorem mask_producer (ctx : ProtocolContext) (maximum : Nat)
    (xs : List (model.Field field)) (n : Nat) (point : List (model.Field field)) :
    maskValues (ctx.roles 0) (ctx.mapScopes (SumcheckVerifierBodies.repeatSpec maximum).stateScopes)
      (Prover.state model xs n 1 point) = Prover.state model xs n 1 point := by
  unfold Prover.state
  iterate 7 unfold maskValues
  simp [ProtocolContext.mapScopes, Participant.restrict]

def callback (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (role : Nat) :
    RegionFunction (Component model.Value) (Occurrence.signature model.toCarriers)
      (.index :: (SumcheckVerifierBodies.repeatState ++ [.service "random.bls12-381.fr/0"]),
        SumcheckVerifierBodies.repeatState) := fun args => SumcheckVerifierBodies.roundBody.denote
  (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
    (ctx.roles role) protocols ctx Occurrence.iterations) args.get

def producerStep (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (maximum : Nat) :=
  Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) ctx (ctx.roles 0) (.cons none .nil)
    (callback model definitions protocols ctx 0) (iterations := Occurrence.iterations)
    (site := SumcheckVerifierBodies.repeatSite)

def validatorStep (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (maximum handle : Nat) :=
  Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) ctx (ctx.roles 1) (.cons (some handle) .nil)
    (callback model definitions protocols ctx 1) (iterations := Occurrence.iterations)
    (site := SumcheckVerifierBodies.repeatSite)

theorem step (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinctP : NormalForm.RosterDistinct ctx 0 2)
    (distinctV : NormalForm.RosterDistinct ctx 1 2)
    (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (delivery : (SumcheckRoundNormalForms.challengeSite ctx,
      SumcheckRoundNormalForms.deliverySite ctx) ∈ scope.deliveries)
    (original : List (model.Field field)) (callerFrame : Frame) (maximum handle n index : Nat)
    (p v : Values (Component model.Value) SumcheckVerifierBodies.repeatState)
    (initial : invariant model original callerFrame (n+1) p v) :
    Pair scope (invariant model original callerFrame n)
      (producerStep model definitions protocols ctx maximum p index)
      (validatorStep model definitions protocols ctx maximum handle v index) := by
  obtain ⟨state, same, retained, honest, bounded, small, rfl, rfl⟩ := initial
  unfold producerStep validatorStep Repeat.stepOn producerSlots validatorSlots
  rw [mask_producer model ctx maximum, SourceIteration.mask_state model ctx maximum]
  exact (Pair.within _ index (round model definitions linked bodies protocols ctx distinctP distinctV
    scope roles delivery index handle state bounded small honest)).bind _ _ (by
    intro p v related
    obtain ⟨challenge, rfl, rfl⟩ := related
    apply Pair.done
    refine ⟨state.advance (endpoints model state) challenge, same, retained,
      advance_honest model state challenge, ?_, by omega, ?_, ?_⟩
    · rw [PrefixState.advance_entries]
      exact ReferenceLibrary.Multilinear.restrict_bound model field _ _ bounded
    · exact mask_producer model ctx maximum _ _ _
    · exact SourceIteration.mask_state model ctx maximum _ _)

theorem loop (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinctP : NormalForm.RosterDistinct ctx 0 2)
    (distinctV : NormalForm.RosterDistinct ctx 1 2)
    (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (delivery : (SumcheckRoundNormalForms.challengeSite ctx,
      SumcheckRoundNormalForms.deliverySite ctx) ∈ scope.deliveries)
    (original : List (model.Field field)) (callerFrame : Frame) (maximum handle count start : Nat)
    (p v : Values (Component model.Value) SumcheckVerifierBodies.repeatState)
    (initial : invariant model original callerFrame count p v) :
    Pair scope (invariant model original callerFrame 0)
      (Finite.fold (producerStep model definitions protocols ctx maximum) (List.range' start count) p)
      (Finite.fold (validatorStep model definitions protocols ctx maximum handle) (List.range' start count) v) :=
  Pair.range (invariant model original callerFrame)
    (producerStep model definitions protocols ctx maximum)
    (validatorStep model definitions protocols ctx maximum handle)
    (fun n index p v related => step model definitions linked bodies protocols ctx distinctP distinctV
      scope roles delivery original callerFrame maximum handle n index p v related)
    count start p v initial

#print axioms loop
end ZkcSecurity.Realizations.Sumcheck.SourcePair
