module

public import ZkcExamples.Construction.GkrDomainLoopBinding
public meta import Zkc.Construction.ProcessViewTactic

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
noncomputable section
namespace ZkcExamples.Construction.GkrDomainPhaseBinding
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol GkrDomainRounds
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Compose already constructed View blocks, retaining their checkpoints.
This contains no instruction dispatch or operation evaluation. -/
def sequenceBlocks {C : Carriers} (blocks : List (Domain.View.Block C)) : Domain.View.Block C :=
  blocks.foldr Domain.View.sequence Domain.View.empty

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem sequence_interpret (head tail : Domain.View.Block (uniformCarriers F G))
    (env : Env (F := F) (G := G)) :
    ((Domain.View.sequence head tail) env).interpret operations =
      ((head env).interpret operations).bind fun next => (tail next).interpret operations := by
  simp only [Domain.View.sequence, PIR.Process.interpret, operations, PIR.Process.bind,
    PIR.Process.interpret_bind]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem sequenceBlocks_append (left right : List (Domain.View.Block (uniformCarriers F G)))
    (env : Env (F := F) (G := G)) :
    ((sequenceBlocks (left ++ right)) env).interpret operations =
      ((sequenceBlocks left env).interpret operations).bind fun next =>
        (sequenceBlocks right next).interpret operations := by
  induction left generalizing env with
  | nil => simp only [List.nil_append, sequenceBlocks, List.foldr_nil,
      Domain.View.empty, PIR.Process.interpret, PIR.Process.bind]
  | cons head left ih =>
      simp only [List.cons_append, sequenceBlocks, List.foldr_cons,
        sequence_interpret, PIR.Process.bind_assoc]
      congr 1
      funext next
      exact ih next

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem receive_split {A : Type} (site : String) (sender : Nat)
    (next : F → PIR.Process (Actions F G) A) (suffix : Hist (F := F) (G := G)) :
    SourceProcess.sourceView context (.call (.receive (.field "bls12-381.fr") site sender) next) (history suffix) =
      (SourceProcess.sourceView context
        (.call (.receive (.field "bls12-381.fr") site sender) .done) (history suffix)).bind fun result =>
          SourceProcess.sourceView context (next result.1) result.2 := by
  simpa only [PIR.Process.bind] using
    (sourceView_bind context (.call (.receive (.field "bls12-381.fr") site sender) .done) next (history suffix))

def receiveBlock (site : String) (sender : Nat) (template : Template)
    (offset historyRef layerRef roundRef : Nat) : Domain.View.Block (uniformCarriers F G) :=
  Domain.View.sequence (Domain.View.receive site site (context.role sender) (.field "bls12-381.fr") [.data (.field "bls12-381.fr")])
  (Domain.View.sequence (Domain.View.indicesEmpty [.indices])
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 1) layerRef [.indices])
  (Domain.View.sequence (Domain.View.indicesAppend (offset + 2) roundRef [.indices])
  (Domain.View.sequence (Domain.View.observe context context.suite template historyRef offset (offset + 3) [.transcript context.suite])
    Domain.View.empty))))

def receivedHistory (origin : Origin) (suffix : Hist (F := F) (G := G)) (value : F) : Hist (F := F) (G := G) :=
  suffix ++ [.message origin (.field "bls12-381.fr" value)]

def receivedFrame (env : Env (F := F) (G := G)) (layerIndex roundIndex : Nat)
    (origin : Origin) (suffix : Hist (F := F) (G := G)) (value : F) : Env (F := F) (G := G) :=
  env ++ [.data (.field "bls12-381.fr" value), .indices [], .indices [layerIndex],
    .indices [layerIndex, roundIndex], .transcript context.suite (receivedHistory origin suffix value)]

def Received (env : Env (F := F) (G := G)) (layerIndex roundIndex : Nat)
    (origin : Origin) (suffix : Hist (F := F) (G := G))
    (source : F × Hist (F := F) (G := G)) (actual : Env (F := F) (G := G)) : Prop :=
  ∃ value, source = (value, history (receivedHistory origin suffix value)) ∧
    actual = receivedFrame env layerIndex roundIndex origin suffix value

/-- A reached receive/observe phase with both dynamic coordinates. All values
and histories are arbitrary; the two metadata premises concern only this exact
reached occurrence, before any oracle or cache invocation. -/
def receive_binding (site : String) (sender : Nat) (template : Template)
    (offset historyRef layerRef roundRef layerIndex roundIndex : Nat)
    (origin : Origin) (env : Env (F := F) (G := G)) (suffix : Hist (F := F) (G := G))
    (size : env.length = offset)
    (historyFound : env[historyRef]? = some (.transcript context.suite suffix))
    (layerFound : env[layerRef]? = some (.data (.index layerIndex)))
    (roundFound : env[roundRef]? = some (.data (.index roundIndex)))
    (resolved : Domain.templateOrigin context template [layerIndex, roundIndex] = some origin)
    (projected : Origin.withoutCoordinates origin = context.message site sender context.validator) :
    Original.Simulation (Received env layerIndex roundIndex origin suffix) (fun _ _ => True)
      (SourceProcess.sourceView context
        (.call (.receive (.field "bls12-381.fr") site sender) .done) (history suffix))
      ((receiveBlock site sender template offset historyRef layerRef roundRef env).interpret operations) := by
  have hHistory : historyRef < offset := by
    rw [← size]
    exact (List.getElem?_eq_some_iff.mp historyFound).choose
  have hLayer : layerRef < offset := by
    rw [← size]
    exact (List.getElem?_eq_some_iff.mp layerFound).choose
  have hRound : roundRef < offset := by
    rw [← size]
    exact (List.getElem?_eq_some_iff.mp roundFound).choose
  have request : origin.request = none := by
    simpa only [Origin.withoutCoordinates, Context.message, Origin.message] using
      congrArg Origin.request projected
  have historyBounds : ∀ k, historyRef < offset + k := fun k => Nat.lt_of_lt_of_le hHistory (Nat.le_add_right _ _)
  have layerBounds : ∀ k, layerRef < offset + k := fun k => Nat.lt_of_lt_of_le hLayer (Nat.le_add_right _ _)
  have roundBounds : ∀ k, roundRef < offset + k := fun k => Nat.lt_of_lt_of_le hRound (Nat.le_add_right _ _)
  normalize_artifact_operations [resolved, request] unfolding
      [receiveBlock, receivedHistory, SourceProcess.sourceView, SourceProcess.receive,
        operations, event, PIR.Process.interpret, PIR.Process.interpret_bind,
        List.getElem?_append, size, historyFound, layerFound, roundFound,
        Nat.add_sub_cancel_left, Nat.lt_add_one, Nat.lt_succ_self,
        hHistory, hLayer, hRound, historyBounds, layerBounds, roundBounds,
        Nat.add_lt_add_iff_left, Nat.add_sub_add_left, Nat.add_sub_cancel_left,
        Nat.lt_add_of_pos_right, Nat.zero_lt_succ, Nat.sub_self, Nat.add_assoc,
        Nat.lt_irrefl, Nat.not_lt_zero, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        Bool.not_false, Bool.false_eq_true, Ty.isService, Payload.ofValue,
        DomainAdapter.embedPayload, eq_mp_eq_cast, cast_eq]
  apply Original.Simulation.call
  intro answer
  simp only [PIR.Process.bind, event]
  rw [projected]
  apply Original.Simulation.call
  intro ignored
  apply Original.Simulation.done
  unfold Received receivedFrame receivedHistory
  refine Exists.intro answer (And.intro ?_ ?_)
  · simp only [history, List.map_append, List.map_cons, List.map_nil, event, projected]
  · simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Bind a source receive and its checked physical receive/observe phase to
arbitrary continuations. The source transcript is projected before the tail. -/
def receive_continue {A B : Type} {relation : (A × Hist (F := F) (G := G)) → B → Prop}
    (site : String) (sender : Nat) (template : Template)
    (offset historyRef layerRef roundRef layerIndex roundIndex : Nat)
    (origin : Origin) (env : Env (F := F) (G := G)) (suffix : Hist (F := F) (G := G))
    (sourceNext : F → PIR.Process (Actions F G) A)
    (targetNext : Env (F := F) (G := G) → PIR.Process (Domain.effects (uniformCarriers F G)) B)
    (size : env.length = offset)
    (historyFound : env[historyRef]? = some (.transcript context.suite suffix))
    (layerFound : env[layerRef]? = some (.data (.index layerIndex)))
    (roundFound : env[roundRef]? = some (.data (.index roundIndex)))
    (resolved : Domain.templateOrigin context template [layerIndex, roundIndex] = some origin)
    (projected : Origin.withoutCoordinates origin = context.message site sender context.validator)
    (next : ∀ answer, Original.Simulation relation (fun _ _ => True)
      (SourceProcess.sourceView context (sourceNext answer) (history (receivedHistory origin suffix answer)))
      (targetNext (receivedFrame env layerIndex roundIndex origin suffix answer))) :
    Original.Simulation relation (fun _ _ => True)
      (SourceProcess.sourceView context
        (.call (.receive (.field "bls12-381.fr") site sender) sourceNext) (history suffix))
      (((receiveBlock site sender template offset historyRef layerRef roundRef env).interpret operations).bind targetNext) := by
  rw [receive_split]
  apply Original.Simulation.bind
    (receive_binding site sender template offset historyRef layerRef roundRef layerIndex roundIndex
      origin env suffix size historyFound layerFound roundFound resolved projected)
    (by intros; trivial)
  intro source actual related
  unfold Received at related
  obtain ⟨answer, sourceEq, actualEq⟩ := Classical.indefiniteDescription _ related
  subst source actual
  exact next answer

end ZkcExamples.Construction.GkrDomainPhaseBinding
