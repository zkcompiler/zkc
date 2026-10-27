module

public import ZkcExamples.Construction.GkrDomainRounds

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainLoops
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol GkrDomainRounds
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Continue a certified loop at every nominal returned suffix and exact
carried ABI. The projection is used only in the source history. -/
def bind_point {A B : Type} {outer : Env (F := F) (G := G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G)) (List F × Hist (F := F) (G := G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Env (F := F) (G := G))}
    {sourceNext : (List F × Hist (F := F) (G := G)) → PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Env (F := F) (G := G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (AppendReturns PointReturns outer) (fun _ _ => True) source target)
    (next : ∀ (point : List F) (suffix : Hist (F := F) (G := G)), Original.Simulation relation (fun _ _ => True)
      (sourceNext (point, history suffix)) (targetNext (outer ++ pointValues point suffix))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨carried, ⟨point, suffix, rfl, rfl⟩, rfl⟩ := related
  exact ⟨next point suffix⟩

/-- Continue a certified loop at every nominal returned suffix and exact
carried ABI. The projection is used only in the source history. -/
def bind_round {A B : Type} {outer : Env (F := F) (G := G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G)) ((List F × F) × Hist (F := F) (G := G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Env (F := F) (G := G))}
    {sourceNext : ((List F × F) × Hist (F := F) (G := G)) → PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Env (F := F) (G := G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (AppendReturns RoundReturns outer) (fun _ _ => True) source target)
    (next : ∀ (point : List F) (claim : F) (suffix : Hist (F := F) (G := G)), Original.Simulation relation (fun _ _ => True)
      (sourceNext ((point, claim), history suffix)) (targetNext (outer ++ roundValues point claim suffix))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨carried, ⟨point, claim, suffix, rfl, rfl⟩, rfl⟩ := related
  exact ⟨next point claim suffix⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem point_sorts (source : List F × Hist (F := F) (G := G)) (actual : Env (F := F) (G := G))
    (related : PointReturns source actual) :
    Domain.sortsMatch [.data (.vector "bls12-381.fr"), .transcript context.suite] actual = true := by
  obtain ⟨point, suffix, _, rfl⟩ := related
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem round_sorts (source : (List F × F) × Hist (F := F) (G := G)) (actual : Env (F := F) (G := G))
    (related : RoundReturns source actual) :
    Domain.sortsMatch [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
      .transcript context.suite] actual = true := by
  obtain ⟨point, claim, suffix, _, rfl⟩ := related
  rfl

/-- The complete output loop, with its exact captures, yields and bound refusal. -/
def output_loop (outer : Env (F := F) (G := G)) (length : outer.length = 35)
    (handle bound : Nat) (point : List F) (suffix : Hist (F := F) (G := G))
    (foundCount : outer[6]? = some (.data (.index bound)))
    (foundInitial : Domain.read outer [34, 7] = some (pointValues point suffix)) :
    Original.Simulation (AppendReturns PointReturns outer) (fun _ _ => True)
      (SourceProcess.sourceView context (output {} handle bound point) (history suffix))
      ((Domain.View.loop 4 [45, 44] 6 [34, 7] [.data (.vector "bls12-381.fr"), .transcript context.suite]
        (View.output (ringModel F G) program context) outer).interpret operations) := by
  have certificate := loop_binding PointReturns (fun state _ => GkrVerifier.outputRound {} handle state)
    (View.output (ringModel F G) program context) outer [45, 44] [.data (.vector "bls12-381.fr"), .transcript context.suite]
    (fun state carried index related => by
      apply Classical.choice
      obtain ⟨point, suffix, rfl, rfl⟩ := related
      exact ⟨output_step outer length handle index point suffix⟩)
    point_sorts bound 6 [34, 7] point suffix (pointValues point suffix)
    foundCount foundInitial ⟨point, suffix, rfl, rfl⟩
  simpa only [output, List.range_eq_range', Finite.fold_range_repeatN] using certificate

/-- The complete left loop, with its exact captures, yields and bound refusal. -/
def left_loop (outer : Env (F := F) (G := G)) (length : outer.length = 50)
    (layerIndex : Nat) (layerFound : outer[40]? = some (.data (.index layerIndex)))
    (handle bound : Nat) (pending : List F) (claim : F) (suffix : Hist (F := F) (G := G))
    (foundCount : outer[6]? = some (.data (.index bound)))
    (foundInitial : Domain.read outer [48, 49, 43] = some (roundValues pending claim suffix)) :
    Original.Simulation (AppendReturns RoundReturns outer) (fun _ _ => True)
      (SourceProcess.sourceView context (rounds (GkrVerifier.leftContext {}) handle bound pending claim) (history suffix))
      ((Domain.View.loop 4 [82, 86, 81] 6 [48, 49, 43] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript context.suite]
        (View.left (ringModel F G) program context) outer).interpret operations) := by
  have certificate := loop_binding RoundReturns (fun state _ => GkrVerifier.round (GkrVerifier.leftContext {}) handle state)
    (View.left (ringModel F G) program context) outer [82, 86, 81] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript context.suite]
    (fun state carried index related => by
      apply Classical.choice
      obtain ⟨point, claim, suffix, rfl, rfl⟩ := related
      exact ⟨left_step outer length layerIndex layerFound handle index point claim suffix⟩)
    round_sorts bound 6 [48, 49, 43] (pending, claim) suffix (roundValues pending claim suffix)
    foundCount foundInitial ⟨pending, claim, suffix, rfl, rfl⟩
  simpa only [rounds, GkrVerifier.rounds, List.range_eq_range', Finite.fold_range_repeatN] using certificate

/-- The complete right loop, with its exact captures, yields and bound refusal. -/
def right_loop (outer : Env (F := F) (G := G)) (length : outer.length = 57)
    (layerIndex : Nat) (layerFound : outer[40]? = some (.data (.index layerIndex)))
    (handle bound : Nat) (pending : List F) (claim : F) (suffix : Hist (F := F) (G := G))
    (foundCount : outer[6]? = some (.data (.index bound)))
    (foundInitial : Domain.read outer [55, 56, 52] = some (roundValues pending claim suffix)) :
    Original.Simulation (AppendReturns RoundReturns outer) (fun _ _ => True)
      (SourceProcess.sourceView context (rounds (GkrVerifier.rightContext {}) handle bound pending claim) (history suffix))
      ((Domain.View.loop 4 [89, 93, 88] 6 [55, 56, 52] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript context.suite]
        (View.right (ringModel F G) program context) outer).interpret operations) := by
  have certificate := loop_binding RoundReturns (fun state _ => GkrVerifier.round (GkrVerifier.rightContext {}) handle state)
    (View.right (ringModel F G) program context) outer [89, 93, 88] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript context.suite]
    (fun state carried index related => by
      apply Classical.choice
      obtain ⟨point, claim, suffix, rfl, rfl⟩ := related
      exact ⟨right_step outer length layerIndex layerFound handle index point claim suffix⟩)
    round_sorts bound 6 [55, 56, 52] (pending, claim) suffix (roundValues pending claim suffix)
    foundCount foundInitial ⟨pending, claim, suffix, rfl, rfl⟩
  simpa only [rounds, GkrVerifier.rounds, List.range_eq_range', Finite.fold_range_repeatN] using certificate

/-- The complete coefficient loop, with its exact captures, yields and bound refusal. -/
def coefficient_loop (outer : Env (F := F) (G := G)) (length : outer.length = 72)
    (layerIndex : Nat) (layerFound : outer[40]? = some (.data (.index layerIndex)))
    (bound : Nat) (point : List F) (suffix : Hist (F := F) (G := G))
    (foundCount : outer[6]? = some (.data (.index bound)))
    (foundInitial : Domain.read outer [71, 69] = some (pointValues point suffix)) :
    Original.Simulation (AppendReturns PointReturns outer) (fun _ _ => True)
      (SourceProcess.sourceView context (coefficients {} bound point) (history suffix))
      ((Domain.View.loop 4 [80, 79] 6 [71, 69] [.data (.vector "bls12-381.fr"), .transcript context.suite]
        (View.coefficient (ringModel F G) program context) outer).interpret operations) := by
  have certificate := loop_binding PointReturns (fun state _ => GkrVerifier.lineCoefficient {} state)
    (View.coefficient (ringModel F G) program context) outer [80, 79] [.data (.vector "bls12-381.fr"), .transcript context.suite]
    (fun state carried index related => by
      apply Classical.choice
      obtain ⟨point, suffix, rfl, rfl⟩ := related
      exact ⟨coefficient_step outer length layerIndex layerFound index point suffix⟩)
    point_sorts bound 6 [71, 69] point suffix (pointValues point suffix)
    foundCount foundInitial ⟨point, suffix, rfl, rfl⟩
  simpa only [coefficients, List.range_eq_range', Finite.fold_range_repeatN] using certificate

end ZkcExamples.Construction.GkrDomainLoops
