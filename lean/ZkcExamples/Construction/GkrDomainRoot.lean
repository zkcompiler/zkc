module

public import ZkcExamples.Construction.GkrDomainLayer
public meta import Zkc.Construction.ProcessViewTactic
public meta import Mathlib.Tactic.FailIfNoProgress

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace ZkcExamples.Construction.GkrDomainRoot
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol GkrDomainHelpers GkrDomainRounds GkrDomainLoops
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
attribute [local irreducible] PIR.Process.bind SourceProcess.sourceView Domain.callHelper GkrSourceProtocol.helper Domain.View.loop GkrSourceProtocol.output GkrSourceProtocol.layers

theorem context_suite : context.suite = "merlin3.bls12-381.fr64be/0" := rfl

/-- The full layer loop, retaining every arbitrary carried point and claim. -/
def layer_loop (outer : Env (F := F) (G := G)) (length : outer.length = 12)
    (add mul : List F) (count selector width handle : Nat)
    (addFound : outer[2]? = some (.data (.vector "bls12-381.fr" add)))
    (mulFound : outer[3]? = some (.data (.vector "bls12-381.fr" mul)))
    (countFound : outer[4]? = some (.data (.index count)))
    (selectorFound : outer[5]? = some (.data (.index selector)))
    (widthFound : outer[6]? = some (.data (.index width)))
    (point : List F) (claim : F) (suffix : Hist (F := F) (G := G))
    (initialFound : Domain.read outer [9, 11, 10] = some (roundValues point claim suffix)) :
    Original.Simulation (AppendReturns RoundReturns outer) (fun _ _ => True)
      (SourceProcess.sourceView context (layers {} handle selector width count add mul (point, claim)) (history suffix))
      ((Domain.View.loop 4 [51, 50, 49] 4 [9, 11, 10]
        [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript context.suite]
        (Generated.Constructed.GkrValidator.bodyStep3Body (ringModel F G) program context) outer).interpret operations) := by
  have certificate := loop_binding RoundReturns
    (fun state index => layer {} index handle selector width add mul state.1 state.2)
    (Generated.Constructed.GkrValidator.bodyStep3Body (ringModel F G) program context) outer
    [51, 50, 49] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript context.suite]
    (fun source carried index related => by
      apply Classical.choice
      obtain ⟨point, claim, suffix, rfl, rfl⟩ := related
      exact ⟨GkrDomainLayer.layer_step outer length add mul selector width handle index
        addFound mulFound selectorFound widthFound point claim suffix⟩)
    round_sorts count 4 [9, 11, 10] (point, claim) suffix (roundValues point claim suffix)
    countFound initialFound ⟨point, claim, suffix, rfl, rfl⟩
  simpa only [layers, List.range_eq_range'] using certificate

def artifactInputs (inputs outputs add mul : List F) (count selector width : Nat)
    (suffix : Hist (F := F) (G := G)) : Env (F := F) (G := G) :=
  [.data (.vector "bls12-381.fr" inputs), .data (.vector "bls12-381.fr" outputs),
   .data (.vector "bls12-381.fr" add), .data (.vector "bls12-381.fr" mul),
   .data (.index count), .data (.index selector), .data (.index width),
   .transcript context.suite suffix]

def RootReturns (source : Bool × Hist (F := F) (G := G))
    (actual : Domain.Result (uniformCarriers F G)) : Prop :=
  ∃ decision suffix, source = (decision, history suffix) ∧
    actual.values = [.data (.boolean decision), .transcript context.suite suffix]

set_option linter.unusedTactic false in
/-- Complete structural binding of the actual full compiled root. The four
public tables, dimensions, selector, source handle and initial suffix are
unrestricted; stopped helpers and every proof reply remain observable. -/
def participant (inputs outputs add mul : List F) (count selector width handle : Nat)
    (suffix : Hist (F := F) (G := G)) :
    Original.Simulation RootReturns (fun _ _ => True)
      (SourceProcess.sourceView context (verifier inputs outputs add mul count selector width handle) (history suffix))
      ((Domain.participant (ringModel F G) program context artifact
        (artifactInputs inputs outputs add mul count selector width suffix)).interpret operations) := by
  rw [Generated.Constructed.GkrValidator.participant_eq]
  unfold_component_bodies [Generated.Constructed.GkrValidator.view]
  derive_artifact_binding
    [query_binding (F := F) (G := G),
     (fun outer size handle bound point suffix countFound initialFound => bind_point (output_loop (F := F) (G := G) outer size handle bound point suffix countFound initialFound)),
     (fun outer size add mul count selector width handle addFound mulFound countFound selectorFound widthFound point claim suffix initialFound => bind_round (layer_loop (F := F) (G := G) outer size add mul count selector width handle addFound mulFound countFound selectorFound widthFound point claim suffix initialFound)),
     (fun xs point env refs read suffix => GkrDomainHelperCalls.bind_field (GkrDomainHelperCalls.evaluate (F := F) (G := G) xs point env refs read suffix))]
    normalizing (
      repeat' (first
      | (fail_if_no_progress normalize_component_operations [GkrDomainHelperCalls.empty_view,
          Domain.Calculations.fieldEqual (F := F) (G := G)]
        unfolding [verifier, sourceView_bind, SourceProcess.sourceView, PIR.Process.interpret_bind,
          PIR.Process.interpret, operations, artifactInputs, context_suite, fieldResult, pointValues, roundValues,
          Values.get, Generated.Constructed.GkrValidator.inputSorts,
          Generated.Constructed.GkrValidator.outputSorts, Generated.Constructed.GkrValidator.returned])
      | (fail_if_no_progress erw [Domain.Calculations.fieldEqual (F := F) (G := G)])))
    solving (solve
      | (exact True.intro)
      | (simp only [artifactInputs, pointValues, roundValues, Domain.read, List.mapM_cons,
          List.mapM_nil, context_suite, ↓reduceTransport, ite_true, ite_false, Bind.bind, Option.bind, eq_mp_eq_cast, cast_eq, Option.bind_some, Option.pure_def, eq_mp_eq_cast, cast_eq, List.getElem?_cons_zero,
          List.getElem?_cons_succ, List.getElem?_nil, List.length_append,
          List.length_cons, List.length_nil, List.cons_append, List.nil_append, Nat.reduceAdd])
      | (unfold RootReturns; exact ⟨_, _, rfl, rfl⟩))

end ZkcExamples.Construction.GkrDomainRoot
