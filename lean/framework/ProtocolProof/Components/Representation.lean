module

public import ProtocolProof.Components.Installation

/-!
# Deterministic state representations

A measurable total state map can identify several concrete states with one mathematical
state. `contractOfMap` constructs the upstream local coupling contract from the equation
that every complete answer-and-successor-state law commutes with that map. Its joint
kernel samples the concrete operation once and pairs its successor with its image. The
two marginal equations and preservation of the graph relation are proved generically.

`initial_of_map` covers every concrete initial state, with the exact model initial law
given by pushforward. `initial_of_map_eq` accepts a separately fixed model law and an
explicit coverage equation. The local law covers all concrete states, including multiple
representatives of the same model state. Measurable equality on the model state makes the
graph measurable.

Operation answers retain their common meaning. A response decoder or other meaning-changing
adapter requires a separate proof of its full pushed-forward answer-and-state law, including
each malformed response and explicit failure outcome, before using this construction.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor

universe uA uB uS uT

namespace ProtocolProof.Representation

variable {S : Type uS} {T : Type uT}
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableEq T]

/-- The graph relation of a measurable total state map is measurable. -/
theorem measurable_graph (encode : S → T) (hencode : Measurable encode) :
    MeasurableSet {state : S × T | encode state.1 = state.2} :=
  measurableSet_eq_fun (hencode.comp measurable_fst) measurable_snd

/-- Pushing the complete initial law forward supplies an exact, graph-supported coupling. -/
theorem initial_of_map (μ : Measure S) (encode : S → T) (hencode : Measurable encode) :
    ExpectationWP.CouplingPost μ (μ.map encode) (fun s t ↦ encode s = t) := by
  refine ⟨⟨μ.map (fun s ↦ (s, encode s)), Measure.IsCoupling.graph μ hencode⟩, ?_⟩
  exact (ae_map_iff (measurable_id.prodMk hencode).aemeasurable
    (measurable_graph encode hencode)).2 (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- A fixed model initial law is covered when it is the entire concrete pushforward. -/
theorem initial_of_map_eq (μ : Measure S) (ν : Measure T)
    (encode : S → T) (hencode : Measurable encode) (hcoverage : μ.map encode = ν) :
    ExpectationWP.CouplingPost μ ν (fun s t ↦ encode s = t) := by
  rw [← hcoverage]
  exact initial_of_map μ encode hencode

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)]

/-- Install a total, possibly non-injective state representation from per-operation laws.
The equation includes the jointly sampled answer and successor state at every concrete state. -/
noncomputable def contractOfMap
    (actual : KernelHandler P S) (model : KernelHandler P T)
    (encode : S → T) (hencode : Measurable encode)
    (hlocal : ∀ a s, (actual a s).map (fun out ↦ (out.1, encode out.2)) =
      model a (encode s)) :
    KernelHandler.CouplingContract actual model (fun s t ↦ encode s = t) where
  joint a := ((actual a).comap Prod.fst measurable_fst).map
    (fun out ↦ (out.1, (out.2, encode out.2)))
  measurable_relation := measurable_graph encode hencode
  map_left a state _ := by
    have hgraph : Measurable (fun out : P.B a × S ↦ (out.1, (out.2, encode out.2))) :=
      measurable_fst.prodMk (measurable_snd.prodMk (hencode.comp measurable_snd))
    rw [Kernel.map_apply _ hgraph, Kernel.comap_apply,
      Measure.map_map (measurable_fst.prodMk measurable_snd.fst) hgraph]
    exact Measure.map_id
  map_right a state hstate := by
    have hgraph : Measurable (fun out : P.B a × S ↦ (out.1, (out.2, encode out.2))) :=
      measurable_fst.prodMk (measurable_snd.prodMk (hencode.comp measurable_snd))
    rw [Kernel.map_apply _ hgraph, Kernel.comap_apply,
      Measure.map_map (measurable_fst.prodMk measurable_snd.snd) hgraph]
    change (actual a state.1).map (fun out ↦ (out.1, encode out.2)) = model a state.2
    rw [← hstate]
    exact hlocal a state.1
  invariant a state _ := by
    have hgraph : Measurable (fun out : P.B a × S ↦ (out.1, (out.2, encode out.2))) :=
      measurable_fst.prodMk (measurable_snd.prodMk (hencode.comp measurable_snd))
    rw [Kernel.map_apply _ hgraph, Kernel.comap_apply]
    exact (ae_map_iff hgraph.aemeasurable
      ((measurable_graph encode hencode).preimage measurable_snd)).2
      (Filter.Eventually.of_forall fun _ ↦ rfl)

end ProtocolProof.Representation
