module

public import Zkc.Protocol.Components.Installation
public import Zkc.Protocol.Internal.Representation

/-! Total state representations preserve complete outcome and event laws. -/

public section
open PIR MeasureTheory ProbabilityTheory PFunctor

namespace ProtocolProof.Representation

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableEq T]

theorem measurable_graph (encode : S → T) (hencode : Measurable encode) :
    MeasurableSet {state : S × T | encode state.1 = state.2} :=
  Internal.Representation.measurable_graph encode hencode

theorem initial_of_map (μ : Measure S) (encode : S → T) (hencode : Measurable encode) :
    ExpectationWP.CouplingPost μ (μ.map encode) (fun s t ↦ encode s = t) :=
  Internal.Representation.initial_of_map μ encode hencode

theorem initial_of_map_eq (μ : Measure S) (ν : Measure T)
    (encode : S → T) (hencode : Measurable encode) (hcoverage : μ.map encode = ν) :
    ExpectationWP.CouplingPost μ ν (fun s t ↦ encode s = t) :=
  Internal.Representation.initial_of_map_eq μ ν encode hencode hcoverage

/-- A map on complete accumulated state installs outcome-valued operation kernels. -/
noncomputable def contractOfMap {I : Signature} {S T L M : Type}
    [∀ op, MeasurableSpace (I.Reply op)]
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace L] [MeasurableSpace M]
    [MeasurableEq (T × List M)]
    (actual : (op : I.Op) → Kernel (S × List L) (Outcome (I.Reply op) × (S × List L)))
    (model : (op : I.Op) → Kernel (T × List M) (Outcome (I.Reply op) × (T × List M)))
    (encode : (S × List L) → (T × List M)) (hencode : Measurable encode)
    (hlocal : ∀ op s, (actual op s).map (fun out ↦ (out.1, encode out.2)) =
      model op (encode s)) :
    KernelHandler.CouplingContract (P := Internal.effects I) actual model (fun s t ↦ encode s = t) :=
  Internal.Representation.contractOfMap (P := Internal.effects I) actual model encode hencode hlocal

end ProtocolProof.Representation
