module

public import Zkc.IR.Source.Structured.ProtocolAlgebra
public import Zkc.IR.Source.Structured.LoopPresentation

@[expose] public section

/-! Mathematical loop presentations for every instance of the protocol algebra.
The same counted invariant supports concrete and lazy protocol values. Boundary
observations, role masks, bounds and stopped prefixes remain in the resulting process.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured

namespace IterationObservations

/-- A boundary wrapper preserves a pure change of returned representation. -/
theorem within_map {I : PIR.Signature} {A B : Type}
    (observations : IterationObservations I) (site : String) (index : Nat)
    (process : PIR.Process I A) (represent : A → B) :
    observations.within site index (process.bind (fun value ↦ .done (represent value))) =
      (observations.within site index process).bind (fun value ↦ .done (represent value)) := by
  simp only [within_eq, PIR.Process.bind_assoc, PIR.Process.bind]

/-- Boundary handlers may stop. Every returned body value still satisfies its invariant. -/
theorem within_yields {I : PIR.Signature} {A : Type}
    (observations : IterationObservations I) (site : String) (index : Nat)
    {process : PIR.Process I A} {property : A → Prop}
    (preserved : PIR.Yields property process) :
    PIR.Yields property (observations.within site index process) := by
  have all {B : Type} (p : PIR.Process I B) : PIR.Yields (fun _ ↦ True) p := by
    induction p with
    | done => trivial
    | halt => trivial
    | call _ _ ih => exact ih
  rw [within_eq]
  exact (all _).bind fun _ _ ↦ preserved.bind fun value valid ↦
    (all _).bind fun _ _ ↦ valid

end IterationObservations

namespace ProtocolLoopPresentation

/-- The companion supplies a state representation, its invariant and one callback law.
The algebra's iteration wrapper is identified once by its library, independently of the
protocol. The conclusion is an exact free-process equality, before any handlers or
probability distributions are selected. -/
theorem present {V : Ty → Type} {I : PIR.Signature}
    (algebra : ProtocolAlgebra V I) (spec : RepeatSpec) (context : ProtocolContext)
    (self : Nat) (site : String)
    (observations : IterationObservations I)
    (iteration : ∀ {A : Type} (index : Nat) (process : PIR.Process I A),
      algebra.iteration context site index process = observations.within site index process)
    (inside : (spec.roles.map context.roles).contains self = true)
    (captures : Values (Component V) spec.captures)
    (body : RegionFunction (Component V) I (.index :: (spec.state ++ spec.captures), spec.state))
    {S : Type} (embed : Nat → S → Values (Component V) spec.state)
    (invariant : Nat → S → Prop)
    (masked : ∀ index value, maskValues self (context.mapScopes spec.stateScopes)
      (embed index value) = embed index value)
    (reference : S → Nat → PIR.Process I S)
    (count : Nat)
    (equation : ∀ index value, index < count → invariant index value →
      body (.cons (some (algebra.index index)) ((embed index value).append captures)) =
        (reference value index).bind (fun next ↦ .done (embed (index + 1) next)))
    (preserved : ∀ index value, index < count → invariant index value →
      PIR.Yields (invariant (index + 1)) (reference value index))
    (countValue : Component V .index) (decoded : countValue.bind algebra.count = some count)
    (bounded : count ≤ spec.maximum)
    (state : Values (Component V) spec.state) (initial : S)
    (start : maskValues self (context.mapScopes spec.stateScopes) state = embed 0 initial)
    (initialInvariant : invariant 0 initial) :
    algebra.repeatProcess spec context self site countValue state captures body =
      (Finite.fold (fun value index ↦ observations.within site index (reference value index))
        (List.range' 0 count) initial).bind (fun result ↦ .done (embed count result)) := by
  simp only [ProtocolAlgebra.repeatProcess, inside, decoded, bounded, ite_true,
    Finite.execute, Finite.Domain.admit, Finite.admitThen, List.range_eq_range', start]
  let step := fun state index ↦
    (algebra.iteration context site index
      (body (.cons (some (algebra.index index))
        ((maskValues self (context.mapScopes spec.stateScopes) state).append captures)))).bind
      fun results ↦ .done (maskValues self (context.mapScopes spec.stateScopes) results)
  have stepLaw : ∀ index value, index < count → invariant index value →
      step (embed index value) index =
        (observations.within site index (reference value index)).bind
          (fun next ↦ .done (embed (index + 1) next)) := by
    intro index value bound valid
    dsimp only [step]
    rw [masked, equation index value bound valid, iteration,
      IterationObservations.within_map, PIR.Process.bind_assoc]
    simp only [PIR.Process.bind, masked]
  have invariantLaw : ∀ index value, index < count → invariant index value →
      PIR.Yields (invariant (index + 1))
        (observations.within site index (reference value index)) := by
    intro index value bound valid
    exact observations.within_yields site index (preserved index value bound valid)
  simpa only [Nat.zero_add] using LoopPresentation.foldInvariant step
    (fun value index ↦ observations.within site index (reference value index))
    embed invariant count stepLaw invariantLaw 0 count (by omega) initial initialInvariant

end ProtocolLoopPresentation
end Zkc.Source.Structured
