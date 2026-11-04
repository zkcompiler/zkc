module

public import Zkc.Source.Structured.DomainEvaluation

@[expose] public section

/-! Install complete callback equations at counted-loop occurrences. The source
and placed callbacks may have different process presentations. Their equation
retains every returned capture, call continuation and stopping branch; the
existing finite fold remains the only loop semantics.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation

variable {carriers : Carriers} {I : PIR.Signature} {state captures : List Ty}

/-- Complete callback equality transports a loop without assumptions on replies,
successful returns or capture preservation. The caller supplies an equation of
the actual placed callback, not a name or a matching ABI. -/
theorem denoteLoopOn_callback_eq
    (source placed : RegionFunction carriers.Value I
      (.index :: (state ++ captures), state ++ captures))
    (eq_process : ∀ arguments, source arguments = placed arguments)
    (lower upper : Nat) (initial : Values carriers.Value state)
    (captured : Values carriers.Value captures) :
    denoteLoopOn state captures placed lower upper initial captured =
      denoteLoopOn state captures source lower upper initial captured := by
  simp only [denoteLoopOn, invokeCallbackOn, eq_process]

/-- A source equation and its mathematical invariant are separate obligations.
Both need hold only at reached indices and states. The invariant specifies the
complete callback return, including every capture; projecting the loop state
alone cannot establish it. This specializes the existing indexed finite fold.
-/
theorem denoteLoopOn_states_of_equation
    (source placed : RegionFunction carriers.Value I
      (.index :: (state ++ captures), state ++ captures))
    (count : Nat) (initial : Values carriers.Value state)
    (captured : Values carriers.Value captures) (states : Nat → Values carriers.Value state)
    (start : states 0 = initial)
    (eq_process : ∀ index, index < count →
      source (.cons index ((states index).append captured)) =
        placed (.cons index ((states index).append captured)))
    (law : ∀ index, index < count →
      source (.cons index ((states index).append captured)) =
        .done ((states (index + 1)).append captured)) :
    denoteLoopOn state captures placed 0 count initial captured = .done (states count) := by
  rw [← start]
  simp only [denoteLoopOn, Finite.execute, Finite.Domain.admit, Finite.admitThen,
    Nat.sub_zero]
  have folded := Finite.fold_range_state
    (fun current index => (invokeCallbackOn placed (.cons index (current.append captured))).bind
      fun results => .done (results.split state).1) states 0 count (by
        intro index _ upper
        rw [invokeCallbackOn, ← eq_process index (by omega), law index (by omega)]
        simp only [PIR.Process.bind, Values.split_append])
  simpa using folded

end Zkc.Source.Structured.Evaluation
