import Zkc.Tests.IR.Core.Controls
import Zkc.Tools.Verification.CoreConstruction

/-! Controls for the control operations of a side: a `branch`, a `repeat` whose body draws, a
count above the maximum, and a function with a `loop`. -/

set_option autoImplicit false
set_option experimental.vcgen true

open PIR Zkc.Source Zkc.Core Zkc.Core.Transcript Std.WP ProtocolProof
open ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open Zkc.Tests.Core.Controls

namespace Zkc.Tests.Verification.Core.Regions

variable (M : Model) [Sampling M]

/-- The exact reading. No side below samples a secret. -/
noncomputable abbrev logic :
    WPMonad (Process (Effects M)) (Assert (Event M.Value)) (StopAssert (Event M.Value)) :=
  chargedMonad (interface .refused) exactEscape exactEscape_antitone

attribute [local instance] logic

/-- The verifier's side of `agreement`: the `branch` receives one value when the verifier's
condition holds, and the `repeat` draws once per iteration. Every returning run appends that
many events; the only stop is `refused`, for a count above the maximum of the `repeat`. The
verifier is the one participant in the side, so its own copies decide and the side never stops
`incomplete`. -/
theorem verifier_counts (condition : Bool) (count : Nat) (start : List (Event M.Value)) :
    ⦃fun history => ⟨history = start⟩⦄
      agreement.agreement.meaning M verifier
        (.cons () (.cons condition (.cons () (.cons count .nil))))
    ⦃fun _ history => ⟨history.length = start.length + (if condition then 1 else 0) + count⟩;
      estack⟨fun reason _ => ⟨reason = .refused ∧ 8 < count⟩⟩⦄ := by
  open_core_definition
  construct_region with_invariants [fun remaining _ => fun history =>
    ⟨history.length + remaining = start.length + (if condition then 1 else 0) + count⟩]
  -- An iteration draws once.
  · intro holds raw value _
    have counted : List.length _ + (_ + 1) = _ := holds
    show (_ ++ [_]).length + _ = _
    rw [List.length_append, List.length_singleton]
    omega
  -- The condition holds: one value is received before the iterations.
  · rintro rfl value
    split
    · show (_ ++ [_]).length + count = _
      simp
    · exact ⟨trivial, by omega⟩
  -- The condition fails: nothing precedes the iterations.
  · intro same
    split
    · show List.length _ + count = _
      have reached : _ = start := same
      simp [reached]
    · exact ⟨trivial, by omega⟩

/-- A function performs no effect: a `loop` leaves the history as it is, and stops `refused`
only for a count above its maximum. -/
theorem accumulate_silent (count first : Nat) (start : List (Event M.Value)) :
    ⦃fun history => ⟨history = start⟩⦄
      locals.accumulate.meaning M (.cons count (.cons first .nil))
    ⦃fun _ history => ⟨history = start⟩;
      estack⟨fun reason _ => ⟨reason = .refused ∧ 16 < count⟩⟩⦄ := by
  open_core_definition
  construct_region with_invariants [fun _ _ => fun history => ⟨history = start⟩]
  exact fun _ => ⟨trivial, by omega⟩

end Zkc.Tests.Verification.Core.Regions

#print axioms Zkc.Tests.Verification.Core.Regions.verifier_counts
#print axioms Zkc.Tests.Verification.Core.Regions.accumulate_silent
