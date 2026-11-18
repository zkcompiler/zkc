import Zkc.Core.Transform.FunctionChecking
import Zkc.Tests.Core.Facts

namespace Zkc.Core.BodyAnalysis.FiniteRefinements
open FactsTests

private def header (upper : Nat) : FnHeader field :=
  ⟨⟨1⟩, [.fin 8], [.fin 9], false, none, ⟨[.below (.arg 0) 4], [.below (.arg 1) upper]⟩⟩

private def widenInput : Region (LocalRaw field) Unit :=
  .mk [0] [.op ⟨1⟩ [1] (widen 8 9) [0]] [1]

/-- Observe successful bounds or the single exit guarantee's verdict after real elaboration. -/
private def check (hdr : FnHeader field) (body : Region (LocalRaw field) Unit) :
    Option (Verdict ⊕ List (Place × Nat)) := do
  let fn ← (typeFn [] hdr body).toOption
  let contracts ← (FunctionContracts.check ([] : List (FnHeader field))).toOption
  match contracts.checkFunction fn with
  | .ok bounds => return .inr bounds
  | .error (.facts (.refused [⟨_, .guarantee, 0, _, verdict, _⟩])) => return .inl verdict
  | .error _ => none

example : verdict [] (header 4) widenInput = accepted := by decide +kernel

theorem wideningPreservesInputBound : check (header 4) widenInput = some (.inr []) := by
  decide +kernel

example : check (header 3) widenInput = some (.inl .unknown) := by decide +kernel

/-- This guard refines the original natural through finToNat, finWiden and natBelow.
The second narrowing needs that refinement on the original input. -/
private def guardedConversions : Region (LocalRaw field) Unit :=
  .mk [0] [
    .op ⟨1⟩ [1] (narrowTo 8) [0],
    .op ⟨2⟩ [2] (widen 8 10) [1],
    .op ⟨3⟩ [3] (toNat 10) [2],
    .op ⟨4⟩ [4] (natural 4) [],
    .op ⟨5⟩ [5] less [3, 4],
    .guard ⟨6⟩ () 5 .reject,
    .op ⟨7⟩ [6] (narrowTo 4) [0],
    .op ⟨8⟩ [7] (widen 4 9) [6]] [7]

private def guardedHeader (upper : Nat) : FnHeader field :=
  ⟨⟨1⟩, [.nat], [.fin 9], true, none, ⟨[.below (.arg 0) 8], [.below (.arg 1) upper]⟩⟩

example : check (guardedHeader 4) guardedConversions = some (.inr []) := by decide +kernel

example : check (guardedHeader 3) guardedConversions = some (.inl .unknown) := by decide +kernel

#print axioms wideningPreservesInputBound
end Zkc.Core.BodyAnalysis.FiniteRefinements
