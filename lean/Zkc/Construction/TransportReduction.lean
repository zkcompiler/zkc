module

public meta import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.WHNF

@[expose] public meta section

/-! Scoped definitional reduction of equality transports in constructed views.
Decidable reflection can leave a proof whose type reduces to equality only at
default transparency. The ordinary simplifier's reducible transparency then
leaves that transport inside arithmetic or a Boolean decision. Ask Lean's
recursor reducer to reduce this node; the kernel checks the resulting
definitional equality. An unresolved transport stays intact.
-/
namespace Zkc.Construction
open Lean Meta Simp

simproc_decl reduceTransport (@Eq.rec _ _ _ _ _ _) := fun expression => do
  if let some reduced ← withDefault <| reduceRecMatcher? expression then
    if reduced != expression then return .visit { expr := reduced }
  return .continue

end Zkc.Construction
