module

public import Zkc.Tests.Protocol.Construction.AdaptiveSource
public meta import Zkc.Tools.Program.Companions.Goals

/-! Definition and mathematical obligation types precede all companion registrations.
The request fixes the actual meaning, postcondition and bound. A chosen scale determines
only the invariant used to establish that request, never the request itself.
-/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source ProtocolProof Std.WP
open ProtocolProofExamples.AdaptiveChecks ProtocolProofExamples.AdaptiveSource

namespace ProtocolProofExamples.ConstructionChoices

companion_goal Scale for def scale : Nat → ENNReal

def ScaleLaw (e : AdaptiveChecks.Environment) (scale : Scale) : Prop :=
  scale 0 = 1 ∧ ∀ remaining, scale (remaining + 1) = factor e.residual * scale remaining

def Budget (e : AdaptiveChecks.Environment) (count : Nat) (scale : Scale) : Prop :=
  scale count = factor e.residual ^ count

companion_goal ScaleLawTemplate for theorem scaleLaw (e : AdaptiveChecks.Environment)
    (scale : Scale) : ScaleLaw e scale
companion_goal BudgetTemplate for theorem budget (e : AdaptiveChecks.Environment) (count : Nat)
    (scale : Scale) : Budget e count scale

attribute [local instance] upperLogic

/-- The source connection is proved once with a mathematical scale and its laws.
No companion selects a source slot, lexical frame or callback cursor. -/
theorem rounds_from_scale (e : AdaptiveChecks.Environment) (count : Nat) (scale : Scale)
    (law : ScaleLaw e scale) (env : Zkc.Source.Environment (meaning e).Value [.accumulator])
    (value : ENNReal) :
    ⦃OrderDual.toDual (potential (scale count * value) (env .here))⦄
      (AdaptiveSource.rounds count).denote (meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold AdaptiveSource.rounds
  construct_region with_invariants [fun remaining acc =>
    OrderDual.toDual (potential (scale remaining * value) acc)]
  all_goals try simp only [law.1, law.2, one_mul, mul_assoc]
  all_goals exact le_rfl

/-- This endpoint does not permit an invariant to change its advertised error bound. -/
theorem fixed_rounds (e : AdaptiveChecks.Environment) (count : Nat) (scale : Scale)
    (law : ScaleLaw e scale) (budget : Budget e count scale)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (potential (factor e.residual ^ count * value) (env .here))⦄
      (AdaptiveSource.rounds count).denote (meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  rw [← budget]
  exact rounds_from_scale e count scale law env value

end ProtocolProofExamples.ConstructionChoices
