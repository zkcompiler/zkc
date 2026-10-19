import Zkc.Source.DeriveRegion
import Tests.RegionDerivation

namespace Tests.DeriveRegionCallbacks
open Zkc.Source PIR Tests.RegionDerivation

/-- Existing callback source is traversed, including its stopping branch. -/
theorem callbacks : Regions.Derivation source lower controls controlProcesses := by
  derive_region using (fail "no operation in these callbacks")

/-- The same local translation law handles effects, lexical binds and callbacks.
This existing toy subject tests traversal; it is not a maintained-source claim. -/
theorem nested (selected : Bool) :
    Derives (schnorr selected) empty (schnorrProcess selected) := by
  derive_region using (exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl)

/-- The count stays symbolic. The proof reuses the existing local repeat law;
no repeated source graph or count-specific unfolding is generated. -/
theorem symbolic_repeat (count claim : Nat) :
    Derives (sumcheck count) (Values.cons claim .nil).get (sumcheckProcess count claim) := by
  derive_region using (exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl)

/-- A structurally stopped lexical prefix does not request suffix laws. -/
theorem stopped_bind :
    Derives (Region.bind (Region.stop (out := []) .abort) (schnorr true)) empty
      (.halt .abort) := by
  derive_region using (fail "unreachable operation")

private def guardedDraw : Region dialect [Ty.scalar, Ty.scalar, Ty.scalar] [Ty.scalar] :=
  .letOp .guard (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    .nil (.letOp .draw .nil .nil (.ret (.cons .here .nil)))

/-- A locally proved stop also avoids the unreachable draw obligation. -/
theorem stopped_operation :
    Derives guardedDraw (Values.cons (0 : Nat) (.cons (1 : Nat) (.cons (1 : Nat) .nil))).get
      (.halt .reject) := by
  derive_region using (
    exact RegionMeaning.OperationLaw.ofTranslation translation .guard _ _ rfl)

end Tests.DeriveRegionCallbacks
