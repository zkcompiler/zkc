module

public import ZkcFormal.Written.Soundness
public import ZkcFormal.Value

@[expose] public section
set_option autoImplicit false

/-!
The value of a written verifier at a short application, and the installed bound as a statement
about it.

`Soundness.Installed` at a bound says: on every path and every valid verifier input at which the
short application is rejected, against every conforming service, the installed verifier returns
with probability at most the bound. `Soundness.ValueWithin` says: on the same paths and inputs,
the value of the verifier's process (`ZkcFormal.Value`) is at most the bound. They are the same
statement (`installed_iff`). So the installed bounds of a goal are exactly the numbers at or
above the value: a proof that the value is some number proves the least bound, and a number
below the value is no bound.
-/

namespace ZkcFormal.Written.Soundness

open Zkc.Core Zkc.Subject ProbabilisticProcess
open scoped ENNReal

open Goal.Internal

variable {V : Vocabulary} (M : Model V)
variable {pkg : Package V} {scheme : WrittenRoot pkg} (app : ShortApplication scheme)
variable (draws : LawDraws M)

/-- The value of the installed verifier at a path and verifier inputs, for the event that it
returns. -/
noncomputable def verifierValue (path : List Frame)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins) : ℝ≥0∞ :=
  Value.value (lawSamplers M draws) (Permitted M) (fun _ ↦ True)
    (roleMeaning M pkg.installed scheme.entry.member scheme.verifier path xs)

/-- **The value within a bound**: on every path and every valid verifier input at which the
short application is rejected, the value of the installed verifier is at most the bound. -/
def ValueWithin (b : ℝ≥0∞) : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Rejected M app pkg.installed app.relation.member xs → verifierValue M draws path xs ≤ b

/-- **The installed bound is the value.** A bound is installed exactly when the value of the
verifier is within it. -/
theorem installed_iff (b : ℝ≥0∞) : Installed M app draws b ↔ ValueWithin M app draws b :=
  ⟨fun installed path ↦ mapInputs M _ _ _ _ (fun _ h rejected ↦
      Value.value_le_of_returnsWithin _ _ _ _ (h rejected)) (installed path),
    fun within path ↦ mapInputs M _ _ _ _ (fun _ h rejected ↦
      Value.returnsWithin_of_value _ _ _ _ (h rejected)) (within path)⟩

end ZkcFormal.Written.Soundness
