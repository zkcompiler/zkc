import Zkc.Source.Mathematical.SubjectAdmission
import Zkc.Source.Mathematical.BlsMeaning

/-! Executable admission and the concrete semantics use the same G1 carrier.

The carrier is a type argument, erased by code generation. Formation needs
neither a primality witness nor a group generator. Group interpretation keeps
those premises explicit, and reuses the admitted header unchanged.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.BlsAdmission
open BlsInstallation Zkc.Algebra.Bls12381

abbrev installed : RegistryAdmission.Contracts Payload := contracts G1Carrier

def admit (source : Raw.Subject) (budget : Nat) :
    Except SubjectAdmission.Error (SubjectAdmission.Admitted installed source) :=
  (SubjectAdmission.admit installed source).run' budget

section Semantics
variable [Fact baseModulus.Prime]

/-- This is the actual admitted header, with no re-elaboration or replacement
program. Generator and native-provider agreement remain caller obligations. -/
noncomputable def interpretation {source : Raw.Subject} (generator : G1)
    (admitted : SubjectAdmission.Admitted installed source) :=
  BlsMeaning.interpretation (model := curveModel generator) admitted.header

theorem lawful {source : Raw.Subject} (generator : G1)
    (admitted : SubjectAdmission.Admitted installed source) :
    (interpretation generator admitted).Lawful :=
  BlsMeaning.lawful (model := curveModel generator) admitted.header

end Semantics
end Zkc.Source.Mathematical.BlsAdmission
