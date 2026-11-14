import Zkc.Tests.Core.Check
import Zkc.Core.RoundTrip

/-! Kernel checks for a package with a `choose` of three arms over an arm number and a
`choose` of two arms over a condition, the branch. -/

set_option autoImplicit false

open Zkc.Core

namespace Choose

raw_package raw from file "fixtures/choose.json"

kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

#print axioms elaborate_eq

end Choose
