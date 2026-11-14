import Zkc.Tests.Core.Check

/-! Kernel checks for a package with `if`, `stop`, `guard`, `block`, `call` and
`branch`. -/

set_option autoImplicit false

open Zkc.Core

namespace Controls

raw_package raw from file "fixtures/controls.json"

kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

kernel_refl elaborated_unelaborate : unelaborate elaborated equals raw

#print axioms accepted
#print axioms elaborated_unelaborate

end Controls
