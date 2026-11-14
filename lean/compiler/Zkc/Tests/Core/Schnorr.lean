import Zkc.Tests.Core.Check
import Zkc.Core.RoundTrip

/-! Per-package kernel checks for one fixture.

The kernel evaluates elaboration (`accepted`, `elaborates`). A literal of the typed
package is proposed by walking the kernel's own evaluation (`typed`), and the kernel
compares `elaborate raw` with it (`elaborate_eq`) and `unelaborate typed` with the raw
package (`unelaborate_eq`). The second comparison is the cheaper one, and with the
round-trip theorem it gives the first (`elaborate_of_unelaborate`). -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Schnorr

raw_package raw from file "fixtures/schnorr.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw
kernel_refl elaborated_unelaborate : unelaborate elaborated equals raw

/-- The equation of the per-package check, from the cheaper comparison and the
round-trip theorem. -/
theorem elaborate_of_unelaborate : elaborate raw = .ok typed :=
  unelaborate_eq ▸ elaborate_unelaborate typed

#print axioms elaborate_eq
#print axioms elaborate_of_unelaborate
#print axioms unelaborate_eq

end Schnorr
