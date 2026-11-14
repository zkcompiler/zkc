import Zkc.Tests.Core.Declare
import Zkc.Core.Construction

/-! The construction steps evaluated by the kernel on the fixture `schnorr`.

`fixtures/construction/schnorr.fiat-shamir.json` and `schnorr.serialized.json` are the
output of the compiled tool. The kernel evaluates the same two functions on the typed
package and finds the same raw protocols, and it accepts both outputs as programs. A
step removes sites, so the outputs are not programs as written. The construction on the
admitted package admits what each step returns. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ConstructSchnorr

raw_package raw from file "fixtures/construction/schnorr.json"
raw_declaration declaration from file "fixtures/construction/schnorr.declaration.json"
raw_package constructed from file "fixtures/construction/schnorr.fiat-shamir.json"
raw_package serialized from file "fixtures/construction/schnorr.serialized.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl fiatShamir_eq :
  steppedProtocols typed (fiatShamir typed declaration) equals Except.ok constructed.protocols
kernel_refl serialize_eq :
  steppedProtocols typed (construct typed declaration) equals Except.ok serialized.protocols

kernel_refl constructed_elaborates : (elaborate constructed).isOk equals true
kernel_refl serialized_elaborates : (elaborate serialized).isOk equals true

/-- The construction on the admitted package: the package is admitted as written, and the
package of what each step returns is admitted. -/
noncomputable def admittedAtEachStep : Bool :=
  match admit raw with
  | .error _ => false
  | .ok admitted =>
      match constructAdmitted admitted declaration with
      | .ok _ => true
      | .error _ => false

kernel_refl admitted_at_each_step : admittedAtEachStep equals true

#print axioms fiatShamir_eq
#print axioms serialize_eq

end ConstructSchnorr
