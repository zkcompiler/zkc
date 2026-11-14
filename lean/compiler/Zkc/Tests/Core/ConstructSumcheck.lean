import Zkc.Tests.Core.Declare

/-! The construction steps evaluated by the kernel on the fixture `sumcheck`.

`fixtures/construction/sumcheck.fiat-shamir.json` and `sumcheck.serialized.json` are the
output of the compiled tool. The kernel evaluates the same two functions on the typed
package and finds the same raw protocols, and it accepts both outputs as programs. A
step removes sites, so the outputs are not programs as written. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ConstructSumcheck

raw_package raw from file "fixtures/construction/sumcheck.json"
raw_declaration declaration from file "fixtures/construction/sumcheck.declaration.json"
raw_package constructed from file "fixtures/construction/sumcheck.fiat-shamir.json"
raw_package serialized from file "fixtures/construction/sumcheck.serialized.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl fiatShamir_eq :
  steppedProtocols typed (fiatShamir typed declaration) equals Except.ok constructed.protocols
kernel_refl serialize_eq :
  steppedProtocols typed (construct typed declaration) equals Except.ok serialized.protocols

kernel_refl constructed_elaborates : (elaborate constructed).isOk equals true
kernel_refl serialized_elaborates : (elaborate serialized).isOk equals true

#print axioms fiatShamir_eq
#print axioms serialize_eq

end ConstructSumcheck
