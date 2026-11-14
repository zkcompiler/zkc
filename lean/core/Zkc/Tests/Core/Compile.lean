import Zkc.Tests.Core.Declare
import Zkc.Tests.Core.CopiesPremises
import Zkc.Core.Construction

/-! Compilation is one path: no role program comes from a package that admission refuses.

`compile` is admission of the package as a program as written, the construction of the
declared scheme on the admitted package, and projection. Each case below is a package that
elaborates and that one gate of admission refuses; a path that applied the steps to a package
that elaborates, without admission, would print role programs for it.

`fixtures/construction/doubling-undefined.json` is the scheme fixture `doubling` with a
division of zero by zero added at the end of its protocol. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace CompileTests

raw_package doubling from file "fixtures/construction/doubling-frontend-scheme.json"
raw_package undefined from file "fixtures/construction/doubling-undefined.json"
raw_declaration declaration from file "fixtures/construction/doubling-frontend-scheme.declaration.json"

-- The fixture compiles, as an interactive protocol and as its declared scheme.
kernel_refl doubling_roles : (compile doubling).isOk equals true
kernel_refl doubling_compiles : (compile doubling {} (some declaration)).isOk equals true

-- The check of facts. The package elaborates, also as a program as written, and its steps
-- return; admission refuses it, so nothing is compiled from it.
kernel_refl undefined_elaborates : (elaborateWritten undefined).isOk equals true
kernel_refl undefined_not_admitted : (admit undefined).isOk equals false
kernel_refl undefined_no_roles : (compile undefined).isOk equals false
kernel_refl undefined_not_compiled : (compile undefined {} (some declaration)).isOk equals false

/-- One exchange whose only site has the number 7: the sites of a program as written are
numbered without gaps. -/
def gap : Raw.Package := CopiesTests.protocol 2 [⟨.nat, 0⟩] [⟨.nat, 1⟩] [] <|
  .step (.exchange 0 1 7 0) (.ret [1])

-- The order of sites. The package elaborates as what a step returned.
kernel_refl gap_elaborates : (elaborate gap).isOk equals true
kernel_refl gap_not_admitted : (admit gap).isOk equals false
kernel_refl gap_not_compiled : (compile gap).isOk equals false

-- The check of copies. Whether a package is a program as written is not the caller's to
-- state: the package that the check of copies refuses is refused whatever is stated.
kernel_refl apart_admitted_as_stepped :
  (admit CopiesTests.apartChoice { written := false }).isOk equals true
kernel_refl apart_not_compiled :
  (compile CopiesTests.apartChoice { written := false }).isOk equals false

/-- A construction starts from a program as written: a package admitted as what a step
returned is refused. -/
noncomputable def steppedSourceRefused : Bool :=
  match admit doubling { written := false } with
  | .error _ => false
  | .ok source =>
      match constructAdmitted source declaration with
      | .error .stepped => true
      | _ => false

kernel_refl stepped_source_refused : steppedSourceRefused equals true

#print axioms compile_checked

end CompileTests
