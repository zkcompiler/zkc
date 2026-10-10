import Zkc.Protocols.ScalarBytecode.Parameters
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode

instance : NeZero Parameters.modulus := ⟨by decide⟩

/-- The residue ring used by the scalar bytecode model. This definition does not assert primality. -/
abbrev Residue := ZMod Parameters.modulus

end Zkc.Protocols.ScalarBytecode
