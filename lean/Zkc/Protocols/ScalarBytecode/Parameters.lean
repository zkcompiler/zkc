import Std

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Parameters
/-- Scalar modulus of the fixed bytecode profile. This declaration alone does not assert primality. -/
def modulus : Nat := 2305843009213697249

/-- The fixed bytecode draw's support cap, distinct from the scalar modulus.
It describes reduction of the first eight digest bytes, not a uniformity law. -/
def challengeBound : Nat := 2305843009213693952

end Zkc.Protocols.ScalarBytecode.Parameters
