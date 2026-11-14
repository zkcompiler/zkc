module

/-! A control of the audit, in no library: a definition that carries `@[extern]`, so that its
compiled code is not its definition but a function of Lean's runtime. The audit must refuse this
module. -/

namespace Zkc.Tools.Audit.Controls

/-- The sum of two numbers, compiled to the runtime's addition. -/
@[extern "lean_nat_add"]
public def externalAdd (left right : @& Nat) : Nat := left + right

end Zkc.Tools.Audit.Controls
