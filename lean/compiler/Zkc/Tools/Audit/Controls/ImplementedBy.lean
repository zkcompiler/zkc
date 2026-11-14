module

/-! A control of the audit, in no library: a definition that carries `@[implemented_by]`, so that
its compiled code is another definition's. The audit must refuse this module. -/

namespace Zkc.Tools.Audit.Controls

/-- The code that runs for `slowSucc`. -/
def fastSucc (number : Nat) : Nat := number + 1

/-- The successor of a number, compiled to `fastSucc`. -/
@[implemented_by fastSucc]
public def slowSucc (number : Nat) : Nat := number + 1

end Zkc.Tools.Audit.Controls
