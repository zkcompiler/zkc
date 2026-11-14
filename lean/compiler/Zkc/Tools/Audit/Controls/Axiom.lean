module

/-! A control of the audit, in no library: a module that states an axiom and proves a theorem
from it. Both are private to the module, so the audit finds them only when it reads what a module
keeps for itself. The audit must refuse this module. -/

namespace Zkc.Tools.Audit.Controls

/-- A false statement, stated as an axiom. -/
axiom unproved : 1 = 2

/-- A theorem proved from the axiom. -/
theorem fromAxiom : 1 = 2 := unproved

end Zkc.Tools.Audit.Controls
