module

meta import Lean.Elab.Tactic

/-! A control of the audit, in no library: a theorem of `False` whose proof is `True.intro`,
stored without the kernel's check (`debug.skipKernelTC`). Read from its file, it is a theorem
like any other, with no axiom; only its replay through the kernel refuses it. The audit must
refuse this module. -/

open Lean Elab Tactic

namespace Zkc.Tools.Audit.Controls

set_option debug.skipKernelTC true in
/-- `False`, with a proof of `True` put in place of the goal. -/
public theorem unchecked : False := by
  run_tac do (← getMainGoal).assign (mkConst ``True.intro)

end Zkc.Tools.Audit.Controls
