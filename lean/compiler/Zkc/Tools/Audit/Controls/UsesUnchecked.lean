module

import Zkc.Tools.Audit.Controls.Unchecked

/-! A control of the audit, in no library: an ordinary theorem, which the kernel checked when it
was built, whose proof is the theorem of `False` of another module that the kernel never checked
(`Zkc.Tools.Audit.Controls.Unchecked`). Its own declarations replay through the kernel on an
environment that takes the other module as built; the audit must refuse this module audited
alone, since its replay goes through the module that it imports. -/

namespace Zkc.Tools.Audit.Controls

/-- `False`, from the theorem that the kernel never checked. -/
public theorem usesUnchecked : False := unchecked

end Zkc.Tools.Audit.Controls
