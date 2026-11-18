module

import Zkc.Core.Program.Located

/-! A control of the audit, in no library: a module, audited as a module for any dialect, that
imports a module of located types, which imports the module of the vocabulary. The audit must
refuse this module, by the path of imports through the module that it imports. -/
