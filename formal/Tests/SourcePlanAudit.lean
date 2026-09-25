import Tests.SourcePlan
import Tests.PhaseAdmission
import Zkc.Compiler.Bounds
import Tools.DeclarationAudit

-- Audit all stored declarations in the selected imported module families.
run_cmd Tools.DeclarationAudit.check [`Zkc, `Tests.SourcePlan, `Tests.PhaseAdmission] "SOURCE-PLAN-AUDIT-PASS"
