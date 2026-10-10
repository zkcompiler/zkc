import Zkc
import Tests.Execution
import Tests.Simulation
import Tests.Interpretation
import Tests.SpecCore
import Tests.Iteration
import Tests.FamilyBoundaries
import Zkc.Source.LocalInputs
import Tools.DeclarationAudit

-- Audit all stored declarations in the selected imported module families.
run_cmd Tools.DeclarationAudit.check [`Zkc, `Tests] "FOUNDATION-AUDIT-PASS"
