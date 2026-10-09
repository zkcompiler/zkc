import Zkc.Probability.UniformIndex
import Tools.DeclarationAudit

set_option autoImplicit false

run_cmd Tools.DeclarationAudit.check [
  `Zkc.Probability.UniformIndex] "UNIFORM-INDEX-AUDIT-PASS" true

#print axioms Zkc.Probability.UniformIndex.word64_exact
#print axioms Zkc.Probability.UniformIndex.word64_three_inexact
