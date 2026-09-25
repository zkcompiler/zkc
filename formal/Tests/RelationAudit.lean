import Tests.RelationEncoding
import Tests.RelationSparse
import Tests.RelationAIR
import Tests.AIRPolynomial
import Zkc.Relation.AIR.Embedding
import Tests.MultisetFingerprint
import Tests.AIRProductConnection
import Tests.RelationReference
import Zkc.Relation.Padding
import Tools.DeclarationAudit

set_option autoImplicit false

-- Covers named declarations, private and generated ones included, and their
-- proof bodies. An `example` leaves no constant in the environment, so the
-- anonymous controls in these families are not what this audit inspects.
-- These controls use kernel proofs, including kernel evaluation of fixtures.
run_cmd Tools.DeclarationAudit.check [
  `Zkc.Relation, `Zkc.Algebra.MultisetFingerprint,
  `Tests.RelationEncoding, `Tests.RelationSparse,
  `Tests.RelationAIR, `Tests.AIRPolynomial, `Tests.RelationReference,
  `Tests.MultisetFingerprint, `Tests.AIRProductConnection] "RELATION-AUDIT-PASS"
