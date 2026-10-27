import Tests.CompositeReuse
import ZkcTools.DeclarationAudit

/-! Audit every declaration in the selected source and contract modules,
including generated/private declarations and opaque proof bodies. -/
run_cmd ZkcTools.DeclarationAudit.check [
  `Tests.Generated.CompositeReuseData, `Tests.Generated.CompositeReuseBodies,
  `Tests.CompositeReuseSource, `Tests.CompositeReuseBodies,
  `Tests.CompositeReuseContracts, `Tests.CompositeReuse] "COMPOSITE-REUSE-AUDIT-PASS" true
