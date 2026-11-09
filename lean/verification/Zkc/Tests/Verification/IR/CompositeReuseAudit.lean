import Zkc.Tests.Verification.IR.CompositeReuse
import Zkc.Tools.Program.DeclarationAudit

/-! Audit every declaration in the selected source and contract modules,
including generated/private declarations and opaque proof bodies. -/
run_cmd ZkcTools.DeclarationAudit.check [`Zkc.Tests.IR.Generated.CompositeReuseData, `Zkc.Tests.IR.Generated.CompositeReuseBodies, `Zkc.Tests.IR.CompositeReuseSource, `Zkc.Tests.IR.CompositeReuseBodies, `Zkc.Tests.Verification.IR.CompositeReuseContracts, `Zkc.Tests.Verification.IR.CompositeReuse] "COMPOSITE-REUSE-AUDIT-PASS" true
