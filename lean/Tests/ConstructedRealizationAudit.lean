import Zkc.Source.Constructed.Scalar
import Zkc.Protocols.Sumcheck.NativeConstruction
import ZkcTools.DeclarationAudit

/-! Standalone exhaustive audit; aggregate audit roots are owned by integration. -/
run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Source.Constructed.Scalar, `Zkc.Protocols.Sumcheck.NativeConstruction]
    "NATIVE-REALIZATION-AUDIT-PASS" (exactModules := true)
