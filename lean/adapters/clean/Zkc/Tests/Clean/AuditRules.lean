import Zkc.Tools.Program.DeclarationAudit

/-! The dependency rule that the generated `TestsClean.Audit` enforces for this
package, evaluated by the kernel on module names. The library may use Clean and
the main zkc library, but never tests, tools, examples or the ArkLib package;
the main library and the ArkLib package may not use this package or Clean. -/

set_option autoImplicit false

namespace TestsClean.AuditRules

open ZkcTools.DeclarationAudit

theorem library_rules :
    permitted `Zkc.Adapters.Clean.Native `Zkc.Tests.Clean.Bits = false ∧
    permitted `Zkc.Adapters.Clean.Native `Zkc.Tests.IR.Audit = false ∧
    permitted `Zkc.Adapters.Clean.Native `Zkc.Tools.Program.DeclarationAudit = false ∧
    permitted `Zkc.Adapters.Clean.Native `Zkc.Protocol.Library.Families.Sumcheck = false ∧
    permitted `Zkc.Adapters.Clean.Native `Clean.Circuit.Expression = true ∧
    permitted `Zkc.Adapters.Clean.Native `Zkc.IR.Relation.AIR = true ∧
    permitted `Zkc.Tests.Clean.Bits `Zkc.Adapters.Clean.Native = true := by
  decide +kernel

theorem other_owner_rules :
    permitted `Zkc.IR.Relation.AIR `Zkc.Adapters.Clean.Native = false ∧
    permitted `Zkc.IR.Relation.AIR `Zkc.Tests.Clean.Bits = false ∧
    permitted `Zkc.IR.Relation.AIR `Clean.Circuit.Expression = false ∧
    permitted `Zkc.Protocol.Library.Families.Sumcheck `Zkc.Adapters.Clean.Native = false ∧
    permitted `Zkc.Protocol.Library.Families.Sumcheck `Zkc.Tests.Clean.Bits = false := by
  decide +kernel

end TestsClean.AuditRules
