import ZkcTools.DeclarationAudit

/-! The dependency rule that the generated `TestsClean.Audit` enforces for this
package, evaluated by the kernel on module names. The library may use Clean and
the main zkc library, but never tests, tools, examples or the ArkLib package;
the main library and the ArkLib package may not use this package or Clean. -/

set_option autoImplicit false

namespace TestsClean.AuditRules

open ZkcTools.DeclarationAudit

theorem library_rules :
    permitted `ZkcClean.Native `TestsClean.Bits = false ∧
    permitted `ZkcClean.Native `Tests.Audit = false ∧
    permitted `ZkcClean.Native `ZkcTools.DeclarationAudit = false ∧
    permitted `ZkcClean.Native `ZkcSecurity.Sumcheck = false ∧
    permitted `ZkcClean.Native `Clean.Circuit.Expression = true ∧
    permitted `ZkcClean.Native `Zkc.Relation.AIR = true ∧
    permitted `TestsClean.Bits `ZkcClean.Native = true := by
  decide +kernel

theorem other_owner_rules :
    permitted `Zkc.Relation.AIR `ZkcClean.Native = false ∧
    permitted `Zkc.Relation.AIR `TestsClean.Bits = false ∧
    permitted `Zkc.Relation.AIR `Clean.Circuit.Expression = false ∧
    permitted `ZkcSecurity.Sumcheck `ZkcClean.Native = false ∧
    permitted `ZkcSecurity.Sumcheck `TestsClean.Bits = false := by
  decide +kernel

end TestsClean.AuditRules
