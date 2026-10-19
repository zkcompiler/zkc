import TestsSecurity.LibraryImports
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [`ZkcSecurity, `TestsSecurity] "SECURITY-AUDIT-PASS"
run_cmd ZkcTools.DeclarationAudit.checkRegistry ZkcSecurity.Registry.audited [`ZkcSecurity] "REGISTRY-AUDIT-PASS"
