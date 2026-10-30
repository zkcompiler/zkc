import TestsSecurity.LibraryImports
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [`ZkcSecurity, `TestsSecurity, `ZkcSecurityExamples, `ZkcSecurityTools] "SECURITY-AUDIT-PASS"
run_cmd ZkcTools.DeclarationAudit.checkRegistry ZkcSecurity.Registry.audited [`ZkcSecurity, `ZkcSecurityTools, `ZkcSecurityExamples] "REGISTRY-AUDIT-PASS"
