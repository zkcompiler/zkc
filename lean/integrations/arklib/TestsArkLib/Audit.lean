import TestsArkLib.LibraryImports
import TestsSecurity.LibraryImports
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [`ZkcArkLib, `TestsArkLib, `ZkcArkLibExamples] "ARKLIB-AUDIT-PASS"
run_cmd ZkcTools.DeclarationAudit.checkRegistry (ZkcSecurity.Registry.audited ++ ZkcArkLib.Registry.audited) [`ZkcArkLib, `ZkcArkLibExamples] "ARKLIB-REGISTRY-AUDIT-PASS"
