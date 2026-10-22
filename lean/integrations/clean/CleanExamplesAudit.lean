import CleanExamples
import ZkcTools.DeclarationAudit

/-! Audit the standalone source-fixture exporter separately: it and
`TestsClean.Control` both declare `main`, so a combined import is invalid. -/

run_cmd ZkcTools.DeclarationAudit.check [`CleanExamples] "CLEAN-EXAMPLES-AUDIT-PASS"
