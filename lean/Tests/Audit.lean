import Tests.LibraryImports
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [`Zkc, `Tests, `ZkcExamples, `ZkcTools.JsonSupport, `ZkcTools.ProcessView, `ZkcTools.ProofAccount, `ZkcTools.Companions, `ZkcTools.StructuredSource, `ZkcTools.ConstructionBindings] "CORE-AUDIT-PASS"
