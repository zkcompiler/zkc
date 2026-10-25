import Tests.LibraryImports
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [`Zkc, `Tests, `ZkcExamples, `ZkcTools.CommonSource.Reference, `ZkcTools.JsonSupport, `ZkcTools.ProofAccount, `ZkcTools.StructuredSource, `ZkcTools.ConstructionBindings] "CORE-AUDIT-PASS"
