import Tests.LibraryImports
import Tools.DeclarationAudit

run_cmd Tools.DeclarationAudit.check [`Zkc, `Tests, `Examples, `Tools.Interactive, `Tools.Artifact, `Tools.Crypto, `Tools.RequirementChecker] "WHOLE-LIBRARY-AUDIT-PASS"
