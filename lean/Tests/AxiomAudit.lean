import Tests.Execution
import Tests.Composition
import Tests.Source
import Tools.DeclarationAudit

-- Exact module selection for the foundational execution/source controls.
run_cmd Tools.DeclarationAudit.check [
    `Zkc.Semantics.Execution, `Zkc.Semantics.Interaction,
    `Zkc.Semantics.ExecutionPath, `Zkc.Semantics.MonadExecution,
    `Zkc.Semantics.Contracts, `Zkc.Semantics.Boundary,
    `Zkc.Semantics.Continuation, `Zkc.Semantics.ContinuationReport,
    `Zkc.Source.Expressions, `Zkc.Source.Availability, `Zkc.Source.Inputs,
    `Zkc.Source.Closures, `Zkc.Source.Elaboration,
    `Tests.Interaction, `Tests.SessionControls, `Tests.Execution, `Tests.Composition, `Tests.Source] "SEMANTICS-AUDIT-PASS" true
