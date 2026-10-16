import Zkc.Source.Structured.Participant
import Lean

/-! Check the actual imported module closure of the generic semantic consumer.
Keep this separate from tests that intentionally import source admission. -/

run_cmd do
  let env ← Lean.getEnv
  for forbidden in [ `Zkc.Source.Structured.Format, `Zkc.Source.Structured.Admission,
      `Zkc.Source.Structured.PreparationAdmission, `Zkc.Source.Structured.Checked ] do
    if env.header.modules.any (·.module == forbidden) then
      throwError "structured semantics imports admission module {forbidden}"

open Zkc.Source Zkc.Source.Structured

-- Formed protocol evidence and its exact-body law remain available to consumers.
example (protocol : CheckedProtocol) : protocol.body.erase = protocol.raw := protocol.exactBody
example (definition : CheckedDefinition) : definition.body.erase = definition.raw := definition.exactBody
