import ZkcSecurity.VCVio.StructuredUniform
import Lean

/-! The optional uniform adapter needs semantic records, not source admission. -/

run_cmd do
  let env ← Lean.getEnv
  for forbidden in [ `Zkc.Source.Structured.Format, `Zkc.Source.Structured.Admission,
      `Zkc.Source.Structured.PreparationAdmission, `Zkc.Source.Structured.Checked ] do
    if env.header.modules.any (·.module == forbidden) then
      throwError "structured uniform adapter imports admission module {forbidden}"
