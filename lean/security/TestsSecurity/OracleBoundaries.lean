import ZkcSecurity.Generation.SigmaCompleteness

/-! Generator refusal is distinct from decoding a logical oracle type. -/
open Zkc.Source.Structured ZkcSecurity.Generation.SigmaCompleteness
private def tableKind : OracleKind := .table (.field "scalar") none
#guard zeroInput (.oracle tableKind) == .error "sigma-completeness-oracle-type"
#guard zeroInput (.oracleSequence tableKind 8) == .error "sigma-completeness-oracle-type"
#guard zeroInput (.groups "g") == .error "sigma-completeness-aggregate-type"
#guard zeroInput .indices == .error "sigma-completeness-aggregate-type"
