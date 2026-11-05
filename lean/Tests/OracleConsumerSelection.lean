module

public import Tests.IndexServices
public import Zkc.Source.Structured.OracleIngress
public import Zkc.Construction.SourceConnection

@[expose] public section

/-! Canonical execution selection is checked before constructing a property
consumer. A successfully admitted Oracle source cannot enter the ordinary
source-to-participant path, whose meaning deliberately refuses Oracle effects. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Tests.OracleConsumerSelection
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private def oracleSource : Snapshot :=
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000",
    "main", [], [], [],
    [.function ⟨"main", .protocol, .publicDef, [.indices], [.boolean],
      some ⟨["P", "V"], [["P"]], [["V"]]⟩, [], some (.protocol ⟨"main", []⟩),
      .block [
        .instruction (.indexConstant "2") [] [.index] [] "",
        .instruction (.oracle (.send "P" ["V"] (.table .index none)
          ["rows"] [("rows", 2)])) [1, 0] [.oracle (.table .index none)] [] "base",
        .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0])⟩],
    [⟨"main", []⟩], blsRows, {}⟩

private def oracleProgram : Program :=
  (Structured.check oracleSource).toOption.get (by decide +kernel)

private theorem oracle_admitted : Structured.check oracleSource = .ok oracleProgram := by
  kernel_rfl

private def oracleImported : Imported oracleSource := ⟨oracleProgram, oracle_admitted⟩

example : oracleSource.requiresOracleRuntime = true := by decide +kernel

/-- Refusal holds for every proposed ordinary artifact, including one with
otherwise valid source-independent construction data. -/
example (artifact : Participant) : select oracleImported artifact = none :=
  select_oracle_refused oracleImported artifact (by decide +kernel)

example (artifact : Participant) :
    SourceConnection.canonicalABI oracleProgram 1 artifact =
      .error "source-connection-oracle-runtime" :=
  SourceConnection.canonicalABI_oracle_refused oracleProgram 1 artifact (by decide +kernel)

/-- Real ordinary scalar and block source exports retain their canonical path. -/
example : (select IndexServices.Scalar.imported
    IndexServices.Scalar.Validator.participant).isSome = true := by decide +kernel

example : (select IndexServices.Block.imported
    IndexServices.Block.Validator.participant).isSome = true := by decide +kernel

example : (SourceConnection.canonicalABI IndexServices.Scalar.program 1
    IndexServices.Scalar.Validator.participant).toOption.isSome = true := by decide +kernel

end Tests.OracleConsumerSelection
