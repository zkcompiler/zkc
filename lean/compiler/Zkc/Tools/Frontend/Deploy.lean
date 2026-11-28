import Zkc.Frontend
import Zkc.Runtime
import Zkc.Tools.Frontend.Names

/-!
# Deployment and CFRG verification CLI commands (`zkc-check deploy`, `zkc-check cfrg-vectors`)
-/

namespace Zkc.Tools.Frontend

open Zkc.Frontend
open Zkc.Frontend.Deploy
open Zkc.Runtime
open Zkc.Runtime.Crypto

/-- `zkc-check deploy [--library <dir>]… [--scheme <name>] [--self-test] <files>…`:
compiles the given `.zkc` files through package admission, deploys the selected scheme(s)
through `Core.deploy` + `Core.deployIdeal` + `Core.specialize`, reports deployment identities
and `ClosedRole` specialization metrics, and (with `--self-test`) constructs the verified
`linkedModel?` runtime model. -/
def deployCommand (options : Names.Options) : IO UInt32 := do
  let inputs ← options.files.mapM Names.readInput
  let session ← Driver.Session.compile (Driver.Session.start) inputs
    (Names.libraryLoader options.libraries) "packages"
  if session.hasErrors then
    for line in session.renderDiagnostics do
      IO.eprintln line
    return 1
  let state := session.state
  let targets : Except String (List SchemeEntry) :=
    match options.scheme with
    | some name => do return [← findSchemeEntry state name]
    | none =>
        if state.results.schemes.isEmpty then
          .error "no schemes declared in the given files"
        else .ok state.results.schemes.toList
  match targets with
  | .error msg =>
      IO.eprintln s!"deploy error: {msg}"
      return 1
  | .ok entries =>
      let mut failed := 0
      for entry in entries do
        match deploySchemeEntry state entry with
        | .error msg =>
            failed := failed + 1
            IO.eprintln s!"scheme {entry.name}: FAILED ({msg})"
        | .ok cs =>
            let idHashHex := bytesToHex (sha256Bytes cs.identity)
            let suiteLabel := match cs.plan.construction with
              | .interactive => "interactive"
              | .authored => "authored"
              | .derived spec _ => spec.describe
            let idealStatus := if cs.ideal?.isSome then "admitted" else "n/a"
            let statsStr := ", ".intercalate (cs.specializationStats.map fun (r, nodes, procs) =>
              s!"role {r}: {nodes} nodes / {procs} procs")
            IO.println s!"scheme {cs.name}: deployed ({suiteLabel})"
            IO.println s!"  identity: sha256={idHashHex} ({cs.identity.length} canonical bytes)"
            IO.println s!"  ideal-ro: {idealStatus}"
            IO.println s!"  closed-ir: {statsStr}"
            if options.selfTest then
              match linkedModel? cs.bindings with
              | .ok _ =>
                  IO.println s!"  self-test: linkedModel? ok ({cs.bindings.rows.length} project rows)"
              | .error err =>
                  failed := failed + 1
                  IO.eprintln s!"  self-test: FAILED ({err})"
      return if failed == 0 then 0 else 1

/-- `zkc-check cfrg-vectors`: runs all CFRG `draft-irtf-cfrg-fiat-shamir-04` test vectors
(direct Duplex + end-to-end Core `admit` → `deploy` → `execute` vs `specialize` → `runClosed`). -/
def cfrgVectorsCommand : IO UInt32 := do
  let (allOk, results) ← Zkc.Runtime.CfrgVectors.runAllCfrgVectors
  let mut passed := 0
  for (label, ok, detail) in results do
    if ok then
      passed := passed + 1
      IO.println s!"[PASS] {label} ({detail})"
    else
      IO.eprintln s!"[FAIL] {label} ({detail})"
  IO.println s!"CFRG draft-04 vectors: {passed}/{results.length} passed"
  return if allOk then 0 else 1

end Zkc.Tools.Frontend
