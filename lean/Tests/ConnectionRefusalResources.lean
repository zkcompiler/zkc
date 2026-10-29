import Tests.ConnectionRefusal

/-! Lean's ordinary tactic backtracking propagates runtime errors. Verify that
our negative-control wrapper preserves this behavior without exhausting a build.
Only this test's outer handler explicitly catches runtime exceptions. -/
open Lean Elab Tactic

run_elab do
  for tag in [`runtime.maxHeartbeats, `runtime.maxRecDepth] do
    let original : Exception := .error .missing (.tagged tag "test resource limit")
    let propagated ← tryCatchRuntimeEx
      (do
        try throw original catch _ => pure ()
        pure false)
      (fun error => pure error.isRuntime)
    unless propagated do throwError "ordinary tactic backtracking swallowed a resource limit"

elab "test_connection_resource_limit" : tactic =>
  throw (.error .missing (.tagged `runtime.maxHeartbeats "test resource limit"))

example : True := by
  run_tac
    let propagated ← tryCatchRuntimeEx
      (do
        evalTactic (← `(tactic|
          expect_connection_refusal "resource control" because "alignment-"
            test_connection_resource_limit))
        pure false)
      (fun error => pure error.isRuntime)
    unless propagated do throwError "resource exhaustion counted as a static refusal"
  trivial
