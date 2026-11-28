import Zkc.Tests.Runtime.Crypto
import Zkc.Tests.Runtime.Examples

/-!
# Runtime verification test driver (`zkc-runtime-tests`)
-/

def main : IO UInt32 := do
  let cryptoRes ← Zkc.Tests.Runtime.runCryptoSuite
  let exampleRes ← Zkc.Tests.Runtime.runExamplesSuite
  let all := cryptoRes ++ exampleRes
  let mut passed := 0
  let mut failed := 0
  for (name, ok, detail) in all do
    if ok then
      passed := passed + 1
      let suffix := if detail.isEmpty then "" else s!" ({detail})"
      IO.println s!"[PASS] {name}{suffix}"
    else
      failed := failed + 1
      IO.eprintln s!"[FAIL] {name} ({detail})"
  IO.println s!"ZkcRuntimeTests: {passed}/{all.length} passed"
  return if failed == 0 then 0 else 1
