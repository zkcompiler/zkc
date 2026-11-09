import Zkc.Adapters.Clean.Specification
import Zkc.Adapters.Clean.Native
import Zkc.Adapters.Clean.NativeExport
import Zkc.Tools.Clean.Control
import Zkc.Tests.Clean.Bits
import Zkc.Tests.Clean.Nested
import Zkc.Tests.Clean.Refusals
import Zkc.Tools.Program.DeclarationAudit

/-! Axiom status of the upstream Clean declarations at the pinned revision. The
boundary is computed rather than listed: every Clean declaration that a
declaration of the bridge, or of the controls imported here, names directly.
Two upstream declarations that only other controls use are named. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted, including inside
upstream proof cones. The generated `TestsClean.Audit` separately audits every
package-owned declaration, the bridge theorems included. -/

run_cmd do
  ZkcTools.DeclarationAudit.checkBoundary [`Zkc.Adapters.Clean, `Zkc.Tools.Clean, `Zkc.Tests.Clean] [`Clean]
    [`Gadgets.ToBits.toBits, `GeneralFormalCircuit.original_full_soundness]
    "CLEAN-UPSTREAM-BOUNDARY-PASS"
