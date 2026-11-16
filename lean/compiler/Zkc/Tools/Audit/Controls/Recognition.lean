module

import all Lean.Environment
meta import Zkc.Tools.Audit.CompilerHelpers
import Zkc.Tools.Audit.Controls.Generated

/-! Focused recognizer checks. Imported-file audit controls separately exercise the full path.
These mutations start with a recognized generated definition, so each refusal isolates a
particular check rather than depending on a counterfeit having the wrong name or body too. -/

open Lean Zkc.Tools.Audit

run_cmd do
  let env ← getEnv
  let name := `Zkc.Tools.Audit.Controls.Generated.Tag.ctorIdx
  let implementation := Name.str name "_impl"
  unless ← isConstructorIndexImplementation env name implementation do
    throwError "the actual generated constructor index was not recognized"
  let some (.defnInfo source) := env.find? name | throwError "missing logical definition"
  let some (.defnInfo native) := env.find? implementation | throwError "missing native definition"
  let replace (info : ConstantInfo) : Environment :=
    Environment.ofKernelEnv { env.toKernelEnv with
      constants := { env.toKernelEnv.constants with
        map₁ := env.toKernelEnv.constants.map₁.insert info.name info } }
  unless ← isConstructorIndexImplementation (replace (.defnInfo source)) name implementation do
    throwError "replacement harness lost the generated form"
  let check (label : String) (env : Environment) : IO Unit := do
    if ← isConstructorIndexImplementation env name implementation then
      throw (IO.userError s!"recognized a changed {label}")
  check "logical body" (replace (.defnInfo { source with value := mkNatLit 0 }))
  check "native body" (replace (.defnInfo { native with value := mkNatLit 0 }))
  check "logical safety" (replace (.defnInfo { source with safety := .unsafe }))
  check "native safety" (replace (.defnInfo { native with safety := .safe }))
  check "native type" (replace (.defnInfo { native with type := mkConst ``Nat }))
  let wrongType := mkForall `x .default (mkConst ``Nat) (mkConst ``Nat)
  let wrongLogical := replace (.defnInfo { source with type := wrongType })
  let wrongPair := Environment.ofKernelEnv { wrongLogical.base.private with
    constants := { wrongLogical.base.private.constants with
      map₁ := wrongLogical.base.private.constants.map₁.insert implementation
        (.defnInfo { native with type := wrongType }) } }
  check "matching but incorrect types" wrongPair
  check "logical universes" (replace (.defnInfo { source with levelParams := [`u] }))
  check "native universes" (replace (.defnInfo { native with levelParams := [`u] }))
  if ← isConstructorIndexImplementation env name `unrelated then
    throwError "recognized an unrelated replacement"
  if ← isConstructorIndexImplementation env `absent implementation then
    throwError "recognized a missing declaration"
  logInfo "constructor-index recognition: generated form accepted; 10 altered forms refused"

run_cmd do
  let env ← getEnv
  for name in [`Zkc.Tools.Audit.Controls.Generated.EmptyType.ctorIdx,
      `Zkc.Tools.Audit.Controls.Generated.Nested.ctorIdx] do
    unless ← isConstructorIndexImplementation env name (Name.str name "_impl") do
      throwError "did not recognize generated helper {name}"
