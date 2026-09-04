import Lake
open Lake DSL

-- Definition text for the M0 mechanized kernel definition spike. The package
-- has no dependency on Mathlib, Batteries, Std, VCVio, or ArkLib: only the
-- Lean core library that ships with the pinned toolchain in `lean-toolchain`.
-- `docs-next/foundation/executable-foundations.md` Section 2 and
-- `docs-next/pir/interactive-core.md` Section 11 own the laws these
-- definitions transcribe; nothing here is normative.
package m0

lean_lib M0

@[default_target]
lean_exe m0 where
  root := `Main
