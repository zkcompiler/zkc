import Zkc.Source.Structured.ClosedProfile

/-! Constant admission must reduce under the kernel, including the structured
closed-profile checker. Runtime parsing and a native decision oracle are not used
to construct these admission proofs. -/


namespace Tests.DecimalAdmission
open Zkc.Source Zkc.Source.Structured

example : Zkc.Source.Format.canonicalDecimal "0" = some 0 := by decide +kernel
example : Zkc.Source.Format.canonicalDecimal "1" = some 1 := by decide +kernel
example : Zkc.Source.Format.canonicalDecimal "1234567890" = some 1234567890 := by decide +kernel
example : Zkc.Source.Format.canonicalDecimal "01" = none := by decide +kernel
example : Zkc.Source.Format.canonicalDecimal "1_000" = none := by decide +kernel
example : Zkc.Source.Format.canonicalDecimal "１２" = none := by decide +kernel
example : Zkc.Source.Format.canonicalDecimal "" = none := by decide +kernel
example : Zkc.Source.Format.canonicalDecimal "10" 1 = none := by decide +kernel

example : Format.decimal "1" = .ok 1 := rfl

private def constantSnapshot : Snapshot :=
  (let contractDefinitions : List Definition := [
    .function ⟨"main", .protocol, .publicDef, [], [.field scalarDomain],
      some ⟨["P"], [], [["P"]]⟩, [], some (.protocol ⟨"main", []⟩),
      .block [.instruction (.fieldConstant scalarDomain "123") []
        [.field scalarDomain] [] ""] (.ret [0])⟩]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows, {}⟩)

private def constantProgram : ClosedProgram :=
  (checkClosed constantSnapshot).toOption.get (by decide +kernel)

-- Direct reduction keeps the dependent admission computation small.
set_option smartUnfolding false in
example (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] :
    constantProgram.denote F G .nil = .done (.cons (123 : F) .nil) := rfl

private def run : IO Unit := do
  let check (label : String) (passed : Bool) : IO Unit :=
    unless passed do throw (IO.userError s!"decimal-admission: {label}")
  for value in List.range 1000 do
    check s!"canonical-{value}"
      (Zkc.Source.Format.canonicalDecimal (toString value) == some value)
  for text in ["", "00", "01", "-1", "+1", " 1", "1 ", "1_0", "1.0", "1e0", "0x1", "١", "１２"] do
    check s!"malformed-{text}" (Zkc.Source.Format.canonicalDecimal text == none)
  check "512-digit-boundary"
    (Zkc.Source.Format.canonicalDecimal (String.ofList (List.replicate 512 '9')) == some (10 ^ 512 - 1))
  check "513-digit-refusal"
    (Zkc.Source.Format.canonicalDecimal (String.ofList (List.replicate 513 '9')) == none)
  check "structured-error"
    (match Format.decimal "01" with | .error error => error == "structured-decimal" | _ => false)
  IO.println "decimal admission: 1016 checks passed"

#eval run
end Tests.DecimalAdmission
