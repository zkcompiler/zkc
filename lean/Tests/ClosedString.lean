import Zkc.Claims.ClosedString

/-! Metadata extraction must normalize ordinary constructors while refusing
unknown data and customized formatting. No rendered expression is an identifier. -/
namespace Tests.ClosedString
open Lean Meta Elab Command

structure Metadata where
  semantic : Nat
  label : String

noncomputable def metadata : Metadata :=
  ⟨Classical.choice (show Nonempty Nat from ⟨7⟩), "source:" ++ toString (2 + 3 : Nat)⟩
noncomputable def unresolved : String :=
  Classical.choice (show Nonempty String from ⟨"unresolved"⟩)

noncomputable def selectedLabel : String :=
  match [metadata].find? (fun item => item.label == "source:5") with
  | some item => item.label
  | none => "missing"

syntax (name := checkDataString) "check_data_string " term " equals " str : command
@[command_elab checkDataString] meta def checkString : CommandElab
  | `(check_data_string $value:term equals $expected:str) => do
      let actual ← liftTermElabM do
        let expression ← Term.elabTerm value (some (mkConst ``String))
        Zkc.Claims.ClosedString.read 4096 expression
      unless actual == expected.getString do throwError "closed metadata changed"
  | _ => throwUnsupportedSyntax

syntax (name := refuseDataString) "refuse_data_string " term : command
@[command_elab refuseDataString] meta def refuseString : CommandElab
  | `(refuse_data_string $value:term) => do
      let saved ← get
      let refused ← try
        discard <| liftTermElabM do
          let expression ← Term.elabTerm value (some (mkConst ``String))
          Zkc.Claims.ClosedString.read 4096 expression
        pure false
      catch _ => pure true
      set saved
      unless refused do throwError "unresolved metadata was interpreted"
  | _ => throwUnsupportedSyntax

check_data_string "α" equals "α"
check_data_string metadata.label equals "source:5"
check_data_string (([metadata] ++ [metadata])[1]).label equals "source:5"
check_data_string selectedLabel equals "source:5"
check_data_string s!"input[{(2 + 3 : Nat)}]" equals "input[5]"
check_data_string (toString "source") equals "source"
refuse_data_string unresolved
refuse_data_string (@toString Nat ⟨fun _ => "forged"⟩ 7)
refuse_data_string (@toString String ⟨fun _ => "forged"⟩ "actual")
refuse_data_string (@HAppend.hAppend String String String ⟨fun _ _ => "forged"⟩ "a" "b")

end Tests.ClosedString
