import ZkcTools.ClosedString

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

syntax (name := checkDataString) "check_data_string " term " equals " str : command
@[command_elab checkDataString] meta def checkString : CommandElab
  | `(check_data_string $value:term equals $expected:str) => do
      let actual ← liftTermElabM do
        let expression ← Term.elabTerm value (some (mkConst ``String))
        ZkcTools.ClosedString.read 4096 expression
      unless actual == expected.getString do throwError "closed metadata changed"
  | _ => throwUnsupportedSyntax

syntax (name := refuseDataString) "refuse_data_string " term : command
@[command_elab refuseDataString] meta def refuseString : CommandElab
  | `(refuse_data_string $value:term) => do
      let saved ← get
      let refused ← try
        discard <| liftTermElabM do
          let expression ← Term.elabTerm value (some (mkConst ``String))
          ZkcTools.ClosedString.read 4096 expression
        pure false
      catch _ => pure true
      set saved
      unless refused do throwError "unresolved metadata was interpreted"
  | _ => throwUnsupportedSyntax

check_data_string "α" equals "α"
check_data_string metadata.label equals "source:5"
refuse_data_string unresolved
refuse_data_string (@toString Nat ⟨fun _ => "forged"⟩ 7)
refuse_data_string (@HAppend.hAppend String String String ⟨fun _ _ => "forged"⟩ "a" "b")

end Tests.ClosedString
