module

public meta import ZkcSecurityTools.ClaimConstruction

@[expose] public section

/-! Closed metadata may project away semantic choices, but cannot evaluate a
choice used as data. These controls exercise the same evaluator as claim_request.
Receipt admission and mathematical proof checking are tested by the root clients.
-/
namespace TestsSecurity.ClaimClosedData
open Lean Meta Elab Command ZkcSecurity.Tools.ClaimConstruction

structure Metadata where
  semantic : Nat
  label : String

noncomputable def metadata : Metadata :=
  ⟨Classical.choice (show Nonempty Nat from ⟨7⟩), "static metadata"⟩

noncomputable def unresolved : String :=
  Classical.choice (show Nonempty String from ⟨"unresolved"⟩)

syntax (name := checkClosedString) "check_closed_string " term " equals " str : command

@[command_elab checkClosedString] meta unsafe def checkString : CommandElab
  | `(check_closed_string $value:term equals $expected:str) => do
    let actual ← liftTermElabM <| evalClosedData String (mkConst ``String) value
    unless actual == expected.getString do throwError "closed metadata changed"
  | _ => throwUnsupportedSyntax

syntax (name := checkUnresolvedString) "check_unresolved_string " term : command

@[command_elab checkUnresolvedString] meta unsafe def checkUnresolved : CommandElab
  | `(check_unresolved_string $value:term) => do
    let saved ← get
    let refused ← try
      discard <| liftTermElabM <| evalClosedData String (mkConst ``String) value
      pure false
    catch _ => pure true
    set saved
    unless refused do throwError "unresolved noncomputable data was evaluated"
  | _ => throwUnsupportedSyntax

check_closed_string "literal" equals "literal"
check_closed_string metadata.label equals "static metadata"
check_unresolved_string unresolved

end TestsSecurity.ClaimClosedData
