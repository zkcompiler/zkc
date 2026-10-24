module

public import Zkc.Source.Structured.BodyBindings
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! Structural selectors for source mathematics aliases. These inspect the
admitted dependency graph, without assigning a mathematical interpretation.
Synthetic bodies have dependency paths, not invented compiler origins. -/

namespace Zkc.Source.Structured.MathematicsAliases
open Zkc.Source

/-- Repeated calls to one complete signature describe one named dependency. -/
def calls (body : RawRegion Ty Op) : List Helper :=
  (body.operations.filterMap fun | .invoke helper => some helper | _ => none).eraseDups

def folds (body : RawRegion Ty Op) : List FoldSpec :=
  body.operations.filterMap fun | .fold spec => some spec | _ => none

/-- Duplicate rows, even identical ones, refuse association. -/
def definition? (definitions : List CheckedDefinition) (helper : Helper) :
    Option CheckedDefinition :=
  match definitions.filter (·.helper == helper) with
  | [definition] => some definition
  | _ => none

/-- Follow the entry's actual final call only when its sole Boolean result is
returned directly. Earlier calls and unused Boolean helpers cannot select it. -/
def finalMath? : RawRegion Ty ProtocolOp → Option Helper
  | .letOp (.calculate (.invoke helper) _) _ [.boolean] .nil (.ret [0]) =>
    if helper.kind == .math && helper.outputs == [.boolean] then some helper else none
  | .letOp _ _ _ _ next => finalMath? next
  | _ => none

end Zkc.Source.Structured.MathematicsAliases
