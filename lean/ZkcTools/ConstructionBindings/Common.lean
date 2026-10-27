module

public import Zkc.Construction.Participant

@[expose] public section

/-! Small structural proposal utilities, independent of any family printer. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings

def unique {α : Type} (label : String) : List α → Except String α
  | [value] => .ok value
  | _ => .error ("construction-binding-" ++ label)

end ZkcTools.ConstructionBindings
