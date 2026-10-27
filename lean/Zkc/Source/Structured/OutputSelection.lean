module

public import Zkc.Source.Structured.Vocabulary

@[expose] public section

/-! Role-local output coordinates. These depend only on the typed source
interface, independently of the selected execution or proof method. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

/-- Position among outputs visible to the selected role. -/
def scopePosition (self : Nat) : List (List Nat) → {tys : List Ty} → {ty : Ty} → Var tys ty → Nat
  | _, _, _, .here => 0
  | scopes, _, _, .there value =>
      (if (scopes.headD []).contains self then 1 else 0) + scopePosition self scopes.tail value

/-- Whether the selected output is visible to the role. -/
def inScope (self : Nat) : List (List Nat) → {tys : List Ty} → {ty : Ty} → Var tys ty → Bool
  | scopes, _, _, .here => (scopes.headD []).contains self
  | scopes, _, _, .there value => inScope self scopes.tail value

end Zkc.Source.Structured
