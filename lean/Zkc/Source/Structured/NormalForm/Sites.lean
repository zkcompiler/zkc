module

public import Zkc.Source.Structured.NormalForm.Syntax

@[expose] public section

/-! Structural site addresses in an existing typed normal form. These retain
branch/continuation positions; they are neither transcript keys nor a second
execution semantics. Printers and checked clients share this metadata. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.NormalForm
variable {laws : List LawKey} {callees : List CalleeKey}

/-- A structural address in the actual form: 0 selects the absent branch,
1 the present branch; every linear continuation advances by 0. These are
static addresses, not runtime occurrence keys. Repeated sites stay distinct. -/
structure Site where
  path : List Nat
  kind : String
  site : String
  deriving BEq, DecidableEq, Repr
def sites {out : List Ty} : {Δ : Scope} → Form laws callees Δ out → List Nat → List Site
  | _, .done _, _ | _, .halt _, _ => []
  | _, .send _ site _ _ next, path => ⟨path, "send", site⟩ :: sites next (path ++ [0])
  | _, .receive _ site _ next, path => ⟨path, "receive", site⟩ :: sites next (path ++ [0])
  | _, .query site _ _ next, path => ⟨path, "query", site⟩ :: sites next (path ++ [0])
  | _, .split _ absent present, path => sites absent (path ++ [0]) ++ sites present (path ++ [1])
  | _, .guard _ _ _ next, path | _, .strict _ _ next, path | _, .compute _ _ _ next, path
  | _, .byLaw _ _ next, path | _, .math _ _ next, path | _, .owned _ _ _ next, path => sites next (path ++ [0])
  | _, .repeat _ site _ _ _ _ next, path => ⟨path, "repeat", site⟩ :: sites next (path ++ [0])
  | _, .apply _ _ _ site _ next, path => ⟨path, "apply", site⟩ :: sites next (path ++ [0])

end Zkc.Source.Structured.NormalForm
