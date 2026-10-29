module

public import ZkcSecurity.Source.Pair
public import Zkc.Semantics.Yields

public section

/-! Pure return invariants attach to source pairing before routing or artifact
installation. They cannot turn a stopped source into a successful pair. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.Pair
open Zkc.Source Zkc.Source.Structured

variable {carriers : Carriers} {scope : PairScope} {A B : Type}

theorem frame_left {Post : A → B → Prop} {property : A → Prop}
    {left : PIR.Process (Occurrence.signature carriers) A}
    {right : PIR.Process (Occurrence.signature carriers) B}
    (paired : Pair scope Post left right) (holds : PIR.Yields property left) :
    Pair scope (fun a b => Post a b ∧ property a) left right := by
  induction paired with
  | done post => exact .done ⟨post, holds⟩
  | enter frame _ ih => exact .enter frame (ih (holds ()))
  | leave frame _ ih => exact .leave frame (ih (holds ()))
  | message ty site producer validator value data roles _ ih =>
      exact .message ty site producer validator value data roles (ih (holds ()))
  | challenge field query delivery producer validator handle roles owned _ ih =>
      exact .challenge field query delivery producer validator handle roles owned
        (fun reply => ih reply (holds reply))

end ZkcSecurity.Source.Pair
