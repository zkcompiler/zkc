module

public import ZkcTools.StructuredSource.Discovery.Address

@[expose] public section

/-! Kernel-reducible coordinate checking. These queries select actual admitted
operands/results and contexts; they do not certify any semantic helper law. -/

namespace ZkcTools.StructuredSource.Discovery
open Zkc.Source Zkc.Source.Structured

mutual
  def contextAt {Op : Type} (body : RawRegion Ty Op) (inputs : List Ty) :
      List Nat → Option (List Ty)
    | [] => some inputs
    | 0 :: path => match body with
      | .bind _ body _ => contextAt body inputs path
      | _ => none
    | 1 :: path => match body with
      | .letOp _ _ results _ next => contextAt next (results ++ inputs) path
      | .bind results _ next => contextAt next (results ++ inputs) path
      | _ => none
    | 2 :: index :: path => match body with
      | .letOp _ _ _ bodies _ => callbackContextAt bodies index path
      | _ => none
    | _ => none
  def callbackContextAt {Op : Type} (bodies : RawRegions Ty Op) (index : Nat)
      (path : List Nat) : Option (List Ty) :=
    match bodies, index with
    | .nil, _ => none
    | .cons inputs _ body _, 0 => contextAt body inputs path
    | .cons _ _ _ tail, index + 1 => callbackContextAt tail index path
end

def protocolTypeAt (program : Program) (address : Address) : Option Ty := do
  let root ← protocolAt program address
  match address.coordinate with
  | .instruction => none
  | .input index => (← contextAt root.raw root.inputs address.region)[index]?
  | .operand index =>
    let .letOp op _ _ _ _ ← regionAt root.raw address.region | none
    op.arguments[index]?
  | .result index =>
    let .letOp _ _ types _ _ ← regionAt root.raw address.region | none
    types[index]?

def protocolOperandAt (program : Program) (address : Address) : Option Nat := do
  let root ← protocolAt program address
  let .operand index := address.coordinate | none
  let .letOp _ indices _ _ _ ← regionAt root.raw address.region | none
  indices[index]?

/-- Existence/type selection is deliberately distinct from implementation laws. -/
structure TypedSelection (program : Program) (address : Address) (type : Ty) : Prop where
  selected : protocolTypeAt program address = some type

end ZkcTools.StructuredSource.Discovery
