module

public import Zkc.Core.WellFormed

public section

/-! Whether a function can stop.

The reference: a function can stop exactly when its body has a guard or a stop, or calls a
function that can stop. An operation with a domain cannot stop: admission excludes the
undefined application.

`Functions.stops` computes it for every function of a program, the most recent first. A
function known by its header only can stop: its meaning is the model's. A loop over a value
with a stated maximum cannot: above the maximum it is outside its domain, which admission
excludes like any other undefined application.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- Whether a local operation can stop by itself, given which earlier functions can: a guard,
and a call of a function that can stop. -/
@[expose] def LocalOp.stops (callees : List Bool) : LocalOp operations functions deployed → Bool
  | .guard _ => true
  | .call callee _ => callees.getD callee.index true
  | _ => false

mutual
  /-- Whether a local region can stop: one of its instructions can, one of their nested
  regions can, or it ends in a stop. -/
  @[expose] def localRegionStops (callees : List Bool) {Γ out : List Ty} :
      Region (LocalDialect operations functions deployed) Γ out → Bool
    | .ret _ => false
    | .stop _ => true
    | .letOp op _ bodies next =>
        op.stops callees || localRegionsStop callees bodies || localRegionStops callees next
    | .bind body next => localRegionStops callees body || localRegionStops callees next

  @[expose] def localRegionsStop (callees : List Bool)
      {signatures : List (List Ty × List Ty)} :
      Regions (LocalDialect operations functions deployed) signatures → Bool
    | .nil => false
    | .cons body tail => localRegionStops callees body || localRegionsStop callees tail
end

end Local

/-- Whether each function of a program can stop, the most recent first. -/
@[expose] def Functions.stops {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → Functions typeTable operations functions → List Bool
  | _, .nil => []
  | _, .snoc earlier definition _ =>
      localRegionStops earlier.stops definition.body :: earlier.stops
  | _, .opaque earlier _ _ => true :: earlier.stops

end Zkc.Core
