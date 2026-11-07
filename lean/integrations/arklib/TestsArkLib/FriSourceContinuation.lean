module

public import ZkcArkLibExamples.Fri.VirtualReads
public import Zkc.Realization.QuerySourceContinuation

@[expose] public section

/-! Specialize the common saved-source relation on the installed FRI virtual
body. Existing helper association and mathematical laws remain in VirtualReads;
no generated coordinate or protocol-specific continuation evaluator is added.
-/
set_option autoImplicit false
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
namespace TestsArkLib.FriSourceContinuation
open Zkc.Source Zkc.Source.Structured Zkc.Realization.QuerySourceContinuation
open ZkcExamples.Structured
open ZkcSecurity.ArkLib.Fri.VirtualReads
open FriSource

variable (model : DomainModel)
  (arenas : (kind : OracleKind) → List (model.Value kind.answer))
  (source : OracleAnchor) (beta : model.Field extension) (sourceRows rows : Nat)
  (shift generator inverseShift inverseGenerator inverseTwo : model.Field extension)
  (position : Nat)
  (leftSlot rightSlot : Nat) (left right : model.Field extension)
  (leftRead : (arenas kind)[leftSlot]? = some left)
  (rightRead : (arenas kind)[rightSlot]? = some right)

/-- The installed source and the two actual arena cells determine the folded
result. Reuse retains both ordered accesses, even when their values coincide. -/
def installed : Associated arenas
    (FriVirtualBody.installed.denote model
      (arguments model source beta sourceRows rows shift generator inverseShift
        inverseGenerator inverseTwo position).present)
    (.done (.cons (some ((left + right) * inverseTwo + beta * (left - right) * inverseTwo *
      (inverseShift * inverseGenerator ^ low position sourceRows))) .nil))
    [leftSlot, rightSlot] := by
  rw [twoReads]
  have cursor := initial arenas
    (twoChildren model source beta sourceRows inverseShift inverseGenerator inverseTwo position)
  have first := cursor.resume (reply := left) leftRead
  have second := first.resume (reply := right) rightRead
  exact second

#print axioms installed
end TestsArkLib.FriSourceContinuation
