module

public import ZkcArkLibExamples.Fri.VirtualReads
public import Zkc.Realization.QuerySourceExecution
public import Zkc.Realization.QuerySourceWork

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

/-- The same installed mathematical connection accepts actual open child
executions. Provider state, interaction phase and logs come from those child
executions, while source locations and the folded output come from `twoReads`.
This is source progress, not an assertion that a generated arm executed. -/
def produced {I : PIR.Signature} {S E : Type}
    (interaction : PIR.Interaction I)
    (operations : (query : OracleRead) → S →
      PIR.Process I (PIR.Execution S E (model.Value query.kind.answer)))
    (initial middle final : S) (initialPhase middlePhase finalPhase : interaction.Phase)
    (leftEvents rightEvents : List E)
    (leftExecution : PIR.Reaches interaction
      (operations (leftRequest source (low position sourceRows)) initial) initialPhase
      (.done ⟨.returned left, middle, leftEvents⟩) middlePhase)
    (rightExecution : PIR.Reaches interaction
      (operations (rightRequest source
        (wrappingAdd (low position sourceRows) (logicalShiftRight sourceRows 1))) middle) middlePhase
      (.done ⟨.returned right, final, rightEvents⟩) finalPhase) :
    Produced interaction operations
      (FriVirtualBody.installed.denote model
        (arguments model source beta sourceRows rows shift generator inverseShift
          inverseGenerator inverseTwo position).present)
      initial initialPhase arenas
      (.done (.cons (some ((left + right) * inverseTwo + beta * (left - right) * inverseTwo *
        (inverseShift * inverseGenerator ^ low position sourceRows))) .nil))
      [leftSlot, rightSlot] final finalPhase (leftEvents ++ rightEvents) := by
  rw [twoReads]
  have start := Produced.initial (interaction := interaction) (operations := operations)
    (source := twoChildren model source beta sourceRows inverseShift inverseGenerator inverseTwo position)
    (initialState := initial) (initialPhase := initialPhase) arenas
  exact (start.resume leftExecution leftRead).resume rightExecution rightRead

/-- The actual installed mathematical connection also determines the work
schedule. Both original child occurrences remain, with their original source
positions; no new FRI traversal or folded-word theorem is needed. The child
expansion facts belong to their installed provider/virtual definitions. -/
theorem scheduled (expansion : OracleRead → Zkc.Realization.QueryWork.Shape → Prop)
    (childShape : Zkc.Realization.QueryWork.Shape)
    (leftShape : expansion (leftRequest source (low position sourceRows)) childShape)
    (rightShape : expansion (rightRequest source
      (wrappingAdd (low position sourceRows) (logicalShiftRight sourceRows 1))) childShape) :
    Zkc.Realization.QuerySourceWork.Body expansion
      (FriVirtualBody.installed.denote model
        (arguments model source beta sourceRows rows shift generator inverseShift
          inverseGenerator inverseTwo position).present) [childShape, childShape] := by
  rw [twoReads]
  exact .call _ _ _ _ leftShape (fun _ ↦ .call _ _ _ _ rightShape (fun _ ↦ .done _))

/-- Even identical child shapes cannot replace the two actual accesses by
one. This checks the installed source, independently of its numerical result. -/
theorem cannot_drop_child
    (expansion : OracleRead → Zkc.Realization.QueryWork.Shape → Prop)
    (childShape : Zkc.Realization.QueryWork.Shape) :
    ¬ Zkc.Realization.QuerySourceWork.Body expansion
      (FriVirtualBody.installed.denote model
        (arguments model source beta sourceRows rows shift generator inverseShift
          inverseGenerator inverseTwo position).present) [childShape] := by
  rw [twoReads]
  intro body
  obtain ⟨first, rest, equal, _, following⟩ :=
    Zkc.Realization.QuerySourceWork.Body.call_iff.mp body
  have empty : rest = [] := (List.cons.inj equal).2.symm
  have next := following (0 : model.Field extension)
  rw [empty] at next
  obtain ⟨_, _, impossible, _⟩ := Zkc.Realization.QuerySourceWork.Body.call_iff.mp next
  contradiction

#print axioms installed
#print axioms produced
#print axioms scheduled
#print axioms cannot_drop_child
end TestsArkLib.FriSourceContinuation
