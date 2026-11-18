module

public import Zkc.Core.Program.NamedProgram
public import Zkc.Core.Program.Dialects

@[expose] public section

/-!
Two transformations of a stored function, written as plain functions on the program by names.

Neither is trusted, and nothing is proved of them. What one of them gives is accepted only
through the step of a transformation from an assured function (`AssuredFn.step`,
`Transform/Assured.lean`): the step elaborates it and follows the analysis of its source with
it. A wrong result of either is refused there.

- `removeUnused` drops the operations none of whose results is used later, in a body and in its
  regions. A guard, a form of control and a call of a function that can stop are kept; the
  regions of a form of control are walked.
- `shareRepeated` drops an operation that has the written form and the operand names of an
  earlier operation in scope, and puts the earlier operation's results for its results in what
  follows. Only an operation that the analysis calls a value (`FunctionContracts.rules`)
  is shared: every operation except a call of a function that can stop.

Both read the headers of the callees for whether a call can stop: a call is dropped or shared
only when a header with its key says that the callee cannot stop.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- Whether a written operation of a function is a value for the analysis, as
the typed operation’s `canStop` flag says of the operation that it writes, by the headers of the
callees: every operation except a call of a function that can stop. A call whose key no header
has is not taken for a value. -/
def LocalRaw.isValue (fns : List (FnHeader V)) : LocalRaw V → Bool
  | .row _ => true
  | .owned .. => true
  | .literal .. => true
  | .call callee => fns.any fun hdr => hdr.key == callee && !hdr.canStop

/-- The name that a loop's count reads, if any. -/
def Repeat.uses : Repeat → List Name
  | .fixed _ => []
  | .count name => [name]

/-! ## Operations whose results are not used -/

mutual
  /-- A body without the operations none of whose results is used later, walked from its end,
  with the names that what is kept and the exit use. Names are bound once in a function, so a
  name used inside a region is never one that the region binds again outside. -/
  def removeUnusedBody (fns : List (FnHeader V)) :
      List (Instruction (LocalRaw V) Unit) → List Name →
        List (Instruction (LocalRaw V) Unit) × List Name
    | [], exit => ([], exit)
    | .op key results raw operands :: rest, exit =>
        let after := removeUnusedBody fns rest exit
        if raw.isValue fns && results.all (fun name => !after.2.contains name) then after
        else (.op key results raw operands :: after.1, operands ++ after.2)
    | .guard key who condition why :: rest, exit =>
        let after := removeUnusedBody fns rest exit
        (.guard key who condition why :: after.1, condition :: after.2)
    | .choose key who condition results onTrue onFalse :: rest, exit =>
        let after := removeUnusedBody fns rest exit
        let yes := removeUnusedRegion fns onTrue
        let no := removeUnusedRegion fns onFalse
        (.choose key who condition results yes.1 no.1 :: after.1,
          condition :: yes.2 ++ no.2 ++ after.2)
    | .cases key who subject results arms :: rest, exit =>
        let after := removeUnusedBody fns rest exit
        let kept := removeUnusedArms fns arms
        (.cases key who subject results kept.1 :: after.1, subject :: kept.2 ++ after.2)
    | .loop key who times carried results body :: rest, exit =>
        let after := removeUnusedBody fns rest exit
        let kept := removeUnusedRegion fns body
        (.loop key who times carried results kept.1 :: after.1,
          times.uses ++ carried ++ kept.2 ++ after.2)
    | .block key number results body :: rest, exit =>
        let after := removeUnusedBody fns rest exit
        let kept := removeUnusedRegion fns body
        (.block key number results kept.1 :: after.1, kept.2 ++ after.2)
    | .attempt key who results body :: rest, exit =>
        let after := removeUnusedBody fns rest exit
        let kept := removeUnusedRegion fns body
        (.attempt key who results kept.1 :: after.1, kept.2 ++ after.2)
  /-- A region without the operations none of whose results is used later, with the names that
  it uses. -/
  def removeUnusedRegion (fns : List (FnHeader V)) :
      Region (LocalRaw V) Unit → Region (LocalRaw V) Unit × List Name
    | .mk inputs body exit =>
        let kept := removeUnusedBody fns body exit
        (.mk inputs kept.1 exit, kept.2)
  /-- The arms of a case analysis, each without the operations whose results are not used, with
  the names that they use. -/
  def removeUnusedArms (fns : List (FnHeader V)) :
      List (Region (LocalRaw V) Unit) → List (Region (LocalRaw V) Unit) × List Name
    | [] => ([], [])
    | arm :: arms =>
        let first := removeUnusedRegion fns arm
        let others := removeUnusedArms fns arms
        (first.1 :: others.1, first.2 ++ others.2)
end

/-- A stored function without the operations none of whose results is used later, in its body
and in its regions; a guard, a form of control and a call of a function that can stop are kept.
Not trusted: what it gives is accepted through the step (`AssuredFn.step`). -/
def removeUnused (fns : List (FnHeader V)) (region : Region (LocalRaw V) Unit) :
    Region (LocalRaw V) Unit :=
  (removeUnusedRegion fns region).1

/-! ## Repeated operations -/

/-- A name, or the name that stands for it after a repeated operation was dropped. -/
def renameShared (renamed : List (Name × Name)) (name : Name) : Name :=
  (renamed.lookup name).getD name

mutual
  /-- A body in which an operation that is a value and repeats the written form and the operand
  names of an earlier one in scope (`computed`: written form, operands, results) is dropped, and
  every later use of its results is renamed to the earlier results (`renamed`); with the exit,
  renamed. A region sees what was computed around it, and what it computes stays inside it. -/
  def shareBody (fns : List (FnHeader V)) (computed : List (LocalRaw V × List Name × List Name))
      (renamed : List (Name × Name)) :
      List (Instruction (LocalRaw V) Unit) → List Name →
        List (Instruction (LocalRaw V) Unit) × List Name
    | [], exit => ([], exit.map (renameShared renamed))
    | .op key results raw operands :: rest, exit =>
        let operands' := operands.map (renameShared renamed)
        if raw.isValue fns then
          match computed.find? (fun earlier => earlier.1 == raw && earlier.2.1 == operands' &&
              earlier.2.2.length == results.length) with
          | some (_, _, earlier) =>
              shareBody fns computed (renamed ++ results.zip earlier) rest exit
          | none =>
              let after := shareBody fns (computed ++ [(raw, operands', results)]) renamed rest exit
              (.op key results raw operands' :: after.1, after.2)
        else
          let after := shareBody fns computed renamed rest exit
          (.op key results raw operands' :: after.1, after.2)
    | .guard key who condition why :: rest, exit =>
        let after := shareBody fns computed renamed rest exit
        (.guard key who (renameShared renamed condition) why :: after.1, after.2)
    | .choose key who condition results onTrue onFalse :: rest, exit =>
        let after := shareBody fns computed renamed rest exit
        (.choose key who (renameShared renamed condition) results
          (shareRegion fns computed renamed onTrue) (shareRegion fns computed renamed onFalse) ::
            after.1, after.2)
    | .cases key who subject results arms :: rest, exit =>
        let after := shareBody fns computed renamed rest exit
        (.cases key who (renameShared renamed subject) results
          (shareArms fns computed renamed arms) :: after.1, after.2)
    | .loop key who times carried results body :: rest, exit =>
        let after := shareBody fns computed renamed rest exit
        let times' : Repeat := match times with
          | .fixed n => .fixed n
          | .count name => .count (renameShared renamed name)
        (.loop key who times' (carried.map (renameShared renamed)) results
          (shareRegion fns computed renamed body) :: after.1, after.2)
    | .block key number results body :: rest, exit =>
        let after := shareBody fns computed renamed rest exit
        (.block key number results (shareRegion fns computed renamed body) :: after.1, after.2)
    | .attempt key who results body :: rest, exit =>
        let after := shareBody fns computed renamed rest exit
        (.attempt key who results (shareRegion fns computed renamed body) :: after.1, after.2)
  /-- A region with the repeated operations of its body shared, against what was computed
  around it. -/
  def shareRegion (fns : List (FnHeader V)) (computed : List (LocalRaw V × List Name × List Name))
      (renamed : List (Name × Name)) : Region (LocalRaw V) Unit → Region (LocalRaw V) Unit
    | .mk inputs body exit =>
        let shared := shareBody fns computed renamed body exit
        .mk inputs shared.1 shared.2
  /-- The arms of a case analysis, each with its repeated operations shared. -/
  def shareArms (fns : List (FnHeader V)) (computed : List (LocalRaw V × List Name × List Name))
      (renamed : List (Name × Name)) :
      List (Region (LocalRaw V) Unit) → List (Region (LocalRaw V) Unit)
    | [] => []
    | arm :: arms => shareRegion fns computed renamed arm :: shareArms fns computed renamed arms
end

/-- A stored function in which a later operation with the written form and the operand names of
an earlier one in scope is dropped, its results replaced by the earlier ones in what follows; only
among the operations that the analysis calls values. Not trusted: what it gives is accepted
through the step (`AssuredFn.step`). -/
def shareRepeated (fns : List (FnHeader V)) (region : Region (LocalRaw V) Unit) :
    Region (LocalRaw V) Unit :=
  shareRegion fns [] [] region

end

end Zkc.Core
