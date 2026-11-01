import ZkcTools.StructuredSource.HelperCallbacks
import Zkc.Source.Structured.Meaning

set_option autoImplicit false
namespace Tests.HelperCallbacks
open Zkc.Source Zkc.Source.Structured
open Zkc.Source.Structured.HelperCallbacks

def keep : Region dialect [.index, .index, .index] [.index, .index] :=
  .ret (.cons (.there .here) (.cons (.there (.there .here)) .nil))

def swap : Region dialect [.index, .index, .index] [.index, .index] :=
  .ret (.cons (.there (.there .here)) (.cons (.there .here) .nil))

def loop (body : Region dialect [.index, .index, .index] [.index, .index]) :
    Region dialect [.index, .index, .index, .index] [.index] :=
  .letOp (.loop [.index] [.index])
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil)))) (.cons body .nil)
    (.ret (.cons .here .nil))

helper_callback Keep from loop keep
helper_callback Swap from loop swap
helper_callback Stopped from loop (.stop .refused)

def Collision_association : Unit := ()

open Lean Elab Command in
run_cmd do
  let name := mkIdent `Collision
  let failed ← try
    ZkcTools.StructuredSource.HelperCallbacks.elabHelperCallback
      (← `(command| helper_callback $name from loop keep))
    pure false
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    pure true
  unless failed do throwError "expected a generated-declaration collision"
  if (← getEnv).contains `Tests.HelperCallbacks.Collision_selection then
    throwError "failed callback generation left a partial installation"

/-- The same full callback type can have a different state/capture boundary.
The operation, rather than the callback ABI or a name, determines that boundary. -/
def capturesOnly : Region dialect [.index, .index, .index, .index] [] :=
  .letOp (.loop [] [.index, .index])
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil)))) (.cons keep .nil) (.ret .nil)

helper_callback CapturesOnly from capturesOnly
example : CapturesOnly_selection.callback.state = [] := rfl
example : CapturesOnly_selection.callback.captures = [.index, .index] := rfl
example : CapturesOnly = Keep := rfl

def stoppedPrefix : Region dialect [.index, .index, .index, .index] [.index] :=
  .bind (.stop (out := []) .reject) (loop keep)

helper_callback Dormant from stoppedPrefix
example : Dormant = Keep := rfl

/-- A conditional callback has a different return contract. -/
def conditional : Region dialect [.index, .index, .index, .index] [.index] :=
  .letOp (.loopCondition [.index] [.index])
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil))))
    (.cons (.stop .refused) .nil) (.ret (.cons .here .nil))

/-- error: helper-callback-missing: no counted loop at the requested source/path -/
#guard_msgs in
helper_callback Conditional from conditional

/-- error: helper-callback-open-source: instantiate the helper's static parameters first -/
#guard_msgs in
helper_callback Open from loop _

example : Keep_selection.callback.state = [.index] := rfl
example : Keep_selection.callback.captures = [.index] := rfl
example : Keep_selection.callback.inputs = [.index, .index, .index] := rfl
example : Keep_selection.callback.outputs = [.index, .index] := rfl
example : Selected (loop keep) none Keep_selection := Keep_association

def duplicate : Region dialect [.index, .index, .index, .index] [.index] :=
  .bind (loop keep) ((loop keep).rename fun value => .there value)

/- Even identical callbacks with identical schemas are ambiguous. -/
/-- error: helper-callback-ambiguous: select an explicit checked path -/
#guard_msgs in
helper_callback Ambiguous from duplicate

/-- error: helper-callback-missing: no counted loop at the requested source/path -/
#guard_msgs in
helper_callback Missing from keep

/-- error: helper-callback-missing: no counted loop at the requested source/path -/
#guard_msgs in
helper_callback WrongPath from duplicate at [.region 0]

helper_callback First from duplicate at [.bound]
helper_callback Second from duplicate at [.next]
example : First = keep := rfl
example : Second = keep := rfl

def nestedBody : Region dialect [.index, .index, .index] [.index, .index] :=
  .letOp (.loop [.index] [.index])
    (.cons .here (.cons .here (.cons (.there .here)
      (.cons (.there (.there .here)) .nil)))) (.cons swap .nil)
    (.ret (.cons .here (.cons (.there (.there (.there .here))) .nil)))

/-- error: helper-callback-ambiguous: select an explicit checked path -/
#guard_msgs in
helper_callback NestedAmbiguous from loop nestedBody

helper_callback Outer from loop nestedBody at []
helper_callback Inner from loop nestedBody at [.region 0]
example : Outer = nestedBody := rfl
example : Inner = swap := rfl

def branched : Region dialect [.boolean, .index, .index, .index, .index] [.index] :=
  .letOp (.branch [.index, .index, .index, .index] [.index])
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) .nil)))))
    (.cons (loop keep) (.cons (loop swap) .nil)) (.ret (.cons .here .nil))

/-- error: helper-callback-ambiguous: select an explicit checked path -/
#guard_msgs in
helper_callback BranchAmbiguous from branched

helper_callback Left from branched at [.region 0]
helper_callback Right from branched at [.region 1]
example : Left = keep := rfl
example : Right = swap := rfl
example : Right = Right_selection.callback.body := Right_body_association

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Every return, including the capture, remains observable in its original order. -/
example (table : Meanings F G) (i state capture : Nat) :
    Keep.denote (meaning F G table) (Values.cons i (.cons state (.cons capture .nil))).get =
      .done (.cons state (.cons capture .nil)) := rfl

example (table : Meanings F G) (i state capture : Nat) :
    Swap.denote (meaning F G table) (Values.cons i (.cons state (.cons capture .nil))).get =
      .done (.cons capture (.cons state .nil)) := rfl

example (table : Meanings F G) (i state capture : Nat) :
    Stopped.denote (meaning F G table) (Values.cons i (.cons state (.cons capture .nil))).get =
      .halt .refused := rfl

example (table : Meanings F G) (state capture : Nat) :
    (loop (.stop .refused)).denote (meaning F G table)
      (Values.cons 0 (.cons 1 (.cons state (.cons capture .nil)))).get =
      .halt .refused := rfl

/-- Selecting syntax never bypasses a stopped prefix or proves reachability. -/
example (table : Meanings F G) (state capture : Nat) :
    stoppedPrefix.denote (meaning F G table)
      (Values.cons 0 (.cons 1 (.cons state (.cons capture .nil)))).get =
      .halt .reject := rfl

/-- The selected body still runs through the existing loop evaluator. It may
return a changed capture, but each iteration receives the original capture. -/
example (table : Meanings F G) (state capture : Nat) :
    Evaluation.denoteLoop [.index] [.index]
      (fun args => Swap.denote (meaning F G table) args.get) 0 2
      (.cons state .nil) (.cons capture .nil) = .done (.cons capture .nil) := rfl

example (table : Meanings F G) (state capture : Nat) :
    Evaluation.denoteLoop [.index] [.index]
      (fun args => Stopped.denote (meaning F G table) args.get) 0 1
      (.cons state .nil) (.cons capture .nil) = .halt .refused := rfl

/-- Empty loops never execute a stopping callback. -/
example (table : Meanings F G) (state capture : Nat) :
    Evaluation.denoteLoop [.index] [.index]
      (fun args => Stopped.denote (meaning F G table) args.get) 0 0
      (.cons state .nil) (.cons capture .nil) = .done (.cons state .nil) := rfl

/-- Fixed old goals do not become true after changing the actual return order. -/
example (table : Meanings F G) :
    Swap.denote (meaning F G table) (Values.cons 0 (.cons 1 (.cons 2 .nil))).get ≠
      .done (.cons 1 (.cons 2 .nil)) := by
  intro same
  have values := PIR.Process.done.inj same
  have first := congrArg (fun values => values.get .here) values
  change (2 : Nat) = 1 at first
  omega

end Tests.HelperCallbacks
