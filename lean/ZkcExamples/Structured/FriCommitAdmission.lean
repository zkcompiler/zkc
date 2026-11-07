module

public import ZkcExamples.Structured.FriCommitRound
public import Zkc.Source.Structured.Bindings.Continuation
public meta import ZkcTools.StructuredSource.Bindings.CheckedCallback
public meta import ZkcExamples.Structured.FriCommitRound

@[expose] public section

/-! Commit's entry, its first repeat, and the three input-side values
the returned declaration still needs after the loop. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCommitAdmission
open Zkc.Source Zkc.Source.Structured Bindings FriCommitRound FriSource FriSourceBodies

theorem roundOnSpine : roundOccurrence.onSpine = true := by kernel_rfl

checked_repeat_prefix admission := roundOccurrence using roundOnSpine

def shiftPort : Var roundSite.context (.field extension) :=
  (roundSite.outerOperand (.field extension) (.returned 6)).get (by decide +kernel)

def sizePort : Var roundSite.context .index :=
  (roundSite.outerOperand .index (.returned 7)).get (by decide +kernel)

def countPort : Var roundSite.context .index :=
  (roundSite.outerOperand .index (.returned 9)).get (by decide +kernel)

def arguments (model : DomainModel) (shift : model.Field extension) (service : Nat) :
    Values (FriBinding.Value model) protocol0Signature.inputs :=
  .cons none (.cons none (.cons (OracleProtocol.concrete model (.field extension) shift)
    (.cons (OracleProtocol.concrete model .index 3)
      (.cons (OracleProtocol.concrete model (.service FriScalarLoop.contract) service) .nil))))

end ZkcExamples.Structured.FriCommitAdmission
