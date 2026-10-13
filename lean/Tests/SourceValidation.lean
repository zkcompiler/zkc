module

public import Zkc.Source.Validation

@[expose] public section

namespace SourceValidationTests
open Zkc.Source

inductive Op where
  | increment | twice | query
  deriving DecidableEq

abbrev language : Language where
  Ty := Unit
  Op := Op
  arguments _ := [()]
  result _ := ()
  condition := ()

abbrev interface : PIR.Signature := ⟨Nat, fun _ => Nat⟩

abbrev meaning : Interpretation language interface where
  Value _ := Nat
  condition value := value != 0
  operation
    | .increment, .cons value .nil => .done (value + 1)
    | .twice, .cons value .nil => .done ((value + 1) + 1)
    | .query, .cons value .nil => .call value .done

def twiceBody : Program language [()] () :=
  .letOp .increment (.cons .here .nil)
    (.letOp .increment (.cons .here .nil) (.ret .here))

def helpers : OperationExpansion language
  | .twice => some twiceBody
  | _ => none

theorem helpers_sound : helpers.Sound meaning := by
  intro op body selected arguments
  cases op <;> simp only [helpers] at selected
  · cases selected
  · cases selected
    cases arguments with
    | cons value rest => cases rest; rfl
  · cases selected

def normalizer : Normalizer meaning := .expansion helpers helpers_sound

def original : RawProgram Unit Op :=
  .letOp .twice [0] (.branch 0 (.letOp .query [0] (.ret 0)) (.stop .reject))

def expanded : RawProgram Unit Op :=
  .letOp .increment [0] (.letOp .increment [0]
    (.branch 0 (.letOp .query [0] (.ret 0)) (.stop .reject)))

example : normalizer.check [()] () original expanded = true := by decide +kernel

def inputValues (value : Nat) : Values meaning.Value [()] := .cons value .nil

/-- A symbolic-input proof, valid for any query handler and its residual state. -/
theorem helper_refinement (input : Nat) :
    original.denote meaning () (inputValues input).get =
      expanded.denote meaning () (inputValues input).get :=
  normalizer.check_sound [()] () original expanded (by decide +kernel) _

/-- Keeping the guard and query occurrence does not excuse using an old operand. -/
def staleOperand : RawProgram Unit Op :=
  .letOp .increment [0] (.letOp .increment [0]
    (.branch 0 (.letOp .query [2] (.ret 0)) (.stop .reject)))

example : normalizer.check [()] () original staleOperand = false := by decide +kernel
example : normalizer.check [()] () original (.ret 0) = false := by decide +kernel

/-- A dead malformed branch is still refused by static validation. -/
def deadMalformed : RawProgram Unit Op := .branch 0 (.ret 0) (.ret 42)
example : deadMalformed.denote meaning () (inputValues 1).get = .done 1 := rfl
example : normalizer.check [()] () deadMalformed deadMalformed = false := by decide +kernel

/-- The same requirement applies to a loop body even when its count is zero. -/
def emptyMalformed : RawProgram Unit Op := .iterate 0 () 0 (.ret 42) (.ret 0)
example : emptyMalformed.denote meaning () (inputValues 7).get = .done 7 := rfl
example : normalizer.check [()] () emptyMalformed emptyMalformed = false := by decide +kernel

def repeated : RawProgram Unit Op := .iterate 4 () 0 original (.ret 0)
def repeatedExpanded : RawProgram Unit Op := .iterate 4 () 0 expanded (.ret 0)
example : normalizer.check [()] () repeated repeatedExpanded = true := by decide +kernel

end SourceValidationTests
