module

public import ZkcTools.ConstructionBindings.MathRegion

@[expose] public section

/-! A closed source slice can occupy different caller frames. Same-typed
operand substitutions, a changed return selection and discarded physical work
must not acquire a connection merely by having the same signature. -/
set_option autoImplicit false
namespace Tests.ConnectionMathSlices
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ConnectionMathRegion

def body : Region dialect [.index, .index] [.index] :=
  .letOp .indexWrappingSubtract (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

def target (left right : Nat) : TargetBlock := fun model ↦
  Domain.View.sequence
    (Domain.View.calculation model .indexWrappingSubtract [left, right] [.data .index])
    Domain.View.empty

/-- One derivation works at any pair of locations and any caller extent. -/
def placed (definitions : List CheckedDefinition) (left right extent : Nat) :
    Alignment definitions body [.data left, .data right] extent
      (target left right) [extent] (extent + 1) := by
  derive_math_region

/-- The actual core soundness rule supplies execution and frame preservation. -/
noncomputable def execution (definitions : List CheckedDefinition) (left right extent : Nat) :=
  (placed definitions left right extent).sound

example : Alignment [] body [.data 1, .data 0] 7 (target 1 0) [7] 8 := by
  derive_math_region

example : True := by
  fail_if_success
    have : Alignment [] body [.data 1, .data 0] 7 (target 0 1) [7] 8 := by
      derive_math_region
  trivial

example : True := by
  fail_if_success
    have : Alignment [] body [.data 1, .data 0] 7 (target 1 0) [0] 8 := by
      derive_math_region
  trivial

example : True := by
  fail_if_success
    have : Alignment [] body [.data 1, .data 0] 7
        (fun model ↦ Domain.View.sequence
          (Domain.View.calculation model .indexWrappingSubtract [1, 0] [.data .index])
          (target 1 0 model)) [7] 8 := by
      derive_math_region
  trivial

#print axioms placed
#print axioms execution

def subtract : CheckedDefinition where
  name := "subtract"
  kind := .math
  inputs := [.index, .index]
  outputs := [.index]
  raw := body.erase
  body := body
  formed := Region.elaborate_erase body

def twiceBody : Region dialect [.index, .index] [.index] :=
  .letOp (.invoke subtract.helper) (.cons .here (.cons (.there .here) .nil)) .nil
    (.letOp (.invoke subtract.helper) (.cons .here (.cons (.there (.there .here)) .nil)) .nil
      (.ret (.cons .here .nil)))

def twice : CheckedDefinition where
  name := "twice"
  kind := .math
  inputs := [.index, .index]
  outputs := [.index]
  raw := twiceBody.erase
  body := twiceBody
  formed := Region.elaborate_erase twiceBody

def nestedBody : Region dialect [.index, .index] [.index] :=
  .letOp (.invoke twice.helper) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

def nestedTarget (left right extent : Nat) : TargetBlock := fun model ↦
  Domain.View.sequence
    (Domain.View.calculation model .indexWrappingSubtract [left, right] [.data .index])
    (target extent right model)

/-- A nested checked call and its two inner applications share the same
derivation at arbitrary caller locations, without a helper-result assumption. -/
def nested (left right extent : Nat) :
    Alignment [subtract, twice] nestedBody [.data left, .data right] extent
      (nestedTarget left right extent) [extent + 1] (extent + 1 + 1) := by
  derive_math_region

noncomputable def nestedExecution (left right extent : Nat) := (nested left right extent).sound

example : True := by
  fail_if_success
    have : Alignment [subtract, twice] nestedBody [.data 1, .data 0] 7
        (nestedTarget 0 1 7) [8] 9 := by
      derive_math_region
  trivial

example : True := by
  fail_if_success
    have : Alignment [twice, subtract] nestedBody [.data 1, .data 0] 7
        (nestedTarget 1 0 7) [8] 9 := by
      derive_math_region
  trivial

#print axioms nested
#print axioms nestedExecution
end Tests.ConnectionMathSlices
