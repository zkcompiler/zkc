import Zkc.Compiler.DefinitionInlining

set_option autoImplicit false

namespace Tests.SourceDefinitions

open Zkc.Source Zkc.Compiler PIR

inductive Ty where
  | natural | boolean
  deriving DecidableEq, Repr

inductive Op where
  | increment | record

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments _ := [.natural]
  result _ := .natural
  condition := .boolean

abbrev Value : Ty → Type
  | .natural => Nat
  | .boolean => Bool

abbrev interface : Signature := ⟨Nat, fun _ => Nat⟩

abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation
    | .increment, .cons value .nil => .done (value + 1)
    | .record, .cons value .nil => .call value .done

/-- The failed effect has a real post-state and an emitted attempt. -/
def handler : Handler interface Nat Nat := fun value state =>
  ⟨if value == 0 then .stopped .exhausted else .returned value, state + 1, [value]⟩

abbrev signature : DefinitionSignature Ty := ⟨[.natural, .boolean], .natural⟩

def step : Region (language.withDefinitions []) signature.arguments signature.result :=
  .letOp (.primitive .record) (.cons .here .nil)
    (.branch (.there (.there .here))
      (.letOp (.primitive .increment) (.cons .here .nil) (.ret .here))
      (.stop .reject))

def steps : Definitions language [signature] :=
  Definitions.snoc (language := language) .nil signature step

/-- The loop calls the stored step; the body is not copied into the loop. -/
def twice : Region (language.withDefinitions [signature]) signature.arguments signature.result :=
  .iterate 2 .here
    (.letOp (.call .here) (.cons .here (.cons (.there (.there .here)) .nil)) (.ret .here))
    (.ret .here)

def definitions : Definitions language [signature, signature] := steps.snoc signature twice

abbrev context : List Ty := [.natural, .boolean, .natural]

def arguments : Operands context signature.arguments := .cons .here (.cons (.there .here) .nil)

/-- Reuse the returned value in another invocation, then use an original capture. -/
def suffix :
    Region (language.withDefinitions [signature, signature]) (.natural :: context) .natural :=
  .letOp (.call .here) (.cons .here (.cons (.there (.there .here)) .nil))
    (.letOp (.primitive .record)
      (.cons (.there (.there (.there (.there .here)))) .nil) (.ret .here))

def entry : Region (language.withDefinitions [signature, signature]) context .natural :=
  .letOp (.call .here) arguments suffix

def values (value : Nat) (enabled : Bool) : Values Value context :=
  .cons value (.cons enabled (.cons 99 .nil))

def run (value : Nat) (enabled : Bool) : Execution Nat Nat Nat :=
  (entry.denote (definitions.meaning meaning) (values value enabled).get).run handler 0

example : run 3 true = ⟨.returned 99, 5, [3, 4, 5, 6, 99]⟩ := rfl
example : run 3 false = ⟨.stopped .reject, 1, [3]⟩ := rfl
example : run 0 true = ⟨.stopped .exhausted, 1, [0]⟩ := rfl

/-- The theorem covers arbitrary inputs and state, including both stop paths. -/
example (value : Nat) (enabled : Bool) (state : Nat) :
    ((inlineDefinition twice arguments suffix).denote (definitions.meaning meaning)
        (values value enabled).get).run handler state =
      (entry.denote (definitions.meaning meaning) (values value enabled).get).run handler state :=
  run_inlineDefinition meaning steps twice arguments suffix handler (values value enabled).get state

/-- Same-typed callee substitution can keep the return value but change effects. -/
def wrongCallee : Region (language.withDefinitions [signature, signature]) context .natural :=
  .letOp (.call (.there .here)) arguments suffix

example : (wrongCallee.denote (definitions.meaning meaning) (values 3 true).get).run handler 0 =
    ⟨.returned 99, 4, [3, 4, 5, 99]⟩ := rfl

example : Var.decode ([] : List (DefinitionSignature Ty)) signature 0 = none := rfl
example : Var.decode [signature, signature] signature 2 = none := by decide
example : Var.decode [signature] (⟨[.boolean], .natural⟩ : DefinitionSignature Ty) 0 = none :=
  by decide
example :
    Var.decode [signature] (⟨signature.arguments, .boolean⟩ : DefinitionSignature Ty) 0 = none :=
  by decide

/-- Scoped primitive accounting: definitions/calls have no extra charge. A
failed primitive retains its attempt even at zero remaining budget. This says
nothing about a native stack interpreter's frame or allocation charges. -/
def budgetHandler : Handler interface Nat Nat := fun value remaining =>
  ⟨if remaining == 0 then .stopped .exhausted else .returned value,
    remaining - 1, [value]⟩

def runBudget (remaining : Nat) : Execution Nat Nat Nat :=
  (entry.denote (definitions.meaning meaning) (values 3 true).get).run budgetHandler remaining

example : runBudget 5 = ⟨.returned 99, 0, [3, 4, 5, 6, 99]⟩ := rfl
example : runBudget 3 = ⟨.stopped .exhausted, 0, [3, 4, 5, 6]⟩ := rfl
example : runBudget 0 = ⟨.stopped .exhausted, 0, [3]⟩ := rfl
example (remaining : Nat) :
    ((inlineDefinition twice arguments suffix).denote (definitions.meaning meaning)
      (values 3 true).get).run budgetHandler remaining = runBudget remaining :=
  run_inlineDefinition meaning steps twice arguments suffix budgetHandler (values 3 true).get remaining

end Tests.SourceDefinitions
