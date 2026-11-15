module

public import Zkc.Core.Program.Problem

@[expose] public section

/-!
A refusal: a rule, the place of a program that breaks it, and what the rule found there. The
frontend words it.
-/

namespace Zkc.Core

/-- A refusal: a rule, a place, and what the rule found, with the types of a function and its
written operations as values. -/
structure Refusal (V : Vocabulary) where
  rule : Rule
  place : Place
  detail : Detail V.Ty (LocalRaw V)
deriving DecidableEq

/-- A problem in the body of a definition, as a refusal at its place. -/
def Problem.refusal {V : Vocabulary} (definition : Key) (problem : Problem V.Ty (LocalRaw V)) :
    Refusal V :=
  ⟨problem.rule, ⟨definition, problem.blocks, problem.instruction, none⟩, problem.detail⟩

/-- A refusal of a definition as a whole, with its key as what was found. -/
def definitionRefusal {V : Vocabulary} (key : Key) (rule : Rule) : Refusal V :=
  ⟨rule, ⟨key, [], none, none⟩, .key key⟩

end Zkc.Core
