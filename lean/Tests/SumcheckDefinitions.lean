import Zkc.Protocols.Sumcheck.Definitions
import Zkc.Source.LocatedExecution
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Tests.SumcheckDefinitions

open Zkc.Polynomial Zkc.Protocols.Sumcheck

abbrev F := ZMod 7

def polynomial : Quadratic F 1 := .node (.constant 1) (.constant 2) (.constant 0)
def message : Zkc.Protocols.AlgebraicRounds.Message F := ⟨1, 2, 0⟩
def send (_ : Unit) := (message, ())
def react (_ : Unit) (_ : F) := ()

example : Definitions.run send react polynomial 4 () [2, 6] =
    ⟨.returned true, ((), [6]), [.message message, .challenge 2]⟩ := rfl

example : Definitions.run send react polynomial 0 () [2, 6] =
    ⟨.stopped .reject, ((), [2, 6]), [.message message, .reject]⟩ := rfl

example : Definitions.run send react polynomial 4 () [] =
    ⟨.stopped .exhausted, ((), []), [.message message]⟩ := rfl

/-- Same message and accepted round, but the wrong original polynomial fails at the terminal. -/
example : Definitions.run send react (.node (.constant 2) (.constant 0) (.constant 0)) 4 () [2, 6] =
    ⟨.returned false, ((), [6]), [.message message, .challenge 2]⟩ := rfl

/-- Storing a whole verifier does not turn its receive into a local computation.
This holds for every positive round count and every actual input environment. -/
example {K : Type} {n : Nat} [CommSemiring K] [DecidableEq K]
    (count : Nat) (env : Zkc.Source.Environment (Source.Value K n) Definitions.signature.arguments)
    (locations : (Zkc.Protocols.AlgebraicRounds.interface K).Op → Option Unit)
    (receive : locations .message = none) :
    ¬ Zkc.Source.LocatedExecution.LocallyAdmitted locations ()
      (Definitions.invocation.denote ((Definitions.definitions (count + 1)).meaning
        Source.meaning) env) := by
  rw [Definitions.invocation_denote, Source.program_denote]
  intro admitted
  have impossible : locations .message = some () := admitted.1
  rw [receive] at impossible
  cases impossible

end Tests.SumcheckDefinitions
