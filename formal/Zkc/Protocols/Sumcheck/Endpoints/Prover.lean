import Zkc.Source.LocalExecution
import Zkc.Protocols.AlgebraicRounds.Source

/-! Bound prover source for message production and delivered-challenge reaction.

Callbacks are mathematical input with explicit private memory. They are fixed
independently of the hidden provider state. The source and local resolver do not
inspect arbitrary host closures or certify a native callback implementation.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Endpoints.Prover

open PIR Zkc.Source Zkc.Source.LocalExecution
open AlgebraicRounds (Message)

inductive Ty where | memory | challenge | emission | boolean
  deriving DecidableEq, Repr
inductive Op where | send | react
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .send => [.memory]
  | .react => [.memory, .challenge]
def result : Op → Ty
  | .send => .emission
  | .react => .memory
abbrev language : Language := ⟨Ty, Op, arguments, result, .boolean⟩
abbrev Value (F S : Type) : Ty → Type
  | .memory => S
  | .challenge => F
  | .emission => Message F × S
  | .boolean => Bool

variable {F S H : Type}

abbrev meaning (send : S → Message F × S) (react : S → F → S) : Interpretation language noEffects where
  Value := Value F S
  condition := id
  operation
    | .send, .cons state .nil => .done (send state)
    | .react, .cons state (.cons challenge .nil) => .done (react state challenge)

def sendInputs : List (InputDeclaration Ty) := [⟨"memory", .memory, .privateTo "prover", .argument⟩]
def reactInputs : List (InputDeclaration Ty) := [
  ⟨"memory", .memory, .privateTo "prover", .argument⟩,
  ⟨"challenge", .challenge, .shared, .argument⟩]

def sendProgram : Program language (sendInputs.map (·.type)) .emission :=
  .letOp .send (.cons .here .nil) (.ret .here)
def reactProgram : Program language (reactInputs.map (·.type)) .memory :=
  .letOp .react (.cons .here (.cons (.there .here) .nil)) (.ret .here)

def world (memory : Option S) (challenge : Option F)
    (other : String → LocalInputs.Store (Value F S)) (hidden : H) : LocalInputs.World (Value F S) H where
  shared name ty := match ty with
    | .challenge => if name = "challenge" then challenge else none
    | _ => none
  privateInputs role name ty :=
    if role = "prover" then match ty with
      | .memory => if name = "memory" then memory else none
      | _ => none
    else other role name ty
  hidden := hidden

theorem send_execution (send : S → Message F × S) (react : S → F → S) (memory : S)
    (other : String → LocalInputs.Store (Value F S)) (hidden : H) :
    LocalInputs.run (meaning send react) noHandler "prover" sendInputs sendProgram
      (world (some memory) none other hidden) () = .ok ⟨.returned (send memory), (), []⟩ := rfl

theorem react_execution (send : S → Message F × S) (react : S → F → S) (memory : S) (challenge : F)
    (other : String → LocalInputs.Store (Value F S)) (hidden : H) :
    LocalInputs.run (meaning send react) noHandler "prover" reactInputs reactProgram
      (world (some memory) (some challenge) other hidden) () = .ok ⟨.returned (react memory challenge), (), []⟩ := rfl

theorem send_locality (send : S → Message F × S) (react : S → F → S)
    (left right : LocalInputs.World (Value F S) H) (same : LocalInputs.SameView "prover" left right) :
    LocalInputs.run (meaning send react) noHandler "prover" sendInputs sendProgram left () =
      LocalInputs.run (meaning send react) noHandler "prover" sendInputs sendProgram right () :=
  LocalInputs.run_agrees _ _ _ _ _ _ _ _ same

theorem react_locality (send : S → Message F × S) (react : S → F → S)
    (left right : LocalInputs.World (Value F S) H) (same : LocalInputs.SameView "prover" left right) :
    LocalInputs.run (meaning send react) noHandler "prover" reactInputs reactProgram left () =
      LocalInputs.run (meaning send react) noHandler "prover" reactInputs reactProgram right () :=
  LocalInputs.run_agrees _ _ _ _ _ _ _ _ same

/-- These callbacks execute the actual bound local programs. The option proof
is supplied by those programs' total-execution laws, without a fallback value. -/
def boundSend (send : S → Message F × S) (react : S → F → S) (memory : S) : Message F × S :=
  (returnedValue? (LocalInputs.run (meaning send react) noHandler "prover" sendInputs sendProgram
    (world (some memory) none (fun _ _ _ => none) ()) ())).get (by rfl)

def boundReact (send : S → Message F × S) (react : S → F → S) (memory : S) (challenge : F) : S :=
  (returnedValue? (LocalInputs.run (meaning send react) noHandler "prover" reactInputs reactProgram
    (world (some memory) (some challenge) (fun _ _ _ => none) ()) ())).get (by rfl)

theorem boundSend_exact (send : S → Message F × S) (react : S → F → S) : boundSend send react = send := rfl
theorem boundReact_exact (send : S → Message F × S) (react : S → F → S) : boundReact send react = react := rfl

end Zkc.Protocols.Sumcheck.Endpoints.Prover
