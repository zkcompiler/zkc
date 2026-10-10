import Zkc.Source.LocalExecution
import Zkc.Protocols.Sumcheck.Source

/-! Bound verifier source for round checking, advancement and terminal evaluation.

The received message, delivered challenge and original statement are explicit
available inputs. The accumulator belongs to verifier memory. Hidden provider
state and another role's private store cannot be resolved by these programs.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Endpoints.Verifier

open PIR Zkc.Source Zkc.Source.LocalExecution Zkc.Polynomial
open AlgebraicRounds (Message)

variable {F H : Type} {n : Nat} [CommSemiring F] [DecidableEq F]

abbrev meaning : Interpretation Source.language noEffects where
  Value := Source.Value F n
  condition := id
  operation op args := match op with
    | .receive | .draw | .reject => .halt .refused
    | .check => match args with
      | .cons message (.cons accumulator .nil) => .done (decide (message.boundary = accumulator.claim))
    | .advance => match args with
      | .cons message (.cons r (.cons accumulator .nil)) => .done (Source.advance message r accumulator)
    | .terminal => match args with
      | .cons p (.cons accumulator .nil) => .done (Source.terminal p accumulator)

def checkInputs : List (InputDeclaration Source.Ty) := [
  ⟨"message", .message, .shared, .argument⟩,
  ⟨"accumulator", .accumulator, .privateTo "verifier", .argument⟩]

def advanceInputs : List (InputDeclaration Source.Ty) := [
  ⟨"message", .message, .shared, .argument⟩,
  ⟨"challenge", .scalar, .shared, .argument⟩,
  ⟨"accumulator", .accumulator, .privateTo "verifier", .argument⟩]

def terminalInputs : List (InputDeclaration Source.Ty) := [
  ⟨"statement", .polynomial, .shared, .argument⟩,
  ⟨"accumulator", .accumulator, .privateTo "verifier", .argument⟩]

def checkProgram : Program Source.language (checkInputs.map (·.type)) .boolean :=
  .letOp .check (.cons .here (.cons (.there .here) .nil)) (.ret .here)
def advanceProgram : Program Source.language (advanceInputs.map (·.type)) .accumulator :=
  .letOp .advance (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) (.ret .here)
def terminalProgram : Program Source.language (terminalInputs.map (·.type)) .boolean :=
  .letOp .terminal (.cons .here (.cons (.there .here) .nil)) (.ret .here)

def world (message : Option (Message F)) (challenge : Option F)
    (accumulator : Option (Source.Accumulator F)) (polynomial : Option (Quadratic F n))
    (other : String → LocalInputs.Store (Source.Value F n)) (hidden : H) :
    LocalInputs.World (Source.Value F n) H where
  shared name ty := match ty with
    | .message => if name = "message" then message else none
    | .scalar => if name = "challenge" then challenge else none
    | .polynomial => if name = "statement" then polynomial else none
    | _ => none
  privateInputs role name ty :=
    if role = "verifier" then match ty with
      | .accumulator => if name = "accumulator" then accumulator else none
      | _ => none
    else other role name ty
  hidden := hidden

theorem check_execution (message : Message F) (accumulator : Source.Accumulator F)
    (other : String → LocalInputs.Store (Source.Value F n)) (hidden : H) :
    LocalInputs.run meaning noHandler "verifier" checkInputs checkProgram
      (world (some message) none (some accumulator) none other hidden) () =
        .ok ⟨.returned (decide (message.boundary = accumulator.claim)), (), []⟩ := rfl

theorem advance_execution (message : Message F) (r : F) (accumulator : Source.Accumulator F)
    (other : String → LocalInputs.Store (Source.Value F n)) (hidden : H) :
    LocalInputs.run meaning noHandler "verifier" advanceInputs advanceProgram
      (world (some message) (some r) (some accumulator) none other hidden) () =
        .ok ⟨.returned (Source.advance message r accumulator), (), []⟩ := rfl

theorem terminal_execution (p : Quadratic F n) (accumulator : Source.Accumulator F)
    (other : String → LocalInputs.Store (Source.Value F n)) (hidden : H) :
    LocalInputs.run meaning noHandler "verifier" terminalInputs terminalProgram
      (world none none (some accumulator) (some p) other hidden) () =
        .ok ⟨.returned (Source.terminal p accumulator), (), []⟩ := rfl

theorem check_locality (left right : LocalInputs.World (Source.Value F n) H)
    (same : LocalInputs.SameView "verifier" left right) :
    LocalInputs.run meaning noHandler "verifier" checkInputs checkProgram left () =
      LocalInputs.run meaning noHandler "verifier" checkInputs checkProgram right () :=
  LocalInputs.run_agrees _ _ _ _ _ _ _ _ same

theorem advance_locality (left right : LocalInputs.World (Source.Value F n) H)
    (same : LocalInputs.SameView "verifier" left right) :
    LocalInputs.run meaning noHandler "verifier" advanceInputs advanceProgram left () =
      LocalInputs.run meaning noHandler "verifier" advanceInputs advanceProgram right () :=
  LocalInputs.run_agrees _ _ _ _ _ _ _ _ same

theorem terminal_locality (left right : LocalInputs.World (Source.Value F n) H)
    (same : LocalInputs.SameView "verifier" left right) :
    LocalInputs.run meaning noHandler "verifier" terminalInputs terminalProgram left () =
      LocalInputs.run meaning noHandler "verifier" terminalInputs terminalProgram right () :=
  LocalInputs.run_agrees _ _ _ _ _ _ _ _ same

def boundCheck (message : Message F) (accumulator : Source.Accumulator F) : Bool :=
  (returnedValue? (LocalInputs.run (meaning (n := n)) noHandler "verifier" checkInputs checkProgram
    (world (some message) none (some accumulator) none (fun _ _ _ => none) ()) ())).get (by rfl)

def boundAdvance (message : Message F) (r : F) (accumulator : Source.Accumulator F) : Source.Accumulator F :=
  (returnedValue? (LocalInputs.run (meaning (n := n)) noHandler "verifier" advanceInputs advanceProgram
    (world (some message) (some r) (some accumulator) none (fun _ _ _ => none) ()) ())).get (by rfl)

def boundTerminal (p : Quadratic F n) (accumulator : Source.Accumulator F) : Bool :=
  (returnedValue? (LocalInputs.run meaning noHandler "verifier" terminalInputs terminalProgram
    (world none none (some accumulator) (some p) (fun _ _ _ => none) ()) ())).get (by rfl)

theorem boundCheck_exact (message : Message F) (accumulator : Source.Accumulator F) :
    boundCheck (n := n) message accumulator = decide (message.boundary = accumulator.claim) := rfl

theorem boundAdvance_exact (message : Message F) (r : F) (accumulator : Source.Accumulator F) :
    boundAdvance (n := n) message r accumulator = Source.advance message r accumulator := rfl

theorem boundTerminal_exact (p : Quadratic F n) (accumulator : Source.Accumulator F) :
    boundTerminal p accumulator = Source.terminal p accumulator := rfl

end Zkc.Protocols.Sumcheck.Endpoints.Verifier
