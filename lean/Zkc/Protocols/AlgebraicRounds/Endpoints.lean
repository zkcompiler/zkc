import Zkc.Protocols.AlgebraicRounds.Fresh
import Zkc.Source.LocalInputs
import Zkc.Source.Arithmetic

/-! Concrete local arithmetic sources used by the algebraic-round endpoints.

The prover's reaction reads its private coefficient and the delivered challenge.
The verifier's evaluation reads the received message and delivered challenge.
The resolver cannot provide another role's private value or hidden provider state.
This is supplied-code locality, not general choreography projection or secrecy
of messages intentionally sent by the protocol.
-/

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.Endpoints

open PIR Source

abbrev noEffects : Signature := ⟨Empty, fun op => nomatch op⟩
def noHandler : Handler noEffects Unit Empty := fun op => nomatch op

variable {F H : Type} [Semiring F]

abbrev localMeaning : Interpretation Arithmetic.language noEffects :=
  Arithmetic.interpretation (fun value : F => .done value)

def proverInputs : List (InputDeclaration Arithmetic.Ty) := [
  ⟨"coefficient", .scalar, .privateTo "prover", .argument⟩,
  ⟨"challenge", .scalar, .shared, .argument⟩]

def verifierInputs : List (InputDeclaration Arithmetic.Ty) := [
  ⟨"constant", .scalar, .shared, .argument⟩,
  ⟨"linear", .scalar, .shared, .argument⟩,
  ⟨"quadratic", .scalar, .shared, .argument⟩,
  ⟨"challenge", .scalar, .shared, .argument⟩]

def reaction : Program Arithmetic.language (proverInputs.map (·.type)) .scalar :=
  .letOp .multiply (.cons .here (.cons (.there .here) .nil)) (.ret .here)

def evaluation : Program Arithmetic.language (verifierInputs.map (·.type)) .scalar :=
  .letOp .quadratic
    (.cons .here (.cons (.there .here)
      (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))))
    (.ret .here)

def proverWorld (coefficient challenge : F) (other : String → LocalInputs.Store (Arithmetic.Value F))
    (hidden : H) : LocalInputs.World (Arithmetic.Value F) H where
  shared name ty := match ty with
    | .boolean => none
    | .scalar => if name = "challenge" then some challenge else none
  privateInputs role name ty :=
    if role = "prover" then match ty with
      | .boolean => none
      | .scalar => if name = "coefficient" then some coefficient else none
    else other role name ty
  hidden := hidden

def verifierWorld (message : Message F) (challenge : F)
    (privateInputs : String → LocalInputs.Store (Arithmetic.Value F)) (hidden : H) :
    LocalInputs.World (Arithmetic.Value F) H where
  shared name ty := match ty with
    | .boolean => none
    | .scalar => match name with
      | "constant" => some message.constant
      | "linear" => some message.linear
      | "quadratic" => some message.quadratic
      | "challenge" => some challenge
      | _ => none
  privateInputs := privateInputs
  hidden := hidden

theorem reaction_execution (coefficient challenge : F)
    (other : String → LocalInputs.Store (Arithmetic.Value F)) (hidden : H) :
    LocalInputs.run localMeaning noHandler "prover" proverInputs reaction
      (proverWorld coefficient challenge other hidden) () =
        .ok ⟨.returned (coefficient * challenge), (), []⟩ := rfl

theorem evaluation_execution (message : Message F) (challenge : F)
    (privateInputs : String → LocalInputs.Store (Arithmetic.Value F)) (hidden : H) :
    LocalInputs.run localMeaning noHandler "verifier" verifierInputs evaluation
      (verifierWorld message challenge privateInputs hidden) () =
        .ok ⟨.returned (message.evaluate challenge), (), []⟩ := rfl

theorem prover_locality (left right : LocalInputs.World (Arithmetic.Value F) H)
    (same : LocalInputs.SameView "prover" left right) :
    LocalInputs.run localMeaning noHandler "prover" proverInputs reaction left () =
      LocalInputs.run localMeaning noHandler "prover" proverInputs reaction right () :=
  LocalInputs.run_agrees localMeaning noHandler "prover" proverInputs reaction left right () same

theorem verifier_locality (left right : LocalInputs.World (Arithmetic.Value F) H)
    (same : LocalInputs.SameView "verifier" left right) :
    LocalInputs.run localMeaning noHandler "verifier" verifierInputs evaluation left () =
      LocalInputs.run localMeaning noHandler "verifier" verifierInputs evaluation right () :=
  LocalInputs.run_agrees localMeaning noHandler "verifier" verifierInputs evaluation left right () same

/-- The actual reaction used by the product-polynomial sender. The execution
theorem above derives this value from declared source and local input binding. -/
def react (coefficient challenge : F) : F := coefficient * challenge

def send (coefficient : F) : Message F × F := (⟨0, coefficient, 0⟩, coefficient)

/-- Tie the actual provider delivery to the bound local reaction, including its
post-state. Future provider data is not part of the world's available store. -/
theorem delivered_reaction {Q : Type} (draw : Construction.Draw F Q)
    (coefficient challenge : F) (provider next : Q)
    (delivered : draw provider = (.returned challenge, next))
    (other : String → LocalInputs.Store (Arithmetic.Value F)) (hidden : H) :
    (Fresh.handler send react draw .sample (coefficient, provider)).state.1 = coefficient * challenge ∧
    LocalInputs.run localMeaning noHandler "prover" proverInputs reaction
      (proverWorld coefficient challenge other hidden) () =
        .ok ⟨.returned (Fresh.handler send react draw .sample (coefficient, provider)).state.1, (), []⟩ := by
  simp only [Fresh.handler, delivered, react]
  exact ⟨trivial, reaction_execution coefficient challenge other hidden⟩

end Zkc.Protocols.AlgebraicRounds.Endpoints
