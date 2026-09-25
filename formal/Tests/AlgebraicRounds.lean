import Zkc.Protocols.AlgebraicRounds.Fresh
import Zkc.Protocols.AlgebraicRounds.Framed
import Zkc.Protocols.AlgebraicRounds.Endpoints
import Mathlib.Data.ZMod.Basic

/-! Operational controls for one actual structured source under two constructions.
The framed query below is deliberately transparent, not a cryptographic hash.
-/

set_option autoImplicit false

namespace Tests.AlgebraicRounds

open PIR Zkc.Protocols.AlgebraicRounds Construction

abbrev F := ZMod 7

/-- Messages for the product of all remaining Boolean variables. Delivered
challenges update the next coefficient, so later messages are adaptive. -/
def send := Endpoints.send (F := F)
def react := Endpoints.react (F := F)
def draw : Draw F (List F)
  | [] => (.stopped .exhausted, [])
  | value :: tail => (.returned value, tail)

def query (frames : List (Frame F)) (state : Nat) : Outcome F × Nat :=
  match frames.reverse.findSome? (fun frame => match frame with
    | .message _ message => some message.linear
    | _ => none) with
  | none => (.stopped .refused, state + 1)
  | some coefficient => (.returned (coefficient + 1), state + 1)

def freshRun := Fresh.run send react draw 2 (1 : F) 1 [2, 3, 4]
def framedRun := Framed.run "product" send react query 2 (1 : F) 1 0

example : freshRun =
    ⟨.returned 6, (6, [4]), [.message ⟨0,1,0⟩, .challenge 2,
      .message ⟨0,2,0⟩, .challenge 3]⟩ := rfl

example : framedRun.outcome = .returned 6 ∧ framedRun.state.provider = 2 ∧
    framedRun.state.position = 2 := ⟨rfl, rfl, rfl⟩

example : framedRun.events = [
    .message ⟨0,1,0⟩,
    .query [.context "product" 2 1, .message 0 ⟨0,1,0⟩, .request 0],
    .challenge 2,
    .message ⟨0,2,0⟩,
    .query [.context "product" 2 1, .message 0 ⟨0,1,0⟩, .request 0, .challenge 0 2,
      .message 1 ⟨0,2,0⟩, .request 1],
    .challenge 3] := rfl

example : framedRun.state.frames = [
    .context "product" 2 1, .message 0 ⟨0,1,0⟩, .request 0, .challenge 0 2,
    .message 1 ⟨0,2,0⟩, .request 1, .challenge 1 3] := rfl

example : Fresh.run send react draw 2 (1 : F) 1 [2] =
    ⟨.stopped .exhausted, (2, []), [.message ⟨0,1,0⟩, .challenge 2, .message ⟨0,2,0⟩]⟩ := rfl

def exhausted : Query F Nat := fun _ state => (.stopped .exhausted, state + 1)
def failed := Framed.run "product" send react exhausted 2 (1 : F) 1 10

example : failed = ⟨.stopped .exhausted,
    ⟨1, 11, [.context "product" 2 1, .message 0 ⟨0,1,0⟩, .request 0], 0⟩,
    [.message ⟨0,1,0⟩, .query [.context "product" 2 1, .message 0 ⟨0,1,0⟩, .request 0]]⟩ := rfl

example : Framed.run "product" send react query 2 (2 : F) 1 0 =
    ⟨.stopped .reject, ⟨1, 0, [.context "product" 2 2, .message 0 ⟨0,1,0⟩], 0⟩,
      [.message ⟨0,1,0⟩, .reject]⟩ := rfl

/-- Replacing only the draw operation misses the message-absorption transition. -/
def missingAbsorption : OperationInterpretation
    (Zkc.Protocols.AlgebraicRounds.interface F) (Construction.interface F)
  | .message => .call .receive .done
  | .challenge => .call .squeeze .done
  | .reject => .call .reject .done

example : ¬Conforms framedInteraction
    ((rounds 1 (1 : F)).interpret missingAbsorption) (.ready (start 1 1)) := by
  intro formed
  have wrong := (formed.2 ⟨0,1,0⟩).1
  exact wrong

example : (((rounds 1 (1 : F)).interpret missingAbsorption).run
    (Framed.handler send react query) (Framed.initial "product" 1 1 1 0)).outcome =
      .stopped .refused := rfl

example : (Framed.run "product" send react query 1 (1 : F) 1 0).outcome = .returned 2 := rfl

example : framedRun.events ≠
    (Framed.run "another-domain" send react query 2 (1 : F) 1 0).events := by decide

example : (Framed.initial "product" 2 (1 : F) (1 : F) (0 : Nat)).frames ≠
    (Framed.initial "product" 3 (1 : F) (1 : F) (0 : Nat)).frames := by decide

open Zkc.Source

def noPrivateInputs : String → LocalInputs.Store (Arithmetic.Value F) := fun _ _ _ => none
def otherPrivateInputs : String → LocalInputs.Store (Arithmetic.Value F) :=
  fun _ _ ty => match ty with | .scalar => some 4 | .boolean => some true

example : LocalInputs.run Endpoints.localMeaning Endpoints.noHandler
    "prover" Endpoints.proverInputs Endpoints.reaction
      (Endpoints.proverWorld (3 : F) 2 noPrivateInputs (10 : Nat)) () =
    LocalInputs.run Endpoints.localMeaning Endpoints.noHandler
      "prover" Endpoints.proverInputs Endpoints.reaction
        (Endpoints.proverWorld (3 : F) 2 otherPrivateInputs (99 : Nat)) () :=
  Endpoints.prover_locality _ _ ⟨rfl, rfl⟩

/-- The verifier consumes no private inputs in this fragment, even its own. -/
example (message : Message F) (challenge : F) :
    LocalInputs.run Endpoints.localMeaning Endpoints.noHandler
      "verifier" Endpoints.verifierInputs Endpoints.evaluation
        (Endpoints.verifierWorld message challenge noPrivateInputs (10 : Nat)) () =
    LocalInputs.run Endpoints.localMeaning Endpoints.noHandler
      "verifier" Endpoints.verifierInputs Endpoints.evaluation
        (Endpoints.verifierWorld message challenge otherPrivateInputs (99 : Nat)) () :=
  (Endpoints.evaluation_execution _ _ _ _).trans (Endpoints.evaluation_execution _ _ _ _).symm

example : LocalInputs.bind "verifier"
    [⟨"coefficient", Arithmetic.Ty.scalar, .privateTo "prover", .capture⟩]
    (Endpoints.proverWorld (3 : F) 2 noPrivateInputs (10 : Nat)) =
      .error (.wrongRole "coefficient") := rfl

example : LocalInputs.bind "prover"
    [⟨"futureChallenge", Arithmetic.Ty.scalar, .shared, .argument⟩]
    (Endpoints.proverWorld (3 : F) 2 noPrivateInputs (10 : Nat)) =
      .error (.missingInput "futureChallenge") := rfl

example : LocalInputs.bind "prover"
    [⟨"providerState", Arithmetic.Ty.scalar, .privateTo "prover", .capture⟩]
    (Endpoints.proverWorld (3 : F) 2 noPrivateInputs (10 : Nat)) =
      .error (.missingInput "providerState") := rfl

end Tests.AlgebraicRounds
