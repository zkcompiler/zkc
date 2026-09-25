import Tests.SumcheckAdversary
import Tests.SumcheckFramed
import Zkc.Protocols.Sumcheck.Endpoints.Composition

/-! Actual local programs, availability failures and complete joined executions. -/

set_option autoImplicit false

namespace Tests.SumcheckEndpoints

open PIR Zkc.Source Zkc.Source.LocalExecution Zkc.Protocols.Sumcheck
open Tests.Sumcheck

example : (Endpoints.Composition.runFresh SumcheckAdversary.send SumcheckAdversary.react
    SumcheckAdversary.statement 1 (0, 1) [0, 2]).events =
    [.message ⟨6, 2, 1⟩, .challenge 0, .message ⟨1, 5, 6⟩, .challenge 2] := by decide
example : (Endpoints.Composition.runFresh SumcheckAdversary.send SumcheckAdversary.react
    SumcheckAdversary.statement 1 (0, 1) [0, 2]).state = ((2, 0), []) := by decide
example : (Endpoints.Composition.runFresh dishonestSend react zeroPolynomial 1 () []).outcome =
    .stopped .exhausted := by decide
example : (Endpoints.Composition.runFresh Security.honestSend Security.honestReact
    squarePolynomial squarePolynomial.booleanSum ⟨2, squarePolynomial⟩ [2, 4]).outcome = .returned true := by decide

example : (Endpoints.Composition.runFramed "sumcheck" wrongBoundary react SumcheckFramed.query
    zeroPolynomial 0 () ([], [])).state.frames = SumcheckFramed.request := by decide
example : (Endpoints.Composition.runFramed "sumcheck" wrongBoundary react SumcheckFramed.query
    zeroPolynomial 0 () ([], [])).state.provider = ([], [SumcheckFramed.request]) := by decide

/-- Sending itself changes private memory. The second query fails after the
first delivered challenge; both sends and only one reaction must remain. -/
def changingSend (state : Nat × F) :
    Zkc.Protocols.AlgebraicRounds.Message F × (Nat × F) :=
  (SumcheckAdversary.message state.2, (state.1 + 10, state.2))

def firstRequest : List (Zkc.Protocols.AlgebraicRounds.Construction.Frame F) := [
  .context "sumcheck" 2 1,
  .statement "sumcheck.quadratic.v1" [0, 0, 0, 0, 0, 0, 0, 0, 0],
  .message 0 ⟨6, 2, 1⟩, .request 0]

def secondRequest : List (Zkc.Protocols.AlgebraicRounds.Construction.Frame F) :=
  firstRequest ++ [.challenge 0 0, .message 1 ⟨1, 5, 6⟩, .request 1]

example : Endpoints.Composition.runFramed "sumcheck" changingSend SumcheckAdversary.react
    SumcheckFramed.query SumcheckAdversary.statement 1 (0, 1) ([0], []) =
    ⟨.stopped .exhausted, ⟨(21, 6), ([], [firstRequest, secondRequest]), secondRequest, 1⟩,
      [.message ⟨6, 2, 1⟩, .query firstRequest, .challenge 0,
       .message ⟨1, 5, 6⟩, .query secondRequest]⟩ := by
  rfl

/-- A prover reaction cannot obtain a future challenge from hidden provider state. -/
example : LocalInputs.run (Endpoints.Prover.meaning dishonestSend react) noHandler "prover"
    Endpoints.Prover.reactInputs Endpoints.Prover.reactProgram
    (Endpoints.Prover.world (some ()) none (fun _ _ _ => none) ([2, 3] : List F)) () =
      .error (.missingInput "challenge") := by rfl

/-- A declared foreign private capture fails even if the body could return a value. -/
def foreignCapture : List (InputDeclaration Endpoints.Prover.Ty) := [
  ⟨"memory", .memory, .privateTo "verifier", .capture⟩]
example : LocalInputs.run (Endpoints.Prover.meaning dishonestSend react) noHandler "prover"
    foreignCapture (.ret .here)
    (Endpoints.Prover.world (some ()) (some 2) (fun _ _ _ => none) ()) () =
      .error (.wrongRole "memory") := by rfl

/-- Verifier advancement requires the delivered challenge; terminal use requires
its original statement as well as its local accumulator. -/
example : LocalInputs.run (Endpoints.Verifier.meaning (F := F) (n := 1)) noHandler "verifier"
    Endpoints.Verifier.advanceInputs Endpoints.Verifier.advanceProgram
    (Endpoints.Verifier.world (some falseMessage) none (some ⟨1, []⟩) (some zeroPolynomial)
      (fun _ _ _ => none) ([2, 3] : List F)) () = .error (.missingInput "challenge") := by rfl

example : LocalInputs.run (Endpoints.Verifier.meaning (F := F) (n := 1)) noHandler "verifier"
    Endpoints.Verifier.terminalInputs Endpoints.Verifier.terminalProgram
    (Endpoints.Verifier.world none none (some ⟨0, [2]⟩) none
      (fun _ _ _ => none) ()) () = .error (.missingInput "statement") := by rfl

/-- Hidden future coins may change while the actual bound local action is fixed. -/
example : LocalInputs.run (Endpoints.Prover.meaning dishonestSend react) noHandler "prover"
    Endpoints.Prover.sendInputs Endpoints.Prover.sendProgram
    (Endpoints.Prover.world (some ()) none (fun _ _ _ => none) ([2, 3] : List F)) () =
    LocalInputs.run (Endpoints.Prover.meaning dishonestSend react) noHandler "prover"
      Endpoints.Prover.sendInputs Endpoints.Prover.sendProgram
      (Endpoints.Prover.world (some ()) none (fun _ _ _ => none) ([4, 5] : List F)) () := by
  exact Endpoints.Prover.send_locality dishonestSend react _ _ ⟨rfl, rfl⟩

end Tests.SumcheckEndpoints
