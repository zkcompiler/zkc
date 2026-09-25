import Tests.Sumcheck
import Zkc.Protocols.Sumcheck.Framed

/-! Full-statement framing and retained failed query state. -/

set_option autoImplicit false

namespace Tests.SumcheckFramed

open PIR Zkc.Polynomial Zkc.Protocols.Sumcheck Tests.Sumcheck
open Zkc.Protocols.AlgebraicRounds.Construction (Frame)

abbrev QueryState := List F × List (List (Frame F))

/-- A deterministic query fixture records its actual request and consumes a tape.
This is not asserted to implement a random oracle. -/
def query (request : List (Frame F)) : QueryState → Outcome F × QueryState
  | ([], history) => (.stopped .exhausted, ([], history ++ [request]))
  | (r :: tail, history) => (.returned r, (tail, history ++ [request]))

def otherPolynomial : Quadratic F 1 := .node (.constant 0) (.constant 6) (.constant 1)

example : otherPolynomial.booleanSum = zeroPolynomial.booleanSum := by decide
example : Framed.root "sumcheck" otherPolynomial 0 ≠ Framed.root "sumcheck" zeroPolynomial 0 := by decide

def request : List (Frame F) := [
  .context "sumcheck" 1 0,
  .statement "sumcheck.quadratic.v1" [0, 0, 0],
  .message 0 ⟨0, 0, 0⟩,
  .request 0]

example : (Framed.run "sumcheck" wrongBoundary react query zeroPolynomial 0 () ([2], [])).outcome =
    .returned true := by decide
example : (Framed.run "sumcheck" wrongBoundary react query zeroPolynomial 0 () ([2], [])).state.provider =
    ([], [request]) := by decide
example : (Framed.run "sumcheck" wrongBoundary react query zeroPolynomial 0 () ([2], [])).events =
    [.message ⟨0, 0, 0⟩, .query request, .challenge 2] := by decide

/-- Same scalar claim and round count, different statement and terminal result. -/
example : (Framed.run "sumcheck" wrongBoundary react query otherPolynomial 0 () ([2], [])).outcome =
    .returned false := by decide
example : (Framed.run "sumcheck" wrongBoundary react query otherPolynomial 0 () ([2], [])).state.provider ≠
    ([], [request]) := by decide

/-- A failed query retains both its complete root and the provider's attempted request. -/
example : (Framed.run "sumcheck" wrongBoundary react query zeroPolynomial 0 () ([], [])).outcome =
    .stopped .exhausted := by decide
example : (Framed.run "sumcheck" wrongBoundary react query zeroPolynomial 0 () ([], [])).state.frames =
    request := by decide
example : (Framed.run "sumcheck" wrongBoundary react query zeroPolynomial 0 () ([], [])).state.provider =
    ([], [request]) := by decide
example : (Framed.run "sumcheck" wrongBoundary react query zeroPolynomial 0 () ([], [])).events =
    [.message ⟨0, 0, 0⟩, .query request] := by decide

example : (Framed.run "sumcheck" Security.honestSend Security.honestReact query
    squarePolynomial squarePolynomial.booleanSum ⟨2, squarePolynomial⟩ ([2, 4], [])).outcome =
      .returned true := by decide

end Tests.SumcheckFramed
