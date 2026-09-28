import Zkc.Source.Mathematical.Meaning
import Zkc.Protocols.Sumcheck.Polynomial
import Mathlib.Data.ZMod.Basic

/-! A compact, indexed Sumcheck source with fixed-capacity prefix state.
The selected messages have three coefficients (degree at most two). The
terminal capability evaluates the same polynomial held privately by the prover. -/

set_option autoImplicit false
namespace Examples.Mathematical.Sumcheck
open Zkc.Source Zkc.Source.Mathematical
open Zkc.Polynomial Zkc.Protocols.AlgebraicRounds

inductive Party where | prover | verifier
  deriving DecidableEq
inductive TypeCode where | scalar | polynomial | state | point | round | boolean | index (n : Nat)
  deriving DecidableEq
inductive Operation where | round | boundary | advance | point | terminal

abbrev parties : List Party := [.prover, .verifier]
abbrev language (n : Nat) : Mathematical.Language where
  Ty := TypeCode
  Op := Operation
  arguments
    | .round => [.polynomial, .state, .index n]
    | .boundary => [.round, .state]
    | .advance => [.state, .round, .scalar, .index n]
    | .point => [.state]
    | .terminal => [.scalar, .state]
  result
    | .round => .round | .boundary | .terminal => .boolean
    | .advance => .state | .point => .point
  index := .index
  condition := .boolean
  Wire _ := Unit

abbrev Value (F : Type) (n : Nat) : TypeCode → Type
  | .scalar => F
  | .polynomial => Quadratic F n
  | .state => (Fin n → F) × F
  | .point => Fin n → F
  | .round => Message F
  | .boolean => Bool
  | .index count => Fin count

/-- Fix exactly the preceding coordinates. The public index controls the
mathematical operation, not just its diagnostic path. -/
def roundAt {F : Type} [CommSemiring F] : {n : Nat} →
    Quadratic F n → (Fin n → F) → Fin n → Message F
  | 0, _, _, index => nomatch index
  | _n + 1, polynomial, challenges, index =>
      Fin.cases (Zkc.Protocols.Sumcheck.roundPolynomial polynomial)
        (fun next => roundAt (polynomial.restrict (challenges 0))
          (fun i => challenges i.succ) next) index

abbrev meaning (F : Type) [CommSemiring F] [DecidableEq F] (n : Nat) :
    Interpretation (language n) where
  Value := Value F n
  pure
    | .round, .cons polynomial (.cons state (.cons index .nil)) => roundAt polynomial state.1 index
    | .boundary, .cons message (.cons state .nil) => decide (message.boundary = state.2)
    | .advance, .cons state (.cons message (.cons challenge (.cons index .nil))) =>
        (Function.update state.1 index challenge, message.evaluate challenge)
    | .point, .cons state .nil => state.1
    | .terminal, .cons evaluation (.cons state .nil) => decide (evaluation = state.2)
  index i := i
  condition b := b

abbrev sampler : Capability Party TypeCode := ⟨[.verifier], [], .scalar⟩
abbrev terminal : Capability Party TypeCode := ⟨[.verifier], [.point], .scalar⟩
abbrev statePort : Port Party TypeCode := ⟨parties, .state⟩
abbrev inputs : List (Port Party TypeCode) := [statePort, ⟨[.prover], .polynomial⟩]

def protocol (n : Nat) : Mathematical.Program parties (language n) [sampler, terminal] [] inputs [] := by
  refine .repeat 0 n (.cons (.exact .here) .nil) ?_ ?_
  · refine .pure (roles := [.prover]) .round
      (.cons ⟨[.prover], .there (.there (.there .here))⟩
        (.cons ⟨parties, .there .here⟩ (.cons ⟨parties, .here⟩ .nil))) (by rfl) ?_
    refine .message 1 () .prover .verifier (by simp)
      (.exact .here) ?_
    refine .pure (roles := parties) .boundary
      (.cons ⟨parties, .here⟩ (.cons ⟨parties, .there (.there (.there .here))⟩ .nil)) (by rfl) ?_
    refine .guard 2 .verifier ⟨parties, .here, by simp⟩ ?_
    refine .query 3 .verifier .here (by simp) .nil (by simp [Inputs.available, parties]) ?_
    refine .message 4 () .verifier .prover (by simp) (.exact .here) ?_
    refine .pure (roles := parties) .advance
      (.cons ⟨parties, .there (.there (.there (.there (.there (.there .here)))))⟩
        (.cons ⟨parties, .there (.there (.there .here))⟩
          (.cons ⟨[.verifier, .prover], .here⟩
            (.cons ⟨parties, .there (.there (.there (.there (.there .here))))⟩ .nil)))) (by rfl) ?_
    exact .ret (.cons (.exact .here) .nil)
  · refine .pure (roles := parties) .point (.cons ⟨parties, .here⟩ .nil) (by rfl) ?_
    refine .query 5 .verifier (.there .here) (by simp)
      (.cons ⟨parties, .here⟩ .nil) (by simp [Inputs.available, parties]) ?_
    refine .pure (roles := [.verifier]) .terminal
      (.cons ⟨[.verifier], .here⟩ (.cons ⟨parties, .there (.there .here)⟩ .nil)) (by rfl) ?_
    exact .guard 6 .verifier (.exact .here) (.ret .nil)

def environment {F : Type} [Zero F] {n : Nat} (self : Party)
    (polynomial : Quadratic F n) (claim : F) : Mathematical.Environment (Value F n) self inputs
  | _, .here => fun _ => (fun _ => 0, claim)
  | _, .there .here => fun _ => polynomial

def verifierHandler {F : Type} [CommSemiring F] {n : Nat}
    (polynomial : Quadratic F n) (messages : Nat → Message F) (challenges : Nat → F) :
    PIR.Handler (Mathematical.interface Party.verifier (language n) [sampler, terminal] (Value F n)) Nat String
  | .receive (ty := .round) ⟨[.iteration 0 i], 1⟩ _ .prover, state =>
      ⟨.returned (messages i), state, ["round"]⟩
  | .receive .., state => ⟨.stopped .refused, state, []⟩
  | .query ⟨[.iteration 0 i], 3⟩ .here _ .nil, state =>
      ⟨.returned (challenges i), state + 1, ["draw"]⟩
  | .query ⟨[], 5⟩ (.there .here) _ (.cons point .nil), state =>
      ⟨.returned (polynomial.eval point), state, ["terminal"]⟩
  | .query .., state => ⟨.stopped .refused, state, []⟩
  | .send .., state => ⟨.returned (), state, ["challenge"]⟩
  | .stop _ reason, state => ⟨.stopped reason, state, ["stop"]⟩

/-- (X₀ + X₁)^2 over F₅; it includes a cross term and degree-two rounds. -/
def square : Quadratic (ZMod 5) 2 :=
  .node (.node (.constant 0) (.constant 0) (.constant 1))
    (.node (.constant 0) (.constant 2) (.constant 0))
    (.node (.constant 1) (.constant 0) (.constant 0))

def honestMessages : Nat → Message (ZMod 5)
  | 0 => ⟨1, 2, 2⟩
  | _ + 1 => ⟨1, 2, 1⟩

example :
    ((protocol 2).openMeaning (meaning (ZMod 5) 2) .verifier
      (environment .verifier square 1)).run (verifierHandler square honestMessages (fun _ => 1)) 0 =
      ⟨.returned .nil, 2, ["round", "draw", "challenge", "round", "draw", "challenge", "terminal"]⟩ := rfl

/-- A malformed algebraic claim stops before the first challenge, with
no verifier component for the prover's private polynomial. -/
example :
    ((protocol 2).openMeaning (meaning (ZMod 5) 2) .verifier
      (environment .verifier square 1)).run
        (verifierHandler square (fun _ => ⟨0, 0, 0⟩) (fun _ => 1)) 0 =
      ⟨.stopped .reject, 0, ["round", "stop"]⟩ := rfl

example :
    ((protocol 0).openMeaning (meaning (ZMod 5) 0) .verifier
      (environment .verifier (.constant 3) 3)).run
        (verifierHandler (.constant 3) (fun _ => ⟨0, 0, 0⟩) (fun _ => 1)) 0 =
      ⟨.returned .nil, 0, ["terminal"]⟩ := rfl

end Examples.Mathematical.Sumcheck
