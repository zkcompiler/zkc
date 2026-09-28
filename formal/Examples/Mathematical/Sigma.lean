import Zkc.Source.Mathematical.Meaning
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! A closed interactive Schnorr-shaped fixture over the additive group of F₅.
Scalar and group sorts are nominally distinct. This tests the language's
message/guard meaning and honest algebra, not discrete-log security. -/

set_option autoImplicit false
namespace Examples.Mathematical.Sigma
open Zkc.Source Zkc.Source.Mathematical

inductive Party where | prover | verifier
  deriving DecidableEq
inductive TypeCode where | scalar | group | challenge | boolean | index (n : Nat)
  deriving DecidableEq
inductive Operation where | commitment | response | verify

abbrev parties : List Party := [.prover, .verifier]
abbrev language : Mathematical.Language where
  Ty := TypeCode
  Op := Operation
  arguments
    | .commitment => [.scalar, .group]
    | .response => [.scalar, .challenge, .scalar]
    | .verify => [.scalar, .group, .group, .challenge, .group]
  result | .commitment => .group | .response => .scalar | .verify => .boolean
  index := .index
  condition := .boolean
  Wire _ := Unit

abbrev Value : TypeCode → Type
  | .scalar | .group => ZMod 5
  | .challenge => (ZMod 5)ˣ
  | .boolean => Bool
  | .index n => Fin n

abbrev meaning : Interpretation language where
  Value := Value
  pure
    | .commitment, .cons nonce (.cons generator .nil) => nonce * generator
    | .response, .cons nonce (.cons challenge (.cons witness .nil)) =>
        nonce + (challenge : ZMod 5) * witness
    | .verify, .cons response (.cons generator (.cons commitment
        (.cons challenge (.cons statement .nil)))) =>
        decide (response * generator = commitment + (challenge : ZMod 5) * statement)
  index i := i
  condition b := b

abbrev nonce : Capability Party TypeCode := ⟨[.prover], [], .scalar⟩
abbrev challenge : Capability Party TypeCode := ⟨[.verifier], [], .challenge⟩
abbrev inputs : List (Port Party TypeCode) :=
  [⟨[.prover], .scalar⟩, ⟨parties, .group⟩, ⟨parties, .group⟩]

def protocol : Mathematical.Program parties language [nonce, challenge] [] inputs [] := by
  refine .query 0 .prover .here (by decide) .nil (by decide) ?_
  refine .pure (roles := [.prover]) .commitment
    (.cons ⟨[.prover], .here⟩ (.cons ⟨parties, (.there (.there .here))⟩ .nil)) (by decide) ?_
  refine .message 1 () .prover .verifier (by decide) (.exact .here) ?_
  refine .query 2 .verifier (.there .here) (by decide) .nil (by decide) ?_
  refine .message 3 () .verifier .prover (by decide) (.exact .here) ?_
  refine .pure (roles := [.prover]) .response
    (.cons ⟨[.prover], (.there (.there (.there (.there .here))))⟩
      (.cons ⟨[.verifier, .prover], .here⟩
        (.cons ⟨[.prover], (.there (.there (.there (.there (.there .here)))))⟩ .nil))) (by decide) ?_
  refine .message 4 () .prover .verifier (by decide) (.exact .here) ?_
  refine .pure (roles := parties) .verify
    (.cons ⟨parties, .here⟩
      (.cons ⟨parties, (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))⟩
        (.cons ⟨parties, (.there (.there (.there (.there .here))))⟩
          (.cons ⟨[.verifier, .prover], (.there (.there .here))⟩
            (.cons ⟨parties, (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))⟩ .nil))))) (by decide) ?_
  refine .guard 5 .verifier ⟨parties, .here, ?_⟩ (.ret .nil)
  simp [parties]

def environment (self : Party) (witness generator statement : ZMod 5) :
    Mathematical.Environment Value self inputs
  | _, .here => fun _ => witness
  | _, .there .here => fun _ => generator
  | _, .there (.there .here) => fun _ => statement

def verifierHandler (receivedCommitment receivedResponse : ZMod 5) (draw : (ZMod 5)ˣ) :
    PIR.Handler (interface Party.verifier language [nonce, challenge] Value) Nat String
  | .receive (ty := .group) .., state => ⟨.returned receivedCommitment, state, ["commitment"]⟩
  | .receive (ty := .scalar) .., state => ⟨.returned receivedResponse, state, ["response"]⟩
  | .receive .., state => ⟨.stopped .refused, state, []⟩
  | .send .., state => ⟨.returned (), state, ["challenge"]⟩
  | .query _ .here denied .nil, _ => nomatch denied
  | .query _ (.there .here) _ .nil, state => ⟨.returned draw, state + 1, ["sample"]⟩
  | .stop _ reason, state => ⟨.stopped reason, state, ["stop"]⟩

theorem verifier_openMeaning (witness generator statement : ZMod 5) :
    protocol.openMeaning meaning .verifier (environment .verifier witness generator statement) =
      .call (.receive (ty := .group) ⟨[], 1⟩ () .prover) (fun a =>
        .call (.query ⟨[], 2⟩ (.there .here) (by decide) .nil) (fun draw =>
          .call (.send (ty := .challenge) ⟨[], 3⟩ () .prover draw) (fun _ =>
            .call (.receive (ty := .scalar) ⟨[], 4⟩ () .prover) (fun z =>
              if decide (z * generator = a + (draw : ZMod 5) * statement) then
                .done .nil
              else .call (.stop ⟨[], 5⟩ .reject) (fun reply => nomatch reply))))) := by
  simp [protocol, Mathematical.Program.openMeaning, Mathematical.Program.denote,
    Mathematical.Definitions.denote, environment, Reference.read, Reference.exact,
    Inputs.read, Zkc.Source.Environment.push, Bindings.read]
  funext a
  congr 1
  funext draw
  congr 1
  funext sent
  congr 1
  funext z
  split_ifs
  · rfl
  · congr 1
    funext reply
    exact nomatch reply

theorem verifier_uses_received_values (witness generator statement a z : ZMod 5)
    (draw : (ZMod 5)ˣ) :
    (protocol.openMeaning meaning .verifier
      (environment .verifier witness generator statement)).run (verifierHandler a z draw) 0 =
      if z * generator = a + (draw : ZMod 5) * statement then
        ⟨.returned .nil, 1, ["commitment", "sample", "challenge", "response"]⟩
      else ⟨.stopped .reject, 1, ["commitment", "sample", "challenge", "response", "stop"]⟩ := by
  rw [verifier_openMeaning]
  split_ifs with valid <;> simp [PIR.Proc.run, PIR.Execution.follow, verifierHandler, valid]

theorem honest_algebra (witness nonce generator : ZMod 5) (draw : (ZMod 5)ˣ) :
    (nonce + (draw : ZMod 5) * witness) * generator =
      nonce * generator + (draw : ZMod 5) * (witness * generator) := by ring

theorem honest_verifier_accepts (witness nonce generator : ZMod 5) (draw : (ZMod 5)ˣ) :
    (protocol.openMeaning meaning .verifier
      (environment .verifier witness generator (witness * generator))).run
        (verifierHandler (nonce * generator) (nonce + (draw : ZMod 5) * witness) draw) 0 =
      ⟨.returned .nil, 1, ["commitment", "sample", "challenge", "response"]⟩ := by
  rw [verifier_uses_received_values, if_pos (honest_algebra witness nonce generator draw)]

/-- All challenge replies enter the prover's response expression. -/
theorem prover_openMeaning (witness generator statement : ZMod 5) :
    protocol.openMeaning meaning .prover (environment .prover witness generator statement) =
      .call (.query ⟨[], 0⟩ .here (by decide) .nil) (fun nonceValue =>
        .call (.send (ty := .group) ⟨[], 1⟩ () .verifier (nonceValue * generator)) (fun _ =>
          .call (.receive (ty := .challenge) ⟨[], 3⟩ () .verifier) (fun draw =>
            .call (.send (ty := .scalar) ⟨[], 4⟩ () .verifier
              (nonceValue + (draw : ZMod 5) * witness)) (fun _ => .done .nil)))) := rfl

def proverHandler (nonceValue : ZMod 5) (draw : (ZMod 5)ˣ) :
    PIR.Handler (interface Party.prover language [nonce, challenge] Value) Nat (ZMod 5)
  | .query _ .here _ .nil, state => ⟨.returned nonceValue, state + 1, []⟩
  | .query _ (.there .here) denied .nil, _ => nomatch denied
  | .receive (ty := .challenge) .., state => ⟨.returned draw, state, []⟩
  | .receive .., state => ⟨.stopped .refused, state, []⟩
  | .send (ty := .group) _ _ _ value, state => ⟨.returned (), state, [value]⟩
  | .send (ty := .scalar) _ _ _ value, state => ⟨.returned (), state, [value]⟩
  | .send .., state => ⟨.returned (), state, []⟩
  | .stop _ reason, state => ⟨.stopped reason, state, []⟩

theorem honest_prover_messages (witness nonceValue generator : ZMod 5) (draw : (ZMod 5)ˣ) :
    (protocol.openMeaning meaning .prover
      (environment .prover witness generator (witness * generator))).run
        (proverHandler nonceValue draw) 0 =
      ⟨.returned .nil, 1, [nonceValue * generator, nonceValue + (draw : ZMod 5) * witness]⟩ := rfl

/-- Deliver the messages produced by the actual prover. A common statement and
one delivered challenge are explicit premises of this finite honest experiment. -/
def deliveredExecution (witness nonceValue generator : ZMod 5) (draw : (ZMod 5)ˣ) :
    PIR.Execution Nat String (Values (Component Value Party.verifier) []) :=
  let prover := (protocol.openMeaning meaning .prover
    (environment .prover witness generator (witness * generator))).run (proverHandler nonceValue draw) 0
  match prover.outcome, prover.events with
  | .returned _, [a, z] =>
      (protocol.openMeaning meaning .verifier
        (environment .verifier witness generator (witness * generator))).run (verifierHandler a z draw) 0
  | _, _ => ⟨.stopped .incomplete, 0, []⟩

theorem honest_delivery_accepts (witness nonceValue generator : ZMod 5) (draw : (ZMod 5)ˣ) :
    deliveredExecution witness nonceValue generator draw =
      ⟨.returned .nil, 1, ["commitment", "sample", "challenge", "response"]⟩ := by
  simp only [deliveredExecution]
  exact honest_verifier_accepts witness nonceValue generator draw

end Examples.Mathematical.Sigma
