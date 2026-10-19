module

public import Zkc.Construction.FiatShamir

@[expose] public section

/-! The model of the guessing fixture's original validator.

The fixture `lean/bridges/construction/fixtures/guess.zkc` declares a protocol in
which the prover sends a guess, the verifier draws a challenge, delivers it and
accepts when the guess plus the public offset is the challenge. `experiment` is
that verifier as a participant process; the generated
`GuessProof.process_equation` states that the admitted original validator is
it, by computation.
-/

namespace ZkcExamples.Construction.GuessProof
open Zkc.Source Zkc.Construction

/-- The field domain of the guess, the offset and the challenge. -/
abbrev fieldDomain : String := "bls12-381.fr"

/-- The prover's guess message site. -/
abbrev guessSite : String := "label_6775657373_0"

/-- The verifier's challenge site. -/
abbrev challengeSite : String := "label_6368616c6c656e6765"

/-- The site that delivers the challenge to the prover. -/
abbrev deliverySite : String := "label_64656c6976657279_0"

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The original verifier as a participant process: receive the guess, query
the challenge on the service `service`, deliver it to the prover, and accept
when the guess plus the offset is the challenge. -/
def experiment (offset : F) (service : Nat) : PIR.Proc (Actions F G) (Option Bool) :=
  .call (.receive (.field fieldDomain) guessSite 0) fun guess =>
  .call (.query challengeSite fieldDomain (.cons service .nil)) fun challenge =>
  .call (.send (ty := .field fieldDomain) deliverySite 0 challenge) fun _ =>
  .done (some (decide (guess + offset = challenge)))

end ZkcExamples.Construction.GuessProof
