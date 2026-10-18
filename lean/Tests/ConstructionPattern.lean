import Zkc.Construction.Pattern

/-! Controls for the interaction-pattern data shape and the reserved salt kind.

A Schnorr-shaped pattern (a public key, a commitment, a challenge, a response)
and a proof-of-work-gated query phase with a bounded number of positions are
admissible. The same Schnorr pattern with a salt before its challenge is not:
the salt kind is reserved and admission refuses it. Two patterns that differ
only in a static maximum or a difficulty are different data, so their digests
can bind those configurations. -/

namespace Tests.ConstructionPattern
open Zkc.Construction

/-- Sorts named by their catalogue spelling. -/
abbrev ValueSort := String

def schnorr : Pattern ValueSort :=
  [⟨.publicValue, "group", .one, "key"⟩, ⟨.message, "group", .one, "commitment"⟩,
    ⟨.challenge, "scalar", .one, "challenge"⟩, ⟨.message, "scalar", .one, "response"⟩]

def queryPhase (difficulty maximum : Nat) : Pattern ValueSort :=
  [⟨.message, "digest", .one, "root"⟩, ⟨.pow, "bits", .exactly difficulty, "grinding"⟩,
    ⟨.challenge, "index", .atMost maximum, "positions"⟩,
    ⟨.hint, "bytes", .atMost maximum, "openings"⟩]

def salted : Pattern ValueSort :=
  [⟨.publicValue, "group", .one, "key"⟩, ⟨.message, "group", .one, "commitment"⟩,
    ⟨.salt, "bytes", .exactly 32, "salt"⟩, ⟨.challenge, "scalar", .one, "challenge"⟩,
    ⟨.message, "scalar", .one, "response"⟩]

theorem schnorr_admissible : schnorr.Admissible := by decide

theorem queryPhase_admissible : (queryPhase 16 100).Admissible := by decide

theorem salted_refused : ¬ salted.Admissible := by decide

theorem difficulty_distinguishes : queryPhase 16 100 ≠ queryPhase 20 100 := by decide

theorem maximum_distinguishes : queryPhase 16 100 ≠ queryPhase 16 128 := by decide

end Tests.ConstructionPattern
