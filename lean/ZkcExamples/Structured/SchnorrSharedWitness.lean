module

public import Zkc.Protocols.Schnorr
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! A small independent Chaum-Pedersen control. There is no new DSL source or
native implementation here. Both equations retain the same response and witness.
Existentially closing each component separately loses that condition. -/
namespace ZkcExamples.Structured.SchnorrSharedWitness

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

def Relation (firstBase secondBase firstKey secondKey : G) (witness : F) : Prop :=
  firstKey = witness • firstBase ∧ secondKey = witness • secondBase

theorem complete (firstBase secondBase : G) (witness nonce challenge : F) :
    (nonce + challenge * witness) • firstBase =
        nonce • firstBase + challenge • (witness • firstBase) ∧
    (nonce + challenge * witness) • secondBase =
        nonce • secondBase + challenge • (witness • secondBase) :=
  ⟨Zkc.Protocols.Schnorr.response_equation ..,
    Zkc.Protocols.Schnorr.response_equation ..⟩

/-- The two coordinates share one commitment pair and the same two responses.
The resulting common witness is a new value, not a supplied honest secret. -/
theorem extract (firstBase secondBase firstKey secondKey firstCommit secondCommit : G)
    (firstChallenge secondChallenge firstResponse secondResponse : F)
    (distinct : firstChallenge ≠ secondChallenge)
    (firstAccept : firstResponse • firstBase = firstCommit + firstChallenge • firstKey ∧
      firstResponse • secondBase = secondCommit + firstChallenge • secondKey)
    (secondAccept : secondResponse • firstBase = firstCommit + secondChallenge • firstKey ∧
      secondResponse • secondBase = secondCommit + secondChallenge • secondKey) :
    Relation firstBase secondBase firstKey secondKey
      ((firstResponse - secondResponse) / (firstChallenge - secondChallenge)) :=
  ⟨(Zkc.Protocols.Schnorr.extract_public_key firstBase firstKey firstCommit
      firstChallenge secondChallenge firstResponse secondResponse distinct
      firstAccept.1 secondAccept.1).symm,
    (Zkc.Protocols.Schnorr.extract_public_key secondBase secondKey secondCommit
      firstChallenge secondChallenge firstResponse secondResponse distinct
      firstAccept.2 secondAccept.2).symm⟩

/-- Independent witnesses exist even though no common witness exists. -/
theorem independent_not_shared :
    ((∃ first : ZMod 3, (0 : ZMod 3) = first • (1 : ZMod 3)) ∧
      (∃ second : ZMod 3, (1 : ZMod 3) = second • (1 : ZMod 3))) ∧
      ¬ ∃ witness : ZMod 3, Relation (1 : ZMod 3) 1 0 1 witness := by
  constructor
  · exact ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩
  · rintro ⟨witness, first, second⟩
    have impossible : (0 : ZMod 3) = 1 := first.trans second.symm
    exact zero_ne_one impossible

end ZkcExamples.Structured.SchnorrSharedWitness
