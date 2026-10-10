import Zkc.Protocols.Pedersen
import Zkc.Protocols.Schnorr
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

namespace Tests.CommitmentComposition

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- A nontrivial base and different challenges at one nonce commitment.
example : (((4 : F) - 2) / ((5 : F) - 1)) • (3 : F) = 5 :=
  Zkc.Protocols.Schnorr.extract_public_key (3 : F) 5 1 (5 : F) 1 4 2
    (by decide) (by decide) (by decide)

-- Changing the nonce commitment invalidates the extraction hypothesis.
example : (4 : F) • (3 : F) = 1 + (5 : F) • (5 : F) := by decide
example : (2 : F) • (3 : F) ≠ 0 + (1 : F) • (5 : F) := by decide

-- Independent existential Pedersen openings do not fix an amount.
example : Zkc.Protocols.Pedersen.commit (F := F) (1 : F) 2 1 2 =
    Zkc.Protocols.Pedersen.commit (F := F) (1 : F) 2 3 1 := by decide

end Tests.CommitmentComposition
