module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.BitTree

@[expose] public section

/-!
The decision of distinct addresses, with what failed: an address that is not an instruction's
own. Linear use is decided where it is defined (`Linear.lean`).
-/

namespace Zkc.Core

section
variable {D : Dialect}

/-- The address at which the decision of distinct addresses fails: one that two instructions
have (the second, in the order of the addresses), or else the address of an instruction whose
key is the key of a block. It places each address once by the bits of its key. -/
def Term.repeatedAddress {Γ outs : List D.Ty} (t : Term D Γ outs) :
    Option (List (Key × Nat) × Key) :=
  match BitTree.addAll (fun address : List (Key × Nat) × Key => address.2.number) (.leaf [])
      (t.addresses []) with
  | .error address => some address
  | .ok placed =>
      t.blockKeys.findSome? fun key =>
        (BitTree.find BitTree.depth key.number placed).find? fun address => address.2 == key

theorem Term.repeatedAddress_eq_none {Γ outs : List D.Ty} (t : Term D Γ outs) :
    t.repeatedAddress = none ↔ t.Distinct := by
  have spec := BitTree.addAll_spec (fun address : List (Key × Nat) × Key => address.2.number)
    (.leaf []) [] (t.addresses []) (BitTree.holds_empty _)
  unfold Term.repeatedAddress Term.Distinct
  split at spec
  · rename_i placed added
    rw [added]
    obtain ⟨⟨distinct, _⟩, holds⟩ := spec
    simp only [List.findSome?_eq_none_iff, List.find?_eq_none, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq, List.append_nil] at holds ⊢
    constructor
    · intro none
      refine ⟨distinct, fun key inBlocks address inAddresses same => ?_⟩
      exact none key inBlocks address (same ▸ holds.2 address (List.mem_reverse.mpr inAddresses))
        same
    · intro ⟨_, apart⟩ key inBlocks address found same
      exact apart key inBlocks address (List.mem_reverse.mp (holds.1 _ address found)) same
  · rename_i repeated added
    rw [added]
    simp only [reduceCtorEq, false_iff, Bool.and_eq_true, decide_eq_true_eq, not_and]
    exact fun distinct _ => spec ⟨distinct, fun _ _ none => nomatch none⟩

end

end Zkc.Core
