module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.BitTree

@[expose] public section

/-!
The decisions of distinct addresses and of single assignment, each with what failed: an address
that is not an instruction's own (`Term.repeatedAddress`), a name that is bound a second time
(`Term.rebound`), each proved to decide its proposition; and, for diagnostics, the place of the
instruction that binds a name a second time (`Term.reboundPlace`). Linear use is decided where
it is defined (`Linear.lean`).
-/

namespace Zkc.Core

section
variable {D : Dialect}

/-! ## Distinct addresses -/

/-- The address at which the decision of distinct addresses fails: one that two instructions
have (the second, in the order of the addresses), or else the address of an instruction whose
key is the key of a block. It places each address once by the bits of its key. -/
def Term.repeatedAddress {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) :
    Option (List (Key × Nat) × Key) :=
  match BitTree.addAll (fun address : List (Key × Nat) × Key => address.2.number) (.leaf [])
      (t.addresses []) with
  | .error address => some address
  | .ok placed =>
      t.blockKeys.findSome? fun key =>
        (BitTree.find BitTree.depth key.number placed).find? fun address => address.2 == key

theorem Term.repeatedAddress_eq_none {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) :
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

/-! ## Single assignment -/

/-- The name at which single assignment fails: the first that is bound a second time, in the
order of the inputs of the definition and then of what its body binds. It places each name once
by its bits. -/
def Term.rebound {Γ : Ctx D.Ty} {outs : List D.Ty} (inputs : List Name) (t : Term D Γ outs) :
    Option Name :=
  match BitTree.addAll (fun name : Name => name) (.leaf []) (inputs ++ t.bindings) with
  | .error name => some name
  | .ok _ => none

theorem Term.rebound_eq_none {Γ : Ctx D.Ty} {outs : List D.Ty} (inputs : List Name)
    (t : Term D Γ outs) :
    t.rebound inputs = none ↔ t.BoundOnce inputs := by
  have spec := BitTree.addAll_spec (fun name : Name => name) (.leaf []) []
    (inputs ++ t.bindings) (BitTree.holds_empty _)
  unfold Term.rebound Term.BoundOnce
  split at spec
  · rename_i placed added
    rw [added]
    exact ⟨fun _ => spec.1.1, fun _ => rfl⟩
  · rename_i repeated added
    rw [added]
    exact ⟨fun found => (nomatch found),
      fun distinct => absurd ⟨distinct, fun _ _ none => (nomatch none)⟩ spec⟩

/-- The names seen, placed by their bits, with the names of a binding added in order; or
nothing when one of them is seen already. -/
def addBound (seen : BitTree Name) (names : List Name) : Option (BitTree Name) :=
  match BitTree.addAll (fun name : Name => name) seen names with
  | .error _ => none
  | .ok seen => some seen

mutual
  /-- What a term binds, added in the order of `Term.bindings` to the names seen before it: the
  names seen after it (`.ok`), or the place of the instruction that binds a name that is seen
  already (`.error`): the blocks around it and its key. The results of an instruction and the
  inputs of its regions are bound at the instruction; the results of a block at the block. -/
  def Term.reboundAt (blocks : List (Key × Nat)) (seen : BitTree Name) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs →
        Except (List (Key × Nat) × Key) (BitTree Name)
    | _, _, .ret _ => .ok seen
    | _, _, .op key _ _ results rest =>
        match addBound seen results.toList with
        | none => .error (blocks, key)
        | some seen => Term.reboundAt blocks seen rest
    | _, _, .guard _ _ _ _ _ rest => Term.reboundAt blocks seen rest
    | _, _, .choose key _ _ _ _ onTrue onFalse results rest =>
        match Term.reboundAt blocks seen onTrue with
        | .error place => .error place
        | .ok seen =>
            match Term.reboundAt blocks seen onFalse with
            | .error place => .error place
            | .ok seen =>
                match addBound seen results.toList with
                | none => .error (blocks, key)
                | some seen => Term.reboundAt blocks seen rest
    | _, _, .cases key _ _ _ _ arms results rest =>
        match Arms.reboundAt blocks key seen arms with
        | .error place => .error place
        | .ok seen =>
            match addBound seen results.toList with
            | none => .error (blocks, key)
            | some seen => Term.reboundAt blocks seen rest
    | _, _, .loop key _ _ _ _ inputs body results rest =>
        match addBound seen inputs.toList with
        | none => .error (blocks, key)
        | some seen =>
            match Term.reboundAt blocks seen body with
            | .error place => .error place
            | .ok seen =>
                match addBound seen results.toList with
                | none => .error (blocks, key)
                | some seen => Term.reboundAt blocks seen rest
    | _, _, .block key number body results rest =>
        match Term.reboundAt (blocks ++ [(key, number)]) seen body with
        | .error place => .error place
        | .ok seen =>
            match addBound seen results.toList with
            | none => .error (blocks, key)
            | some seen => Term.reboundAt blocks seen rest
    | _, _, .attempt key _ _ inputs body results rest =>
        match addBound seen inputs.toList with
        | none => .error (blocks, key)
        | some seen =>
            match Term.reboundAt blocks seen body with
            | .error place => .error place
            | .ok seen =>
                match addBound seen results.toList with
                | none => .error (blocks, key)
                | some seen => Term.reboundAt blocks seen rest
  /-- What the arms of the case analysis with the key bind, added in order to the names seen;
  the name of a payload is bound at the case analysis. -/
  def Arms.reboundAt (blocks : List (Key × Nat)) (key : Key) (seen : BitTree Name) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
        Except (List (Key × Nat) × Key) (BitTree Name)
    | _, _, _, .nil => .ok seen
    | _, _, _, .cons inputs arm rest =>
        match addBound seen inputs.toList with
        | none => .error (blocks, key)
        | some seen =>
            match Term.reboundAt blocks seen arm with
            | .error place => .error place
            | .ok seen => Arms.reboundAt blocks key seen rest
end

/-- Where single assignment fails, for diagnostics: the blocks around the instruction that binds
a name a second time, and its key, for the first name that is bound a second time in the order
of `Term.rebound` (an instruction binds its results and the inputs of its regions, a block its
results). None when that name is an input of the definition bound a second time among its
inputs, which no instruction binds; none also when every name is bound at one place. -/
def Term.reboundPlace {Γ : Ctx D.Ty} {outs : List D.Ty} (inputs : List Name)
    (t : Term D Γ outs) : Option (List (Key × Nat) × Key) :=
  match addBound (.leaf []) inputs with
  | none => none
  | some seen =>
      match Term.reboundAt [] seen t with
      | .error place => some place
      | .ok _ => none

end

end Zkc.Core
