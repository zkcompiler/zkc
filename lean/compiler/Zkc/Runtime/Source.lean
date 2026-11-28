module

public import Zkc.Runtime.Model
public import Zkc.Core.World.Runs
public import Zkc.Core.Scheme.Identity

@[expose] public section
set_option autoImplicit false

/-!
Deterministic cryptographic `Core.Source` implementations for `ZkcRuntime`:
- `emptySource`: answers no coin or oracle queries (`fun _ _ => none`), verifying that schemes with
  `samples derived by` and Fiat–Shamir require zero external randomness.
- `seededSource (b : Bindings) (M : Core.Model b.vocabulary) (seed : List Nat)`: deterministic
  SHAKE128-based PRNG keyed canonically by `(seed, occurrence.path, occurrence.key)`, supporting
  every inhabited `LinkedType` (prime/extension fields, nonzero fields, G1, `bool`, `fin`, tuples,
  sized sequences).
-/

namespace Zkc.Runtime

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project
open Zkc.Runtime.Crypto

/-- An empty external world (`Source`) that supplies no coins or service replies. -/
def emptySource {V : Vocabulary} (M : Model V) : Source M :=
  fun _ _ => none

/-- Encode a `Frame` canonically for deterministic PRNG domain separation. -/
def encodeFrameBytes : Frame → List Nat
  | .iteration k i => 0 :: encodeNat k.number ++ encodeNat i
  | .application k => 1 :: encodeNat k.number
  | .attempt k i => 2 :: encodeNat k.number ++ encodeNat i

/-- Encode an `Occurrence` canonically for deterministic PRNG domain separation. -/
def encodeOccurrenceBytes (occ : Occurrence) : List Nat :=
  encodeList encodeFrameBytes occ.path ++ encodeNat occ.key.number

/-- Deterministic SHAKE128-seeded `Source` for `linkedModel? b` (and any model sharing
`linkedCarriers b`), keyed uniquely by `(seed, occurrence)`. -/
def seededSource (b : Bindings) (M : Model b.vocabulary)
    (hCarriers : M.toCarriers = linkedCarriers b) (seed : List Nat) : Source M :=
  fun occ τ =>
    if hInhab : τ.noValue = false then
      let domain :=
        utf8Bytes "zkc.runtime.source.shake128/0" ++
        encodeList encodeNat seed ++
        encodeOccurrenceBytes occ
      let nextB := fun (n : Nat) (ctr : Nat) =>
        (shake128Bytes (domain ++ encodeNat ctr) n, ctr + 1)
      let val : τ.Val (linkedCarriers b) := (deriveVal b nextB false 0 τ hInhab).1
      some (cast (congrArg (fun c => τ.Val c) hCarriers.symm) val)
    else
      none

/-- Convenience helper constructing a seeded `Source` directly from `linkedModel? b`. -/
def linkedSeededSource (b : Bindings) (seed : List Nat) :
    Except String ((M : Model b.vocabulary) × Source M) := do
  match hInhab : outputsInhabited b with
  | true =>
      match hM : linkedModel? b with
      | .ok M =>
          have hC : M.toCarriers = linkedCarriers b := by
            unfold linkedModel? at hM
            simp only [hInhab, ↓reduceDIte, Except.ok.injEq] at hM
            subst hM
            rfl
          .ok ⟨M, seededSource b M hC seed⟩
      | .error e => .error e
  | false => .error "project bindings contain an uninhabited primitive output type"

end Zkc.Runtime
