import Zkc.Core.Format.Canonical
import Zkc.Core.Scheme.Deploy.Compile
import Zkc.Core.Scheme.Theorems
import Zkc.Core.Run.Execute
import Zkc.Core.Run.Specialize.Sound
import Zkc.Core.Admission.Admit
import Zkc.Core.Admission.Theorems
import Zkc.Tests.Core.Consumers

/-!
Shared fixtures, concrete models, protocols, declarations, and execution helpers for the Core
deployment, specialization, and ideal random-oracle test suite.

Includes:
- Toy Schnorr vocabulary (`deployVocab`), multiplicative subgroup model (`deployModel`, `q = 11`,
  `p = 23`), and prime-order additive group model (`primeOrderModel`, `q = 11`, where every valid
  point has exact prime order `11` for compact Schnorr commitment recovery).
- Admitted suite, layout, recovery, and deterministic sampling functions (`suiteAndLayoutDefs`).
- Standard, multi-draw, abort-and-retry, branching, authored, subprotocol-apply, looped,
  depth-8 diamond-DAG (`dagSchnorrProto`), and negative-control protocols.
- A two-distribution vocabulary (`twoLawVocab`, `twoLawModel`, `twoLawEncoder`) exercising
  distribution-aware `V.LawKey` dispatch in `SuiteSlot.derive` (`ModuleRef.lawMembers`) over the
  same Core type `.fin 11` (`uniform` vs `nonzero`).
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

-- Compute concrete protocol runs by kernel reduction in tests.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

set_option maxRecDepth 16000

/-! ## Toy Schnorr vocabulary and concrete models (`q = 11`) -/

inductive DeployType where
  | scalar
  | point
deriving DecidableEq

inductive DeployRow where
  | base
  | add
  | mul
  | scale
  | plus
  | negScale
  | same
  | sameScalar
  | scalarToByte
  | byteToScalar
  | pointToByte
  | byteToPoint
  | mix
  | squeezeScalar
  | natToScalar
deriving DecidableEq

abbrev dScalar : Ty DeployType := .nominal .scalar
abbrev dPoint : Ty DeployType := .nominal .point
abbrev dByte : Ty DeployType := .fin 256
abbrev dBytes : Ty DeployType := .seq dByte none

/-- A vocabulary with a prime-order group, byte codecs, and a transcript sponge. -/
def deployVocab : Vocabulary where
  TypeKey := DeployType
  RowKey := DeployRow
  LawKey := Unit
  row r := some <| match r with
    | .base => ⟨[dScalar], [dPoint], .pure⟩
    | .add => ⟨[dScalar, dScalar], [dScalar], .pure⟩
    | .mul => ⟨[dScalar, dScalar], [dScalar], .pure⟩
    | .scale => ⟨[dScalar, dPoint], [dPoint], .pure⟩
    | .plus => ⟨[dPoint, dPoint], [dPoint], .pure⟩
    | .negScale => ⟨[dScalar, dPoint], [dPoint], .pure⟩
    | .same => ⟨[dPoint, dPoint], [.bool], .pure⟩
    | .sameScalar => ⟨[dScalar, dScalar], [.bool], .pure⟩
    | .scalarToByte => ⟨[dScalar], [dByte], .pure⟩
    | .byteToScalar => ⟨[dByte], [dScalar], .pure⟩
    | .pointToByte => ⟨[dPoint], [dByte], .pure⟩
    | .byteToPoint => ⟨[dByte], [dPoint], .pure⟩
    | .mix => ⟨[.nat, dBytes], [.nat], .pure⟩
    | .squeezeScalar => ⟨[.nat, dBytes], [dScalar, .nat], .pure⟩
    | .natToScalar => ⟨[.nat], [dScalar], .pure⟩
  law _ := some ⟨[], dScalar⟩
  literal _ _ := true
  decided key _ _ found kind := by cases key <;> cases found <;> cases kind

/-- Modular exponentiation `(base ^ exp) % modulus`. -/
def powMod (base : Nat) : Nat → Nat → Nat
  | 0, m => 1 % m
  | exp + 1, m => (base * powMod base exp m) % m

theorem powMod_lt (base exp m : Nat) (hm : 0 < m) : powMod base exp m < m := by
  cases exp with
  | zero => exact Nat.mod_lt 1 hm
  | succ _ => exact Nat.mod_lt _ hm

/-- Simple deterministic polynomial sponge state update for testing Fiat–Shamir binding. -/
def mixBytes (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: rest => mixBytes ((acc * 131 + b + 31) % 65521) rest

/-- Concrete model for `deployVocab` (`q = 11`, `p = 23`, generator `g = 2`). -/
def deployModel : Model deployVocab where
  Carrier
    | .scalar => Nat
    | .point => Nat
  valid
    | .scalar, x => x < 11
    | .point, y => y < 23
  literal
    | .scalar, n => some (n % 11)
    | .point, n => some (n % 23)
  apply key _ known args :=
    match key, known, args with
    | .base, rfl, .cons s .nil => some (.cons (powMod 2 s 23) .nil)
    | .add, rfl, .cons a (.cons b .nil) => some (.cons ((a + b) % 11) .nil)
    | .mul, rfl, .cons a (.cons b .nil) => some (.cons ((a * b) % 11) .nil)
    | .scale, rfl, .cons s (.cons p .nil) => some (.cons (powMod p s 23) .nil)
    | .plus, rfl, .cons a (.cons b .nil) => some (.cons ((a * b) % 23) .nil)
    | .negScale, rfl, .cons s (.cons p .nil) => some (.cons (powMod p ((11 - s % 11) % 11) 23) .nil)
    | .same, rfl, .cons a (.cons b .nil) => some (.cons (decide (a = b)) .nil)
    | .sameScalar, rfl, .cons a (.cons b .nil) => some (.cons (decide (a = b)) .nil)
    | .scalarToByte, rfl, .cons s .nil => some (.cons (s % 256) .nil)
    | .byteToScalar, rfl, .cons b .nil => some (.cons (b % 11) .nil)
    | .pointToByte, rfl, .cons p .nil => some (.cons (p % 256) .nil)
    | .byteToPoint, rfl, .cons b .nil => some (.cons (b % 23) .nil)
    | .mix, rfl, .cons st (.cons bs .nil) => some (.cons (mixBytes st bs) .nil)
    | .squeezeScalar, rfl, .cons st (.cons lbl .nil) =>
        let st' := mixBytes st (0xFF :: lbl)
        some (.cons (st' % 11) (.cons st' .nil))
    | .natToScalar, rfl, .cons n .nil => some (.cons (n % 11) .nil)
  inDomain _ _ _ _ := true
  defined key _ known args := by
    cases key <;> cases known
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r; rfl
  total _ _ _ _ _ := rfl
  decides key _ known _ kind _ := by cases key <;> cases known <;> cases kind
  keeps key _ known args outs _ h := by
    cases key <;> cases known
    · cases args with | cons s r => cases r; injection h with e; subst e; exact ⟨powMod_lt 2 s 23 (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons s r => cases r with | cons p r2 => cases r2; injection h with e; subst e; exact ⟨powMod_lt p s 23 (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons s r => cases r with | cons p r2 => cases r2; injection h with e; subst e; exact ⟨powMod_lt p _ 23 (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨trivial, trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨trivial, trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨trivial, trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial, trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
  literals key n _ := by
    cases key
    · exact ⟨n % 11, rfl, Nat.mod_lt _ (by decide)⟩
    · exact ⟨n % 23, rfl, Nat.mod_lt _ (by decide)⟩
  support law _ known _ v :=
    match law, known with
    | (), rfl => v < 11
  supported law _ known _ _ _ h := by
    cases law; cases known; exact h

/-- Prime-order additive group model for `deployVocab` (`G = ℤ_11`, every valid point has exact
prime order `11` with no cofactor), so Schnorr compact recovery `A = g^z + (-c)Y` holds for every
valid `(Y, c, z)`. -/
def primeOrderModel : Model deployVocab where
  Carrier
    | .scalar => Nat
    | .point => Nat
  valid
    | .scalar, x => x < 11
    | .point, y => y < 11
  literal
    | .scalar, n => some (n % 11)
    | .point, n => some (n % 11)
  apply key _ known args :=
    match key, known, args with
    | .base, rfl, .cons s .nil => some (.cons (s % 11) .nil)
    | .add, rfl, .cons a (.cons b .nil) => some (.cons ((a + b) % 11) .nil)
    | .mul, rfl, .cons a (.cons b .nil) => some (.cons ((a * b) % 11) .nil)
    | .scale, rfl, .cons s (.cons p .nil) => some (.cons ((s * p) % 11) .nil)
    | .plus, rfl, .cons a (.cons b .nil) => some (.cons ((a + b) % 11) .nil)
    | .negScale, rfl, .cons s (.cons p .nil) => some (.cons (((11 - s % 11) % 11 * p) % 11) .nil)
    | .same, rfl, .cons a (.cons b .nil) => some (.cons (decide (a = b)) .nil)
    | .sameScalar, rfl, .cons a (.cons b .nil) => some (.cons (decide (a = b)) .nil)
    | .scalarToByte, rfl, .cons s .nil => some (.cons (s % 256) .nil)
    | .byteToScalar, rfl, .cons b .nil => some (.cons (b % 11) .nil)
    | .pointToByte, rfl, .cons p .nil => some (.cons (p % 256) .nil)
    | .byteToPoint, rfl, .cons b .nil => some (.cons (b % 11) .nil)
    | .mix, rfl, .cons st (.cons bs .nil) => some (.cons (mixBytes st bs) .nil)
    | .squeezeScalar, rfl, .cons st (.cons lbl .nil) =>
        let st' := mixBytes st (0xFF :: lbl)
        some (.cons (st' % 11) (.cons st' .nil))
    | .natToScalar, rfl, .cons n .nil => some (.cons (n % 11) .nil)
  inDomain _ _ _ _ := true
  defined key _ known args := by
    cases key <;> cases known
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r; rfl
  total _ _ _ _ _ := rfl
  decides key _ known _ kind _ := by cases key <;> cases known <;> cases kind
  keeps key _ known args outs _ h := by
    cases key <;> cases known
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨trivial, trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨trivial, trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨trivial, trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial, trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
  literals key n _ := by
    cases key
    · exact ⟨n % 11, rfl, Nat.mod_lt _ (by decide)⟩
    · exact ⟨n % 11, rfl, Nat.mod_lt _ (by decide)⟩
  support law _ known _ v :=
    match law, known with
    | (), rfl => v < 11
  supported law _ known _ _ _ h := by
    cases law; cases known; exact h

/-- Lawful nominal codecs for `deployModel`. -/
def deployCodecs : Codecs deployModel where
  format
    | .scalar => formatFin 11
    | .point => formatFin 23
  lawful
    | .scalar => formatFin_lawful 11
    | .point => formatFin_lawful 23

/-- Vocabulary encoder for `deployVocab`. -/
def deployEncoder : VocabEncoder deployVocab where
  typeKey
    | .scalar => [0]
    | .point => [1]
  rowKey
    | .base => [0]
    | .add => [1]
    | .mul => [2]
    | .scale => [3]
    | .plus => [4]
    | .negScale => [5]
    | .same => [6]
    | .sameScalar => [7]
    | .scalarToByte => [8]
    | .byteToScalar => [9]
    | .pointToByte => [10]
    | .byteToPoint => [11]
    | .mix => [12]
    | .squeezeScalar => [13]
    | .natToScalar => [14]
  lawKey _ := [0]

theorem deployEncoder_injective : deployEncoder.Injective := by
  refine ⟨?_, ?_, ?_⟩
  · intro k₁ k₂ h; cases k₁ <;> cases k₂ <;> cases h <;> rfl
  · intro k₁ k₂ h; cases k₁ <;> cases k₂ <;> cases h <;> rfl
  · intro k₁ k₂ _; cases k₁; cases k₂; rfl

/-! ## Admitted suite, layout, recovery, and sample functions (`ModuleRef` targets) -/

/-- `SuiteSlot.start : [bytes] → [nat]`. -/
def fnStart : Definition deployVocab :=
  .fn ⟨100⟩ [dBytes] [.nat] false none Summary.empty (.mk [0] [
    .op ⟨1⟩ [1] (.literal .nat [1]) [],
    .op ⟨2⟩ [2] (.row .mix) [1, 0]] [2])

/-- `SuiteSlot.absorb : [nat, bytes, bytes] → [nat]`. -/
def fnAbsorb : Definition deployVocab :=
  .fn ⟨101⟩ [.nat, dBytes, dBytes] [.nat] false none Summary.empty (.mk [0, 1, 2] [
    .op ⟨1⟩ [3] (.row .mix) [0, 1],
    .op ⟨2⟩ [4] (.row .mix) [3, 2]] [4])

/-- `SuiteSlot.encode` / `LayoutSlot.write` for `scalar : [scalar] → [bytes]`. -/
def fnEncodeScalar : Definition deployVocab :=
  .fn ⟨102⟩ [dScalar] [dBytes] false none Summary.empty (.mk [0] [
    .op ⟨1⟩ [1] (.row .scalarToByte) [0],
    .op ⟨2⟩ [2] (.owned .seqFill [.seq dByte (some 1)] []) [1],
    .op ⟨3⟩ [3] (.owned .seqUnsized [.seq dByte (some 1)] []) [2]] [3])

/-- `SuiteSlot.encode` / `LayoutSlot.write` for `point : [point] → [bytes]`. -/
def fnEncodePoint : Definition deployVocab :=
  .fn ⟨103⟩ [dPoint] [dBytes] false none Summary.empty (.mk [0] [
    .op ⟨1⟩ [1] (.row .pointToByte) [0],
    .op ⟨2⟩ [2] (.owned .seqFill [.seq dByte (some 1)] []) [1],
    .op ⟨3⟩ [3] (.owned .seqUnsized [.seq dByte (some 1)] []) [2]] [3])

/-- `SuiteSlot.derive : [nat, bytes] → [scalar, nat]`. -/
def fnDeriveScalar : Definition deployVocab :=
  .fn ⟨104⟩ [.nat, dBytes] [dScalar, .nat] false none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2, 3] (.row .squeezeScalar) [0, 1]] [2, 3])

/-- `LayoutSlot.read` for `scalar : [bytes, nat] → [scalar, nat]` (rejects EOF or byte ≥ 11). -/
def fnReadScalar : Definition deployVocab :=
  .fn ⟨105⟩ [dBytes, .nat] [dScalar, .nat] true none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2] (.owned .seqLength [dBytes] []) [0],
    .op ⟨2⟩ [3] (.owned .natLess [] []) [1, 2],
    .guard ⟨3⟩ () 3 .reject,
    .op ⟨4⟩ [4] (.owned .seqAt [dBytes] []) [0, 1],
    .op ⟨5⟩ [5] (.owned .finToNat [dByte] []) [4],
    .op ⟨6⟩ [6] (.literal .nat [11]) [],
    .op ⟨7⟩ [7] (.owned .natLess [] []) [5, 6],
    .guard ⟨8⟩ () 7 .reject,
    .op ⟨9⟩ [8] (.row .byteToScalar) [4],
    .op ⟨10⟩ [9] (.literal .nat [1]) [],
    .op ⟨11⟩ [10] (.owned .natAdd [] []) [1, 9]] [8, 10])

/-- `LayoutSlot.read` for `point : [bytes, nat] → [point, nat]` (rejects EOF or byte ≥ 23). -/
def fnReadPoint : Definition deployVocab :=
  .fn ⟨106⟩ [dBytes, .nat] [dPoint, .nat] true none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2] (.owned .seqLength [dBytes] []) [0],
    .op ⟨2⟩ [3] (.owned .natLess [] []) [1, 2],
    .guard ⟨3⟩ () 3 .reject,
    .op ⟨4⟩ [4] (.owned .seqAt [dBytes] []) [0, 1],
    .op ⟨5⟩ [5] (.owned .finToNat [dByte] []) [4],
    .op ⟨6⟩ [6] (.literal .nat [23]) [],
    .op ⟨7⟩ [7] (.owned .natLess [] []) [5, 6],
    .guard ⟨8⟩ () 7 .reject,
    .op ⟨9⟩ [8] (.row .byteToPoint) [4],
    .op ⟨10⟩ [9] (.literal .nat [1]) [],
    .op ⟨11⟩ [10] (.owned .natAdd [] []) [1, 9]] [8, 10])

/-- `LayoutSlot.equal` for `scalar : [scalar, scalar] → [bool]`. -/
def fnEqScalar : Definition deployVocab :=
  .fn ⟨107⟩ [dScalar, dScalar] [.bool] false none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2] (.row .sameScalar) [0, 1]] [2])

/-- Compact Schnorr recovery: `A = g^z * Y^(-c)` from `(Y : point, c : scalar, z : scalar)`. -/
def fnRecoverCommit : Definition deployVocab :=
  .fn ⟨108⟩ [dPoint, dScalar, dScalar] [dPoint] false none Summary.empty (.mk [0, 1, 2] [
    .op ⟨1⟩ [3] (.row .base) [2],
    .op ⟨2⟩ [4] (.row .negScale) [1, 0],
    .op ⟨3⟩ [5] (.row .plus) [3, 4]] [5])

/-- Witness-, statement-, session-, site-, attempt-, and sequence-bound deterministic sample
derivation `[w : scalar, Y : point, sess : bytes, site : bytes, att : nat, seq : nat] → [scalar]`. -/
def fnSamples : Definition deployVocab :=
  .fn ⟨109⟩ [dScalar, dPoint, dBytes, dBytes, .nat, .nat] [dScalar] false none Summary.empty
    (.mk [0, 1, 2, 3, 4, 5] [
      .op ⟨1⟩ [6] (.row .scalarToByte) [0],
      .op ⟨2⟩ [7] (.row .pointToByte) [1],
      .op ⟨3⟩ [8] (.owned .finToNat [dByte] []) [6],
      .op ⟨4⟩ [9] (.owned .finToNat [dByte] []) [7],
      .op ⟨5⟩ [10] (.row .mix) [8, 2],
      .op ⟨6⟩ [11] (.owned .natAdd [] []) [10, 9],
      .op ⟨7⟩ [12] (.row .mix) [11, 3],
      .op ⟨8⟩ [13] (.literal .nat [17]) [],
      .op ⟨9⟩ [14] (.owned .natMul [] []) [4, 13],
      .op ⟨10⟩ [15] (.owned .natAdd [] []) [12, 14],
      .op ⟨11⟩ [16] (.owned .natAdd [] []) [15, 5],
      .op ⟨12⟩ [17] (.row .natToScalar) [16]] [17])

def toySuite : ModuleRef where
  members := [
    (SuiteSlot.start, ⟨100⟩),
    (SuiteSlot.absorb, ⟨101⟩),
    (SuiteSlot.encode, ⟨102⟩),
    (SuiteSlot.encode, ⟨103⟩),
    (SuiteSlot.derive, ⟨104⟩)
  ]

/-- Minimal suite containing only `SuiteSlot.encode` (no `start`, `absorb`, or `derive`):
demonstrates that `deployIdeal` has zero dependence on concrete hash/sponge functions. -/
def toyIdealOnlySuite : ModuleRef where
  members := [
    (SuiteSlot.encode, ⟨102⟩),
    (SuiteSlot.encode, ⟨103⟩)
  ]

def toyLayoutModule : ModuleRef where
  members := [
    (LayoutSlot.write, ⟨102⟩),
    (LayoutSlot.write, ⟨103⟩),
    (LayoutSlot.read, ⟨105⟩),
    (LayoutSlot.read, ⟨106⟩),
    (LayoutSlot.equal, ⟨107⟩)
  ]

def suiteAndLayoutDefs : List (Definition deployVocab) :=
  [fnStart, fnAbsorb, fnEncodeScalar, fnEncodePoint, fnDeriveScalar,
   fnReadScalar, fnReadPoint, fnEqScalar, fnRecoverCommit, fnSamples]

/-! ## Protocols under test -/

/-- Standard Schnorr identification protocol (`key = 200`). -/
def schnorrProto : Definition deployVocab :=
  .protocol ⟨200⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨10⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨11⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨12⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
      .op ⟨13⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
      .op ⟨14⟩ [6] (.compute [0] (.row .mul)) [5, 0],
      .op ⟨15⟩ [7] (.compute [0] (.row .add)) [2, 6],
      .op ⟨16⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
      .op ⟨17⟩ [9] (.compute [1] (.row .base)) [8],
      .op ⟨18⟩ [10] (.compute [1] (.row .scale)) [5, 1],
      .op ⟨19⟩ [11] (.compute [1] (.row .plus)) [4, 10],
      .op ⟨20⟩ [12] (.compute [1] (.row .same)) [9, 11],
      .guard ⟨21⟩ [1] 12 .reject] [])

/-- Multi-draw Schnorr (`key = 201`): two consecutive verifier draws `c1`, `c2` with no
intervening prover message; verifies transcript state advances on squeeze. -/
def multiDrawProto : Definition deployVocab :=
  .protocol ⟨201⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨310⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨311⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨312⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
      .op ⟨313⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
      .op ⟨314⟩ [6] (.event (.given (.coin ()) 1 [0]) dScalar) [],
      .op ⟨315⟩ [7] (.compute [0, 1] (.row .add)) [5, 6],
      .op ⟨316⟩ [8] (.compute [0] (.row .mul)) [7, 0],
      .op ⟨317⟩ [9] (.compute [0] (.row .add)) [2, 8],
      .op ⟨318⟩ [10] (.event (.flow .message 0 [1]) dScalar) [9],
      .op ⟨319⟩ [11] (.compute [1] (.row .base)) [10],
      .op ⟨320⟩ [12] (.compute [1] (.row .scale)) [7, 1],
      .op ⟨321⟩ [13] (.compute [1] (.row .plus)) [4, 12],
      .op ⟨322⟩ [14] (.compute [1] (.row .same)) [11, 13],
      .guard ⟨323⟩ [1] 14 .reject,
      .op ⟨324⟩ [15] (.compute [1] (.row .sameScalar)) [5, 6],
      .op ⟨325⟩ [16] (.compute [1] (.owned .boolNot [] [])) [15],
      .guard ⟨326⟩ [1] 16 .reject] [])

/-- Retried Schnorr inside prover-owned `.attempt ⟨409⟩ [0]` (`key = 202`).
Attempt 0 sends `A` and derives `c` before aborting on `attemptIdx = 0`, exercising rollback of both
transcript state and proof buffer via `restoreAgain` while `samplesAgain` advances the attempt
counter and preserves `callSeq` so attempt 1 derives a strictly distinct nonce. -/
def retrySchnorrProto : Definition deployVocab :=
  .protocol ⟨202⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .attempt ⟨409⟩ [0] [] (.mk [50] [
        .op ⟨410⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
        .op ⟨411⟩ [3] (.compute [0] (.row .base)) [2],
        .op ⟨412⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
        .op ⟨413⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
        .op ⟨414⟩ [20] (.compute [0] (.literal .nat [0])) [],
        .op ⟨415⟩ [21] (.compute [0] (.owned .natEqual [] [])) [50, 20],
        .op ⟨416⟩ [22] (.compute [0] (.owned .boolNot [] [])) [21],
        .guard ⟨417⟩ [0] 22 .abort,
        .op ⟨418⟩ [6] (.compute [0] (.row .mul)) [5, 0],
        .op ⟨419⟩ [7] (.compute [0] (.row .add)) [2, 6],
        .op ⟨420⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
        .op ⟨421⟩ [9] (.compute [1] (.row .base)) [8],
        .op ⟨422⟩ [10] (.compute [1] (.row .scale)) [5, 1],
        .op ⟨423⟩ [11] (.compute [1] (.row .plus)) [4, 10],
        .op ⟨424⟩ [12] (.compute [1] (.row .same)) [9, 11],
        .guard ⟨425⟩ [1] 12 .reject] [])] [])

/-- Branching Schnorr (`key = 203`): non-straight-line `.choose` on `same(Y, Y)`; accepted by
streaming deployment and refused by compact `recover` deployment. -/
def branchingProto : Definition deployVocab :=
  .protocol ⟨203⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨508⟩ [20] (.compute [0, 1] (.row .same)) [1, 1],
      .choose ⟨509⟩ [0, 1] 20 []
        (.mk [] [
          .op ⟨510⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
          .op ⟨511⟩ [3] (.compute [0] (.row .base)) [2],
          .op ⟨512⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
          .op ⟨513⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
          .op ⟨514⟩ [6] (.compute [0] (.row .mul)) [5, 0],
          .op ⟨515⟩ [7] (.compute [0] (.row .add)) [2, 6],
          .op ⟨516⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
          .op ⟨517⟩ [9] (.compute [1] (.row .base)) [8],
          .op ⟨518⟩ [10] (.compute [1] (.row .scale)) [5, 1],
          .op ⟨519⟩ [11] (.compute [1] (.row .plus)) [4, 10],
          .op ⟨520⟩ [12] (.compute [1] (.row .same)) [9, 11],
          .guard ⟨521⟩ [1] 12 .reject] [])
        (.mk [] [] [])] [])

/-- Authored non-interactive Schnorr (`key = 204`): derives the challenge directly in both roles
without verifier draws, exercising `.authored` layout-only deployment. -/
def authoredSchnorrProto : Definition deployVocab :=
  .protocol ⟨204⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨610⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨611⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨612⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
      .op ⟨613⟩ [5] (.compute [0, 1] (.call ⟨103⟩)) [1],
      .op ⟨614⟩ [6] (.compute [0, 1] (.call ⟨103⟩)) [4],
      .op ⟨615⟩ [7] (.compute [0, 1] (.call ⟨100⟩)) [5],
      .op ⟨616⟩ [8] (.compute [0, 1] (.call ⟨101⟩)) [7, 5, 6],
      .op ⟨617⟩ [9, 10] (.compute [0, 1] (.call ⟨104⟩)) [8, 6],
      .op ⟨618⟩ [11] (.compute [0] (.row .mul)) [9, 0],
      .op ⟨619⟩ [12] (.compute [0] (.row .add)) [2, 11],
      .op ⟨620⟩ [13] (.event (.flow .message 0 [1]) dScalar) [12],
      .op ⟨621⟩ [14] (.compute [1] (.row .base)) [13],
      .op ⟨622⟩ [15] (.compute [1] (.row .scale)) [9, 1],
      .op ⟨623⟩ [16] (.compute [1] (.row .plus)) [4, 15],
      .op ⟨624⟩ [17] (.compute [1] (.row .same)) [14, 16],
      .guard ⟨625⟩ [1] 17 .reject] [])

/-- Single Schnorr sub-round (`key = 205`) invoked twice by `doubleApplyProto`. -/
def subRoundProto : Definition deployVocab :=
  .protocol ⟨205⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨710⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨711⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨712⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
      .op ⟨713⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
      .op ⟨714⟩ [6] (.compute [0] (.row .mul)) [5, 0],
      .op ⟨715⟩ [7] (.compute [0] (.row .add)) [2, 6],
      .op ⟨716⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
      .op ⟨717⟩ [9] (.compute [1] (.row .base)) [8],
      .op ⟨718⟩ [10] (.compute [1] (.row .scale)) [5, 1],
      .op ⟨719⟩ [11] (.compute [1] (.row .plus)) [4, 10],
      .op ⟨720⟩ [12] (.compute [1] (.row .same)) [9, 11],
      .guard ⟨721⟩ [1] 12 .reject] [])

/-- Protocol applying `subRoundProto` twice (`key = 206`) at distinct call sites `⟨740⟩`, `⟨741⟩`. -/
def doubleApplyProto : Definition deployVocab :=
  .protocol ⟨206⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨740⟩ [] (.apply ⟨205⟩ [0, 1]) [0, 1],
      .op ⟨741⟩ [] (.apply ⟨205⟩ [0, 1]) [0, 1]] [])

/-- Looped two-round Schnorr (`key = 207`) exercising `.loop` deployment, specialization, and
per-iteration `callSeq` separation in `samples`. -/
def loopSchnorrProto : Definition deployVocab :=
  .protocol ⟨207⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .loop ⟨809⟩ [0, 1] (.fixed 2) [] [] (.mk [80] [
        .op ⟨810⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
        .op ⟨811⟩ [3] (.compute [0] (.row .base)) [2],
        .op ⟨812⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
        .op ⟨813⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
        .op ⟨814⟩ [6] (.compute [0] (.row .mul)) [5, 0],
        .op ⟨815⟩ [7] (.compute [0] (.row .add)) [2, 6],
        .op ⟨816⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
        .op ⟨817⟩ [9] (.compute [1] (.row .base)) [8],
        .op ⟨818⟩ [10] (.compute [1] (.row .scale)) [5, 1],
        .op ⟨819⟩ [11] (.compute [1] (.row .plus)) [4, 10],
        .op ⟨820⟩ [12] (.compute [1] (.row .same)) [9, 11],
        .guard ⟨821⟩ [1] 12 .reject] [])] [])

/-- Negative-control protocol (`key = 208`) whose attempt is owned by the verifier (`[1]`): must be
refused by non-interactive retry declarations with `Rule.attempt`. -/
def verifierAttemptProto : Definition deployVocab :=
  .protocol ⟨208⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .attempt ⟨909⟩ [1] [] (.mk [90] [
        .op ⟨910⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
        .op ⟨911⟩ [3] (.compute [0] (.row .base)) [2],
        .op ⟨912⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
        .op ⟨913⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
        .op ⟨914⟩ [6] (.compute [0] (.row .mul)) [5, 0],
        .op ⟨915⟩ [7] (.compute [0] (.row .add)) [2, 6],
        .op ⟨916⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
        .op ⟨917⟩ [9] (.compute [1] (.row .base)) [8],
        .op ⟨918⟩ [10] (.compute [1] (.row .scale)) [5, 1],
        .op ⟨919⟩ [11] (.compute [1] (.row .plus)) [4, 10],
        .op ⟨920⟩ [12] (.compute [1] (.row .same)) [9, 11],
        .guard ⟨921⟩ [1] 12 .reject] [])] [])

/-- Negative-control protocol (`key = 209`) with an `abort` guard in sibling attempt `⟨941⟩` outside
retry target `⟨940⟩`: must be refused with `Rule.attempt`. -/
def abortOutsideTargetProto : Definition deployVocab :=
  .protocol ⟨209⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .attempt ⟨940⟩ [0] [] (.mk [91] [
        .op ⟨942⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
        .op ⟨943⟩ [3] (.compute [0] (.row .base)) [2],
        .op ⟨944⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
        .op ⟨945⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
        .op ⟨946⟩ [6] (.compute [0] (.row .mul)) [5, 0],
        .op ⟨947⟩ [7] (.compute [0] (.row .add)) [2, 6],
        .op ⟨948⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
        .op ⟨949⟩ [9] (.compute [1] (.row .base)) [8],
        .op ⟨950⟩ [10] (.compute [1] (.row .scale)) [5, 1],
        .op ⟨951⟩ [11] (.compute [1] (.row .plus)) [4, 10],
        .op ⟨952⟩ [12] (.compute [1] (.row .same)) [9, 11],
        .guard ⟨953⟩ [1] 12 .reject] []),
      .attempt ⟨941⟩ [0] [] (.mk [92] [
        .op ⟨954⟩ [20] (.compute [0] (.literal .bool [1])) [],
        .guard ⟨955⟩ [0] 20 .abort] [])] [])

/-! ## Depth-8 diamond-DAG subprotocol chain (`2^8 = 256` call paths, linear `ClosedProcs`) -/

/-- Leaf gadget `dag0` (`key = 250`): doubles a shared scalar `x ↦ (x + x) mod 11`. -/
def dagLeafProto : Definition deployVocab :=
  .protocol ⟨250⟩ 2 [⟨dScalar, [0, 1]⟩] [⟨dScalar, [0, 1]⟩]
    (.mk [0] [
      .op ⟨3000⟩ [1] (.compute [0, 1] (.row .add)) [0, 0]] [1])

/-- Diamond level `dag(k+1)` (`key = 250 + k + 1`): calls `dag(k)` twice at distinct sites. -/
def dagLevelProto (k : Nat) : Definition deployVocab :=
  .protocol ⟨251 + k⟩ 2 [⟨dScalar, [0, 1]⟩] [⟨dScalar, [0, 1]⟩]
    (.mk [0] [
      .op ⟨3010 + 2 * k⟩ [1] (.apply ⟨250 + k⟩ [0, 1]) [0],
      .op ⟨3011 + 2 * k⟩ [2] (.apply ⟨250 + k⟩ [0, 1]) [1]] [2])

/-- Schnorr identification protocol calling `dag8` (`2^8 = 256` dynamic call paths) on the derived
Fiat–Shamir challenge `c` (`key = 260`). Because `dag8`'s subtree contains no handler clauses,
`Core.specialize` deduplicates all 9 levels into 9 `ClosedProcs` (linear `astSize`) instead of
inlining a 511-node exponential call tree. -/
def dagSchnorrProto : Definition deployVocab :=
  .protocol ⟨260⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨2610⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨2611⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨2612⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
      .op ⟨2613⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
      .op ⟨2614⟩ [20] (.apply ⟨258⟩ [0, 1]) [5],
      .op ⟨2615⟩ [6] (.compute [0] (.row .mul)) [20, 0],
      .op ⟨2616⟩ [7] (.compute [0] (.row .add)) [2, 6],
      .op ⟨2617⟩ [8] (.event (.flow .message 0 [1]) dScalar) [7],
      .op ⟨2618⟩ [9] (.compute [1] (.row .base)) [8],
      .op ⟨2619⟩ [10] (.compute [1] (.row .scale)) [20, 1],
      .op ⟨2620⟩ [11] (.compute [1] (.row .plus)) [4, 10],
      .op ⟨2621⟩ [12] (.compute [1] (.row .same)) [9, 11],
      .guard ⟨2622⟩ [1] 12 .reject] [])

def dagChainDefs : List (Definition deployVocab) :=
  [dagLeafProto, dagLevelProto 0, dagLevelProto 1, dagLevelProto 2, dagLevelProto 3,
   dagLevelProto 4, dagLevelProto 5, dagLevelProto 6, dagLevelProto 7, dagSchnorrProto]

def deployTestProgram : NamedProgram deployVocab where
  definitions := suiteAndLayoutDefs ++ [
    schnorrProto, multiDrawProto, retrySchnorrProto, branchingProto,
    authoredSchnorrProto, subRoundProto, doubleApplyProto, loopSchnorrProto,
    verifierAttemptProto, abortOutsideTargetProto
  ]

def dagTestProgram : NamedProgram deployVocab where
  definitions := suiteAndLayoutDefs ++ dagChainDefs

theorem except_toOption_get_ok {E A : Type} (x : Except E A) (h : x.toOption.isSome) :
    x = .ok (x.toOption.get h) := by
  cases x with
  | error _ => cases h
  | ok a => rfl

private theorem admittedSuite_isSome :
    (admit deployTestProgram noAssociation).toOption.isSome = true := by
  decide +kernel

/-- Kernel-verified admission of the main test suite (functions + protocols). -/
def admittedSuite : Admitted deployVocab :=
  (admit deployTestProgram noAssociation).toOption.get admittedSuite_isSome

theorem admittedSuite_ok :
    admit deployTestProgram noAssociation = .ok admittedSuite :=
  except_toOption_get_ok _ admittedSuite_isSome

private theorem admittedDag_isSome :
    (admit dagTestProgram noAssociation).toOption.isSome = true := by
  decide +kernel

/-- Kernel-verified admission of the depth-8 diamond-DAG test program. -/
def admittedDag : Admitted deployVocab :=
  (admit dagTestProgram noAssociation).toOption.get admittedDag_isSome

theorem admittedDag_ok :
    admit dagTestProgram noAssociation = .ok admittedDag :=
  except_toOption_get_ok _ admittedDag_isSome

/-! ## Declarations and deployments -/

def schnorrDecl : Declaration where
  key := ⟨1⟩
  entry := ⟨200⟩
  kinds := [.online, .online]
  construction := .derived toySuite none
  prover := none
  layout := some ⟨toyLayoutModule, [], []⟩
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

def schnorrTaggedDecl : Declaration :=
  { schnorrDecl with construction := .derived toySuite (some [115, 99, 104, 110, 111, 114, 114, 49]) }

def schnorrTaggedOtherAppDecl : Declaration :=
  { schnorrTaggedDecl with application := [99, 17] }

def schnorrAppCtxDecl : Declaration :=
  { schnorrDecl with application := [42, 7, 3] }

def schnorrSamplesDecl : Declaration :=
  { schnorrDecl with key := ⟨10⟩, samples := some ⟨109⟩ }

def schnorrSamplesAppDecl : Declaration :=
  { schnorrSamplesDecl with application := [42, 7] }

def schnorrCompactDecl : Declaration :=
  { schnorrDecl with
    key := ⟨2⟩
    layout := some ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩], [(⟨[], ⟨12⟩⟩, ⟨108⟩)]⟩ }

def multiDrawDecl : Declaration where
  key := ⟨3⟩
  entry := ⟨201⟩
  kinds := [.online, .online]
  construction := .derived toySuite none
  prover := none
  layout := some ⟨toyLayoutModule, [], []⟩
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

def retrySchnorrDecl : Declaration where
  key := ⟨4⟩
  entry := ⟨202⟩
  kinds := [.online, .online]
  construction := .derived toySuite none
  prover := none
  layout := some ⟨toyLayoutModule, [], []⟩
  retry := some (4, ⟨[], ⟨409⟩⟩)
  samples := some ⟨109⟩
  context := []
  grinds := []
  commits := []
  pins := []

def interactiveDecl : Declaration where
  key := ⟨11⟩
  entry := ⟨200⟩
  kinds := [.online, .online]
  construction := .interactive
  prover := none
  layout := none
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

def authoredDecl : Declaration where
  key := ⟨12⟩
  entry := ⟨204⟩
  kinds := [.online, .online]
  construction := .authored
  prover := none
  layout := some ⟨toyLayoutModule, [], []⟩
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

def doubleApplyDecl : Declaration :=
  { schnorrDecl with key := ⟨13⟩, entry := ⟨206⟩ }

def doubleApplySamplesDecl : Declaration :=
  { doubleApplyDecl with key := ⟨14⟩, samples := some ⟨109⟩ }

def loopSchnorrDecl : Declaration :=
  { schnorrDecl with key := ⟨15⟩, entry := ⟨207⟩ }

def loopSchnorrSamplesDecl : Declaration :=
  { loopSchnorrDecl with key := ⟨16⟩, samples := some ⟨109⟩ }

def dagSchnorrDecl : Declaration :=
  { schnorrDecl with key := ⟨17⟩, entry := ⟨260⟩ }

private theorem schnorr_deploy_isSome :
    (deploy deployEncoder admittedSuite schnorrDecl).toOption.isSome = true := by
  decide +kernel

def schnorrDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrDecl).toOption.get schnorr_deploy_isSome

theorem schnorr_deploy_ok :
    deploy deployEncoder admittedSuite schnorrDecl = .ok schnorrDeployed :=
  except_toOption_get_ok _ schnorr_deploy_isSome

def schnorrTaggedDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrTaggedDecl).toOption.get (by decide +kernel)

def schnorrTaggedOtherAppDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrTaggedOtherAppDecl).toOption.get (by decide +kernel)

def schnorrAppCtxDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrAppCtxDecl).toOption.get (by decide +kernel)

def schnorrSamplesDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrSamplesDecl).toOption.get (by decide +kernel)

def schnorrSamplesAppDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrSamplesAppDecl).toOption.get (by decide +kernel)

def schnorrCompactDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrCompactDecl).toOption.get (by decide +kernel)

def multiDrawDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite multiDrawDecl).toOption.get (by decide +kernel)

private theorem retrySchnorr_deploy_isSome :
    (deploy deployEncoder admittedSuite retrySchnorrDecl).toOption.isSome = true := by
  decide +kernel

def retrySchnorrDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite retrySchnorrDecl).toOption.get retrySchnorr_deploy_isSome

theorem retrySchnorr_deploy_ok :
    deploy deployEncoder admittedSuite retrySchnorrDecl = .ok retrySchnorrDeployed :=
  except_toOption_get_ok _ retrySchnorr_deploy_isSome

def interactiveDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite interactiveDecl).toOption.get (by decide +kernel)

def authoredDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite authoredDecl).toOption.get (by decide +kernel)

def doubleApplyDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite doubleApplyDecl).toOption.get (by decide +kernel)

def doubleApplySamplesDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite doubleApplySamplesDecl).toOption.get (by decide +kernel)

def loopSchnorrDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite loopSchnorrDecl).toOption.get (by decide +kernel)

def loopSchnorrSamplesDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite loopSchnorrSamplesDecl).toOption.get (by decide +kernel)

private theorem dagSchnorr_deploy_isSome :
    (deploy deployEncoder admittedDag dagSchnorrDecl).toOption.isSome = true := by
  decide +kernel

def dagSchnorrDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedDag dagSchnorrDecl).toOption.get dagSchnorr_deploy_isSome

theorem dagSchnorr_deploy_ok :
    deploy deployEncoder admittedDag dagSchnorrDecl = .ok dagSchnorrDeployed :=
  except_toOption_get_ok _ dagSchnorr_deploy_isSome

def idealServiceKey : Key := ⟨999⟩

private theorem schnorrIdeal_deploy_isSome :
    (deployIdeal deployEncoder idealServiceKey admittedSuite schnorrDecl).toOption.isSome = true := by
  decide +kernel

def schnorrIdealDeployed : Deployed deployVocab :=
  (deployIdeal deployEncoder idealServiceKey admittedSuite schnorrDecl).toOption.get
    schnorrIdeal_deploy_isSome

theorem schnorrIdeal_deploy_ok :
    deployIdeal deployEncoder idealServiceKey admittedSuite schnorrDecl = .ok schnorrIdealDeployed :=
  except_toOption_get_ok _ schnorrIdeal_deploy_isSome

def schnorrIdealOnlyDecl : Declaration :=
  { schnorrDecl with key := ⟨5⟩, construction := .derived toyIdealOnlySuite none }

def schnorrIdealOnlyDeployed : Deployed deployVocab :=
  (deployIdeal deployEncoder idealServiceKey admittedSuite schnorrIdealOnlyDecl).toOption.get (by decide +kernel)

def multiDrawIdealDeployed : Deployed deployVocab :=
  (deployIdeal deployEncoder idealServiceKey admittedSuite multiDrawDecl).toOption.get (by decide +kernel)

def doubleApplyIdealDeployed : Deployed deployVocab :=
  (deployIdeal deployEncoder idealServiceKey admittedSuite doubleApplyDecl).toOption.get (by decide +kernel)

def loopSchnorrIdealDeployed : Deployed deployVocab :=
  (deployIdeal deployEncoder idealServiceKey admittedSuite loopSchnorrDecl).toOption.get (by decide +kernel)

def branchingStreamingDecl : Declaration :=
  { schnorrDecl with key := ⟨6⟩, entry := ⟨203⟩ }

def branchingStreamingDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite branchingStreamingDecl).toOption.get (by decide +kernel)

/-! ## Execution helpers -/

/-- Fixed private randomness source returning `nonce % 11` for any scalar coin. -/
def fixedNonceSource (nonce : Nat) : Source deployModel := fun _ τ =>
  match τ with
  | .nominal .scalar => some (nonce % 11)
  | _ => none

/-- Build `(witness, statement)` inputs for any of our Schnorr-shaped protocols. -/
def schnorrInputs (insTys : List (LTy deployVocab)) (witness statement : Nat) :
    Option (HList (LVal deployModel) insTys) :=
  match insTys with
  | [⟨.nominal .scalar, [0]⟩, ⟨.nominal .point, [0, 1]⟩] =>
      some (.cons (witness : Nat) (.cons (statement : Nat) .nil))
  | _ => none

/-- Extract the single proof byte list from `Stack.Gives (d.stack 0)`. -/
def extractProofBytes : {ts : List (Ty DeployType)} → HList deployModel.Val ts → Option (List Nat)
  | [.seq (.fin 256) none], .cons bs .nil => some bs
  | _, _ => none

/-- Pack a proof byte list into `Stack.Takes (d.stack 1)`. -/
def packProofBytes (bs : List Nat) : (ts : List (Ty DeployType)) → Option (HList deployModel.Val ts)
  | [.seq (.fin 256) none] => some (.cons bs .nil)
  | _ => none

/-- Run prover on `(d, witness, statement, nonce)` using official `Core.execute`. -/
def runProve (d : Deployed deployVocab) (witness statement nonce : Nat) : Option (List Nat) :=
  if hEmpty : Stack.Takes (d.stack 0) = [] then
    (schnorrInputs d.entry.ins witness statement).bind fun ins =>
      (prove execute d deployModel 0 (hideAll deployModel 0 ins) hEmpty
        (fixedNonceSource nonce) 512).bind extractProofBytes
  else none

/-- Run verifier on `(d, statement, proof)` using official `Core.execute`. -/
def runVerify (d : Deployed deployVocab) (statement : Nat) (proof : List Nat) : Bool :=
  match schnorrInputs d.entry.ins 0 statement, packProofBytes proof (Stack.Takes (d.stack 1)) with
  | some ins, some taken =>
      (verify execute d deployModel 1 (hideAll deployModel 1 ins) taken
        (fixedNonceSource 0) 512).isSome
  | _, _ => false

/-- Run prover via `Core.specialize` and compare its exact proof bytes against `d.run`. -/
def runProveSpecialized (d : Deployed deployVocab) (witness statement nonce : Nat) :
    Option (List Nat) :=
  if hEmpty : Stack.Takes (d.stack 0) = [] then
    (schnorrInputs d.entry.ins witness statement).bind fun ins =>
      let cr := specialize d 0
      let p := cr.denote deployModel (Defs.fnTable deployModel d.admitted.program.defs)
        (hideAll deployModel 0 ins) (cast (congrArg (HList deployModel.Val) hEmpty.symm) .nil)
      match (runProcess deployModel (fixedNonceSource nonce) 0 p 512).1 with
      | .ended (.returned (_, gives)) => extractProofBytes gives
      | _ => none
  else none

/-- Run verifier via `Core.specialize`. -/
def runVerifySpecialized (d : Deployed deployVocab) (statement : Nat) (proof : List Nat) : Bool :=
  match schnorrInputs d.entry.ins 0 statement, packProofBytes proof (Stack.Takes (d.stack 1)) with
  | some ins, some taken =>
      let cr := specialize d 1
      let p := cr.denote deployModel (Defs.fnTable deployModel d.admitted.program.defs)
        (hideAll deployModel 1 ins) taken
      match (runProcess deployModel (fixedNonceSource 0) 1 p 512).1 with
      | .ended (.returned _) => true
      | _ => false
  | _, _ => false

/-- Fold a pure `(metaLog, dataLog)` ideal transcript path through the concrete toy sponge
(`fnStart`, `fnAbsorb`, `fnDeriveScalar`), demonstrating exact agreement with concrete prover runs. -/
def foldIdealPathEntries (st : Nat) : List (List Nat) → List (List Nat) → Option Nat
  | [], [] => some st
  | (1 :: lbl) :: ms, enc :: ds => foldIdealPathEntries (mixBytes (mixBytes st lbl) enc) ms ds
  | (2 :: lbl) :: ms, enc :: ds => foldIdealPathEntries (mixBytes (mixBytes st lbl) enc) ms ds
  | (3 :: lbl) :: ms, _ :: ds => foldIdealPathEntries (mixBytes st (0xFF :: lbl)) ms ds
  | _, _ => none

def evalIdealPathConcrete : List (List Nat) → List (List Nat) → Option Nat
  | (0 :: sess) :: ms, ds => foldIdealPathEntries (mixBytes 1 sess) ms ds
  | _, _ => none

/-- Concrete partial random oracle `IdealRO deployModel dByte` answering scalar draws via
`evalIdealPathConcrete` and returning `none` on non-scalar types. -/
def schnorrIdealRO : LayerBuild.IdealRO deployModel dByte := fun st lbl τ =>
  match τ with
  | .nominal .scalar =>
      match evalIdealPathConcrete st.1 st.2.1 with
      | some s => some ((mixBytes s (0xFF :: lbl)) % 11)
      | none => some (0 : Nat)
  | _ => none

/-- Run an ideal random-oracle verifier process by answering every `.own (.request idealServiceKey)`
query over `idealQueryTy dByte` (`((metaLog, dataLog), drawLbl)`) and recording every queried path. -/
def runIdealOracle {A : Type} :
    Process (RSig deployModel) Stop A → Nat →
      Option A × List (List (List Nat) × List (List Nat) × List Nat)
  | .done a, _ => (some a, [])
  | .halt _, _ => (none, [])
  | .call (.own (.request k) [] _
        [.tuple (.cons (.tuple (.cons (.seq (.seq (.fin 256) none) none)
                                (.cons (.seq (.seq (.fin 256) none) none) .nil)))
                       (.cons (.seq (.fin 256) none) .nil))]
        (.cons ((metaLog, dataLog, ()), lbl, ()) .nil) (.nominal .scalar)) next, n + 1 =>
      if k = idealServiceKey then
        match evalIdealPathConcrete metaLog dataLog with
        | some st =>
            let c := (mixBytes st (0xFF :: lbl)) % 11
            let (res, qs) := runIdealOracle (next c) n
            (res, (metaLog, dataLog, lbl) :: qs)
        | none => (none, [])
      else (none, [])
  | .call _ _, _ => (none, [])

def constructionClauseSites (d : Deployed deployVocab) (r : Role) : List Site :=
  match (d.stack r).find? (fun l => l.line == .construction) with
  | some l => l.clauses.map (·.site.site)
  | none => []

/-! ## Distribution-aware two-law vocabulary (`uniform` vs `nonzero` on `.fin 11`) -/

inductive TwoLaw where
  | uniform
  | nonzero
deriving DecidableEq

inductive TwoLawRow where
  | mix
  | squeezeUniform
  | squeezeNonZero
  | fin11ToByte
  | byteToFin11
  | fin11Add
deriving DecidableEq

abbrev tlElem : Ty Empty := .fin 11
abbrev tlByte : Ty Empty := .fin 256
abbrev tlBytes : Ty Empty := .seq tlByte none

/-- Vocabulary with TWO distinct sampling laws (`uniform` ∈ `[0, 11)` and `nonzero` ∈ `[1, 11)`)
sharing the exact same Core value type `.fin 11`. -/
def twoLawVocab : Vocabulary where
  TypeKey := Empty
  RowKey := TwoLawRow
  LawKey := TwoLaw
  row r := some <| match r with
    | .mix => ⟨[.nat, tlBytes], [.nat], .pure⟩
    | .squeezeUniform => ⟨[.nat, tlBytes], [tlElem, .nat], .pure⟩
    | .squeezeNonZero => ⟨[.nat, tlBytes], [tlElem, .nat], .pure⟩
    | .fin11ToByte => ⟨[tlElem], [tlByte], .pure⟩
    | .byteToFin11 => ⟨[tlByte], [tlElem], .pure⟩
    | .fin11Add => ⟨[tlElem, tlElem], [tlElem], .pure⟩
  law _ := some ⟨[], tlElem⟩
  literal _ _ := true
  decided key _ _ found kind := by cases key <;> cases found <;> cases kind

def twoLawModel : Model twoLawVocab where
  Carrier k := nomatch k
  valid k := nomatch k
  literal k := nomatch k
  apply key _ known args :=
    match key, known, args with
    | .mix, rfl, .cons st (.cons bs .nil) => some (.cons (mixBytes st bs) .nil)
    | .squeezeUniform, rfl, .cons st (.cons lbl .nil) =>
        let st' := mixBytes st (0xFE :: lbl)
        some (.cons (st' % 11) (.cons st' .nil))
    | .squeezeNonZero, rfl, .cons st (.cons lbl .nil) =>
        let st' := mixBytes st (0xFD :: lbl)
        some (.cons (1 + st' % 10) (.cons st' .nil))
    | .fin11ToByte, rfl, .cons x .nil => some (.cons (x % 256) .nil)
    | .byteToFin11, rfl, .cons b .nil => some (.cons (b % 11) .nil)
    | .fin11Add, rfl, .cons a (.cons b .nil) => some (.cons ((a + b) % 11) .nil)
  inDomain _ _ _ _ := true
  defined key _ known args := by
    cases key <;> cases known
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r; rfl
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; rfl
  total _ _ _ _ _ := rfl
  decides key _ known _ kind _ := by cases key <;> cases known <;> cases kind
  keeps key _ known args outs _ h := by
    cases key <;> cases known
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨trivial, trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial, trivial⟩
    · cases args with | cons st r => cases r with | cons lbl r2 => cases r2; injection h with e; subst e; exact ⟨Nat.add_lt_add_left (Nat.mod_lt (mixBytes st (0xFD :: lbl)) (show 0 < 10 by decide)) 1, trivial, trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons _ r => cases r with | cons _ r2 => cases r2; injection h with e; subst e; exact ⟨Nat.mod_lt _ (by decide), trivial⟩
  literals k := nomatch k
  support law _ known _ v :=
    match law, known with
    | .uniform, rfl => v < 11
    | .nonzero, rfl => 0 < v ∧ v < 11
  supported law _ known _ _ _ h := by
    cases law <;> cases known
    · exact h
    · exact h.2

def twoLawEncoder : VocabEncoder twoLawVocab where
  typeKey k := nomatch k
  rowKey
    | .mix => [0]
    | .squeezeUniform => [1]
    | .squeezeNonZero => [2]
    | .fin11ToByte => [3]
    | .byteToFin11 => [4]
    | .fin11Add => [5]
  lawKey
    | .uniform => [0]
    | .nonzero => [1]

def tlFnStart : Definition twoLawVocab :=
  .fn ⟨100⟩ [tlBytes] [.nat] false none Summary.empty (.mk [0] [
    .op ⟨1⟩ [1] (.literal .nat [1]) [],
    .op ⟨2⟩ [2] (.row .mix) [1, 0]] [2])

def tlFnAbsorb : Definition twoLawVocab :=
  .fn ⟨101⟩ [.nat, tlBytes, tlBytes] [.nat] false none Summary.empty (.mk [0, 1, 2] [
    .op ⟨1⟩ [3] (.row .mix) [0, 1],
    .op ⟨2⟩ [4] (.row .mix) [3, 2]] [4])

def tlFnEncode : Definition twoLawVocab :=
  .fn ⟨102⟩ [tlElem] [tlBytes] false none Summary.empty (.mk [0] [
    .op ⟨1⟩ [1] (.row .fin11ToByte) [0],
    .op ⟨2⟩ [2] (.owned .seqFill [.seq tlByte (some 1)] []) [1],
    .op ⟨3⟩ [3] (.owned .seqUnsized [.seq tlByte (some 1)] []) [2]] [3])

def tlFnDeriveUniform : Definition twoLawVocab :=
  .fn ⟨104⟩ [.nat, tlBytes] [tlElem, .nat] false none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2, 3] (.row .squeezeUniform) [0, 1]] [2, 3])

def tlFnDeriveNonZero : Definition twoLawVocab :=
  .fn ⟨105⟩ [.nat, tlBytes] [tlElem, .nat] false none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2, 3] (.row .squeezeNonZero) [0, 1]] [2, 3])

def tlFnRead : Definition twoLawVocab :=
  .fn ⟨106⟩ [tlBytes, .nat] [tlElem, .nat] true none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2] (.owned .seqLength [tlBytes] []) [0],
    .op ⟨2⟩ [3] (.owned .natLess [] []) [1, 2],
    .guard ⟨3⟩ () 3 .reject,
    .op ⟨4⟩ [4] (.owned .seqAt [tlBytes] []) [0, 1],
    .op ⟨5⟩ [5] (.owned .finToNat [tlByte] []) [4],
    .op ⟨6⟩ [6] (.literal .nat [11]) [],
    .op ⟨7⟩ [7] (.owned .natLess [] []) [5, 6],
    .guard ⟨8⟩ () 7 .reject,
    .op ⟨9⟩ [8] (.row .byteToFin11) [4],
    .op ⟨10⟩ [9] (.literal .nat [1]) [],
    .op ⟨11⟩ [10] (.owned .natAdd [] []) [1, 9]] [8, 10])

/-- Protocol drawing BOTH a `.uniform` and a `.nonzero` challenge of the SAME type `.fin 11`,
verifying `0 < c_nonzero` and checking `resp = c_uniform + c_nonzero + w`. -/
def twoLawProto : Definition twoLawVocab :=
  .protocol ⟨200⟩ 2 [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨10⟩ [2] (.event (.flow .message 0 [1]) tlElem) [1],
      .op ⟨11⟩ [3] (.event (.given (.coin .uniform) 1 [0]) tlElem) [],
      .op ⟨12⟩ [4] (.event (.given (.coin .nonzero) 1 [0]) tlElem) [],
      .op ⟨13⟩ [5] (.compute [0, 1] (.row .fin11Add)) [3, 4],
      .op ⟨14⟩ [6] (.compute [0] (.row .fin11Add)) [5, 0],
      .op ⟨15⟩ [7] (.event (.flow .message 0 [1]) tlElem) [6],
      .op ⟨16⟩ [8] (.compute [1] (.owned .finToNat [tlElem] [])) [4],
      .op ⟨17⟩ [9] (.compute [1] (.literal .nat [0])) [],
      .op ⟨18⟩ [10] (.compute [1] (.owned .natLess [] [])) [9, 8],
      .guard ⟨19⟩ [1] 10 .reject,
      .op ⟨20⟩ [11] (.compute [1] (.row .fin11Add)) [5, 2],
      .op ⟨21⟩ [12] (.compute [1] (.owned .finToNat [tlElem] [])) [7],
      .op ⟨22⟩ [13] (.compute [1] (.owned .finToNat [tlElem] [])) [11],
      .op ⟨23⟩ [14] (.compute [1] (.owned .natEqual [] [])) [12, 13],
      .guard ⟨24⟩ [1] 14 .reject] [])

def twoLawSuite : ModuleRef where
  members := [
    (SuiteSlot.start, ⟨100⟩),
    (SuiteSlot.absorb, ⟨101⟩),
    (SuiteSlot.encode, ⟨102⟩)
  ]
  lawMembers := [
    (SuiteSlot.derive, twoLawEncoder.lawKey .uniform, ⟨104⟩),
    (SuiteSlot.derive, twoLawEncoder.lawKey .nonzero, ⟨105⟩)
  ]

def twoLawSuiteSwapped : ModuleRef where
  members := twoLawSuite.members
  lawMembers := [
    (SuiteSlot.derive, twoLawEncoder.lawKey .uniform, ⟨105⟩),
    (SuiteSlot.derive, twoLawEncoder.lawKey .nonzero, ⟨105⟩)
  ]

def twoLawSuiteIncomplete : ModuleRef where
  members := twoLawSuite.members
  lawMembers := [
    (SuiteSlot.derive, twoLawEncoder.lawKey .uniform, ⟨104⟩)
  ]

def twoLawLayout : ModuleRef where
  members := [
    (LayoutSlot.write, ⟨102⟩),
    (LayoutSlot.read, ⟨106⟩)
  ]

def twoLawProgram : NamedProgram twoLawVocab where
  definitions := [tlFnStart, tlFnAbsorb, tlFnEncode, tlFnDeriveUniform, tlFnDeriveNonZero, tlFnRead, twoLawProto]

private theorem admittedTwoLaw_isSome :
    (admit twoLawProgram noAssociation).toOption.isSome = true := by
  decide +kernel

def admittedTwoLaw : Admitted twoLawVocab :=
  (admit twoLawProgram noAssociation).toOption.get admittedTwoLaw_isSome

def twoLawDecl : Declaration where
  key := ⟨1⟩
  entry := ⟨200⟩
  kinds := [.online, .online]
  construction := .derived twoLawSuite none
  prover := none
  layout := some ⟨twoLawLayout, [], []⟩
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

def twoLawSwappedDecl : Declaration :=
  { twoLawDecl with construction := .derived twoLawSuiteSwapped none }

def twoLawDeployed : Deployed twoLawVocab :=
  (deploy twoLawEncoder admittedTwoLaw twoLawDecl).toOption.get (by decide +kernel)

def twoLawSwappedDeployed : Deployed twoLawVocab :=
  (deploy twoLawEncoder admittedTwoLaw twoLawSwappedDecl).toOption.get (by decide +kernel)

end Zkc.Core.Tests.Deployment
