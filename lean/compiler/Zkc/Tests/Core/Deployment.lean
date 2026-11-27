import Zkc.Core.Format.Canonical
import Zkc.Core.Scheme.Deploy
import Zkc.Core.Scheme.Theorems
import Zkc.Core.Run.Execute
import Zkc.Core.Run.Specialize
import Zkc.Core.Admission.Admit
import Zkc.Tests.Core.Consumers

/-!
End-to-end kernel-checked tests and negative controls for:
1. Canonical wire formats (`Zkc.Core.Format.Canonical`).
2. Official `Core.deploy` building checked `Core.Layer` IR stacks (`[samples?, construction, layout]`)
   from real admitted suite, layout, recovery, and sampling functions passed via `ModuleRef`.
3. Official `Core.deployIdeal` replacing verifier concrete draws with ideal RO service requests.
4. Verified Core-level handler specialization (`Core.specialize` + `specialize_sound`): verifying
   that `(specialize d r).denote` matches `d.run` identically on standard, multi-draw, compact,
   and retried deployments.
5. Reference execution (`execute`, `prove`, `verify`, `runInteractive`) across honest runs,
   Weak Fiat-Shamir binding, compact `carry`+`recover`, multi-draw state advancement, retried
   attempts with `samples` + `restoreAgain`, and all verifier negative controls.
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

-- Compute concrete protocol runs by kernel reduction in tests.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

set_option maxRecDepth 16000

/-! ## Canonical wire format checks -/

theorem byteWidth_cases :
    byteWidth 0 = 0 ∧
    byteWidth 1 = 0 ∧
    byteWidth 2 = 1 ∧
    byteWidth 256 = 1 ∧
    byteWidth 257 = 2 ∧
    byteWidth (2 ^ 64) = 8 ∧
    byteWidth (2 ^ 65) = 9 := by
  decide +kernel

theorem formatFin_roundtrip_and_reject :
    (formatFin 257).write 256 = [0, 1] ∧
    (formatFin 257).read [0, 1, 99] = some (256, [99]) ∧
    (formatFin 257).read [1, 1] = none ∧
    (formatFin 257).read [256, 0] = none ∧
    (formatFin 17).write 16 = [16] ∧
    (formatFin 17).read [17] = none ∧
    (formatFin 17).read [] = none := by
  decide +kernel

theorem formatBool_roundtrip_and_reject :
    formatBool.write false = [0] ∧
    formatBool.write true = [1] ∧
    formatBool.read [0, 42] = some (false, [42]) ∧
    formatBool.read [1] = some (true, []) ∧
    formatBool.read [2] = none ∧
    formatBool.read [] = none := by
  decide +kernel

theorem formatNat_leb128_roundtrip_and_canonical :
    formatNat.write 0 = [0] ∧
    formatNat.write 127 = [127] ∧
    formatNat.write 128 = [128, 1] ∧
    formatNat.write 300 = [172, 2] ∧
    formatNat.read [0, 7] = some (0, [7]) ∧
    formatNat.read [128, 1, 9] = some (128, [9]) ∧
    formatNat.read [172, 2] = some (300, []) ∧
    -- Non-canonical encodings with trailing zero 7-bit groups must be rejected.
    formatNat.read [128, 0] = none ∧
    formatNat.read [129, 0] = none ∧
    formatNat.read [128, 128, 0] = none ∧
    formatNat.read [256] = none := by
  decide +kernel

theorem formatSeq_roundtrip_and_reject :
    (formatSeqSized (formatFin 17) 3).write [1, 5, 16] = [1, 5, 16] ∧
    (formatSeqSized (formatFin 17) 3).read [1, 5, 16, 99] = some ([1, 5, 16], [99]) ∧
    (formatSeqSized (formatFin 17) 3).read [1, 5] = none ∧
    (formatSeqSized (formatFin 17) 3).read [1, 5, 17] = none ∧
    (formatSeqUnsized formatBool).write [true, false, true] = [3, 1, 0, 1] ∧
    (formatSeqUnsized formatBool).read [3, 1, 0, 1, 88] = some ([true, false, true], [88]) ∧
    (formatSeqUnsized formatBool).read [3, 1, 0] = none ∧
    (formatSeqUnsized formatBool).read [128, 0] = none := by
  decide +kernel

/-! ## Toy Schnorr vocabulary and concrete model (`q = 11`, `p = 23`, generator `g = 2`) -/

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

/-- Simple deterministic polynomial sponge state update for testing Fiat-Shamir binding. -/
def mixBytes (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: rest => mixBytes ((acc * 257 + b + 31) % 65521) rest

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

/-- Deterministic per-attempt sample function `[attempt, siteKey] → [scalar]`. -/
def fnSamples : Definition deployVocab :=
  .fn ⟨109⟩ [.nat, .nat] [dScalar] false none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 1],
    .op ⟨2⟩ [3] (.row .natToScalar) [2]] [3])

def toySuite : ModuleRef where
  members := [
    (SuiteSlot.start, ⟨100⟩),
    (SuiteSlot.absorb, ⟨101⟩),
    (SuiteSlot.encode, ⟨102⟩),
    (SuiteSlot.encode, ⟨103⟩),
    (SuiteSlot.derive, ⟨104⟩)
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

/-- Protocol 1 (`key = 200`): Standard Schnorr identification protocol. -/
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

/-- Protocol 2 (`key = 201`): Multi-draw Schnorr (two consecutive verifier draws `c1`, `c2`
with no intervening prover message; verifies transcript state advances on squeeze). -/
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
      -- Also check the two consecutive challenges are distinct (proves squeeze advances state).
      .op ⟨324⟩ [15] (.compute [1] (.row .sameScalar)) [5, 6],
      .op ⟨325⟩ [16] (.compute [1] (.owned .boolNot [] [])) [15],
      .guard ⟨326⟩ [1] 16 .reject] [])

/-- Protocol 3 (`key = 202`): Retried Schnorr inside `.attempt ⟨409⟩ [0]`.
On attempt 0 (`fnSamples (0, 410) = 410 % 11 = 3`), the prover sends `A = 2^3 % 23 = 8`, derives `c`,
and then aborts because `r = 3` is forbidden — exercising rollback of BOTH the transcript state and
the proof buffer via `restoreAgain` while `attemptNumAgain` advances `samples` to attempt 1 (`r = 4`). -/
def retrySchnorrProto : Definition deployVocab :=
  .protocol ⟨202⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .attempt ⟨409⟩ [0] [] (.mk [50] [
        .op ⟨410⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
        .op ⟨411⟩ [3] (.compute [0] (.row .base)) [2],
        .op ⟨412⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
        .op ⟨413⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
        -- Abort on attempt 0's nonce `3` AFTER sending `A` and deriving `c` to verify full rollback.
        .op ⟨414⟩ [20] (.compute [0] (.literal dScalar [3])) [],
        .op ⟨415⟩ [21] (.compute [0] (.row .sameScalar)) [2, 20],
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

def deployTestProgram : NamedProgram deployVocab where
  definitions := suiteAndLayoutDefs ++ [schnorrProto, multiDrawProto, retrySchnorrProto]

/-- Kernel-verified admission of the entire test suite (functions + 3 protocols). -/
def admittedSuite : Admitted deployVocab :=
  (admit deployTestProgram noAssociation).toOption.get (by decide +kernel)

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
  { schnorrDecl with construction := .derived toySuite (some [115, 99, 104, 110, 111, 114, 114]) }

def schnorrAppCtxDecl : Declaration :=
  { schnorrDecl with application := [42, 7] }

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

def schnorrDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrDecl).toOption.get (by decide +kernel)

def schnorrTaggedDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrTaggedDecl).toOption.get (by decide +kernel)

def schnorrAppCtxDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrAppCtxDecl).toOption.get (by decide +kernel)

def schnorrCompactDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrCompactDecl).toOption.get (by decide +kernel)

def multiDrawDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite multiDrawDecl).toOption.get (by decide +kernel)

def retrySchnorrDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite retrySchnorrDecl).toOption.get (by decide +kernel)

def idealServiceKey : Key := ⟨999⟩

def schnorrIdealDeployed : Deployed deployVocab :=
  (deployIdeal deployEncoder idealServiceKey admittedSuite schnorrDecl).toOption.get (by decide +kernel)

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
        (fixedNonceSource nonce) 256).bind extractProofBytes
  else none

/-- Run verifier on `(d, statement, proof)` using official `Core.execute`. -/
def runVerify (d : Deployed deployVocab) (statement : Nat) (proof : List Nat) : Bool :=
  match schnorrInputs d.entry.ins 0 statement, packProofBytes proof (Stack.Takes (d.stack 1)) with
  | some ins, some taken =>
      (verify execute d deployModel 1 (hideAll deployModel 1 ins) taken
        (fixedNonceSource 0) 256).isSome
  | _, _ => false

/-- Run prover via `Core.specialize` and compare its exact proof bytes against `d.run`. -/
def runProveSpecialized (d : Deployed deployVocab) (witness statement nonce : Nat) :
    Option (List Nat) :=
  if hEmpty : Stack.Takes (d.stack 0) = [] then
    (schnorrInputs d.entry.ins witness statement).bind fun ins =>
      let cr := specialize d 0
      let p := cr.denote deployModel (Defs.fnTable deployModel d.admitted.program.defs)
        (hideAll deployModel 0 ins) (cast (congrArg (HList deployModel.Val) hEmpty.symm) .nil)
      match (runProcess deployModel (fixedNonceSource nonce) 0 p 256).1 with
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
      match (runProcess deployModel (fixedNonceSource 0) 1 p 256).1 with
      | .ended (.returned _) => true
      | _ => false
  | _, _ => false

/-! ## Test 1: Deployment roles, layer stacks, and identity binding -/

theorem schnorr_roles_and_distinct_identities :
    schnorrDeployed.roles = some (0, 1) ∧
    (schnorrDeployed.stack 0).map (·.line) = [.construction, .layout] ∧
    (schnorrDeployed.stack 1).map (·.line) = [.construction, .layout] ∧
    (retrySchnorrDeployed.stack 0).map (·.line) = [.samples, .construction, .layout] ∧
    (retrySchnorrDeployed.stack 1).map (·.line) = [.construction, .layout] ∧
    deployedIdentity deployEncoder schnorrDeployed ≠
      deployedIdentity deployEncoder schnorrTaggedDeployed ∧
    deployedIdentity deployEncoder schnorrDeployed ≠
      deployedIdentity deployEncoder schnorrAppCtxDeployed ∧
    deployedIdentity deployEncoder schnorrDeployed ≠
      deployedIdentity deployEncoder schnorrCompactDeployed := by
  decide +kernel

/-! ## Test 2: Standard Schnorr prove, verify, specialization agreement, and negative controls -/

def checkSchnorrHonestAndSpecialized : Bool :=
  match runProve schnorrDeployed 7 13 5, runProveSpecialized schnorrDeployed 7 13 5 with
  | some p1, some p2 =>
      decide (p1 = p2) &&
      decide (p1.length = 2) &&
      p1.all (fun b => decide (b < 256)) &&
      runVerify schnorrDeployed 13 p1 &&
      runVerifySpecialized schnorrDeployed 13 p1
  | _, _ => false

theorem schnorr_honest_and_specialized : checkSchnorrHonestAndSpecialized = true := by
  decide +kernel

/-- All 6 verifier negative controls: wrong statement, mutated response byte, truncated proof,
trailing garbage byte, out-of-range scalar byte (`11`), and dishonest witness (`w = 6`) reject. -/
def checkSchnorrNegativeControls : Bool :=
  match runProve schnorrDeployed 7 13 5, runProve schnorrDeployed 6 13 5 with
  | some goodProof, some badWitnessProof =>
      !runVerify schnorrDeployed 12 goodProof &&
      !runVerify schnorrDeployed 13 [goodProof.getD 0 0, (goodProof.getD 1 0 + 1) % 11] &&
      !runVerify schnorrDeployed 13 (goodProof.take 1) &&
      !runVerify schnorrDeployed 13 (goodProof ++ [0]) &&
      !runVerify schnorrDeployed 13 [goodProof.getD 0 0, 11] &&
      !runVerify schnorrDeployed 13 badWitnessProof &&
      !runVerifySpecialized schnorrDeployed 12 goodProof &&
      !runVerifySpecialized schnorrDeployed 13 (goodProof ++ [0])
  | _, _ => false

theorem schnorr_negative_controls : checkSchnorrNegativeControls = true := by
  decide +kernel

/-- Weak Fiat-Shamir prevention: two valid statements (`Y = 13` with `w = 7`, `Y = 2` with `w = 1`)
with the same nonce `r = 5` (same commitment byte `A = 2^5 % 23 = 9`) produce distinct proofs and
do not cross-verify, and proofs from different `sessionTag` / `application` deployments do not
cross-verify either. -/
def checkWeakFsAndDomainSeparation : Bool :=
  match runProve schnorrDeployed 7 13 5, runProve schnorrDeployed 1 2 5,
      runProve schnorrTaggedDeployed 7 13 5, runProve schnorrAppCtxDeployed 7 13 5 with
  | some p1, some p2, some pTag, some pApp =>
      decide (p1.getD 0 0 = p2.getD 0 0) &&
      decide (p1 ≠ p2) &&
      decide (p1 ≠ pTag) &&
      decide (p1 ≠ pApp) &&
      runVerify schnorrDeployed 13 p1 &&
      runVerify schnorrDeployed 2 p2 &&
      !runVerify schnorrDeployed 13 p2 &&
      !runVerify schnorrDeployed 2 p1 &&
      runVerify schnorrTaggedDeployed 13 pTag &&
      !runVerify schnorrDeployed 13 pTag &&
      runVerify schnorrAppCtxDeployed 13 pApp &&
      !runVerify schnorrDeployed 13 pApp
  | _, _, _, _ => false

theorem schnorr_weak_fs_and_domain_separation : checkWeakFsAndDomainSeparation = true := by
  decide +kernel

/-! ## Test 3: Multi-draw protocol (transcript state advances across consecutive draws) -/

def checkMultiDraw : Bool :=
  match runProve multiDrawDeployed 7 13 4, runProveSpecialized multiDrawDeployed 7 13 4,
      runProve multiDrawDeployed 7 13 6, runProveSpecialized multiDrawDeployed 7 13 6 with
  | some p1, some p2, some q1, some q2 =>
      decide (p1 = p2) &&
      decide (q1 = q2) &&
      decide (p1 ≠ q1) &&
      decide (p1.length = 2) &&
      runVerify multiDrawDeployed 13 p1 &&
      runVerifySpecialized multiDrawDeployed 13 p1 &&
      !runVerify multiDrawDeployed 12 p1 &&
      runVerify multiDrawDeployed 13 q1 &&
      runVerifySpecialized multiDrawDeployed 13 q1 &&
      !runVerify multiDrawDeployed 12 q1
  | _, _, _, _ => false

theorem multiDraw_honest_and_specialized : checkMultiDraw = true := by
  decide +kernel

/-! ## Test 4: Compact layout (`carry` challenge + `recover` commitment `A = g^z * Y^(-c)`) -/

def checkCompactLayout : Bool :=
  match runProve schnorrCompactDeployed 7 13 5,
      runProveSpecialized schnorrCompactDeployed 7 13 5 with
  | some p1, some p2 =>
      decide (p1 = p2) &&
      decide (p1.length = 2) &&
      runVerify schnorrCompactDeployed 13 p1 &&
      runVerifySpecialized schnorrCompactDeployed 13 p1 &&
      -- Tampered carried challenge must reject (layout equality guard).
      !runVerify schnorrCompactDeployed 13 [(p1.getD 0 0 + 1) % 11, p1.getD 1 0] &&
      -- Tampered response must reject.
      !runVerify schnorrCompactDeployed 13 [p1.getD 0 0, (p1.getD 1 0 + 1) % 11] &&
      -- Out-of-range carried scalar or trailing byte must reject.
      !runVerify schnorrCompactDeployed 13 [11, p1.getD 1 0] &&
      !runVerify schnorrCompactDeployed 13 (p1 ++ [0]) &&
      !runVerify schnorrCompactDeployed 12 p1
  | _, _ => false

theorem schnorr_compact_layout : checkCompactLayout = true := by
  decide +kernel

/-! ## Test 5: Retried attempt (`retry` + `samples` + `restoreAgain` + `specialize`) -/

theorem retrySchnorr_wellNested : retrySchnorrDeployed.WellNestedRetry := by
  have hRetry : retrySchnorrDeployed.retry = some (4, ⟨[], ⟨409⟩⟩) := by decide +kernel
  have hNo : Shape.noNestedAttempt ⟨[], ⟨409⟩⟩ [] retrySchnorrDeployed.entry.shape = true := by
    decide +kernel
  simpa [Deployed.WellNestedRetry, hRetry] using hNo

def checkRetrySchnorr : Bool :=
  match runProve retrySchnorrDeployed 7 13 0,
      runProveSpecialized retrySchnorrDeployed 7 13 0 with
  | some p1, some p2 =>
      decide (p1 = p2) &&
      -- Attempt 0 had `r = 3` (aborted after writing `A = 8`), rollback restored empty buffer,
      -- attempt 1 had `r = 4`, so final proof has length 2 and commitment byte `2^4 % 23 = 16`.
      decide (p1.length = 2) &&
      decide (p1.getD 0 0 = 16) &&
      runVerify retrySchnorrDeployed 13 p1 &&
      runVerifySpecialized retrySchnorrDeployed 13 p1 &&
      !runVerify retrySchnorrDeployed 12 p1
  | _, _ => false

theorem retry_schnorr_rollback_and_specialized : checkRetrySchnorr = true := by
  decide +kernel

/-! ## Test 6: Ideal RO deployment (`deployIdeal`) -/

/-- Run an ideal-RO verifier process by answering every `.own (.request idealServiceKey)` query
with the matching concrete `squeezeScalar` output `(mixBytes st (0xFF :: lbl)) % 11`. -/
def runIdealOracle {A : Type} :
    Process (RSig deployModel) Stop A → Nat → Option A × Nat
  | .done a, _ => (some a, 0)
  | .halt _, _ => (none, 0)
  | .call (.own (.request k) [] _ [.tuple (.cons .nat (.cons (.seq (.fin 256) none) .nil))]
        (.cons (st, lbl, ()) .nil) (.nominal .scalar)) next, n + 1 =>
      if k = idealServiceKey then
        let c := (mixBytes st (0xFF :: lbl)) % 11
        let (res, q) := runIdealOracle (next c) n
        (res, q + 1)
      else (none, 0)
  | .call _ _, _ => (none, 0)

def checkIdealVerifier : Bool :=
  match runProve schnorrDeployed 7 13 5,
      schnorrInputs schnorrIdealDeployed.entry.ins 0 13,
      packProofBytes (runProve schnorrDeployed 7 13 5 |>.getD [])
        (Stack.Takes (schnorrIdealDeployed.stack 1)) with
  | some goodProof, some ins, some taken =>
      let pGood := schnorrIdealDeployed.run deployModel 1 (hideAll deployModel 1 ins) taken
      let (resGood, queriesGood) := runIdealOracle pGood 64
      match packProofBytes [goodProof.getD 0 0, (goodProof.getD 1 0 + 1) % 11]
          (Stack.Takes (schnorrIdealDeployed.stack 1)) with
      | some badTaken =>
          let pBad := schnorrIdealDeployed.run deployModel 1 (hideAll deployModel 1 ins) badTaken
          let (resBad, _) := runIdealOracle pBad 64
          resGood.isSome && decide (queriesGood = 1) && resBad.isNone
      | none => false
  | _, _, _ => false

theorem schnorr_ideal_ro_verifier : checkIdealVerifier = true := by
  decide +kernel

/-! ## Test 7: Interactive two-role scheduler (`runInteractive`) -/

def checkInteractiveAccepts : Bool :=
  match schnorrInputs schnorrDeployed.entry.ins 7 13 with
  | some ins =>
      let pProg := roleMeaning deployModel schnorrDeployed.admitted.program
        schnorrDeployed.callee 0 [] (hideAll deployModel 0 ins)
      let vProg := roleMeaning deployModel schnorrDeployed.admitted.program
        schnorrDeployed.callee 1 [] (hideAll deployModel 1 ins)
      match runInteractive deployModel (fixedNonceSource 5) 0 1 pProg vProg 32 with
      | (.ended (.returned _), .ended (.returned _), _) => true
      | _ => false
  | none => false

theorem schnorr_interactive_accepts : checkInteractiveAccepts = true := by
  decide +kernel

end Zkc.Core.Tests.Deployment
