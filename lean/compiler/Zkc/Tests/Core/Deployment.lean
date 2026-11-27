import Zkc.Core.Format.Canonical
import Zkc.Core.Scheme.Deploy
import Zkc.Core.Scheme.Theorems
import Zkc.Core.Run.Execute
import Zkc.Core.Run.Specialize
import Zkc.Core.Admission.Admit
import Zkc.Core.Admission.Theorems
import Zkc.Tests.Core.Consumers

/-!
End-to-end kernel-checked tests, concrete witness instantiations, and negative controls for:
- Canonical wire formats (`Zkc.Core.Format.Canonical`).
- Official `Core.deploy` building checked `Core.Layer` stacks (`[samples?, construction, layout]`)
  from admitted suite, layout, recovery, and sampling functions passed via `ModuleRef`, across
  `.derived`, `.authored`, and `.interactive` schemes.
- Official `Core.deployIdeal` replacing verifier concrete draws with ideal random-oracle service
  requests and linking directly to the bare verifier role program (`BareIdealReturn`).
- Concrete witness instantiations of `Statements.*`, `canonicalFormat_lawful`, `deploy_complete`,
  `deployIdeal_link`, `idealPath_msgStep_injective`, and `execute_runs` on `deployModel`.
- Verified Core-level handler specialization (`Core.specialize` + `specialize_sound`) matching
  `d.run` identically across standard, multi-draw, compact, branching, subprotocol-apply, looped,
  authored, retried, and ideal random-oracle deployments.
- Reference execution (`execute`, `prove`, `verify`, `runInteractive`, `Process.answerService`) and
  fail-closed attack regressions asserting exact `Rule` identifiers.
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

def deployTestProgram : NamedProgram deployVocab where
  definitions := suiteAndLayoutDefs ++ [
    schnorrProto, multiDrawProto, retrySchnorrProto, branchingProto,
    authoredSchnorrProto, subRoundProto, doubleApplyProto, loopSchnorrProto,
    verifierAttemptProto, abortOutsideTargetProto
  ]

private theorem except_toOption_get_ok {E A : Type} (x : Except E A) (h : x.toOption.isSome) :
    x = .ok (x.toOption.get h) := by
  cases x with
  | error _ => cases h
  | ok a => rfl

private theorem admittedSuite_isSome :
    (admit deployTestProgram noAssociation).toOption.isSome = true := by
  decide +kernel

/-- Kernel-verified admission of the entire test suite (functions + protocols). -/
def admittedSuite : Admitted deployVocab :=
  (admit deployTestProgram noAssociation).toOption.get admittedSuite_isSome

private theorem admittedSuite_ok :
    admit deployTestProgram noAssociation = .ok admittedSuite :=
  except_toOption_get_ok _ admittedSuite_isSome

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

private theorem schnorr_deploy_isSome :
    (deploy deployEncoder admittedSuite schnorrDecl).toOption.isSome = true := by
  decide +kernel

def schnorrDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedSuite schnorrDecl).toOption.get schnorr_deploy_isSome

private theorem schnorr_deploy_ok :
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

private theorem retrySchnorr_deploy_ok :
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

def idealServiceKey : Key := ⟨999⟩

private theorem schnorrIdeal_deploy_isSome :
    (deployIdeal deployEncoder idealServiceKey admittedSuite schnorrDecl).toOption.isSome = true := by
  decide +kernel

def schnorrIdealDeployed : Deployed deployVocab :=
  (deployIdeal deployEncoder idealServiceKey admittedSuite schnorrDecl).toOption.get
    schnorrIdeal_deploy_isSome

private theorem schnorrIdeal_deploy_ok :
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

/-! ## Deployment roles, layer stacks, and identity binding -/

theorem schnorr_roles_and_distinct_identities :
    schnorrDeployed.roles = some (0, 1) ∧
    interactiveDeployed.roles = none ∧
    (interactiveDeployed.stack 0).isEmpty = true ∧
    (interactiveDeployed.stack 1).isEmpty = true ∧
    authoredDeployed.roles = some (0, 1) ∧
    (authoredDeployed.stack 0).map (·.line) = [.layout] ∧
    (authoredDeployed.stack 1).map (·.line) = [.layout] ∧
    (schnorrDeployed.stack 0).map (·.line) = [.construction, .layout] ∧
    (schnorrDeployed.stack 1).map (·.line) = [.construction, .layout] ∧
    (retrySchnorrDeployed.stack 0).map (·.line) = [.samples, .construction, .layout] ∧
    (retrySchnorrDeployed.stack 1).map (·.line) = [.construction, .layout] ∧
    deployedIdentity deployEncoder schnorrDeployed ≠
      deployedIdentity deployEncoder schnorrTaggedDeployed ∧
    deployedIdentity deployEncoder schnorrTaggedDeployed ≠
      deployedIdentity deployEncoder schnorrTaggedOtherAppDeployed ∧
    deployedIdentity deployEncoder schnorrDeployed ≠
      deployedIdentity deployEncoder schnorrAppCtxDeployed ∧
    deployedIdentity deployEncoder schnorrDeployed ≠
      deployedIdentity deployEncoder schnorrCompactDeployed := by
  decide +kernel

/-! ## Standard Schnorr prove, verify, specialization agreement, and negative controls -/

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

/-- All verifier negative controls: wrong statement, mutated response byte, truncated proof,
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

/-- Weak Fiat–Shamir prevention and session-tag + application binding: two valid statements with
the same nonce produce distinct proofs and do not cross-verify, and changing `application` even
with an explicit `sessionTag` produces distinct proofs that do not cross-verify. -/
def checkWeakFsStmtSep : Bool :=
  match runProve schnorrDeployed 7 13 5, runProve schnorrDeployed 1 2 5 with
  | some p1, some p2 =>
      decide (p1.getD 0 0 = p2.getD 0 0) &&
      decide (p1 ≠ p2) &&
      runVerify schnorrDeployed 13 p1 &&
      runVerify schnorrDeployed 2 p2 &&
      !runVerify schnorrDeployed 13 p2 &&
      !runVerify schnorrDeployed 2 p1
  | _, _ => false

def checkTagSep : Bool :=
  match runProve schnorrDeployed 7 13 5, runProve schnorrTaggedDeployed 7 13 5 with
  | some p1, some pTag =>
      decide (p1 ≠ pTag) &&
      runVerify schnorrTaggedDeployed 13 pTag &&
      !runVerify schnorrDeployed 13 pTag
  | _, _ => false

def checkTagAppSep : Bool :=
  match runProve schnorrTaggedDeployed 7 13 5, runProve schnorrTaggedOtherAppDeployed 7 13 5 with
  | some pTag, some pTagApp =>
      decide (pTag ≠ pTagApp) &&
      runVerify schnorrTaggedOtherAppDeployed 13 pTagApp &&
      !runVerify schnorrTaggedDeployed 13 pTagApp &&
      !runVerify schnorrTaggedOtherAppDeployed 13 pTag
  | _, _ => false

def checkAppCtxSep : Bool :=
  match runProve schnorrDeployed 7 13 5, runProve schnorrAppCtxDeployed 7 13 5 with
  | some p1, some pApp =>
      decide (p1 ≠ pApp) &&
      runVerify schnorrAppCtxDeployed 13 pApp &&
      !runVerify schnorrDeployed 13 pApp
  | _, _ => false

theorem schnorr_weak_fs_and_domain_separation :
    checkWeakFsStmtSep = true ∧
    checkTagSep = true ∧
    checkTagAppSep = true ∧
    checkAppCtxSep = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## Authored, branching (`.choose`), subprotocol (`.apply`), and looped (`.loop`) deployments -/

def checkAuthoredAndBranching : Bool :=
  match runProve authoredDeployed 7 13 5, runProveSpecialized authoredDeployed 7 13 5,
      runProve branchingStreamingDeployed 7 13 5,
      runProveSpecialized branchingStreamingDeployed 7 13 5 with
  | some pa1, some pa2, some pb1, some pb2 =>
      decide (pa1 = pa2) &&
      decide (pa1.length = 2) &&
      runVerify authoredDeployed 13 pa1 &&
      runVerifySpecialized authoredDeployed 13 pa1 &&
      !runVerify authoredDeployed 12 pa1 &&
      !runVerify authoredDeployed 13 (pa1 ++ [0]) &&
      decide (pb1 = pb2) &&
      decide (pb1.length = 2) &&
      runVerify branchingStreamingDeployed 13 pb1 &&
      runVerifySpecialized branchingStreamingDeployed 13 pb1 &&
      !runVerify branchingStreamingDeployed 12 pb1 &&
      !runVerify branchingStreamingDeployed 13 [pb1.getD 0 0, (pb1.getD 1 0 + 1) % 11]
  | _, _, _, _ => false

theorem authored_and_branching_executed : checkAuthoredAndBranching = true := by
  decide +kernel

/-- Exercises `.apply` (two calls to `subRoundProto`), `.loop` (two fixed iterations), and
hardened `samples` derivation across witness/statement, application, subprotocol call paths, and
loop iterations. -/
def checkApplyLoopAndHardenedSamples : Bool :=
  match runProve schnorrSamplesDeployed 7 13 0,
      runProve schnorrSamplesDeployed 1 2 0,
      runProve schnorrSamplesAppDeployed 7 13 0,
      runProve doubleApplyDeployed 7 13 5,
      runProveSpecialized doubleApplyDeployed 7 13 5,
      runProve doubleApplySamplesDeployed 7 13 0,
      runProveSpecialized doubleApplySamplesDeployed 7 13 0,
      runProve loopSchnorrDeployed 7 13 5,
      runProveSpecialized loopSchnorrDeployed 7 13 5,
      runProve loopSchnorrSamplesDeployed 7 13 0,
      runProveSpecialized loopSchnorrSamplesDeployed 7 13 0 with
  | some ps1, some ps2, some psApp,
    some pd1, some pd2, some pds1, some pds2,
    some pl1, some pl2, some pls1, some pls2 =>
      -- Hardened `samples`: distinct witness/statement and distinct `application` yield distinct nonces.
      decide (ps1.getD 0 0 ≠ ps2.getD 0 0) &&
      decide (ps1.getD 0 0 ≠ psApp.getD 0 0) &&
      runVerify schnorrSamplesDeployed 13 ps1 &&
      runVerify schnorrSamplesDeployed 2 ps2 &&
      runVerify schnorrSamplesAppDeployed 13 psApp &&
      -- Double `.apply` without and with `samples`: two distinct commitment bytes across call sites.
      decide (pd1 = pd2) &&
      decide (pd1.length = 4) &&
      runVerify doubleApplyDeployed 13 pd1 &&
      runVerifySpecialized doubleApplyDeployed 13 pd1 &&
      !runVerify doubleApplyDeployed 12 pd1 &&
      decide (pds1 = pds2) &&
      decide (pds1.length = 4) &&
      decide (pds1.getD 0 0 ≠ pds1.getD 2 0) &&
      runVerify doubleApplySamplesDeployed 13 pds1 &&
      runVerifySpecialized doubleApplySamplesDeployed 13 pds1 &&
      !runVerify doubleApplySamplesDeployed 12 pds1 &&
      -- Looped `.loop` without and with `samples`: two distinct commitment bytes across iterations.
      decide (pl1 = pl2) &&
      decide (pl1.length = 4) &&
      runVerify loopSchnorrDeployed 13 pl1 &&
      runVerifySpecialized loopSchnorrDeployed 13 pl1 &&
      !runVerify loopSchnorrDeployed 12 pl1 &&
      decide (pls1 = pls2) &&
      decide (pls1.length = 4) &&
      decide (pls1.getD 0 0 ≠ pls1.getD 2 0) &&
      runVerify loopSchnorrSamplesDeployed 13 pls1 &&
      runVerifySpecialized loopSchnorrSamplesDeployed 13 pls1 &&
      !runVerify loopSchnorrSamplesDeployed 12 pls1
  | _, _, _, _, _, _, _, _, _, _, _ => false

theorem apply_loop_and_hardened_samples : checkApplyLoopAndHardenedSamples = true := by
  decide +kernel

/-! ## Multi-draw protocol (transcript state advances across consecutive draws) -/

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

/-! ## Compact layout (`carry` challenge + `recover` commitment `A = g^z * Y^(-c)`) -/

def checkCompactLayout : Bool :=
  match runProve schnorrCompactDeployed 7 13 5,
      runProveSpecialized schnorrCompactDeployed 7 13 5 with
  | some p1, some p2 =>
      let c0 := p1.getD 0 0
      let z0 := p1.getD 1 0
      let wrongCh := [(c0 + 1) % 11, (c0 + 2) % 11, (c0 + 3) % 11, (c0 + 4) % 11]
      let wrongResp := [(z0 + 1) % 11, (z0 + 2) % 11, (z0 + 3) % 11, (z0 + 4) % 11]
      let wrongStmts := [1, 2, 3, 4]
      let rejCh := (wrongCh.filter fun c => !runVerify schnorrCompactDeployed 13 [c, z0]).length
      let rejResp := (wrongResp.filter fun z => !runVerify schnorrCompactDeployed 13 [c0, z]).length
      let rejStmts := (wrongStmts.filter fun y => !runVerify schnorrCompactDeployed y p1).length
      decide (p1 = p2) &&
      decide (p1.length = 2) &&
      runVerify schnorrCompactDeployed 13 p1 &&
      runVerifySpecialized schnorrCompactDeployed 13 p1 &&
      !runVerify schnorrCompactDeployed 13 [11, z0] &&
      !runVerify schnorrCompactDeployed 13 (p1 ++ [0]) &&
      !runVerify schnorrCompactDeployed 13 (p1.take 1) &&
      decide (rejCh ≥ 3) &&
      decide (rejResp ≥ 3) &&
      decide (rejStmts ≥ 3)
  | _, _ => false

theorem schnorr_compact_layout : checkCompactLayout = true := by
  decide +kernel

/-! ## Retried attempt (`retry` + `samples` + `restoreAgain` + `specialize_deploy_sound`) -/

theorem retrySchnorr_wellNested : retrySchnorrDeployed.WellNestedRetry :=
  deploy_wellNestedRetry deployEncoder admittedSuite retrySchnorrDecl retrySchnorrDeployed
    retrySchnorr_deploy_ok

theorem retrySchnorr_specialize_sound (r : Role)
    (ins : HList (RV deployModel r) retrySchnorrDeployed.entry.ins)
    (taken : HList deployModel.Val (Stack.Takes (retrySchnorrDeployed.stack r))) :
    (specialize retrySchnorrDeployed r).denote deployModel
        (Defs.fnTable deployModel retrySchnorrDeployed.admitted.program.defs) ins taken =
      retrySchnorrDeployed.run deployModel r ins taken :=
  specialize_deploy_sound deployModel deployEncoder admittedSuite retrySchnorrDecl
    retrySchnorrDeployed retrySchnorr_deploy_ok r ins taken

theorem schnorrIdeal_specialize_sound (r : Role)
    (ins : HList (RV deployModel r) schnorrIdealDeployed.entry.ins)
    (taken : HList deployModel.Val (Stack.Takes (schnorrIdealDeployed.stack r))) :
    (specialize schnorrIdealDeployed r).denote deployModel
        (Defs.fnTable deployModel schnorrIdealDeployed.admitted.program.defs) ins taken =
      schnorrIdealDeployed.run deployModel r ins taken :=
  specialize_deployIdeal_sound deployModel deployEncoder idealServiceKey admittedSuite schnorrDecl
    schnorrIdealDeployed schnorrIdeal_deploy_ok r ins taken

def checkRetrySchnorr : Bool :=
  match resolveSessionBytes deployEncoder admittedSuite retrySchnorrDecl none,
      runProve retrySchnorrDeployed 7 13 0,
      runProveSpecialized retrySchnorrDeployed 7 13 0 with
  | .ok ⟨sessBytes, _⟩, some p1, some p2 =>
      let baseHash := mixBytes (mixBytes 7 sessBytes + 13) (encodeSite ⟨[], ⟨410⟩⟩)
      let r0 := baseHash % 11
      let r1 := (baseHash + 17 + 1) % 11
      let commit0 := powMod 2 r0 23
      let commit1 := powMod 2 r1 23
      decide (p1 = p2) &&
      decide (p1.length = 2) &&
      -- Attempt 0 aborted after writing `commit0`; rollback cleared the buffer and attempt 1
      -- advanced `(att := 1, seq := 1)` to produce `commit1 ≠ commit0`.
      decide (commit0 ≠ commit1) &&
      decide (p1.getD 0 0 = commit1) &&
      runVerify retrySchnorrDeployed 13 p1 &&
      runVerifySpecialized retrySchnorrDeployed 13 p1 &&
      !runVerify retrySchnorrDeployed 12 p1
  | _, _, _ => false

theorem retry_schnorr_rollback_and_specialized : checkRetrySchnorr = true := by
  decide +kernel

/-! ## Pure collision-free ideal random-oracle deployment (`deployIdeal`) -/

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

/-- Exercises both `runIdealOracle` (query inspection) and `Process.answerService` directly with
`LayerBuild.IdealRO.asOracle deployModel schnorrIdealRO`. -/
def checkIdealVerifierAndAnswerService : Bool :=
  match runProve schnorrDeployed 7 13 5,
      schnorrInputs schnorrIdealDeployed.entry.ins 0 13,
      packProofBytes (runProve schnorrDeployed 7 13 5 |>.getD [])
        (Stack.Takes (schnorrIdealDeployed.stack 1)) with
  | some goodProof, some ins, some taken =>
      let pGood := schnorrIdealDeployed.run deployModel 1 (hideAll deployModel 1 ins) taken
      let (resGood, queriesGood) := runIdealOracle pGood 64
      let pAnswered := Process.answerService idealServiceKey
        (LayerBuild.IdealRO.asOracle deployModel schnorrIdealRO) pGood
      let ansGood := match (runProcess deployModel (fixedNonceSource 0) 1 pAnswered 128).1 with
        | .ended (.returned _) => true
        | _ => false
      match packProofBytes [goodProof.getD 0 0, (goodProof.getD 1 0 + 1) % 11]
          (Stack.Takes (schnorrIdealDeployed.stack 1)) with
      | some badTaken =>
          let pBad := schnorrIdealDeployed.run deployModel 1 (hideAll deployModel 1 ins) badTaken
          let (resBad, _) := runIdealOracle pBad 64
          let pBadAnswered := Process.answerService idealServiceKey
            (LayerBuild.IdealRO.asOracle deployModel schnorrIdealRO) pBad
          let ansBad := match (runProcess deployModel (fixedNonceSource 0) 1 pBadAnswered 128).1 with
            | .ended (.returned _) => true
            | _ => false
          resGood.isSome && decide (queriesGood.length = 1) && resBad.isNone &&
          ansGood && !ansBad
      | none => false
  | _, _, _ => false

theorem schnorr_ideal_verifier_and_answerService :
    checkIdealVerifierAndAnswerService = true := by
  decide +kernel

/-- Multi-draw, double-`.apply`, and `.loop` ideal random-oracle linkage: consecutive draws across
straight-line, subprotocol call paths, and loop iterations query strictly distinct pure
`(metaLog, dataLog)` paths without calling any concrete hash/sponge function. -/
def checkMultiApplyLoopIdealVerifier : Bool :=
  match runProve multiDrawDeployed 7 13 4,
      schnorrInputs multiDrawIdealDeployed.entry.ins 0 13,
      packProofBytes (runProve multiDrawDeployed 7 13 4 |>.getD [])
        (Stack.Takes (multiDrawIdealDeployed.stack 1)),
      runProve doubleApplyDeployed 7 13 5,
      schnorrInputs doubleApplyIdealDeployed.entry.ins 0 13,
      packProofBytes (runProve doubleApplyDeployed 7 13 5 |>.getD [])
        (Stack.Takes (doubleApplyIdealDeployed.stack 1)),
      runProve loopSchnorrDeployed 7 13 5,
      schnorrInputs loopSchnorrIdealDeployed.entry.ins 0 13,
      packProofBytes (runProve loopSchnorrDeployed 7 13 5 |>.getD [])
        (Stack.Takes (loopSchnorrIdealDeployed.stack 1)) with
  | some goodMulti, some insMulti, some takenMulti,
    some _goodApp, some insApp, some takenApp,
    some _goodLoop, some insLoop, some takenLoop =>
      let (resMulti, qsMulti) := runIdealOracle
        (multiDrawIdealDeployed.run deployModel 1 (hideAll deployModel 1 insMulti) takenMulti) 64
      let (resApp, qsApp) := runIdealOracle
        (doubleApplyIdealDeployed.run deployModel 1 (hideAll deployModel 1 insApp) takenApp) 64
      let (resLoop, qsLoop) := runIdealOracle
        (loopSchnorrIdealDeployed.run deployModel 1 (hideAll deployModel 1 insLoop) takenLoop) 64
      match packProofBytes [goodMulti.getD 0 0, (goodMulti.getD 1 0 + 1) % 11]
          (Stack.Takes (multiDrawIdealDeployed.stack 1)) with
      | some badTaken =>
          let (resBad, _) := runIdealOracle
            (multiDrawIdealDeployed.run deployModel 1 (hideAll deployModel 1 insMulti) badTaken) 64
          resMulti.isSome && decide (qsMulti.length = 2) && decide (qsMulti[0]? ≠ qsMulti[1]?) &&
          resBad.isNone &&
          resApp.isSome && decide (qsApp.length = 2) && decide (qsApp[0]? ≠ qsApp[1]?) &&
          resLoop.isSome && decide (qsLoop.length = 2) && decide (qsLoop[0]? ≠ qsLoop[1]?)
      | none => false
  | _, _, _, _, _, _, _, _, _ => false

theorem multiDraw_apply_loop_ideal_verifier : checkMultiApplyLoopIdealVerifier = true := by
  decide +kernel

/-- Ideal-only suite (no `SuiteSlot.start`, `absorb`, or `derive`) deploys cleanly and queries
the random oracle with a well-formed tagged `(metaLog, dataLog)` path. -/
def checkIdealOnlySuiteDeployed : Bool :=
  match schnorrInputs schnorrIdealOnlyDeployed.entry.ins 0 13,
      packProofBytes [9, 0] (Stack.Takes (schnorrIdealOnlyDeployed.stack 1)) with
  | some ins, some taken =>
      let p := schnorrIdealOnlyDeployed.run deployModel 1 (hideAll deployModel 1 ins) taken
      let (_, qs) := runIdealOracle p 64
      decide (qs.length = 1) &&
      match qs with
      | [(metaLog, dataLog, _)] =>
          decide (metaLog.length = 3) && decide (dataLog.length = 2)
      | _ => false
  | _, _ => false

theorem schnorr_ideal_only_suite_no_hash_slots : checkIdealOnlySuiteDeployed = true := by
  decide +kernel

/-! ## Interactive two-role scheduler (`runInteractive`) -/

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

/-! ## Trailing-message absorption elision (Chiesa and Orrù (2025), Construction 4.3) -/

def constructionClauseSites (d : Deployed deployVocab) (r : Role) : List Site :=
  match (d.stack r).find? (fun l => l.line == .construction) with
  | some l => l.clauses.map (·.site.site)
  | none => []

/-- Commitment `A` (`key 12`) and challenge `c` (`key 13`) have construction clauses, while the
trailing response `z` (`key 16`, with no subsequent verifier draw) is elided from absorption on
prover, verifier, and ideal random-oracle verifier alike. -/
theorem schnorr_trailing_message_elision :
    (⟨[], ⟨12⟩⟩ : Site) ∈ constructionClauseSites schnorrDeployed 0 ∧
    (⟨[], ⟨13⟩⟩ : Site) ∈ constructionClauseSites schnorrDeployed 0 ∧
    (⟨[], ⟨16⟩⟩ : Site) ∉ constructionClauseSites schnorrDeployed 0 ∧
    (⟨[], ⟨12⟩⟩ : Site) ∈ constructionClauseSites schnorrDeployed 1 ∧
    (⟨[], ⟨13⟩⟩ : Site) ∈ constructionClauseSites schnorrDeployed 1 ∧
    (⟨[], ⟨16⟩⟩ : Site) ∉ constructionClauseSites schnorrDeployed 1 ∧
    (⟨[], ⟨12⟩⟩ : Site) ∈ constructionClauseSites schnorrIdealDeployed 1 ∧
    (⟨[], ⟨13⟩⟩ : Site) ∈ constructionClauseSites schnorrIdealDeployed 1 ∧
    (⟨[], ⟨16⟩⟩ : Site) ∉ constructionClauseSites schnorrIdealDeployed 1 := by
  decide +kernel

/-! ## Subprotocol call-path domain separation and literal identity injectivity -/

theorem site_label_through_path_separation :
    msgLabel ⟨[⟨1⟩], ⟨5⟩⟩ ≠ msgLabel ⟨[⟨2⟩], ⟨5⟩⟩ ∧
    msgLabel ⟨[], ⟨5⟩⟩ ≠ msgLabel ⟨[⟨1⟩], ⟨5⟩⟩ ∧
    drawLabel ⟨[⟨1⟩], ⟨5⟩⟩ ≠ drawLabel ⟨[⟨2⟩], ⟨5⟩⟩ ∧
    msgLabel ⟨[⟨1⟩], ⟨5⟩⟩ ≠ drawLabel ⟨[⟨1⟩], ⟨5⟩⟩ := by
  decide +kernel

theorem deployed_identity_determines_declaration (d₁ d₂ : Deployed deployVocab)
    (h : deployedIdentity deployEncoder d₁ = deployedIdentity deployEncoder d₂) :
    d₁.declaration = d₂.declaration :=
  (deployedIdentity_injective deployEncoder deployEncoder_injective d₁ d₂ h).1

/-! ## Concrete witness instantiations of `Statements.*` and core theorems -/

/-- Concrete `Functions deployVocab` record instantiating all proved Core statement theorems. -/
def cDeploy : Functions deployVocab where
  elaborate := elaborateProgram
  eraseRole := fun {_} _ {_} {_} _ => .mk [] [] []
  format := canonicalFormat
  admit := admit
  check := check
  deploy := deploy deployEncoder
  identity := deployedIdentity deployEncoder
  execute := execute
  schedule := fun _ _ _ _ _ _ _ => ([], fun _ => .limit)

theorem deploy_statements_instantiated :
    Statements.formats cDeploy ∧
    Statements.identityReads cDeploy ∧
    Statements.deployKeeps cDeploy ∧
    Statements.deployFindsRoles cDeploy ∧
    Statements.deployMatches cDeploy ∧
    Statements.deployScoped cDeploy ∧
    Statements.deployFresh cDeploy ∧
    Statements.deployedSafe cDeploy ∧
    Statements.deployCoverage cDeploy ∧
    Statements.completeStreaming cDeploy ∧
    Statements.idealLink deployEncoder ∧
    Statements.executorRuns cDeploy :=
  ⟨canonicalFormat_formats cDeploy rfl,
   deployedIdentity_identityReads deployEncoder cDeploy rfl,
   statements_deployKeeps deployEncoder cDeploy rfl,
   statements_deployFindsRoles deployEncoder cDeploy rfl,
   statements_deployMatches deployEncoder cDeploy rfl,
   statements_deployScoped deployEncoder cDeploy rfl,
   statements_deployFresh deployEncoder cDeploy rfl,
   statements_deployedSafe deployEncoder cDeploy rfl rfl,
   statements_deployCoverage deployEncoder cDeploy rfl,
   statements_completeStreaming deployEncoder cDeploy rfl rfl,
   statements_idealLink deployEncoder,
   execute_runs cDeploy rfl⟩

/-- Direct concrete witness of `canonicalFormat_lawful` on `(scalar, point)` in `deployModel`. -/
theorem deployModel_canonicalFormat_witness :
    (canonicalFormat deployModel deployCodecs
      (.tuple (.cons dScalar (.cons dPoint .nil)))).Lawful
      (deployModel.Valid (.tuple (.cons dScalar (.cons dPoint .nil)))) :=
  canonicalFormat_lawful deployModel deployCodecs (.tuple (.cons dScalar (.cons dPoint .nil)))

-- Explicit typed Schnorr + suite + layout program for fast kernel-checked witness proofs
-- (connected to `admit` via `admitsWhatWasGiven` + `elaborateProgram_erase` so `whnf` never
-- unfolds `admit`).

local macro "wvar " name:term:max : term => `(⟨$name, rfl⟩)

private def wFnStart {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dBytes]) [.nat] :=
  .op ⟨1⟩ (.literal .nat [1] rfl) .nil (.cons 1 .nil) <|
  .op ⟨2⟩ (.row DeployRow.mix _ rfl) (.cons (wvar 1) (.cons (wvar 0) .nil)) (.cons 2 .nil) <|
  .ret (.cons (wvar 2) .nil)

private def wFnAbsorb {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [.nat, dBytes, dBytes]) [.nat] :=
  .op ⟨1⟩ (.row DeployRow.mix _ rfl) (.cons (wvar 0) (.cons (wvar 1) .nil)) (.cons 3 .nil) <|
  .op ⟨2⟩ (.row DeployRow.mix _ rfl) (.cons (wvar 3) (.cons (wvar 2) .nil)) (.cons 4 .nil) <|
  .ret (.cons (wvar 4) .nil)

private def wFnEncodeScalar {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dScalar]) [dBytes] :=
  .op ⟨1⟩ (.row DeployRow.scalarToByte _ rfl) (.cons (wvar 0) .nil) (.cons 1 .nil) <|
  .op ⟨2⟩ (.owned (.seqFill dByte 1 rfl)) (.cons (wvar 1) .nil) (.cons 2 .nil) <|
  .op ⟨3⟩ (.owned (.seqUnsized dByte 1)) (.cons (wvar 2) .nil) (.cons 3 .nil) <|
  .ret (.cons (wvar 3) .nil)

private def wFnEncodePoint {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dPoint]) [dBytes] :=
  .op ⟨1⟩ (.row DeployRow.pointToByte _ rfl) (.cons (wvar 0) .nil) (.cons 1 .nil) <|
  .op ⟨2⟩ (.owned (.seqFill dByte 1 rfl)) (.cons (wvar 1) .nil) (.cons 2 .nil) <|
  .op ⟨3⟩ (.owned (.seqUnsized dByte 1)) (.cons (wvar 2) .nil) (.cons 3 .nil) <|
  .ret (.cons (wvar 3) .nil)

private def wFnDeriveScalar {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [.nat, dBytes]) [dScalar, .nat] :=
  .op ⟨1⟩ (.row DeployRow.squeezeScalar _ rfl) (.cons (wvar 0) (.cons (wvar 1) .nil))
    (.cons 2 (.cons 3 .nil)) <|
  .ret (.cons (wvar 2) (.cons (wvar 3) .nil))

private def wFnReadScalar {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dBytes, .nat]) [dScalar, .nat] :=
  .op ⟨1⟩ (.owned (.seqLength dByte none rfl)) (.cons (wvar 0) .nil) (.cons 2 .nil) <|
  .op ⟨2⟩ (.owned .natLess) (.cons (wvar 1) (.cons (wvar 2) .nil)) (.cons 3 .nil) <|
  .guard ⟨3⟩ () (wvar 3) rfl .reject <|
  .op ⟨4⟩ (.owned (.seqAt dByte none rfl)) (.cons (wvar 0) (.cons (wvar 1) .nil)) (.cons 4 .nil) <|
  .op ⟨5⟩ (.owned (.finToNat 256)) (.cons (wvar 4) .nil) (.cons 5 .nil) <|
  .op ⟨6⟩ (.literal .nat [11] rfl) .nil (.cons 6 .nil) <|
  .op ⟨7⟩ (.owned .natLess) (.cons (wvar 5) (.cons (wvar 6) .nil)) (.cons 7 .nil) <|
  .guard ⟨8⟩ () (wvar 7) rfl .reject <|
  .op ⟨9⟩ (.row DeployRow.byteToScalar _ rfl) (.cons (wvar 4) .nil) (.cons 8 .nil) <|
  .op ⟨10⟩ (.literal .nat [1] rfl) .nil (.cons 9 .nil) <|
  .op ⟨11⟩ (.owned .natAdd) (.cons (wvar 1) (.cons (wvar 9) .nil)) (.cons 10 .nil) <|
  .ret (.cons (wvar 8) (.cons (wvar 10) .nil))

private def wFnReadPoint {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dBytes, .nat]) [dPoint, .nat] :=
  .op ⟨1⟩ (.owned (.seqLength dByte none rfl)) (.cons (wvar 0) .nil) (.cons 2 .nil) <|
  .op ⟨2⟩ (.owned .natLess) (.cons (wvar 1) (.cons (wvar 2) .nil)) (.cons 3 .nil) <|
  .guard ⟨3⟩ () (wvar 3) rfl .reject <|
  .op ⟨4⟩ (.owned (.seqAt dByte none rfl)) (.cons (wvar 0) (.cons (wvar 1) .nil)) (.cons 4 .nil) <|
  .op ⟨5⟩ (.owned (.finToNat 256)) (.cons (wvar 4) .nil) (.cons 5 .nil) <|
  .op ⟨6⟩ (.literal .nat [23] rfl) .nil (.cons 6 .nil) <|
  .op ⟨7⟩ (.owned .natLess) (.cons (wvar 5) (.cons (wvar 6) .nil)) (.cons 7 .nil) <|
  .guard ⟨8⟩ () (wvar 7) rfl .reject <|
  .op ⟨9⟩ (.row DeployRow.byteToPoint _ rfl) (.cons (wvar 4) .nil) (.cons 8 .nil) <|
  .op ⟨10⟩ (.literal .nat [1] rfl) .nil (.cons 9 .nil) <|
  .op ⟨11⟩ (.owned .natAdd) (.cons (wvar 1) (.cons (wvar 9) .nil)) (.cons 10 .nil) <|
  .ret (.cons (wvar 8) (.cons (wvar 10) .nil))

private def wFnEqScalar {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dScalar, dScalar]) [.bool] :=
  .op ⟨1⟩ (.row DeployRow.sameScalar _ rfl) (.cons (wvar 0) (.cons (wvar 1) .nil)) (.cons 2 .nil) <|
  .ret (.cons (wvar 2) .nil)

private def wSchnorrTerm {hs : Headers deployVocab} :
    Term (protocolDialect deployVocab hs)
      (Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]) [] :=
  .op ⟨10⟩ (.given (.coin ()) 0 [] [] dScalar ⟨⟨[], dScalar⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 2 .nil) <|
  .op ⟨11⟩ (.compute [0] (.row DeployRow.base _ rfl) [⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 2) .nil) (.cons 3 .nil) <|
  .op ⟨12⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (wvar 3) .nil) (.cons 4 .nil) <|
  .op ⟨13⟩ (.given (.coin ()) 1 [0] [] dScalar ⟨⟨[], dScalar⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 5 .nil) <|
  .op ⟨14⟩ (.compute [0] (.row DeployRow.mul _ rfl) [⟨dScalar, [0, 1]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 5) (.cons (wvar 0) .nil)) (.cons 6 .nil) <|
  .op ⟨15⟩ (.compute [0] (.row DeployRow.add _ rfl) [⟨dScalar, [0]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 2) (.cons (wvar 6) .nil)) (.cons 7 .nil) <|
  .op ⟨16⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (wvar 7) .nil) (.cons 8 .nil) <|
  .op ⟨17⟩ (.compute [1] (.row DeployRow.base _ rfl) [⟨dScalar, [0, 1]⟩] rfl (by decide))
      (.cons (wvar 8) .nil) (.cons 9 .nil) <|
  .op ⟨18⟩ (.compute [1] (.row DeployRow.scale _ rfl) [⟨dScalar, [0, 1]⟩, ⟨dPoint, [0, 1]⟩] rfl (by decide))
      (.cons (wvar 5) (.cons (wvar 1) .nil)) (.cons 10 .nil) <|
  .op ⟨19⟩ (.compute [1] (.row DeployRow.plus _ rfl) [⟨dPoint, [0, 1]⟩, ⟨dPoint, [1]⟩] rfl (by decide))
      (.cons (wvar 4) (.cons (wvar 10) .nil)) (.cons 11 .nil) <|
  .op ⟨20⟩ (.compute [1] (.row DeployRow.same _ rfl) [⟨dPoint, [1]⟩, ⟨dPoint, [1]⟩] rfl (by decide))
      (.cons (wvar 9) (.cons (wvar 11) .nil)) (.cons 12 .nil) <|
  .guard ⟨21⟩ [1] (wvar 12) ⟨rfl, by decide, by decide⟩ .reject <|
  .ret .nil

private abbrev wHdrStart : FnHeader deployVocab := ⟨⟨100⟩, [dBytes], [.nat], false, none, Summary.empty⟩
private abbrev wHdrAbsorb : FnHeader deployVocab := ⟨⟨101⟩, [.nat, dBytes, dBytes], [.nat], false, none, Summary.empty⟩
private abbrev wHdrEncScalar : FnHeader deployVocab := ⟨⟨102⟩, [dScalar], [dBytes], false, none, Summary.empty⟩
private abbrev wHdrEncPoint : FnHeader deployVocab := ⟨⟨103⟩, [dPoint], [dBytes], false, none, Summary.empty⟩
private abbrev wHdrDerive : FnHeader deployVocab := ⟨⟨104⟩, [.nat, dBytes], [dScalar, .nat], false, none, Summary.empty⟩
private abbrev wHdrReadScalar : FnHeader deployVocab := ⟨⟨105⟩, [dBytes, .nat], [dScalar, .nat], true, none, Summary.empty⟩
private abbrev wHdrReadPoint : FnHeader deployVocab := ⟨⟨106⟩, [dBytes, .nat], [dPoint, .nat], true, none, Summary.empty⟩
private abbrev wHdrEqScalar : FnHeader deployVocab := ⟨⟨107⟩, [dScalar, dScalar], [.bool], false, none, Summary.empty⟩

private abbrev wFnHeaders : List (FnHeader deployVocab) :=
  [wHdrEqScalar, wHdrReadPoint, wHdrReadScalar, wHdrDerive, wHdrEncPoint, wHdrEncScalar, wHdrAbsorb, wHdrStart]

private abbrev wSchnorrHdr : ProtocolHeader deployVocab :=
  ⟨⟨200⟩, 2, [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩], [], shapeOf (wSchnorrTerm (hs := ⟨wFnHeaders, []⟩))⟩

private def wFnDefs : Defs deployVocab ⟨wFnHeaders, []⟩ :=
  .fn wHdrEqScalar (Names.counting 0 _) wFnEqScalar
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrReadPoint (Names.counting 0 _) wFnReadPoint
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrReadScalar (Names.counting 0 _) wFnReadScalar
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrDerive (Names.counting 0 _) wFnDeriveScalar
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrEncPoint (Names.counting 0 _) wFnEncodePoint
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrEncScalar (Names.counting 0 _) wFnEncodeScalar
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrAbsorb (Names.counting 0 _) wFnAbsorb
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrStart (Names.counting 0 _) wFnStart
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .nil

private def witnessDefs : Defs deployVocab ⟨wFnHeaders, [wSchnorrHdr]⟩ :=
  .protocol wSchnorrHdr (Names.counting 0 _) wSchnorrTerm
    ⟨by simp [Within, ProtocolOp.Within, wSchnorrTerm, wSchnorrHdr],
     by decide,
     by simp [Enclosed, wSchnorrTerm],
     (Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     rfl,
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel)⟩
    wFnDefs

private def witnessTyped : Typed deployVocab :=
  ⟨⟨wFnHeaders, [wSchnorrHdr]⟩, witnessDefs, by decide⟩

private theorem witness_admit_isOk :
    (admit (erase witnessTyped) noAssociation).isOk = true := by
  decide +kernel

private theorem witness_deploy_isOk :
    (match admit (erase witnessTyped) noAssociation with
     | .ok a => (deploy deployEncoder a schnorrDecl).isOk
     | .error _ => false) = true := by
  decide +kernel

private theorem witness_deployIdeal_isOk :
    (match admit (erase witnessTyped) noAssociation with
     | .ok a => (deployIdeal deployEncoder idealServiceKey a schnorrDecl).isOk
     | .error _ => false) = true := by
  decide +kernel

private theorem witness_admit_exists :
    ∃ a : Admitted deployVocab,
      admit (erase witnessTyped) noAssociation = .ok a ∧ a.program = witnessTyped := by
  cases h : admit (erase witnessTyped) noAssociation with
  | error _ => have hOk := witness_admit_isOk; rw [h] at hOk; cases hOk
  | ok a => exact ⟨a, rfl, admitted_eq_of_readback h rfl⟩

private theorem witness_deploy_exists :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      a.program = witnessTyped ∧
      deploy deployEncoder a schnorrDecl = .ok d := by
  obtain ⟨a, hAdm, hProg⟩ := witness_admit_exists
  cases hDep : deploy deployEncoder a schnorrDecl with
  | error _ =>
      have hOk := witness_deploy_isOk
      rw [hAdm] at hOk; dsimp only at hOk; rw [hDep] at hOk; cases hOk
  | ok d => exact ⟨a, d, hAdm, hProg, hDep⟩

private theorem witness_deployIdeal_exists :
    ∃ (a : Admitted deployVocab) (dIdeal : Deployed deployVocab),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      a.program = witnessTyped ∧
      deployIdeal deployEncoder idealServiceKey a schnorrDecl = .ok dIdeal := by
  obtain ⟨a, hAdm, hProg⟩ := witness_admit_exists
  cases hDep : deployIdeal deployEncoder idealServiceKey a schnorrDecl with
  | error _ =>
      have hOk := witness_deployIdeal_isOk
      rw [hAdm] at hOk; dsimp only at hOk; rw [hDep] at hOk; cases hOk
  | ok dIdeal => exact ⟨a, dIdeal, hAdm, hProg, hDep⟩

private theorem member_unique_of_find {V : Vocabulary} {p : Typed V} {k : Key}
    {h₁ h₂ : FnHeader V} {f₁ : Member p.headers.fns h₁} {f₂ : Member p.headers.fns h₂}
    (hf₁ : p.find k = some (.fn f₁)) (hf₂ : p.find k = some (.fn f₂)) :
    ∃ e : h₁ = h₂, e ▸ f₁ = f₂ := by
  have he := Option.some.inj (hf₁.symm.trans hf₂)
  cases he
  exact ⟨rfl, rfl⟩

private theorem wfn102_eval (hdr : FnHeader deployVocab)
    (f : Member witnessTyped.headers.fns hdr)
    (hFind : witnessTyped.find ⟨102⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dScalar]) (hOut : hdr.outs = [dBytes]),
      ∀ (v : Nat),
        Defs.fnTable deployModel witnessTyped.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons v .nil)) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm) (.cons [v % 256] .nil)) := by
  have h102 : witnessTyped.find ⟨102⟩ =
      some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head)))))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h102
  subst e; subst he
  exact ⟨rfl, rfl, fun _ => rfl⟩

private theorem wfn103_eval (hdr : FnHeader deployVocab)
    (f : Member witnessTyped.headers.fns hdr)
    (hFind : witnessTyped.find ⟨103⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dPoint]) (hOut : hdr.outs = [dBytes]),
      ∀ (v : Nat),
        Defs.fnTable deployModel witnessTyped.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons v .nil)) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm) (.cons [v % 256] .nil)) := by
  have h103 : witnessTyped.find ⟨103⟩ =
      some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h103
  subst e; subst he
  exact ⟨rfl, rfl, fun _ => rfl⟩

private theorem wfn104_eval (hdr : FnHeader deployVocab)
    (f : Member witnessTyped.headers.fns hdr)
    (hFind : witnessTyped.find ⟨104⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [.nat, dBytes]) (hOut : hdr.outs = [dScalar, .nat]),
      ∀ (st : Nat) (lbl : List Nat),
        Defs.fnTable deployModel witnessTyped.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons st (.cons lbl .nil))) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm)
            (.cons (mixBytes st (0xFF :: lbl) % 11) (.cons (mixBytes st (0xFF :: lbl)) .nil))) := by
  have h104 : witnessTyped.find ⟨104⟩ =
      some (.fn (Member.tail (Member.tail (Member.tail Member.head)))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h104
  subst e; subst he
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem cast_inj {α β : Type} {e : α = β} {x y : α} (h : cast e x = cast e y) : x = y := by
  subst e; exact h

private theorem ownedOp_seqAt_some {V : Vocabulary} (M : Model V) (item : V.Ty)
    (free : Ty.isLinear V item = false) (buf : List (M.Val item)) (off : Nat)
    (hlt : off < buf.length) :
    ownedOp M (.seqAt item none free) (.cons buf (.cons off .nil)) =
      Process.done (.cons (buf[off]'hlt) .nil) := by
  simp only [ownedOp, List.getElem?_eq_getElem hlt]

private theorem wfn105_eval (hdr : FnHeader deployVocab)
    (f : Member witnessTyped.headers.fns hdr)
    (hFind : witnessTyped.find ⟨105⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dBytes, .nat]) (hOut : hdr.outs = [dScalar, .nat]),
      ∀ (buf : List Nat) (off : Nat),
        Defs.fnTable deployModel witnessTyped.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons buf (.cons off .nil))) =
          if hlt : off < buf.length then
            let b := buf[off]'hlt
            if b < 11 then
              .done (cast (congrArg (HList deployModel.Val) hOut.symm)
                (.cons (b % 11) (.cons (off + 1) .nil)))
            else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
          else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  have h105 : witnessTyped.find ⟨105⟩ =
      some (.fn (Member.tail (Member.tail Member.head))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h105
  subst e; subst he
  refine ⟨rfl, rfl, fun buf off => ?_⟩
  change wFnReadScalar.denote (localSem deployModel _ (Defs.fnTable deployModel _)) []
      (Env.empty.extend (Names.counting 0 [dBytes, .nat]) (.cons buf (.cons off .nil))) = _
  dsimp only [wFnReadScalar]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := deployModel.Val) (a := .nat) buf.length HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := deployModel.Val) (a := .bool) (Nat.blt off buf.length) HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_guard]
  by_cases hlt : off < buf.length
  · rw [dite_eq_left hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = true := Nat.blt_eq.mpr hlt
    rw [hltB]; dsimp only [cond]
    erw [Term.denote_op]
    change (ownedOp deployModel (.seqAt dByte none rfl) (.cons buf (.cons off .nil))).bind _ = _
    rw [ownedOp_seqAt_some deployModel dByte rfl buf off hlt]; dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := deployModel.Val) (a := .nat) (buf[off]'hlt) HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := deployModel.Val) (a := .nat) 11 HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := deployModel.Val) (a := .bool) (Nat.blt (buf[off]'hlt) 11) HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_guard]
    by_cases hb : buf[off]'hlt < 11
    · rw [ite_eq_left hb]
      change (bif Nat.blt (buf[off]'hlt) 11 then _ else _) = _
      have hbB : Nat.blt (buf[off]'hlt) 11 = true := Nat.blt_eq.mpr hb
      rw [hbB]; rfl
    · rw [ite_eq_right hb]
      change (bif Nat.blt (buf[off]'hlt) 11 then _ else _) = _
      have hbB : Nat.blt (buf[off]'hlt) 11 = false :=
        Bool.eq_false_iff.mpr (fun h => hb (Nat.blt_eq.mp h))
      rw [hbB]; rfl
  · rw [dite_eq_right hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = false :=
      Bool.eq_false_iff.mpr (fun h => hlt (Nat.blt_eq.mp h))
    rw [hltB]; rfl

private theorem wfn106_eval (hdr : FnHeader deployVocab)
    (f : Member witnessTyped.headers.fns hdr)
    (hFind : witnessTyped.find ⟨106⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dBytes, .nat]) (hOut : hdr.outs = [dPoint, .nat]),
      ∀ (buf : List Nat) (off : Nat),
        Defs.fnTable deployModel witnessTyped.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons buf (.cons off .nil))) =
          if hlt : off < buf.length then
            let b := buf[off]'hlt
            if b < 23 then
              .done (cast (congrArg (HList deployModel.Val) hOut.symm)
                (.cons (b % 23) (.cons (off + 1) .nil)))
            else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
          else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  have h106 : witnessTyped.find ⟨106⟩ = some (.fn (Member.tail Member.head)) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h106
  subst e; subst he
  refine ⟨rfl, rfl, fun buf off => ?_⟩
  change wFnReadPoint.denote (localSem deployModel _ (Defs.fnTable deployModel _)) []
      (Env.empty.extend (Names.counting 0 [dBytes, .nat]) (.cons buf (.cons off .nil))) = _
  dsimp only [wFnReadPoint]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := deployModel.Val) (a := .nat) buf.length HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := deployModel.Val) (a := .bool) (Nat.blt off buf.length) HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_guard]
  by_cases hlt : off < buf.length
  · rw [dite_eq_left hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = true := Nat.blt_eq.mpr hlt
    rw [hltB]; dsimp only [cond]
    erw [Term.denote_op]
    change (ownedOp deployModel (.seqAt dByte none rfl) (.cons buf (.cons off .nil))).bind _ = _
    rw [ownedOp_seqAt_some deployModel dByte rfl buf off hlt]; dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := deployModel.Val) (a := .nat) (buf[off]'hlt) HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := deployModel.Val) (a := .nat) 23 HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := deployModel.Val) (a := .bool) (Nat.blt (buf[off]'hlt) 23) HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_guard]
    by_cases hb : buf[off]'hlt < 23
    · rw [ite_eq_left hb]
      change (bif Nat.blt (buf[off]'hlt) 23 then _ else _) = _
      have hbB : Nat.blt (buf[off]'hlt) 23 = true := Nat.blt_eq.mpr hb
      rw [hbB]; rfl
    · rw [ite_eq_right hb]
      change (bif Nat.blt (buf[off]'hlt) 23 then _ else _) = _
      have hbB : Nat.blt (buf[off]'hlt) 23 = false :=
        Bool.eq_false_iff.mpr (fun h => hb (Nat.blt_eq.mp h))
      rw [hbB]; rfl
  · rw [dite_eq_right hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = false :=
      Bool.eq_false_iff.mpr (fun h => hlt (Nat.blt_eq.mp h))
    rw [hltB]; rfl

private theorem wfn107_eval (hdr : FnHeader deployVocab)
    (f : Member witnessTyped.headers.fns hdr)
    (hFind : witnessTyped.find ⟨107⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dScalar, dScalar]) (hOut : hdr.outs = [.bool]),
      ∀ (a b : Nat),
        Defs.fnTable deployModel witnessTyped.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons a (.cons b .nil))) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm) (.cons (decide (a = b)) .nil)) := by
  have h107 : witnessTyped.find ⟨107⟩ = some (.fn Member.head) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h107
  subst e; subst he
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem witness_suiteLawful_of {d : Deployed deployVocab}
    (hDecl : d.declaration = schnorrDecl) (hProg : d.admitted.program = witnessTyped) :
    d.SuiteLawful deployModel := by
  cases d with
  | mk adm decl found stack =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDecl hProg
          subst hDecl; subst hProg
          intro suite sessionTag hCon
          have hSEq : suite = toySuite := (Construction.derived.inj hCon).1.symm
          subst hSEq
          constructor
          · intro defKey hMem hdr f hFind stateTy drawIns e law owner h0 hs _ _ hLaw hins houts
              st label payload coin st' _ _ _ hEval
            have hK : defKey = ⟨104⟩ := by
              simp only [toySuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
              rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
              · cases h
              · cases h
              · cases h
              · cases h
              · exact h
            subst hK
            obtain ⟨hIn, hOut, hEv⟩ := wfn104_eval hdr f hFind
            have hST : stateTy = .nat ∧ drawIns = [] := by
              have hc := hIn.symm.trans hins
              injection hc with h1 h2
              injection h2 with _ h3
              exact ⟨h1.symm, h3.symm⟩
            obtain ⟨rfl, rfl⟩ := hST
            cases e with
            | mk eSite eCls eTau =>
                dsimp only at hLaw houts hEval ⊢
                have hTau : eTau = dScalar := by
                  have hc := hOut.symm.trans houts
                  injection hc with h1 _
                  exact h1.symm
                subst hTau
                cases payload; cases law
                change Nat at st coin st'
                change List Nat at label
                have hEv' := hEv st label
                erw [hEv'] at hEval
                have hDone := Process.done.inj hEval
                have hCoinEq : mixBytes st (0xFF :: label) % 11 = coin := by
                  have hc2 : (.cons (mixBytes st (0xFF :: label) % 11) (.cons (mixBytes st (0xFF :: label)) .nil) :
                      HList deployModel.Val [dScalar, .nat]) = .cons coin (.cons st' .nil) :=
                    cast_inj hDone
                  cases hc2; rfl
                have hCoinLt : coin < 11 := by
                  rw [← hCoinEq]
                  exact Nat.mod_lt _ (by decide)
                exact ⟨hCoinLt, ⟨[], dScalar⟩, rfl, rfl, rfl, hCoinLt⟩
          · intro eKey hMem hdr f hFind unitTy τ hIn hOut v₁ v₂ u hv₁ hv₂ hEv₁ hEv₂
            have hK : eKey = ⟨102⟩ ∨ eKey = ⟨103⟩ := by
              simp only [toySuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
              rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
              · cases h
              · cases h
              · exact .inl h
              · exact .inr h
              · cases h
            rcases hK with rfl | rfl
            · obtain ⟨hIn0, hOut0, hEv⟩ := wfn102_eval hdr f hFind
              have hTau : τ = dScalar := List.cons.inj (hIn.symm.trans hIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hOut.symm.trans hOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v₁ v₂
              change List Nat at u
              have h1 := hEv v₁; have h2 := hEv v₂
              erw [h1] at hEv₁
              erw [h2] at hEv₂
              have hd1 : ([v₁ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₁))
              have hd2 : ([v₂ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₂))
              have hMod : v₁ % 256 = v₂ % 256 := List.cons.inj (hd1.trans hd2.symm) |>.1
              have hv1Lt : v₁ < 11 := hv₁
              have hv2Lt : v₂ < 11 := hv₂
              exact (Nat.mod_eq_of_lt (Nat.lt_trans hv1Lt (by decide))).symm.trans
                (hMod.trans (Nat.mod_eq_of_lt (Nat.lt_trans hv2Lt (by decide))))
            · obtain ⟨hIn0, hOut0, hEv⟩ := wfn103_eval hdr f hFind
              have hTau : τ = dPoint := List.cons.inj (hIn.symm.trans hIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hOut.symm.trans hOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v₁ v₂
              change List Nat at u
              have h1 := hEv v₁; have h2 := hEv v₂
              erw [h1] at hEv₁
              erw [h2] at hEv₂
              have hd1 : ([v₁ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₁))
              have hd2 : ([v₂ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₂))
              have hMod : v₁ % 256 = v₂ % 256 := List.cons.inj (hd1.trans hd2.symm) |>.1
              have hv1Lt : v₁ < 23 := hv₁
              have hv2Lt : v₂ < 23 := hv₂
              exact (Nat.mod_eq_of_lt (Nat.lt_trans hv1Lt (by decide))).symm.trans
                (hMod.trans (Nat.mod_eq_of_lt (Nat.lt_trans hv2Lt (by decide))))

private theorem list_take_elem_drop {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs = xs.take i ++ [xs[i]'h] ++ xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => cases h
  | cons a rest ih =>
      cases i with
      | zero => rfl
      | succ k =>
          simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
            List.cons_append]
          exact congrArg (a :: ·) (ih k (Nat.lt_of_succ_lt_succ h))

private theorem witness_layoutLawful_of {d : Deployed deployVocab}
    (hDecl : d.declaration = schnorrDecl) (hProg : d.admitted.program = witnessTyped) :
    d.LayoutLawful deployModel := by
  cases d with
  | mk adm decl found stack =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDecl hProg
          subst hDecl; subst hProg
          intro layout hLay
          have hLEq : layout = ⟨toyLayoutModule, [], []⟩ := Option.some.inj hLay.symm
          subst hLEq
          refine ⟨?_, ?_, ?_⟩
          · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
              v chunk pre post hv _ _ hW
            have hWK : wKey = ⟨102⟩ ∨ wKey = ⟨103⟩ := by
              simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
              rcases hwMem with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
              · exact .inl h
              · exact .inr h
              · cases h
              · cases h
              · cases h
            have hRK : rKey = ⟨105⟩ ∨ rKey = ⟨106⟩ := by
              simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
              rcases hrMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
              · cases h
              · cases h
              · exact .inl h
              · exact .inr h
              · cases h
            rcases hWK with rfl | rfl <;> rcases hRK with rfl | rfl
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn102_eval wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn105_eval rHdr fR hrFind
              have hTau : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v
              change List Nat at chunk pre post
              have hW0 := hEvW v
              erw [hW0] at hW
              have hCh : [v % 256] = chunk :=
                congrArg HList.single (cast_inj (Process.done.inj hW))
              subst hCh
              have hR0 := hEvR (pre ++ [v % 256] ++ post) pre.length
              have hvLt : v < 11 := hv
              have hvMod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hlt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hElem : (pre ++ [v % 256] ++ post)[pre.length]'hlt = v := by
                simp [List.append_assoc, hvMod]
              erw [hR0]
              rw [dite_eq_left hlt]; dsimp only; rw [hElem, ite_eq_left hvLt]
              have hvm : v % 11 = v := Nat.mod_eq_of_lt hvLt
              erw [hvm]; rfl
            · obtain ⟨hwIn0, _, _⟩ := wfn102_eval wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn106_eval rHdr fR hrFind
              have h1 : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dPoint := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, _, _⟩ := wfn103_eval wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn105_eval rHdr fR hrFind
              have h1 : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dScalar := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn103_eval wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn106_eval rHdr fR hrFind
              have hTau : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v
              change List Nat at chunk pre post
              have hW0 := hEvW v
              erw [hW0] at hW
              have hCh : [v % 256] = chunk :=
                congrArg HList.single (cast_inj (Process.done.inj hW))
              subst hCh
              have hR0 := hEvR (pre ++ [v % 256] ++ post) pre.length
              have hvLt : v < 23 := hv
              have hvMod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hlt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hElem : (pre ++ [v % 256] ++ post)[pre.length]'hlt = v := by
                simp [List.append_assoc, hvMod]
              erw [hR0]
              rw [dite_eq_left hlt]; dsimp only; rw [hElem, ite_eq_left hvLt]
              have hvm : v % 23 = v := Nat.mod_eq_of_lt hvLt
              erw [hvm]; rfl
          · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
              buf off v nextOff _ _ hR
            have hWK : wKey = ⟨102⟩ ∨ wKey = ⟨103⟩ := by
              simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
              rcases hwMem with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
              · exact .inl h
              · exact .inr h
              · cases h
              · cases h
              · cases h
            have hRK : rKey = ⟨105⟩ ∨ rKey = ⟨106⟩ := by
              simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
              rcases hrMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
              · cases h
              · cases h
              · exact .inl h
              · exact .inr h
              · cases h
            rcases hWK with rfl | rfl <;> rcases hRK with rfl | rfl
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn102_eval wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn105_eval rHdr fR hrFind
              have hTau : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change List Nat at buf
              change Nat at off v nextOff
              have hR0 := hEvR buf off
              erw [hR0] at hR
              by_cases hlt : off < buf.length
              · simp only [hlt, ↓reduceDIte] at hR
                by_cases hb : buf[off]'hlt < 11
                · simp only [hb, ↓reduceIte] at hR
                  have hPair : (HList.cons (buf[off]'hlt % 11) (.cons (off + 1) .nil) :
                      HList deployModel.Val [dScalar, .nat]) = .cons v (.cons nextOff .nil) :=
                    cast_inj (Process.done.inj hR)
                  have hvEq : buf[off]'hlt % 11 = v := by cases hPair; rfl
                  have hNextEq : off + 1 = nextOff := by cases hPair; rfl
                  subst hvEq; subst hNextEq
                  have hbMod : buf[off]'hlt % 11 = buf[off]'hlt := Nat.mod_eq_of_lt hb
                  refine ⟨by rw [hbMod]; exact hb, Nat.le_succ off, hlt, [buf[off]'hlt], ?_,
                    list_take_elem_drop buf off hlt⟩
                  have hW0 := hEvW (buf[off]'hlt % 11)
                  have hMod256 : (buf[off]'hlt % 11) % 256 = buf[off]'hlt := by omega
                  erw [hW0]; simp only [hMod256]; rfl
                · simp only [hb, ↓reduceIte] at hR; cases hR
              · simp only [hlt, ↓reduceDIte] at hR; cases hR
            · obtain ⟨hwIn0, _, _⟩ := wfn102_eval wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn106_eval rHdr fR hrFind
              have h1 : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dPoint := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, _, _⟩ := wfn103_eval wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn105_eval rHdr fR hrFind
              have h1 : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dScalar := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn103_eval wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn106_eval rHdr fR hrFind
              have hTau : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change List Nat at buf
              change Nat at off v nextOff
              have hR0 := hEvR buf off
              erw [hR0] at hR
              by_cases hlt : off < buf.length
              · simp only [hlt, ↓reduceDIte] at hR
                by_cases hb : buf[off]'hlt < 23
                · simp only [hb, ↓reduceIte] at hR
                  have hPair : (HList.cons (buf[off]'hlt % 23) (.cons (off + 1) .nil) :
                      HList deployModel.Val [dPoint, .nat]) = .cons v (.cons nextOff .nil) :=
                    cast_inj (Process.done.inj hR)
                  have hvEq : buf[off]'hlt % 23 = v := by cases hPair; rfl
                  have hNextEq : off + 1 = nextOff := by cases hPair; rfl
                  subst hvEq; subst hNextEq
                  have hbMod : buf[off]'hlt % 23 = buf[off]'hlt := Nat.mod_eq_of_lt hb
                  refine ⟨by rw [hbMod]; exact hb, Nat.le_succ off, hlt, [buf[off]'hlt], ?_,
                    list_take_elem_drop buf off hlt⟩
                  have hW0 := hEvW (buf[off]'hlt % 23)
                  have hMod256 : (buf[off]'hlt % 23) % 256 = buf[off]'hlt := by omega
                  erw [hW0]; simp only [hMod256]; rfl
                · simp only [hb, ↓reduceIte] at hR; cases hR
              · simp only [hlt, ↓reduceDIte] at hR; cases hR
          · intro eqKey hMem eqHdr fEq hFind τ hIn hOut v₁ v₂ b _ _ hEv
            have hK : eqKey = ⟨107⟩ := by
              simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
              rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
              · cases h
              · cases h
              · cases h
              · cases h
              · exact h
            subst hK
            obtain ⟨hIn0, hOut0, hEv0⟩ := wfn107_eval eqHdr fEq hFind
            have hTau : τ = dScalar := List.cons.inj (hIn.symm.trans hIn0) |>.1
            subst hTau
            change Nat at v₁ v₂
            change Bool at b
            have hEq := hEv0 v₁ v₂
            erw [hEq] at hEv
            have hb : decide (v₁ = v₂) = b :=
              congrArg HList.single (cast_inj (Process.done.inj hEv))
            rw [← hb]
            exact decide_eq_true_iff

/-- Concrete witness of `idealPath_msgStep_injective` concluding literal equality of sites,
values, and prior paths on an admitted and deployed Schnorr scheme. -/
theorem witness_idealPath_msgStep_injective :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      deploy deployEncoder a schnorrDecl = .ok d ∧
      ∀ {encRef : LayerBuild.TypedFnRef deployVocab d.admitted.program.headers.fns [dPoint] [dBytes]},
        findSuiteEncode d.admitted toySuite dByte dPoint = some encRef →
        ∀ {st₁ st₂ : deployModel.Val (LayerBuild.idealPathTy dByte)}
          {s₁ s₂ : Site} {v₁ v₂ : Nat} {enc₁ enc₂ : List Nat},
          v₁ < 23 → v₂ < 23 →
          encRef.eval deployModel (Defs.fnTable deployModel d.admitted.program.defs)
            (.cons v₁ .nil) = .done (.cons enc₁ .nil) →
          encRef.eval deployModel (Defs.fnTable deployModel d.admitted.program.defs)
            (.cons v₂ .nil) = .done (.cons enc₂ .nil) →
          LayerBuild.idealPathPush deployModel st₁ (2 :: msgLabel s₁) enc₁ =
            LayerBuild.idealPathPush deployModel st₂ (2 :: msgLabel s₂) enc₂ →
          st₁ = st₂ ∧ s₁ = s₂ ∧ v₁ = v₂ := by
  obtain ⟨a, d, hAdm, hProg, hDep⟩ := witness_deploy_exists
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps deployEncoder a schnorrDecl d hDep
  have hDProg : d.admitted.program = witnessTyped := by rw [hAdmEq, hProg]
  have hSL := witness_suiteLawful_of hDeclEq hDProg
  refine ⟨a, d, hAdm, hDep, ?_⟩
  intro encRef hFind st₁ st₂ s₁ s₂ v₁ v₂ enc₁ enc₂ hv₁ hv₂ hE₁ hE₂ hEq
  exact idealPath_msgStep_injective deployModel (by rw [hDeclEq]; rfl) hSL hFind hv₁ hv₂ hE₁ hE₂ hEq

private theorem schnorr_group_law_w7 (r c : Nat) (hr : r < 11) (hc : c < 11) :
    powMod 2 ((r + c * 7) % 11) 23 = (powMod 2 r 23 * powMod 13 c 23) % 23 := by
  have hAll : ∀ a : Fin 11, ∀ b : Fin 11,
      powMod 2 ((a.1 + b.1 * 7) % 11) 23 = (powMod 2 a.1 23 * powMod 13 b.1 23) % 23 := by
    decide +kernel
  exact hAll ⟨r, hr⟩ ⟨c, hc⟩

private theorem witness_protocol_unfold :
    protocolMeaning deployModel witnessTyped Member.head []
      (.cons (7 : Nat) (.cons (13 : Nat) .nil)) =
      Process.call (GOp.given (.coin ()) 0 [] ⟨[], ⟨10⟩⟩ [] .nil dScalar) fun (r : Nat) =>
        Process.call (GOp.flow .message 0 [1] ⟨[], ⟨12⟩⟩ dPoint (powMod 2 r 23)) fun _ =>
          Process.call (GOp.given (.coin ()) 1 [0] ⟨[], ⟨13⟩⟩ [] .nil dScalar) fun (c : Nat) =>
            Process.call (GOp.flow .message 0 [1] ⟨[], ⟨16⟩⟩ dScalar ((r + (c * 7) % 11) % 11))
              fun _ =>
                ((((bif decide (powMod 2 ((r + (c * 7) % 11) % 11) 23 =
                    (powMod 2 r 23 * powMod 13 c 23) % 23) then
                  (Process.done (HList.nil, ()) :
                    Protocol deployModel (HList (LVal deployModel) [] × Unit))
                else
                  Process.halt ([1], Stop.declared .reject ⟨[], ⟨21⟩⟩)).map
                  fun out => (out.1, (((r + (c * 7) % 11) % 11), out.2))).map
                  fun out => (out.1, (c, out.2))).map
                  fun out => (out.1, (powMod 2 r 23, out.2))).map
                  fun out => (out.1, out.2) := rfl

private theorem witness_deploy_complete_of (a : Admitted deployVocab) (d : Deployed deployVocab)
    (hAdm : admit (erase witnessTyped) noAssociation = .ok a)
    (hDep : deploy deployEncoder a schnorrDecl = .ok d)
    (hDProg : d.admitted.program = witnessTyped)
    (hDeclEq : d.declaration = schnorrDecl) :
    ∃ (hIns : d.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      let ins := cast (congrArg (HList (LVal deployModel)) hIns.symm)
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone deployModel (fixedNonceSource 5) 0
          (d.run deployModel 0 (hideAll deployModel 0 ins)
            (cast (congrArg (HList deployModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone deployModel (fixedNonceSource 5) 1
          (d.run deployModel 1 (hideAll deployModel 1 ins)
            (cast (congrArg (HList deployModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins) ∧
          (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins →
            source' at_ τ = fixedNonceSource 5 at_ τ) ∧
          GExec deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins)
            (.returned out) ∧
          outP = hideAll deployModel 0 out.1 ∧ outV = hideAll deployModel 1 out.1 := by
  have hSL := witness_suiteLawful_of hDeclEq hDProg
  have hLL := witness_layoutLawful_of hDeclEq hDProg
  cases d with
  | mk adm decl found stack =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier wSchnorrHdr schnorrDecl = some (0, 1) := by decide +kernel
          obtain ⟨hFirst, hMatched⟩ := deploy_matches deployEncoder a schnorrDecl _ hDep 0 1 hRoles
          have hInsV : (HList.cons (7 : Nat) (.cons (13 : Nat) .nil) :
              HList (LVal deployModel) wSchnorrHdr.ins).All (fun a v => deployModel.Valid a.ty v) :=
            ⟨show (7 : Nat) < 11 by decide, show (13 : Nat) < 23 by decide, trivial⟩
          have hNoRec : ∀ l, schnorrDecl.layout = some l → l.recover = [] := fun _ h => by
            cases Option.some.inj h; rfl
          have hNoHalt : ∀ source,
              Lawful deployModel source
                (protocolMeaning deployModel witnessTyped Member.head []
                  (.cons (7 : Nat) (.cons (13 : Nat) .nil))) →
              ∀ e,
                GExec deployModel source
                  (protocolMeaning deployModel witnessTyped Member.head []
                    (.cons (7 : Nat) (.cons (13 : Nat) .nil))) e →
                ∃ out, e = .returned out := by
            intro source hLaw e hExec
            rw [witness_protocol_unfold] at hLaw hExec
            obtain ⟨events, hRun⟩ := hExec
            cases hRun with
            | @given _ _ _ _ _ _ _ vR _ _ _ hSrcR hRun1 =>
                have hrLt : deployModel.Valid dScalar vR := (hLaw _ hSrcR).1.1
                change Nat at vR
                change vR < 11 at hrLt
                have hLaw1 := (hLaw _ hSrcR).2
                cases hRun1 with
                | flow hRun2 =>
                    cases hRun2 with
                    | @given _ _ _ _ _ _ _ vC _ _ _ hSrcC hRun3 =>
                        have hcLt : deployModel.Valid dScalar vC := (hLaw1 _ hSrcC).1.1
                        change Nat at vC
                        change vC < 11 at hcLt
                        cases hRun3 with
                        | flow hRun4 =>
                            dsimp only at hRun4
                            have hEq := schnorr_group_law_w7 vR vC hrLt hcLt
                            have hAdd : ∀ r c : Nat, (r + c * 7 % 11) % 11 = (r + c * 7) % 11 :=
                              fun r c => by omega
                            have hDec : decide (powMod 2 ((vR + vC * 7 % 11) % 11) 23 =
                                (powMod 2 vR 23 * powMod 13 vC 23) % 23) = true :=
                              decide_eq_true (by rw [hAdd, hEq])
                            erw [hDec] at hRun4
                            cases hRun4
                            exact ⟨_, rfl⟩
          have hLP : LawfulPrivate deployModel (fixedNonceSource 5)
              (protocolMeaning deployModel witnessTyped Member.head []
                (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
            rw [witness_protocol_unfold]
            intro v hv
            cases Option.some.inj hv
            refine ⟨⟨show (5 % 11 : Nat) < 11 by decide,
              ⟨[], dScalar⟩, rfl, rfl, rfl, show (5 % 11 : Nat) < 11 by decide⟩, ?_⟩
            intro (c : Nat) _
            dsimp only [LawfulPrivate]
            cases decide (powMod 2 ((5 % 11 + c * 7 % 11) % 11) 23 =
                (powMod 2 (5 % 11) 23 * powMod 13 c 23) % 23) <;> trivial
          have hFed : Fed deployModel (fixedNonceSource 5)
              (protocolMeaning deployModel witnessTyped Member.head []
                (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
            rw [witness_protocol_unfold]
            refine ⟨(5 : Nat), rfl, fun (c : Nat) _ => ?_⟩
            dsimp only [Fed]
            cases decide (powMod 2 ((5 + c * 7 % 11) % 11) 23 =
                (powMod 2 5 23 * powMod 13 c 23) % 23) <;> trivial
          refine ⟨rfl, hFirst, hMatched, ?_⟩
          exact deploy_complete deployModel deployEncoder hAdm hDep
            rfl rfl rfl hNoRec
            0 1 hRoles hFirst hMatched (.cons (7 : Nat) (.cons (13 : Nat) .nil)) hInsV hSL hLL
            hNoHalt (fixedNonceSource 5) hLP hFed

/-- Concrete non-vacuous instantiation of `deploy_complete` on an admitted & deployed Schnorr
scheme at `(w = 7, Y = 13)` with every hypothesis (`SuiteLawful`, `LayoutLawful`, honest
completeness, `LawfulPrivate`, `Fed`) discharged cleanly. -/
theorem witness_deploy_complete :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab)
      (hIns : d.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      deploy deployEncoder a schnorrDecl = .ok d ∧
      let ins := cast (congrArg (HList (LVal deployModel)) hIns.symm)
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone deployModel (fixedNonceSource 5) 0
          (d.run deployModel 0 (hideAll deployModel 0 ins)
            (cast (congrArg (HList deployModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone deployModel (fixedNonceSource 5) 1
          (d.run deployModel 1 (hideAll deployModel 1 ins)
            (cast (congrArg (HList deployModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins) ∧
          (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins →
            source' at_ τ = fixedNonceSource 5 at_ τ) ∧
          GExec deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins)
            (.returned out) ∧
          outP = hideAll deployModel 0 out.1 ∧ outV = hideAll deployModel 1 out.1 := by
  obtain ⟨a, d, hAdm, hProg, hDep⟩ := witness_deploy_exists
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps deployEncoder a schnorrDecl d hDep
  have hDProg : d.admitted.program = witnessTyped := by rw [hAdmEq, hProg]
  obtain ⟨hIns, hFirst, hMatched, hRest⟩ := witness_deploy_complete_of a d hAdm hDep hDProg hDeclEq
  exact ⟨a, d, hIns, hFirst, hMatched, hAdm, hDep, hRest⟩

/-- Concrete proof that `schnorrIdealRO` satisfies `IdealRO.AnswersDraws` on `wSchnorrHdr`. -/
theorem schnorrIdealRO_answersDraws :
    schnorrIdealRO.AnswersDraws deployModel 0 1 (wSchnorrHdr.shape.events [] id) := by
  intro e he law hearers hCls hPin st lbl _ _
  have hTau : e.τ = dScalar := by
    simp only [wSchnorrTerm, shapeOf, ProtocolOp.shape, Shape.events,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> cases hCls <;> rfl
  rw [hTau]
  dsimp only [schnorrIdealRO]
  split
  · exact ⟨_, rfl, Nat.mod_lt _ (by decide)⟩
  · exact ⟨_, rfl, show (0 : Nat) < 11 by decide⟩

private theorem witness_deployIdeal_link_of (a : Admitted deployVocab) (dIdeal : Deployed deployVocab)
    (hProg : a.program = witnessTyped)
    (hDep : deployIdeal deployEncoder idealServiceKey a schnorrDecl = .ok dIdeal)
    (hDProg : dIdeal.admitted.program = witnessTyped)
    (hDeclEq : dIdeal.declaration = schnorrDecl) :
    ∃ (hIns : dIdeal.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
      (st0 : deployModel.Val (LayerBuild.idealPathTy dByte))
      (hTakes : Stack.Takes (dIdeal.stack 1) = [dBytes]),
      resolveSessionBytes deployEncoder a schnorrDecl none = .ok ⟨sessBytes, hSess⟩ ∧
      let vIns := hideAll deployModel 1
        (cast (congrArg (HList (LVal deployModel)) hIns.symm)
          (.cons (0 : Nat) (.cons (13 : Nat) .nil)))
      idealInitialPath deployModel a toySuite dByte 0 1 sessBytes vIns = some st0 ∧
      ∀ (outV : HList (RV deployModel 1) dIdeal.entry.outs),
        (∃ record givesV,
          Alone deployModel (fixedNonceSource 5) 1
            (Process.answerService idealServiceKey
              (LayerBuild.IdealRO.asOracle deployModel schnorrIdealRO)
              (dIdeal.run deployModel 1 vIns
                (cast (congrArg (HList deployModel.Val) hTakes.symm)
                  (.cons ([9, 0] : List (deployModel.Val dByte)) .nil))))
            record (.returned (outV, givesV))) ↔
        BareIdealReturn deployModel a toySuite ⟨toyLayoutModule, [], []⟩
          idealServiceKey 0 1
          (dIdeal.entry.shape.eventsWithAbsorb 0 1 [] id false)
          (fixedNonceSource 5) schnorrIdealRO
          (roleMeaning deployModel dIdeal.admitted.program dIdeal.callee 1 [] vIns)
          st0 ([9, 0] : List (deployModel.Val dByte)) 0 outV := by
  cases dIdeal with
  | mk adm decl found stack =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier wSchnorrHdr schnorrDecl = some (0, 1) := by decide +kernel
          let vIns : HList (RV deployModel 1) wSchnorrHdr.ins :=
            hideAll deployModel 1 (.cons (0 : Nat) (.cons (13 : Nat) .nil))
          have hVInsV : vIns.All (RV.Valid deployModel 1) :=
            hideAll_valid deployModel 1 _
              ⟨show (0 : Nat) < 11 by decide, show (13 : Nat) < 23 by decide, trivial⟩
          obtain ⟨suiteUnitTy, unitTy, hSuiteFree, sessBytes, hSess, st0, hTakes, hUnit, hRes, hInit, hIff⟩ :=
            deployIdeal_link deployModel deployEncoder idealServiceKey hDep
              rfl rfl rfl rfl rfl 0 1 hRoles vIns hVInsV
          have hSU : suiteUnitTy = dByte := by
            cases a with
            | mk progA annA assocA assuA =>
                dsimp only at hProg; subst hProg
                have hExp : findSuiteUnit ⟨witnessTyped, annA, assocA, assuA⟩ toySuite = some ⟨dByte, ⟨rfl⟩⟩ := rfl
                exact congrArg Sigma.fst (Option.some.inj (hUnit.symm.trans hExp))
          have hLU : unitTy = dByte := by
            have hExp : findLayoutUnit a toyLayoutModule = some ⟨dByte, ⟨rfl⟩⟩ := by
              cases a with
              | mk progA annA assocA assuA =>
                  dsimp only at hProg; subst hProg; rfl
            have hTak : Stack.Takes (stack 1) = [dBytes] := by
              obtain ⟨w, hEq⟩ := deployIdeal_ok_elim deployEncoder idealServiceKey a schnorrDecl _ hDep
              have hLay : w.prep.layout = ⟨toyLayoutModule, [], []⟩ :=
                (Option.some.inj w.prep.hLayOpt).symm
              cases buildLayoutLayers_ok_elim w.prep.hLay with
              | compact wL _ =>
                  have hne := wL.hNonEmpty; rw [hLay] at hne; cases hne
              | streaming wL _ hLVW =>
                  have hUL : wL.unitTy = dByte := by
                    have h1 := wL.hUnit
                    have hModEq : w.prep.layout.module = toyLayoutModule := congrArg Layout.module hLay
                    rw [hModEq] at h1
                    exact congrArg Sigma.fst (Option.some.inj (h1.symm.trans hExp))
                  have hV1 : w.prep.verifier = 1 := by
                    have hR : proverAndVerifier w.foundPair.1 schnorrDecl = some (0, 1) := by
                      have hR' : (w.toDeployed).roles = some (0, 1) := by
                        rw [← hEq]; exact hRoles
                      simpa [Deployed.roles, Deployed.entry, w.hFound] using hR'
                    rw [w.prep.hPV] at hR; exact (Prod.mk.inj (Option.some.inj hR)).2
                  have hSt : Stack.Takes (stack 1) = Stack.Takes (w.toDeployed.stack 1) :=
                    congrArg (fun x => Stack.Takes (x.stack 1)) hEq
                  have hCastR : ∀ {r₁ r₂ : Role} (e : r₁ = r₂) {ins}
                      (st : List (Layer deployVocab a.program.headers r₁ ins)),
                      Stack.Takes (e ▸ st) = Stack.Takes st := by
                    intro r₁ r₂ e ins st; subst e; rfl
                  rw [hSt]
                  dsimp only [DeployIdealWitness.toDeployed]
                  rw [dite_eq_left hV1.symm, hCastR, stack_takes_cast_ins (by simp [w.hFound]), hLVW]
                  simp [Stack.Takes, hUL]; rfl
            have hEq := List.cons.inj (hTakes.symm.trans hTak) |>.1
            injection hEq
          subst hSU; subst hLU
          have hProofV : deployModel.Valid dBytes ([9, 0] : List (deployModel.Val dByte)) :=
            ⟨(fun b hb => by
                rcases List.mem_cons.mp hb with rfl | hb2
                · show (9 : Nat) < 256; decide
                · rcases List.mem_cons.mp hb2 with rfl | hb3
                  · show (0 : Nat) < 256; decide
                  · cases hb3),
             (fun _ h => nomatch h)⟩
          exact ⟨rfl, sessBytes, hSess, st0, hTakes, hRes, hInit,
            fun outV => hIff ([9, 0] : List (deployModel.Val dByte)) hProofV
              (fixedNonceSource 5) schnorrIdealRO schnorrIdealRO_answersDraws outV⟩

/-- Concrete non-vacuous instantiation of `deployIdeal_link` on an admitted & ideal-deployed
Schnorr scheme, applied all the way through concrete partial oracle `schnorrIdealRO`
(`schnorrIdealRO_answersDraws`), concrete proof bytes `[9, 0]`, statement `Y = 13`, and
`fixedNonceSource 5`. -/
theorem witness_deployIdeal_link_concrete_ro :
    ∃ (a : Admitted deployVocab) (dIdeal : Deployed deployVocab)
      (hIns : dIdeal.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
      (st0 : deployModel.Val (LayerBuild.idealPathTy dByte))
      (hTakes : Stack.Takes (dIdeal.stack 1) = [dBytes]),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      deployIdeal deployEncoder idealServiceKey a schnorrDecl = .ok dIdeal ∧
      resolveSessionBytes deployEncoder a schnorrDecl none = .ok ⟨sessBytes, hSess⟩ ∧
      let vIns := hideAll deployModel 1
        (cast (congrArg (HList (LVal deployModel)) hIns.symm)
          (.cons (0 : Nat) (.cons (13 : Nat) .nil)))
      idealInitialPath deployModel a toySuite dByte 0 1 sessBytes vIns = some st0 ∧
      ∀ (outV : HList (RV deployModel 1) dIdeal.entry.outs),
        (∃ record givesV,
          Alone deployModel (fixedNonceSource 5) 1
            (Process.answerService idealServiceKey
              (LayerBuild.IdealRO.asOracle deployModel schnorrIdealRO)
              (dIdeal.run deployModel 1 vIns
                (cast (congrArg (HList deployModel.Val) hTakes.symm)
                  (.cons ([9, 0] : List (deployModel.Val dByte)) .nil))))
            record (.returned (outV, givesV))) ↔
        BareIdealReturn deployModel a toySuite ⟨toyLayoutModule, [], []⟩
          idealServiceKey 0 1
          (dIdeal.entry.shape.eventsWithAbsorb 0 1 [] id false)
          (fixedNonceSource 5) schnorrIdealRO
          (roleMeaning deployModel dIdeal.admitted.program dIdeal.callee 1 [] vIns)
          st0 ([9, 0] : List (deployModel.Val dByte)) 0 outV := by
  obtain ⟨a, dIdeal, hAdm, hProg, hDep⟩ := witness_deployIdeal_exists
  obtain ⟨w, hWEq⟩ := deployIdeal_ok_elim deployEncoder idealServiceKey a schnorrDecl dIdeal hDep
  have hAdmEq : dIdeal.admitted = a := by rw [hWEq]
  have hDeclEq : dIdeal.declaration = schnorrDecl := by rw [hWEq]
  have hDProg : dIdeal.admitted.program = witnessTyped := by rw [hAdmEq, hProg]
  obtain ⟨hIns, sessBytes, hSess, st0, hTakes, hRes, hInit, hIff⟩ :=
    witness_deployIdeal_link_of a dIdeal hProg hDep hDProg hDeclEq
  exact ⟨a, dIdeal, hIns, sessBytes, hSess, st0, hTakes, hAdm, hDep, hRes, hInit, hIff⟩

/-! ## Fail-closed declaration, session, retry, sample, and layout regressions (exact `Rule`) -/

private def deployFailsWith (decl : Declaration) (r : Rule) : Bool :=
  match deploy deployEncoder admittedSuite decl with
  | .error errs => errs.any (fun e => decide (e.rule = r))
  | .ok _ => false

private def deployIdealFailsWith (decl : Declaration) (r : Rule) : Bool :=
  match deployIdeal deployEncoder idealServiceKey admittedSuite decl with
  | .error errs => errs.any (fun e => decide (e.rule = r))
  | .ok _ => false

theorem deploy_fail_closed_declaration_and_session_controls :
    -- Mismatched `kinds.length`
    deployFailsWith { schnorrDecl with kinds := [.online] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with kinds := [.online] } .protocol = true ∧
    -- Unsupported non-empty `context`, `grinds`, `commits`, `pins`
    deployFailsWith { schnorrDecl with context := [⟨99⟩] } .protocol = true ∧
    deployFailsWith { schnorrDecl with grinds := [⟨8, []⟩] } .protocol = true ∧
    deployFailsWith { schnorrDecl with commits := [⟨⟨1⟩, ⟨[]⟩, none, none⟩] } .protocol = true ∧
    deployFailsWith { schnorrDecl with pins := [⟨⟨[], ⟨12⟩⟩, ⟨1⟩, [0]⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with context := [⟨99⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with grinds := [⟨8, []⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with commits := [⟨⟨1⟩, ⟨[]⟩, none, none⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with pins := [⟨⟨[], ⟨12⟩⟩, ⟨1⟩, [0]⟩] } .protocol = true ∧
    -- Empty or non-byte `sessionTag` refused with `Rule.literal`
    deployFailsWith { schnorrDecl with construction := .derived toySuite (some []) } .literal = true ∧
    deployFailsWith { schnorrDecl with construction := .derived toySuite (some [300]) } .literal = true ∧
    deployIdealFailsWith { schnorrDecl with construction := .derived toySuite (some []) } .literal = true ∧
    deployIdealFailsWith { schnorrDecl with construction := .derived toySuite (some [300]) } .literal = true ∧
    -- Interactive declaration validation (`layout`, `samples`, `retry`, online count, `prover`)
    deployFailsWith { interactiveDecl with layout := some ⟨toyLayoutModule, [], []⟩ } .protocol = true ∧
    deployFailsWith { interactiveDecl with samples := some ⟨109⟩ } .protocol = true ∧
    deployFailsWith { interactiveDecl with kinds := [.online, .offline] } .protocol = true ∧
    deployFailsWith { interactiveDecl with prover := some 7 } .protocol = true ∧
    deployFailsWith { interactiveDecl with retry := some (2, ⟨[], ⟨409⟩⟩) } .attempt = true ∧
    -- Authored declaration with `samples` refused
    deployFailsWith { authoredDecl with samples := some ⟨109⟩ } .protocol = true ∧
    -- Missing layout / missing suite slots / non-derived `deployIdeal` / bogus `samples` in `deployIdeal`
    deployFailsWith { schnorrDecl with layout := none } .callee = true ∧
    deployFailsWith { schnorrDecl with construction := .derived toyIdealOnlySuite none } .callee = true ∧
    deployIdealFailsWith interactiveDecl .protocol = true ∧
    deployIdealFailsWith authoredDecl .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with samples := some ⟨9999⟩ } .callee = true := by
  decide +kernel

theorem deploy_fail_closed_retry_and_layout_controls :
    -- Retry targeting verifier-owned attempt refused with `Rule.attempt`
    deployFailsWith { schnorrDecl with entry := ⟨208⟩, retry := some (4, ⟨[], ⟨909⟩⟩) } .attempt = true ∧
    deployIdealFailsWith { schnorrDecl with entry := ⟨208⟩, retry := some (4, ⟨[], ⟨909⟩⟩) } .attempt = true ∧
    -- `abort` guard outside the declared retry target refused with `Rule.attempt`
    deployFailsWith { schnorrDecl with entry := ⟨209⟩, retry := some (4, ⟨[], ⟨940⟩⟩) } .attempt = true ∧
    deployIdealFailsWith { schnorrDecl with entry := ⟨209⟩, retry := some (4, ⟨[], ⟨940⟩⟩) } .attempt = true ∧
    -- Retry bound `0` refused with `Rule.attempt`
    deployFailsWith { retrySchnorrDecl with retry := some (0, ⟨[], ⟨409⟩⟩) } .attempt = true ∧
    deployIdealFailsWith { retrySchnorrDecl with retry := some (0, ⟨[], ⟨409⟩⟩) } .attempt = true ∧
    -- Unknown / duplicate / wrong-kind `layout.carry`
    deployFailsWith { schnorrDecl with layout := some ⟨toyLayoutModule, [⟨[], ⟨999⟩⟩], []⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with layout := some ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩, ⟨[], ⟨13⟩⟩], []⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with layout := some ⟨toyLayoutModule, [⟨[], ⟨12⟩⟩], []⟩ } .protocol = true ∧
    -- Unknown / duplicate / wrong-kind `layout.recover`
    deployFailsWith { schnorrDecl with
      layout := some ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩], [(⟨[], ⟨999⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with
      layout := some ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩], [(⟨[], ⟨12⟩⟩, ⟨108⟩), (⟨[], ⟨12⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with
      layout := some ⟨toyLayoutModule, [], [(⟨[], ⟨13⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    -- Compact `recover` refused on non-straight-line `.choose` protocol (streaming accepted above)
    deployFailsWith { branchingStreamingDecl with
      layout := some ⟨toyLayoutModule, [⟨[], ⟨513⟩⟩], [(⟨[], ⟨512⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    -- Nested self-retry detected by `Shape.noNestedAttempt`
    Shape.noNestedAttempt (V := deployVocab) ⟨[], ⟨500⟩⟩ []
      (.attempt ⟨500⟩ [0] (.attempt ⟨500⟩ [0] .nil .nil) .nil) = false := by
  decide +kernel

end Zkc.Core.Tests.Deployment
