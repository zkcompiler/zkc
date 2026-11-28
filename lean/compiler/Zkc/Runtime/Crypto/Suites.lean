module

public import Zkc.Runtime.Crypto.Curve
public import Zkc.Runtime.Crypto.Hash

@[expose] public section
set_option autoImplicit false

/-!
Concrete Fiat–Shamir transcript suites and signature helpers for `ZkcRuntime`:
1. **Merlin 1.0 / STROBE-128** (`suite.merlin3.bls12-381.fr64be/0` and `suite.schnorr-signature`)
2. **CFRG `draft-irtf-cfrg-fiat-shamir-04` Duplex** for both `SHAKE128` (`suite.cfrg.shake128/0`)
   and `TurboSHAKE128` (`suite.cfrg.turboshake128/0`), including exact Section 4.2 `Duplex` and
   Section 4.3 `deriveSessionId`
3. **Poseidon2-KoalaBear Duplex** (`suite.poseidon2-duplex.koala-bear/0`), operating over native
   `koala-bear` field elements
4. **Signature helpers**: deterministic `signature::nonce`, `signature::commitment` recovery,
   and `signature::keygen`
-/

namespace Zkc.Runtime.Crypto

/-! ## 1. Merlin 1.0 / STROBE-128 -/

namespace Merlin

def rate : Nat := 166
def flagI : Nat := 1
def flagA : Nat := 2
def flagC : Nat := 4
def flagM : Nat := 16
def flagK : Nat := 32

structure Strobe where
  state : ByteArray
  position : Nat
  begun : Nat
  flags : Nat

namespace Strobe

def xorAt (state : ByteArray) (index value : Nat) : ByteArray :=
  state.set! index (state.get! index ^^^ value.toUInt8)

def runF (s : Strobe) : Strobe :=
  let st := xorAt s.state s.position s.begun
  let st := xorAt st (s.position + 1) 0x04
  let st := xorAt st (rate + 1) 0x80
  { s with state := Keccak.permute st 24, position := 0, begun := 0 }

def absorb (s : Strobe) (data : List Nat) : Strobe :=
  data.foldl (init := s) fun s byte =>
    let s := { s with state := xorAt s.state s.position byte, position := s.position + 1 }
    if s.position == rate then s.runF else s

def squeeze (s : Strobe) (count : Nat) : List Nat × Strobe := Id.run do
  let mut st := s
  let mut out : Array Nat := Array.emptyWithCapacity count
  for _ in [0:count] do
    out := out.push (st.state.get! st.position).toNat
    st := { st with state := st.state.set! st.position 0, position := st.position + 1 }
    if st.position == rate then st := st.runF
  return (out.toList, st)

def beginOperation (s : Strobe) (flags : Nat) (more : Bool) : Strobe :=
  if more then s
  else
    let prev := s.begun
    let s := { s with begun := s.position + 1, flags }
    let s := s.absorb [prev, flags]
    if flags &&& (flagC ||| flagK) != 0 && s.position != 0 then s.runF else s

def metaAd (s : Strobe) (data : List Nat) (more : Bool) : Strobe :=
  (s.beginOperation (flagM ||| flagA) more).absorb data

def ad (s : Strobe) (data : List Nat) (more : Bool) : Strobe :=
  (s.beginOperation flagA more).absorb data

def prf (s : Strobe) (count : Nat) (more : Bool) : List Nat × Strobe :=
  (s.beginOperation (flagI ||| flagA ||| flagC) more).squeeze count

def initialState : ByteArray := Id.run do
  let mut st := ByteArray.mk (Array.replicate 200 0)
  let header := [1, rate + 2, 1, 0, 1, 96] ++ utf8Bytes "STROBEv1.0.2"
  for (byte, idx) in header.zip (List.range header.length) do
    st := st.set! idx byte.toUInt8
  return Keccak.permute st 24

def new (label : List Nat) : Strobe :=
  ({ state := initialState, position := 0, begun := 0, flags := 0 } : Strobe).metaAd label false

end Strobe

structure State where
  strobe : Strobe

def start (identity : List Nat) : State :=
  let s := Strobe.new (utf8Bytes "Merlin v1.0")
  let s := s.metaAd (utf8Bytes "dom-sep") false
  let s := s.metaAd (leBytes 4 identity.length) true
  ⟨s.ad identity false⟩

def absorb (st : State) (label message : List Nat) : State :=
  let s := st.strobe.metaAd label false
  let s := s.metaAd (leBytes 4 message.length) true
  ⟨s.ad message false⟩

def challengeBytes (st : State) (label : List Nat) (count : Nat) : List Nat × State :=
  let s := st.strobe.metaAd label false
  let s := s.metaAd (leBytes 4 count) true
  let (bs, s) := s.prf count false
  (bs, ⟨s⟩)

/-- Derive a BLS12-381 `Fr` scalar via 64 big-endian challenge bytes reduced mod `Fr` (`fr64be`). -/
def deriveFr (st : State) (label : List Nat) : Nat × State :=
  let (bs, st') := challengeBytes st label 64
  (fromBeBytes bs % bls12381FrOrder, st')

/-- Derive a `KoalaBear` field element via 16 little-endian challenge bytes reduced mod `p`. -/
def deriveKoalaBear (st : State) (label : List Nat) : Nat × State :=
  let (bs, st') := challengeBytes st label 16
  (fromLeBytes bs % koalaBearOrder, st')

/-- Derive a `KoalaBear4` element via 4 × 16 challenge bytes. -/
def deriveKoalaBear4 (st : State) (label : List Nat) : List Nat × State :=
  let (bs, st') := challengeBytes st label 64
  let c0 := fromLeBytes (bs.take 16) % koalaBearOrder
  let c1 := fromLeBytes ((bs.drop 16).take 16) % koalaBearOrder
  let c2 := fromLeBytes ((bs.drop 32).take 16) % koalaBearOrder
  let c3 := fromLeBytes (bs.drop 48) % koalaBearOrder
  ([c0, c1, c2, c3], st')

/-- Derive a `fin bound` value via 16 little-endian challenge bytes reduced mod `bound`. -/
def deriveFin (st : State) (label : List Nat) (bound : Nat) : Nat × State :=
  let (bs, st') := challengeBytes st label 16
  (if bound == 0 then 0 else fromLeBytes bs % bound, st')

/-- Derive a `bool` via 1 challenge byte (LSB). -/
def deriveBool (st : State) (label : List Nat) : Bool × State :=
  let (bs, st') := challengeBytes st label 1
  (bs.headD 0 % 2 == 1, st')

end Merlin

/-! ## 2. CFRG `draft-irtf-cfrg-fiat-shamir-04` Duplex -/

namespace Cfrg

inductive Variant where
  | shake128
  | turboShake128
  deriving DecidableEq, Repr

def xof (v : Variant) (msg : ByteArray) (outLen : Nat) : ByteArray :=
  match v with
  | .shake128 => shake128 msg outLen
  | .turboShake128 => turboShake128 msg outLen

/-- Rate `R = 168` bytes for both SHAKE128 and TurboSHAKE128 (Section 9 of draft-04). -/
def rate : Nat := 168

/-- Section 4.2 Duplex state: absorbed byte stream `m` (padded 32B session ID prefix + absorbed data)
and byte offset into the current squeeze stream. -/
structure Duplex where
  variant : Variant
  m : ByteArray
  offset : Nat

/-- Construct a CFRG duplex directly from a 32-byte `sessionId` (padded with `R - 32` zero bytes). -/
def initRaw (v : Variant) (sessionId : ByteArray) : Duplex := Id.run do
  let mut buf := ByteArray.emptyWithCapacity rate
  for i in [0:32] do
    buf := buf.push (if i < sessionId.size then sessionId.get! i else 0)
  for _ in [0:(rate - 32)] do
    buf := buf.push 0
  return { variant := v, m := buf, offset := 0 }

/-- Absorb bytes into the duplex; resets squeeze offset when non-empty (Section 4.2). -/
def absorbRaw (d : Duplex) (data : ByteArray) : Duplex :=
  if data.size == 0 then d
  else { d with m := d.m ++ data, offset := 0 }

/-- Squeeze `n` bytes from the duplex, advancing `offset` (Section 4.2). -/
def squeezeRaw (d : Duplex) (n : Nat) : ByteArray × Duplex :=
  let full := xof d.variant d.m (d.offset + n)
  let out := full.extract d.offset (d.offset + n)
  (out, { d with offset := d.offset + n })

/-- Section 4.3 `derive_session_id`: initializes a Duplex with `"irtf-cfrg-fiat-shamir/session-id"`,
absorbs `tag`, and squeezes 32 bytes. -/
def deriveSessionId (v : Variant) (tag : ByteArray) : ByteArray :=
  let d := initRaw v "irtf-cfrg-fiat-shamir/session-id".toUTF8
  let d := absorbRaw d tag
  (squeezeRaw d 32).1

/-- Start a CFRG duplex from arbitrary identity bytes: if `identity` is tagged as a 32-byte raw
session ID (`identity.length == 32` when called directly via `startRaw`), use `initRaw`; for
general scheme identity bytes, derive the 32-byte session ID via `deriveSessionId`. -/
def start (v : Variant) (identity : List Nat) : Duplex :=
  let sid := deriveSessionId v (toByteArray identity)
  initRaw v sid

/-- Start a CFRG duplex from an explicit 32-byte session identifier without re-hashing. -/
def startRaw (v : Variant) (sessionId : List Nat) : Duplex :=
  initRaw v (toByteArray sessionId)

/-- Absorb a message into the CFRG duplex (ignores Core's extra `label` bytes because CFRG draft-04
duplex absorbs raw canonical message bytes directly without per-message framing labels). -/
def absorb (d : Duplex) (_label message : List Nat) : Duplex :=
  absorbRaw d (toByteArray message)

/-- Squeeze `count` bytes from the CFRG duplex. -/
def squeeze (d : Duplex) (count : Nat) : List Nat × Duplex :=
  let (ba, d') := squeezeRaw d count
  (ofByteArray ba, d')

/-- Derive a prime-field scalar mod `order` by squeezing `byteCount` little-endian bytes (draft-04 §4.4). -/
def derivePrime (d : Duplex) (byteCount order : Nat) : Nat × Duplex :=
  let (bs, d') := squeeze d byteCount
  (if order == 0 then 0 else fromLeBytes bs % order, d')

/-- Derive a BLS12-381 `Fr` scalar (48 little-endian bytes mod `r`, >128 bits excess). -/
def deriveFr (d : Duplex) : Nat × Duplex :=
  derivePrime d 48 bls12381FrOrder

/-- Derive a `KoalaBear` field element (16 little-endian bytes mod `p`). -/
def deriveKoalaBear (d : Duplex) : Nat × Duplex :=
  derivePrime d 16 koalaBearOrder

/-- Derive a `KoalaBear4` element (4 × 16 little-endian bytes). -/
def deriveKoalaBear4 (d : Duplex) : List Nat × Duplex :=
  let (bs, d') := squeeze d 64
  ([fromLeBytes (bs.take 16) % koalaBearOrder,
    fromLeBytes ((bs.drop 16).take 16) % koalaBearOrder,
    fromLeBytes ((bs.drop 32).take 16) % koalaBearOrder,
    fromLeBytes (bs.drop 48) % koalaBearOrder], d')

/-- Derive a `fin bound` value using the minimal byte width (exact for draft-04 C.5.1 `Mersenne31`
where `bound = 2^31 - 1`, `byteWidth = 4`, as well as arbitrary `fin bound`). -/
def deriveFinExact (d : Duplex) (bound : Nat) : Nat × Duplex :=
  let ns := if bound ≤ 1 then 0 else (bound.log2 + 8) / 8
  let (bs, d') := squeeze d ns
  (if bound == 0 then 0 else fromLeBytes bs % bound, d')

def deriveBool (d : Duplex) : Bool × Duplex :=
  let (bs, d') := squeeze d 1
  (bs.headD 0 % 2 == 1, d')

end Cfrg

/-! ## 3. Poseidon2-KoalaBear Duplex (`suite.poseidon2-duplex.koala-bear/0`) -/

namespace Poseidon2Suite

/-- Sponge duplex state over 16 KoalaBear field elements (rate 8, capacity 8). -/
structure Duplex where
  state : Array Nat
  pos : Nat
  squeezing : Bool

def empty : Duplex :=
  { state := Array.replicate Poseidon2KoalaBear.width 0, pos := 0, squeezing := false }

/-- Pack raw bytes into KoalaBear field elements (3 bytes per element, strictly `< 2^24 < p`). -/
def packBytesToFields (bs : List Nat) : List Nat :=
  go bs
where
  go : List Nat → List Nat
    | [] => []
    | [b0] => [b0 % 256]
    | [b0, b1] => [(b0 % 256) + 256 * (b1 % 256)]
    | b0 :: b1 :: b2 :: rest =>
        ((b0 % 256) + 256 * (b1 % 256) + 65536 * (b2 % 256)) :: go rest

/-- Absorb a sequence of KoalaBear field elements (overwrite-rate sponge). -/
def absorbFields (d : Duplex) (elems : List Nat) : Duplex := Id.run do
  let p := koalaBearOrder
  let mut st := d.state
  let mut pos := if d.squeezing then 0 else d.pos
  for e in elems do
    st := st.set! pos ((st[pos]! + e % p) % p)
    pos := pos + 1
    if pos == Poseidon2KoalaBear.rate then
      st := Poseidon2KoalaBear.permute st
      pos := 0
  return { state := st, pos, squeezing := false }

/-- Squeeze `count` native KoalaBear field elements from the duplex. -/
def squeezeFields (d : Duplex) (count : Nat) : List Nat × Duplex := Id.run do
  let mut st := d.state
  let mut pos := d.pos
  if !d.squeezing then
    st := Poseidon2KoalaBear.permute st
    pos := 0
  let mut out : Array Nat := Array.emptyWithCapacity count
  for _ in [0:count] do
    if pos == Poseidon2KoalaBear.rate then
      st := Poseidon2KoalaBear.permute st
      pos := 0
    out := out.push (st[pos]! % koalaBearOrder)
    pos := pos + 1
  return (out.toList, { state := st, pos, squeezing := true })

def start (identity : List Nat) : Duplex :=
  let packed := packBytesToFields identity
  let d := absorbFields empty (packed.length :: packed)
  { state := Poseidon2KoalaBear.permute d.state, pos := 0, squeezing := false }

def absorb (d : Duplex) (label units : List Nat) : Duplex :=
  let lblFields := packBytesToFields label
  absorbFields d (lblFields.length :: lblFields ++ (units.length :: units))

def deriveKoalaBear (d : Duplex) (label : List Nat) : Nat × Duplex :=
  let d1 := absorbFields d (0 :: packBytesToFields label)
  let (xs, d2) := squeezeFields d1 1
  (xs.headD 0 % koalaBearOrder, d2)

def deriveKoalaBear4 (d : Duplex) (label : List Nat) : List Nat × Duplex :=
  let d1 := absorbFields d (1 :: packBytesToFields label)
  let (xs, d2) := squeezeFields d1 4
  (ext4Norm xs, d2)

def deriveFin (d : Duplex) (label : List Nat) (bound : Nat) : Nat × Duplex :=
  let d1 := absorbFields d (2 :: packBytesToFields label)
  let (xs, d2) := squeezeFields d1 2
  let combined := xs.headD 0 + koalaBearOrder * xs.getD 1 0
  (if bound == 0 then 0 else combined % bound, d2)

def deriveBool (d : Duplex) (label : List Nat) : Bool × Duplex :=
  let (x, d') := deriveKoalaBear d label
  (x % 2 == 1, d')

def deriveFr (d : Duplex) (label : List Nat) : Nat × Duplex :=
  let d1 := absorbFields d (3 :: packBytesToFields label)
  let (xs, d2) := squeezeFields d1 12
  let v := xs.foldr (fun x acc => x + koalaBearOrder * acc) 0
  (v % bls12381FrOrder, d2)

end Poseidon2Suite

/-! ## 4. Signature helpers (`signature::nonce`, `signature::commitment`, `signature::keygen`) -/

namespace Signature

/-- Deterministic 64-byte nonce derivation (`signature::nonce`) via domain-separated SHAKE256. -/
def nonceBytes (secret : Nat) (contextBytes : List Nat) (site attempt : Nat) : List Nat :=
  let input :=
    utf8Bytes "zkc.signature.nonce/0" ++
    leBytes 32 (secret % bls12381FrOrder) ++
    leBytes 8 contextBytes.length ++ contextBytes ++
    leBytes 8 site ++ leBytes 8 attempt
  shake256Bytes input 64

/-- Deterministic `Fr` nonce scalar derived from prover inputs, session bytes, site bytes, attempt,
and call sequence number. -/
def nonceScalar (secret : Nat) (sessBytes siteBytes : List Nat) (attempt callSeq : Nat) : Nat :=
  let input :=
    utf8Bytes "zkc.signature.nonce.fr/0" ++
    leBytes 32 (secret % bls12381FrOrder) ++
    leBytes 8 sessBytes.length ++ sessBytes ++
    leBytes 8 siteBytes.length ++ siteBytes ++
    leBytes 8 attempt ++ leBytes 8 callSeq
  let raw := fromBeBytes (shake256Bytes input 64) % bls12381FrOrder
  if raw == 0 then 1 else raw

/-- Recover the Schnorr commitment `R = base * response - point * challenge`. -/
def recoverCommitment (base point : G1Point) (challenge response : Nat) : G1Point :=
  g1Sub (g1Scale base response) (g1Scale point challenge)

/-- Recover the Schnorr commitment from canonically serialized `(base, point, ...)` statement bytes,
challenge, and response. -/
def recoverCommitmentFromStatementBytes (stmtBytes : List Nat) (challenge response : Nat) :
    Option G1Point := do
  let base ← decompressG1 (stmtBytes.take 48)
  let point ← decompressG1 ((stmtBytes.drop 48).take 48)
  pure (recoverCommitment base point challenge response)

/-- Derive a deterministic `(secret, G1::generator * secret)` keypair from a 32-byte seed. -/
def keygen (seed : List Nat) : Nat × G1Point :=
  let sk0 := fromBeBytes (shake256Bytes (utf8Bytes "zkc.signature.keygen/0" ++ seed) 64) % bls12381FrOrder
  let sk := if sk0 == 0 then 1 else sk0
  (sk, g1OfScalar sk)

end Signature

end Zkc.Runtime.Crypto
