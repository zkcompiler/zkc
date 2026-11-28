import Zkc.Runtime

/-!
# Cryptographic primitive, codec, and CFRG draft-04 vector tests (`Zkc.Tests.Runtime.Crypto`)
-/

namespace Zkc.Tests.Runtime

open Zkc.Runtime
open Zkc.Runtime.Crypto

abbrev TestResult := String × Bool × String

def check (name : String) (ok : Bool) (detail : String := "") : TestResult :=
  (name, ok, detail)

/-- Unit checks for finite fields, BLS12-381 `G1`, hashes/XOFs/Poseidon2, canonical codecs,
and all 33 CFRG `draft-irtf-cfrg-fiat-shamir-04` test vectors (direct + Core end-to-end). -/
def runCryptoSuite : IO (List TestResult) := do
  let mut res : List TestResult := []

  -- 1. Finite-field arithmetic & 2-adic roots
  let p := koalaBearOrder
  let r := bls12381FrOrder
  let kbRoot := primeTwoAdicRoot koalaBearTwoAdicGen 24 p 24
  let kbHalf := modPow kbRoot (2 ^ 23) p
  let kbFull := modPow kbRoot (2 ^ 24) p
  res := res ++ [
    check "Fields: KoalaBear 2^24-th root exact order"
      (kbFull == 1 && kbHalf == p - 1) s!"w^(2^23)={kbHalf}, w^(2^24)={kbFull}"
  ]

  let frRoot := primeTwoAdicRoot bls12381FrTwoAdicGen 32 r 32
  let frHalf := modPow frRoot (2 ^ 31) r
  let frFull := modPow frRoot (2 ^ 32) r
  res := res ++ [
    check "Fields: BLS12-381 Fr 2^32-th root exact order"
      (frFull == 1 && frHalf == r - 1) "exact"
  ]

  let a4 : List Nat := [17, 42, 99991, 1234567]
  let inv4 := ext4Inv a4
  let prod4 := ext4Mul a4 inv4
  res := res ++ [
    check "Fields: KoalaBear4 a * inv(a) == 1"
      (prod4 == ext4One) s!"{reprStr prod4}",
    check "Fields: LE/BE 8-byte round-trip"
      (fromLeBytes (leBytes 8 0x0123456789ABCDEF) == 0x0123456789ABCDEF &&
       fromBeBytes (beBytes 8 0x0123456789ABCDEF) == 0x0123456789ABCDEF) "ok"
  ]

  -- 2. BLS12-381 G1 arithmetic & ZCash 48-byte compression
  let g := g1Generator
  let g2 := g1Scale g 2
  let g3 := g1Scale g 3
  let g5 := g1Scale g 5
  let gPrev := g1Scale g (r - 1)
  let cG := compressG1 g
  let cInf := compressG1 none
  let c5 := compressG1 g5
  let cPrev := compressG1 gPrev
  -- Negative controls for decompressG1:
  -- off-curve x = 0 -> x^3 + 4 = 4 (Wait: 4 is a square 2^2! Use x = 5: check non-residue or wrong flag)
  let badShort := cG.take 47
  let badUncompressed := (cG.headD 0 &&& 0x7f) :: cG.tail
  -- Non-canonical x >= q: all 0x1f / 0xff bytes with compression bit 0x80
  let badNonCanon := 0x9f :: List.replicate 47 0xff
  -- Point on curve (0, 2) is NOT in the prime-order subgroup G1 (cofactor h != 1)
  let nonSubgroup := compressG1 (some (0, 2))
  res := res ++ [
    check "Curve: G1 generator on-curve & in prime-order subgroup"
      (g1OnCurve g && g1InGroup g) "ok",
    check "Curve: [0]G = O, [1]G = G, [r]G = O, [r-1]G + G = O"
      (g1Scale g 0 == none && g1Scale g 1 == g && g1Scale g r == none && g1Add gPrev g == none) "ok",
    check "Curve: G + G == [2]G and [2]G + [3]G == [5]G"
      (g1Add g g == g2 && g1Add g2 g3 == g5 && g1Sub g5 g2 == g3) "ok",
    check "Curve: ZCash 48B compress/decompress round-trip (O, G, 5G, (r-1)G)"
      (cG.length == 48 && cInf.length == 48 &&
       decompressG1 cInf == some none &&
       decompressG1 cG == some g &&
       decompressG1 c5 == some g5 &&
       decompressG1 cPrev == some gPrev) "48B",
    check "Curve: decompressG1 rejects truncated, uncompressed, x>=q, and non-subgroup (0,2)"
      (decompressG1 badShort == none &&
       decompressG1 badUncompressed == none &&
       decompressG1 badNonCanon == none &&
       g1OnCurve (some (0, 2)) && !g1InGroup (some (0, 2)) &&
       decompressG1 nonSubgroup == none) "all rejected"
  ]

  -- 3. Hash / XOF / Poseidon2 NIST & Ethereum reference vectors
  let shaEmpty := bytesToHex (sha256Bytes [])
  let shaAbc := bytesToHex (sha256Bytes (utf8Bytes "abc"))
  let kecEmpty := bytesToHex (keccak256Bytes [])
  let kecAbc := bytesToHex (keccak256Bytes (utf8Bytes "abc"))
  let s128a := shake128Bytes (utf8Bytes "abc") 32
  let s128b := shake128Bytes (utf8Bytes "abd") 32
  let s256 := shake256Bytes (utf8Bytes "abc") 64
  let ts128 := turboShake128Bytes (utf8Bytes "abc") 32
  let p2a := Poseidon2KoalaBear.permute (Array.replicate 16 0)
  let p2b := Poseidon2KoalaBear.permute ((Array.replicate 16 0).set! 0 1)
  res := res ++ [
    check "Hash: SHA-256(\"\") NIST vector"
      (shaEmpty == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855") shaEmpty,
    check "Hash: SHA-256(\"abc\") NIST vector"
      (shaAbc == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") shaAbc,
    check "Hash: Keccak-256(\"\") Ethereum vector"
      (kecEmpty == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470") kecEmpty,
    check "Hash: Keccak-256(\"abc\") Ethereum vector"
      (kecAbc == "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45") kecAbc,
    check "Hash: SHAKE128 / SHAKE256 / TurboSHAKE128 lengths & distinctness"
      (s128a.length == 32 && s128a != s128b && s256.length == 64 && ts128.length == 32 && ts128 != s128a) "ok",
    check "Hash: Poseidon2-KoalaBear determinism & avalanche"
      (p2a.size == 16 && p2b.size == 16 && p2a != p2b &&
       p2a == Poseidon2KoalaBear.permute (Array.replicate 16 0) &&
       p2a.toList.all (· < p)) "16 lanes"
  ]

  -- 4. Verified canonical codecs (`formatKoalaBear`, `formatBls12381Fr`, `formatKoalaBear4`)
  let kbEnc := formatKoalaBear.write 123456789
  let kbOver := leBytes 4 koalaBearOrder
  let frVal := r - 7
  let frEnc := formatBls12381Fr.write frVal
  let frOver := leBytes 32 r
  let kb4Enc := formatKoalaBear4.write a4
  let kb4Bad := leBytes 4 koalaBearOrder ++ kb4Enc.drop 4
  res := res ++ [
    check "Codecs: formatKoalaBear round-trip & >= p rejection"
      (formatKoalaBear.read kbEnc == some (123456789, []) &&
       formatKoalaBear.read kbOver == none &&
       formatKoalaBear.read (kbEnc.take 3) == none) "4B",
    check "Codecs: formatBls12381Fr round-trip & >= r rejection"
      (formatBls12381Fr.read frEnc == some (frVal, []) &&
       formatBls12381Fr.read frOver == none &&
       formatBls12381Fr.read (frEnc.take 31) == none) "32B",
    check "Codecs: formatKoalaBear4 round-trip & non-canonical lane rejection"
      (formatKoalaBear4.read kb4Enc == some (a4, []) &&
       formatKoalaBear4.read kb4Bad == none) "16B"
  ]

  -- 5. All 33 CFRG `draft-irtf-cfrg-fiat-shamir-04` vectors (direct + end-to-end Core)
  let (_, cfrgRes) ← CfrgVectors.runAllCfrgVectors
  res := res ++ cfrgRes
  return res

end Zkc.Tests.Runtime
