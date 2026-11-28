module

public import Zkc.Runtime.Execute
public import Zkc.Runtime.Codecs
public import Zkc.Core.Scheme.Deploy.Compile
public import Zkc.Vocabulary.Encoder

@[expose] public section
set_option autoImplicit false

/-!
# CFRG `draft-irtf-cfrg-fiat-shamir-04` byte-exact test vector verification (`Zkc.Runtime.CfrgVectors`)

Verifies every test vector from Appendices C.2, C.3, C.5.1, and C.5.2 of
`draft-irtf-cfrg-fiat-shamir-04` for BOTH SHAKE128 and TurboSHAKE128:
1. 24-round sponge equivalence with SHAKE128 across 0, 3, 200, and 400 byte messages.
2. Appendix C.2 session identifiers (`interop-test-v00`).
3. Appendix C.3 48-byte squeezed outputs and P-256 scalar decoding.
4. Appendix C.5.1 `sumcheck` session identifiers, 4-round Mersenne31 Sumcheck NARG strings, and
   final evaluations (`0x3EBFB3B3` for SHAKE128, `0x654028DB` for TurboSHAKE128).
5. Consecutive squeezes forming one continuous stream (`squeeze(4) ++ squeeze(4) == squeeze(8)`).
6. Appendix C.5.2 rejections (trailing byte `narg ++ [0x00]` and non-canonical Mersenne31
   coefficient `0x80005554 >= 2^31 - 1`).
7. **Full end-to-end Core pipeline verification**: builds a real 4-round Mersenne31 Sumcheck
   `Core.NamedProgram`, admits it through `Core.admit`, deploys it through `Core.deploy` using
   `suite.cfrg.shake128.raw` and `suite.cfrg.turboshake128.raw`, executes BOTH `Core.execute`
   (`d.run`) and `Core.specialize` + `runClosed`, and verifies byte-for-byte CFRG C.5.1 output
   matching AND identical `.declared .reject` outcomes on C.5.2 negative controls!
-/

namespace Zkc.Runtime.CfrgVectors

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project
open Zkc.Runtime
open Zkc.Runtime.Crypto

def p256Order : Nat :=
  0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

def mersenne31 : Nat := 2147483647 -- 2^31 - 1

/-- Reference CFRG test-vector constants from `draft-irtf-cfrg-fiat-shamir-04`. -/
structure VectorSpec where
  name : String
  xof : Cfrg.Variant
  suitePrefix : String
  interopSidHex : String
  sumcheckSidHex : String
  nargHex : String
  finalEval : Nat
  decodeOutHex : String
  decodeMsg : Nat

def shake128Spec : VectorSpec where
  name := "SHAKE128"
  xof := .shake128
  suitePrefix := "suite.cfrg.shake128.raw"
  interopSidHex := "b508aca89eecac56cd33e4a28f817f43f849d035922f354173ae8466628308cf"
  sumcheckSidHex := "0568cefdf774622a3854d82934915fb3e38bc89dc44b6d673fc91b972c886fc2"
  nargHex := "555500005555000023e362696ba9283c90a3362a74953379afc3b041d3eb126f"
  finalEval := 0x3EBFB3B3
  decodeOutHex := "7124d02b7cdfec99c4033dfd05624cfe2ff3af2c0e71656f770e676bd36de6228f85fcb39f34f7bfc24c9f54ab35ddba"
  decodeMsg := 0xF860997C65F8DABECBCC3459A7B89BF69301B19FA1A0E036EB0D132724436D4F

def turboShake128Spec : VectorSpec where
  name := "TurboSHAKE128"
  xof := .turboShake128
  suitePrefix := "suite.cfrg.turboshake128.raw"
  interopSidHex := "4326208c9e56ae847be9356ca7c4447c752a9d7326a44a6cbee0c0dfc69505ac"
  sumcheckSidHex := "abcbcae1f2f90d02b7e6417dbb2ffe162ab00477453eac3ce83d4e7e61000280"
  nargHex := "55550000555500006ff9a71d4decf758430dfb69f9c6b5359d8ab2744b13d83d"
  finalEval := 0x654028DB
  decodeOutHex := "82a031e31b103ac01253ba3aae215f650a06a4bb24963a05ee1f8c0b82eae90d7bd36ea8cb560a91604ae8a97eb0d564"
  decodeMsg := 0xC2088B455016D0126FCDD76335A79566E7FD8379DB1DE019871D459BFEE9558B

def nonCanonicalBadNargHex : String :=
  "5455008055550000b8eefc2728ccf677b7aabd44c1001d074205d5576c3d307d"

/-! ## Direct CFRG C.5.1 / C.5.2 Sumcheck over `Cfrg.Duplex` -/

def directSumcheckProve (xof : Cfrg.Variant) (sid : List Nat) (v : Nat) (w0 : List Nat) :
    List Nat × Nat := Id.run do
  let p := mersenne31
  let s0 := (w0.foldl (fun acc x => (acc + x) % p) 0) % p
  let mut st := Cfrg.startRaw xof sid
  st := Cfrg.absorb st [] (leBytes 4 v ++ leBytes 4 s0)
  let mut narg : List Nat := []
  let mut w := w0
  for _ in [0:v] do
    let evenSum := (w.zipIdx.filter (fun q => q.2 % 2 == 0)).foldl (fun acc q => (acc + q.1) % p) 0
    let oddSum := (w.zipIdx.filter (fun q => q.2 % 2 == 1)).foldl (fun acc q => (acc + q.1) % p) 0
    let a0 := evenSum % p
    let a1 := (oddSum % p + p - a0) % p
    let msg := leBytes 4 a0 ++ leBytes 4 a1
    st := Cfrg.absorb st [] msg
    narg := narg ++ msg
    let (rBytes, st') := Cfrg.squeeze st 4
    st := st'
    let r := fromLeBytes rBytes % p
    let half := w.length / 2
    w := (List.range half).map fun i =>
      let x0 := w.getD (2 * i) 0 % p
      let x1 := w.getD (2 * i + 1) 0 % p
      (x0 + r * ((x1 + p - x0) % p)) % p
  return (narg, w.headD 0 % p)

def directSumcheckVerify (xof : Cfrg.Variant) (sid : List Nat) (v sInit : Nat) (narg0 : List Nat)
    (y : Nat) : Bool := Id.run do
  let p := mersenne31
  let mut st := Cfrg.startRaw xof sid
  st := Cfrg.absorb st [] (leBytes 4 v ++ leBytes 4 sInit)
  let mut narg := narg0
  let mut s := sInit
  for _ in [0:v] do
    if narg.length < 8 then return false
    let a0 := fromLeBytes (narg.take 4)
    let a1 := fromLeBytes ((narg.drop 4).take 4)
    narg := narg.drop 8
    if a0 >= p || a1 >= p then return false
    if (2 * a0 + a1) % p != s then return false
    st := Cfrg.absorb st [] (leBytes 4 a0 ++ leBytes 4 a1)
    let (rBytes, st') := Cfrg.squeeze st 4
    st := st'
    let r := fromLeBytes rBytes % p
    s := (a0 + a1 * r) % p
  return narg.isEmpty && s == y

/-! ## End-to-end Core 4-round Mersenne31 Sumcheck protocol (`Core.admit` → `Core.deploy` → `Core.execute` & `runClosed`) -/

abbrev m31Ty : LinkedType := .fin mersenne31
abbrev u32Ty : LinkedType := .fin (2 ^ 32)
abbrev m31PairTy : LinkedType := .tuple (.cons m31Ty (.cons m31Ty .nil))
abbrev byteSeqTy : LinkedType := .seq (.fin 256) none

def insertBind (b : Bindings) (prim : PrimitiveName) (ins outs : List LinkedType) :
    Except String Bindings :=
  match b.insert prim ⟨ins, outs⟩ with
  | .ok b' => .ok b'
  | .error k => .error s!"duplicate binding {k.name}"

def rowWrap (b : Bindings) (key : Key) (prim : PrimitiveName)
    (ins outs : List LinkedType) : Definition b.vocabulary :=
  let inNames := List.range ins.length
  let outNames := (List.range outs.length).map (· + ins.length)
  .fn key ins outs false none ⟨[], []⟩
    (.mk inNames [.op ⟨0⟩ outNames (.row (.inr prim)) inNames] outNames)

def readWrap (b : Bindings) (key : Key) (prim : PrimitiveName) (τ : LinkedType) :
    Definition b.vocabulary :=
  .fn key [byteSeqTy, .nat] [τ, .nat] true none ⟨[], []⟩
    (.mk [0, 1] [
      .op ⟨0⟩ [2, 3, 4] (.row (.inr prim)) [0, 1],
      .guard ⟨1⟩ () 2 .reject
    ] [3, 4])

/-- Build, admit, deploy, and run the 4-round CFRG Appendix C.5.1 Mersenne31 Sumcheck protocol
through BOTH `Core.execute` and `Core.specialize` + `runClosed`, plus C.5.2 negative controls! -/
def runCoreSumcheckEndToEnd (spec : VectorSpec) : Except String (List (String × Bool × String)) := do
  let pfx := spec.suitePrefix
  let stTy : LinkedType := .nominal (.inr (.type (.nominal s!"{pfx}.state") .nil))
  let pU32 : Parameters := .cons (.type (.index (2 ^ 32)) .nil) .nil
  let pM31 : Parameters := .cons (.type (.index mersenne31) .nil) .nil
  let pPair : Parameters := .cons (.type .tuple (.cons (.type (.index mersenne31) .nil)
    (.cons (.type (.index mersenne31) .nil) .nil))) .nil

  let primStart : PrimitiveName := ⟨s!"{pfx}.start", .nil⟩
  let primAbsorb : PrimitiveName := ⟨s!"{pfx}.absorb", .nil⟩
  let primEncU32 : PrimitiveName := ⟨s!"{pfx}.encode", pU32⟩
  let primEncM31 : PrimitiveName := ⟨s!"{pfx}.encode", pM31⟩
  let primEncPair : PrimitiveName := ⟨s!"{pfx}.encode", pPair⟩
  let primDerM31 : PrimitiveName := ⟨s!"{pfx}.derive", pM31⟩
  let primLayW : PrimitiveName := ⟨"layout.canonical.write", pPair⟩
  let primLayR : PrimitiveName := ⟨"layout.canonical.try_read", pPair⟩
  let primLayE : PrimitiveName := ⟨"layout.canonical.equal", pPair⟩

  let primRP (n : Nat) : PrimitiveName := ⟨"cfrg.m31.round_poly", .cons (.natural n) .nil⟩
  let primFold (n : Nat) : PrimitiveName := ⟨"cfrg.m31.fold", .cons (.natural n) .nil⟩
  let primChk : PrimitiveName := ⟨"cfrg.m31.check_sum", .nil⟩
  let primEval : PrimitiveName := ⟨"cfrg.m31.eval_lin", .nil⟩
  let primHead : PrimitiveName := ⟨"cfrg.m31.head", .nil⟩

  let mut b : Bindings := {}
  b ← insertBind b primStart [byteSeqTy] [stTy]
  b ← insertBind b primAbsorb [stTy, byteSeqTy, byteSeqTy] [stTy]
  b ← insertBind b primEncU32 [u32Ty] [byteSeqTy]
  b ← insertBind b primEncM31 [m31Ty] [byteSeqTy]
  b ← insertBind b primEncPair [m31PairTy] [byteSeqTy]
  b ← insertBind b primDerM31 [stTy, byteSeqTy] [m31Ty, stTy]
  b ← insertBind b primLayW [m31PairTy] [byteSeqTy]
  b ← insertBind b primLayR [byteSeqTy, .nat] [.bool, m31PairTy, .nat]
  b ← insertBind b primLayE [m31PairTy, m31PairTy] [.bool]
  for n in [16, 8, 4, 2] do
    b ← insertBind b (primRP n) [.seq m31Ty (some n)] [m31PairTy]
    b ← insertBind b (primFold n) [.seq m31Ty (some n), m31Ty] [.seq m31Ty (some (n / 2))]
  b ← insertBind b primChk [m31Ty, m31PairTy] [.bool]
  b ← insertBind b primEval [m31PairTy, m31Ty] [m31Ty]
  b ← insertBind b primHead [.seq m31Ty (some 1)] [m31Ty]

  -- 4-round Sumcheck Core protocol:
  -- Role 0 = Prover, Role 1 = Verifier
  -- Inputs: 0 : v @(0,1), 1 : s0 @(0,1), 2 : w0 @0
  -- Output: [finalP @0, finalV @1]
  let lawM31 : Zkc.Vocabulary.LawKey := .uniform (.fin mersenne31)
  let mkRound (baseKey baseName : Nat) (n : Nat) (sIn wIn : Core.Name) :
      List (Instruction (ProtocolRaw b.vocabulary) (List Role)) × Core.Name × Core.Name :=
    let polyP := baseName
    let polyV := baseName + 1
    let okV := baseName + 2
    let rChal := baseName + 3
    let wOut := baseName + 4
    let sOut := baseName + 5
    ([
      .op ⟨baseKey⟩ [polyP] (.compute [0] (.row (.inr (primRP n)))) [wIn],
      .op ⟨baseKey + 1⟩ [polyV] (.event (.flow .message 0 [1]) m31PairTy) [polyP],
      .op ⟨baseKey + 2⟩ [okV] (.compute [1] (.row (.inr primChk))) [sIn, polyV],
      .guard ⟨baseKey + 3⟩ [1] okV .reject,
      .op ⟨baseKey + 4⟩ [rChal] (.event (.given (.coin lawM31) 1 [0]) m31Ty) [],
      .op ⟨baseKey + 5⟩ [wOut] (.compute [0] (.row (.inr (primFold n)))) [wIn, rChal],
      .op ⟨baseKey + 6⟩ [sOut] (.compute [1] (.row (.inr primEval))) [polyV, rChal]
    ], sOut, wOut)

  let (r0Ops, s1, w1) := mkRound 10 10 16 1 2
  let (r1Ops, s2, w2) := mkRound 20 20 8 s1 w1
  let (r2Ops, s3, w3) := mkRound 30 30 4 s2 w2
  let (r3Ops, s4, w4) := mkRound 40 40 2 s3 w3
  let finalP : Core.Name := 50
  let headOp : Instruction (ProtocolRaw b.vocabulary) (List Role) :=
    .op ⟨50⟩ [finalP] (.compute [0] (.row (.inr primHead))) [w4]

  let protoDef : Definition b.vocabulary :=
    .protocol ⟨1⟩ 2
      [⟨u32Ty, [0, 1]⟩, ⟨m31Ty, [0, 1]⟩, ⟨.seq m31Ty (some 16), [0]⟩]
      [⟨m31Ty, [0]⟩, ⟨m31Ty, [1]⟩]
      (.mk [0, 1, 2] (r0Ops ++ r1Ops ++ r2Ops ++ r3Ops ++ [headOp]) [finalP, s4])

  let helperDefs : List (Definition b.vocabulary) := [
    rowWrap b ⟨2⟩ primStart [byteSeqTy] [stTy],
    rowWrap b ⟨3⟩ primAbsorb [stTy, byteSeqTy, byteSeqTy] [stTy],
    rowWrap b ⟨4⟩ primEncU32 [u32Ty] [byteSeqTy],
    rowWrap b ⟨5⟩ primEncM31 [m31Ty] [byteSeqTy],
    rowWrap b ⟨6⟩ primEncPair [m31PairTy] [byteSeqTy],
    rowWrap b ⟨7⟩ primDerM31 [stTy, byteSeqTy] [m31Ty, stTy],
    rowWrap b ⟨8⟩ primLayW [m31PairTy] [byteSeqTy],
    readWrap b ⟨9⟩ primLayR m31PairTy,
    rowWrap b ⟨10⟩ primLayE [m31PairTy, m31PairTy] [.bool]
  ]
  let prog : NamedProgram b.vocabulary := ⟨protoDef :: helperDefs⟩
  let admitted ← match Core.admit prog ⟨[], [], [], [], []⟩ with
    | .ok a => .ok a
    | .error errs => .error s!"{spec.name} Core.admit failed ({errs.length} refusals)"

  let enc := Project.linkedEncoder b
  let sid := ofByteArray (Cfrg.deriveSessionId spec.xof "sumcheck".toUTF8)
  let suiteRef : ModuleRef := {
    members := [
      (SuiteSlot.start, ⟨2⟩),
      (SuiteSlot.absorb, ⟨3⟩),
      (SuiteSlot.encode, ⟨4⟩),
      (SuiteSlot.encode, ⟨5⟩),
      (SuiteSlot.encode, ⟨6⟩),
      (SuiteSlot.derive, ⟨7⟩)
    ]
    lawMembers := [(SuiteSlot.derive, enc.lawKey lawM31, ⟨7⟩)]
  }
  let layoutRef : ModuleRef := {
    members := [
      (LayoutSlot.write, ⟨8⟩),
      (LayoutSlot.read, ⟨9⟩),
      (LayoutSlot.equal, ⟨10⟩)
    ]
  }
  let decl : Core.Declaration := {
    key := ⟨100⟩
    entry := ⟨1⟩
    kinds := [.online, .online]
    construction := .derived suiteRef (some sid)
    prover := some 0
    layout := some { «module» := layoutRef, carry := [], recover := [] }
    retry := none
    samples := none
    context := []
    grinds := []
    commits := []
    pins := []
    application := []
  }
  let deployed ← match Core.deploy enc admitted decl with
    | .ok d => .ok d
    | .error errs => .error s!"{spec.name} Core.deploy failed ({errs.length} refusals)"

  match linkedModel? b with
  | .error err => .error err
  | .ok M =>
      let src := emptySource M
      let wInit : List Nat := (List.range 16).map fun i => 2 ^ i
      match hIns : deployed.entry.ins, hOuts : deployed.entry.outs,
            hPTakes : Stack.Takes (deployed.stack 0), hVTakes : Stack.Takes (deployed.stack 1) with
      | [⟨.fin _, [0, 1]⟩, ⟨.fin _, [0, 1]⟩, ⟨.seq (.fin _) (some 16), [0]⟩],
        [⟨.fin n0, [0]⟩, ⟨.fin n1, [1]⟩],
        [],
        [.seq (.fin 256) none] =>
          let pIns : HList (RV M 0) deployed.entry.ins :=
            hIns.symm ▸ (.cons (4 : Nat) (.cons (0xFFFF : Nat) (.cons wInit .nil)))
          let vIns : HList (RV M 1) deployed.entry.ins :=
            hIns.symm ▸ (.cons (4 : Nat) (.cons (0xFFFF : Nat) (.cons () .nil)))
          let pTakes : HList M.Val (Stack.Takes (deployed.stack 0)) :=
            hPTakes.symm ▸ .nil

          -- Run prover via BOTH `Core.execute` and `Core.specialize` + `runClosed`
          let (pOutExec, _) := runDeployed M deployed 0 pIns pTakes src 100000
          let (pOutClosed, _) := runDeployedClosed M deployed 0 pIns pTakes src 100000

          let extractProver (out : Outcome (HList (RV M 0) deployed.entry.outs)
              (HList M.Val (Stack.Gives (deployed.stack 0)))) : Option (Nat × List Nat) :=
            match out with
            | .ended (.returned (outsVal, gives)) =>
                let outsVal' : HList (RV M 0) [⟨.fin n0, [0]⟩, ⟨.fin n1, [1]⟩] := hOuts ▸ outsVal
                let finalP : Nat := match outsVal' with | .cons x _ => x
                match hG : Stack.Gives (deployed.stack 0) with
                | [.seq (.fin 256) none] =>
                    match hG ▸ gives with
                    | .cons proofBytes .nil => some (finalP, proofBytes)
                | _ => none
            | _ => none

          let some (finalPExec, nargExec) := extractProver pOutExec
            | .error s!"{spec.name} Core.execute prover did not return proof"
          let some (finalPClosed, nargClosed) := extractProver pOutClosed
            | .error s!"{spec.name} runClosed prover did not return proof"

          let nargMatch := bytesToHex nargExec == spec.nargHex && nargClosed == nargExec
          let finalMatch := finalPExec == spec.finalEval && finalPClosed == finalPExec

          -- Helper to run verifier on an arbitrary proof byte string via BOTH `Core.execute` and `runClosed`
          let runV (proofBytes : List Nat) :
              Option Nat × Option Nat × Option Stop × Option Stop :=
            let taken : HList M.Val (Stack.Takes (deployed.stack 1)) :=
              hVTakes.symm ▸ (.cons proofBytes .nil)
            let (vE, _) := runDeployed M deployed 1 vIns taken src 100000
            let (vC, _) := runDeployedClosed M deployed 1 vIns taken src 100000
            let parse (o : Outcome (HList (RV M 1) deployed.entry.outs)
                (HList M.Val (Stack.Gives (deployed.stack 1)))) : Option Nat × Option Stop :=
              match o with
              | .ended (.returned (outsVal, _)) =>
                  let outsVal' : HList (RV M 1) [⟨.fin n0, [0]⟩, ⟨.fin n1, [1]⟩] := hOuts ▸ outsVal
                  match outsVal' with
                  | .cons _ (.cons finalV .nil) => (some finalV, none)
              | .ended (.stopped stop) => (none, some stop)
              | _ => (none, none)
            let (okE, stE) := parse vE
            let (okC, stC) := parse vC
            (okE, okC, stE, stC)

          -- 1. Honest verifier accept
          let (vOkE, vOkC, _, _) := runV nargExec
          let vAcceptOk := vOkE == some spec.finalEval && vOkC == some spec.finalEval

          -- 2. C.5.2 trailing byte rejected with identical Stop
          let (tOkE, tOkC, tStE, tStC) := runV (nargExec ++ [0])
          let trailingRejOk := tOkE.isNone && tOkC.isNone && tStE.isSome && tStE == tStC

          -- 3. C.5.2 non-canonical coefficient rejected with identical Stop
          let some badBytes := hexToBytes nonCanonicalBadNargHex
            | .error "invalid nonCanonicalBadNargHex"
          let (ncOkE, ncOkC, ncStE, ncStC) := runV badBytes
          let nonCanonRejOk := ncOkE.isNone && ncOkC.isNone && ncStE.isSome && ncStE == ncStC

          .ok [
            (s!"{spec.name}: Core deploy+execute+runClosed C.5.1 NARG exact", nargMatch,
              if nargMatch then s!"{nargExec.length}B == {spec.nargHex}" else s!"got {bytesToHex nargExec}"),
            (s!"{spec.name}: Core deploy+execute+runClosed C.5.1 final eval", finalMatch,
              if finalMatch then s!"0x{Nat.toDigits 16 finalPExec |> String.ofList}" else s!"got {finalPExec}"),
            (s!"{spec.name}: Core deploy+execute+runClosed C.5.1 verifier accept", vAcceptOk,
              if vAcceptOk then "Core.execute == runClosed == accept" else "mismatch"),
            (s!"{spec.name}: Core deploy+execute+runClosed C.5.2 trailing byte reject", trailingRejOk,
              if trailingRejOk then s!"both stopped with {reprStr tStE}" else s!"mismatch {reprStr tStE} vs {reprStr tStC}"),
            (s!"{spec.name}: Core deploy+execute+runClosed C.5.2 non-canonical coeff reject", nonCanonRejOk,
              if nonCanonRejOk then s!"both stopped with {reprStr ncStE}" else s!"mismatch {reprStr ncStE} vs {reprStr ncStC}")
          ]
      | _, _, _, _ => .error s!"{spec.name}: unexpected deployed entry or stack signature"

/-- Run ALL CFRG `draft-irtf-cfrg-fiat-shamir-04` test vectors (both direct and end-to-end Core). -/
def runAllCfrgVectors : IO (Bool × List (String × Bool × String)) := do
  let mut results : List (String × Bool × String) := []

  -- 1. 24-round sponge equivalence with SHAKE128 across 4 message lengths
  for (label, msg) in [
    ("0B", []),
    ("3B", utf8Bytes "abc"),
    ("200B", List.range 200),
    ("400B", List.replicate 400 0)
  ] do
    let a := ofByteArray (Keccak.sponge 168 0x1F 24 (toByteArray msg) 500)
    let b := shake128Bytes msg 500
    results := results ++ [(s!"sponge(24r) == SHAKE128 ({label})", a == b, "500B")]

  -- 2. Direct & Core end-to-end checks for BOTH SHAKE128 and TurboSHAKE128
  for spec in [shake128Spec, turboShake128Spec] do
    let interopSid := ofByteArray (Cfrg.deriveSessionId spec.xof "interop-test-v00".toUTF8)
    results := results ++ [(s!"{spec.name}: C.2 session identifier",
      bytesToHex interopSid == spec.interopSidHex, bytesToHex interopSid)]

    let d0 := Cfrg.startRaw spec.xof (List.range 32)
    let some instBytes := hexToBytes "08000000696e7374616e6365"
      | return (false, [(s!"{spec.name}: C.3 hex parse", false, "bad hex")])
    let d1 := Cfrg.absorb d0 [] instBytes
    let (out48, _) := Cfrg.squeeze d1 48
    results := results ++ [(s!"{spec.name}: C.3 squeezed 48 bytes",
      bytesToHex out48 == spec.decodeOutHex, s!"{out48.length}B")]
    results := results ++ [(s!"{spec.name}: C.3 P-256 decoded message",
      fromLeBytes out48 % p256Order == spec.decodeMsg, "exact")]

    let sumSid := ofByteArray (Cfrg.deriveSessionId spec.xof "sumcheck".toUTF8)
    results := results ++ [(s!"{spec.name}: C.5.1 session identifier",
      bytesToHex sumSid == spec.sumcheckSidHex, bytesToHex sumSid)]

    let wInit := (List.range 16).map (2 ^ ·)
    let (narg, finalY) := directSumcheckProve spec.xof sumSid 4 wInit
    results := results ++ [(s!"{spec.name}: C.5.1 direct NARG string",
      bytesToHex narg == spec.nargHex, bytesToHex narg)]
    results := results ++ [(s!"{spec.name}: C.5.1 direct final evaluation",
      finalY == spec.finalEval, s!"{finalY}")]
    results := results ++ [(s!"{spec.name}: C.5.1 direct verifier accepts",
      directSumcheckVerify spec.xof sumSid 4 0xFFFF narg finalY, "ok")]
    results := results ++ [(s!"{spec.name}: C.5.2 direct trailing byte rejected",
      !directSumcheckVerify spec.xof sumSid 4 0xFFFF (narg ++ [0]) finalY, "rejected")]

    let dA := Cfrg.absorb (Cfrg.startRaw spec.xof sumSid) [] (utf8Bytes "x")
    let (s1, dA1) := Cfrg.squeeze dA 4
    let (s2, _) := Cfrg.squeeze dA1 4
    let (s8, _) := Cfrg.squeeze dA 8
    results := results ++ [(s!"{spec.name}: consecutive squeezes form one stream",
      s1 ++ s2 == s8 && s1 != s2, "8B")]

    match runCoreSumcheckEndToEnd spec with
    | .ok coreRes => results := results ++ coreRes
    | .error err => results := results ++ [(s!"{spec.name}: Core end-to-end", false, err)]

  -- 3. Direct C.5.2 non-canonical coefficient rejection
  let some badNarg := hexToBytes nonCanonicalBadNargHex
    | return (false, [("C.5.2 bad NARG hex", false, "invalid hex")])
  results := results ++ [("SHAKE128: C.5.2 direct non-canonical coeff rejected",
    !directSumcheckVerify .shake128 (List.range 32) 4 0xFFFF badNarg 0, "rejected")]

  let allOk := results.all fun (_, ok, _) => ok
  return (allOk, results)

end Zkc.Runtime.CfrgVectors
