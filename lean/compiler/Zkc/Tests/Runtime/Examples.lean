import Zkc.Frontend
import Zkc.Runtime
import Zkc.Tools.Frontend.Names
import Zkc.Tests.Runtime.Crypto

/-!
# End-to-end runtime verification across real `.zkc` examples (`Zkc.Tests.Runtime.Examples`)

Compiles real `.zkc` source files from `examples/` (plus inline schemes covering
`Poseidon2KoalaBear`, `interactive`, and `retry` with `abort`), deploys them through
`Zkc.Frontend.Deploy`, and verifies:
1. Bit-for-bit differential equivalence between `Core.execute` (`runDeployed`) and
   `Core.specialize` + `runClosed` (`runDeployedClosed`) on BOTH honest runs and mutation
   negative controls (exact matching `Stop` including `Reason` and `Occurrence`).
2. `ideal?.isSome` (ideal random-oracle deployment admitted by `Core.deployIdeal`).
3. Compact proof layout (`carry`/`recover`), deterministic nonce derivation (`emptySource`),
   pure Core IR `HashChain<Keccak256, Fr>`, `ClosedProcs` DAG sharing, native `KoalaBear`
   transcript units (`Poseidon2KoalaBear`), interactive two-party execution, and bounded retry
   with abort / exhaustion.
-/

namespace Zkc.Tests.Runtime

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project
open Zkc.Frontend
open Zkc.Frontend.Deploy
open Zkc.Tools.Frontend
open Zkc.Runtime
open Zkc.Runtime.Crypto

/-! ## Dynamic input builder for arbitrary compiled `CompiledScheme` signatures -/

inductive DynVal where
  | bool (b : Bool)
  | nat (n : Nat)
  | fin (n : Nat)
  | bytes (bs : List Nat)
  | fr (n : Nat)
  | koala (n : Nat)
  | koala4 (cs : List Nat)
  | g1 (p : G1Point)
  | seq (vs : List DynVal)
  | tuple (vs : List DynVal)
  | variant (tag : Nat) (payload : DynVal)
  | unit

mutual
  partial def decodeDynVal (b : Bindings) (τ : LinkedType) (v : DynVal) :
      Except String (τ.Val (linkedCarriers b)) :=
    match τ, v with
    | .bool, .bool x => .ok x
    | .nat, .nat n => .ok n
    | .fin _, .fin n => .ok n
    | .fin _, .nat n => .ok n
    | .seq (.fin 256) _, .bytes bs => .ok bs
    | .seq item _, .seq vs => vs.mapM (decodeDynVal b item)
    | .tuple items, .tuple vs => decodeDynTys b items vs
    | .record _ _ fields, .tuple vs => decodeDynTys b fields vs
    | .variant _ alts, .variant tag payload => decodeDynChoice b alts tag payload
    | .nominal (.inl (.field .bls12381Fr)), .fr n => .ok (n % bls12381FrOrder)
    | .nominal (.inl (.nonzero .bls12381Fr)), .fr n => .ok (n % bls12381FrOrder)
    | .nominal (.inl (.field .koalaBear)), .koala n => .ok (n % koalaBearOrder)
    | .nominal (.inl (.nonzero .koalaBear)), .koala n => .ok (n % koalaBearOrder)
    | .nominal (.inl (.field .koalaBear4)), .koala4 cs => .ok (ext4Norm cs)
    | .nominal (.inl (.nonzero .koalaBear4)), .koala4 cs => .ok (ext4Norm cs)
    | .nominal (.inl (.group .g1)), .g1 p => .ok p
    | _, _ => .error s!"DynVal type mismatch for target Core type"

  partial def decodeDynTys (b : Bindings) : (τs : Core.Tys (Sum TypeKey Parameter)) →
      List DynVal → Except String (τs.Val (linkedCarriers b))
    | .nil, [] => .ok ()
    | .cons head rest, v :: vs => do
        let h ← decodeDynVal b head v
        let t ← decodeDynTys b rest vs
        .ok (h, t)
    | _, _ => .error "DynVal tuple/record arity mismatch"

  partial def decodeDynChoice (b : Bindings) : (alts : Core.Tys (Sum TypeKey Parameter)) →
      Nat → DynVal → Except String (alts.Choice (linkedCarriers b))
    | .nil, _, _ => .error "DynVal variant tag out of range"
    | .cons head _, 0, payload => .inl <$> decodeDynVal b head payload
    | .cons _ rest, tag + 1, payload => .inr <$> decodeDynChoice b rest tag payload
end

def buildRoleInputs (b : Bindings) (M : Model b.vocabulary) (hC : M.toCarriers = linkedCarriers b)
    (r : Role) : (ins : List (LTy b.vocabulary)) → List DynVal → Except String (HList (RV M r) ins)
  | [], [] => .ok .nil
  | a :: rest, v :: vs => do
      let tail ← buildRoleInputs b M hC r rest vs
      if hMem : r ∈ a.holders then
        let val ← decodeDynVal b a.ty v
        let valM : a.ty.Val M.toCarriers := cast (congrArg (fun c => a.ty.Val c) hC.symm) val
        let rv : RV M r a := cast (by simp [RV, hMem]) valM
        .ok (.cons rv tail)
      else
        let rv : RV M r a := cast (by simp [RV, hMem]) ()
        .ok (.cons rv tail)
  | _, _ => .error "DynVal input list length mismatch"

/-! ## Compilation & differential execution harness -/

def defaultLibs : Array System.FilePath :=
  #["../../libraries", "../../examples", "../../examples/support"]

def compileFiles (files : Array String) : IO (Except String Compile.State) := do
  let inputs ← files.mapM Names.readInput
  let session ← Driver.Session.compile Driver.Session.start inputs (Names.libraryLoader defaultLibs) "packages"
  if session.hasErrors then
    return .error ("\n".intercalate session.renderDiagnostics.toList)
  return .ok session.state

def compileInline (name text : String) : IO (Except String Compile.State) := do
  let input : SourceInput := { name, parsed := Syntax.parse name text.toUTF8 }
  let session ← Driver.Session.compile Driver.Session.start #[input] (Names.libraryLoader defaultLibs) "packages"
  if session.hasErrors then
    return .error ("\n".intercalate session.renderDiagnostics.toList)
  return .ok session.state

/-- Extract proof bytes from a prover outcome when the stack gives `[byte]`. -/
def extractProofBytes {V : Core.Vocabulary} {M : Model V} {r : Role} {outs : List (LTy V)}
    {gives : List V.Ty} (out : Outcome (HList (RV M r) outs) (HList M.Val gives)) :
    Except String (List Nat) :=
  match out with
  | .ended (.returned (_, gs)) =>
      match gives, gs with
      | [.seq (.fin 256) none], .cons bs .nil => .ok bs
      | _, _ => .error "prover stack did not produce a single byte sequence"
  | .ended (.stopped stop) => .error s!"prover stopped: {reprStr stop}"
  | .ended (.blocked at_) => .error s!"prover blocked at {reprStr at_}"
  | .limit => .error "prover hit step limit"
  | .failed msg => .error s!"prover failed: {msg}"

/-- Run prover via BOTH `Core.execute` (`runDeployed`) and `Core.specialize` + `runClosed`,
asserting exact byte-for-byte equality of the emitted proof. -/
def proveDifferential (cs : CompiledScheme) (M : Model cs.bindings.vocabulary)
    (hC : M.toCarriers = linkedCarriers cs.bindings) (src : Source M)
    (inputs : List DynVal) (limit : Nat := 200000) : Except String (List Nat) := do
  let some p := cs.proverRole? | throw s!"{cs.name}: missing prover role"
  let pIns ← buildRoleInputs cs.bindings M hC p cs.deployed.entry.ins inputs
  match hT : Stack.Takes (cs.deployed.stack p) with
  | [] =>
      let taken : HList M.Val (Stack.Takes (cs.deployed.stack p)) := hT.symm ▸ .nil
      let (oExec, _) := runDeployed M cs.deployed p pIns taken src limit
      let (oClosed, _) := runDeployedClosed M cs.deployed p pIns taken src limit
      let pfExec ← extractProofBytes oExec
      let pfClosed ← extractProofBytes oClosed
      if pfExec != pfClosed then
        throw s!"{cs.name}: prover differential mismatch (execute={pfExec.length}B vs runClosed={pfClosed.length}B)"
      return pfExec
  | _ => throw s!"{cs.name}: unexpected non-empty prover stack takes"

/-- Run verifier via BOTH `Core.execute` and `runClosed`, returning:
`Except.ok none` when BOTH accept, `Except.ok (some stop)` when BOTH stop with the exact
same `Stop` (`Reason` + `Occurrence`), or `Except.error` on any discrepancy. -/
def verifyDifferential (cs : CompiledScheme) (M : Model cs.bindings.vocabulary)
    (hC : M.toCarriers = linkedCarriers cs.bindings) (src : Source M)
    (inputs : List DynVal) (proofBytes : List Nat) (limit : Nat := 200000) :
    Except String (Option Stop) := do
  let some v := cs.verifierRole? | throw s!"{cs.name}: missing verifier role"
  let vIns ← buildRoleInputs cs.bindings M hC v cs.deployed.entry.ins inputs
  match hT : Stack.Takes (cs.deployed.stack v) with
  | [.seq (.fin 256) none] =>
      let taken : HList M.Val (Stack.Takes (cs.deployed.stack v)) := hT.symm ▸ (.cons proofBytes .nil)
      let (oExec, _) := runDeployed M cs.deployed v vIns taken src limit
      let (oClosed, _) := runDeployedClosed M cs.deployed v vIns taken src limit
      match oExec, oClosed with
      | .ended (.returned _), .ended (.returned _) => .ok none
      | .ended (.stopped s1), .ended (.stopped s2) =>
          if s1 == s2 then .ok (some s1)
          else .error s!"{cs.name}: verifier Stop mismatch ({reprStr s1} vs {reprStr s2})"
      | _, _ => .error s!"{cs.name}: verifier outcome class mismatch between execute and runClosed"
  | _ => throw s!"{cs.name}: unexpected verifier stack takes"

/-- Flip one byte at index `idx` of a byte list. -/
def flipByte (bs : List Nat) (idx : Nat) : List Nat :=
  bs.zipIdx.map fun (b, i) => if i == idx then (b ^^^ 1) % 256 else b

/-- Expect verifier to reject with matching `Stop` across `Core.execute` and `runClosed`. -/
def checkReject (label : String) (cs : CompiledScheme) (M : Model cs.bindings.vocabulary)
    (hC : M.toCarriers = linkedCarriers cs.bindings) (src : Source M)
    (inputs : List DynVal) (proofBytes : List Nat) (limit : Nat := 200000) : TestResult :=
  match verifyDifferential cs M hC src inputs proofBytes limit with
  | .ok (some stop) => check label true s!"both stopped: {reprStr stop}"
  | .ok none => check label false "unexpectedly accepted!"
  | .error err => check label false err

/-! ## Individual end-to-end example suites -/

/-- 1 & 2. `examples/schnorr_example.zkc`: `Proof` (`Merlin3Bls12381`) + `Signature` (`context`,
`samples derived by`, compact `carry`/`recover`, `emptySource`). -/
def testSchnorrExample : IO (List TestResult) := do
  let mut out : List TestResult := []
  match ← compileFiles #["../../examples/schnorr_example.zkc"] with
  | .error err => return [check "schnorr_example.zkc compile" false err]
  | .ok state =>
      -- 1. `schnorr_example::Proof`
      match deployScheme state "Proof" with
      | .error err => out := out ++ [check "schnorr_example::Proof deploy" false err]
      | .ok cs =>
          match hM : linkedModel? cs.bindings with
          | .error err => out := out ++ [check "schnorr_example::Proof linkedModel?" false err]
          | .ok M =>
              have hC := linkedModel?_carriers hM
              let src := seededSource cs.bindings M hC (utf8Bytes "zkc-schnorr-proof-seed")
              let sk : Nat := 0x123456789abcdef0123456789abcdef
              let g := g1Generator
              let pk := g1Scale g sk
              let inputs := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr sk]
              out := out ++ [check "schnorr_example::Proof ideal-RO admitted" cs.ideal?.isSome "ok"]
              match proveDifferential cs M hC src inputs with
              | .error err => out := out ++ [check "schnorr_example::Proof prove" false err]
              | .ok pf =>
                  out := out ++ [
                    check "schnorr_example::Proof prove (Core.execute == runClosed, 80B)"
                      (pf.length == 80) s!"{pf.length}B"
                  ]
                  match verifyDifferential cs M hC src inputs pf with
                  | .ok none => out := out ++ [check "schnorr_example::Proof honest verify" true "accept"]
                  | .ok (some st) => out := out ++ [check "schnorr_example::Proof honest verify" false s!"stopped {reprStr st}"]
                  | .error err => out := out ++ [check "schnorr_example::Proof honest verify" false err]
                  -- Mutation negative controls
                  let nonCanonScalar := pf.take 48 ++ leBytes 32 bls12381FrOrder
                  let badG1 := (0x9f :: List.replicate 47 0xff) ++ pf.drop 48
                  let wrongInputs := [DynVal.g1 g, DynVal.g1 (g1Scale g (sk + 1)), DynVal.fr sk]
                  out := out ++ [
                    checkReject "schnorr_example::Proof reject flipped proof byte" cs M hC src inputs (flipByte pf 5),
                    checkReject "schnorr_example::Proof reject truncated proof" cs M hC src inputs (pf.take 79),
                    checkReject "schnorr_example::Proof reject trailing byte" cs M hC src inputs (pf ++ [0]),
                    checkReject "schnorr_example::Proof reject non-canonical scalar >= r" cs M hC src inputs nonCanonScalar,
                    checkReject "schnorr_example::Proof reject invalid G1 point" cs M hC src inputs badG1,
                    checkReject "schnorr_example::Proof reject wrong statement (Weak-FS)" cs M hC src wrongInputs pf
                  ]

      -- 2. `schnorr_example::Signature` (`emptySource`, deterministic 64B compact proof)
      match deployScheme state "Signature" with
      | .error err => out := out ++ [check "schnorr_example::Signature deploy" false err]
      | .ok cs =>
          match hM : linkedModel? cs.bindings with
          | .error err => out := out ++ [check "schnorr_example::Signature linkedModel?" false err]
          | .ok M =>
              have hC := linkedModel?_carriers hM
              let empty := emptySource M
              let sk : Nat := 0xdeadbeefcafebabe1337
              let g := g1Generator
              let pk := g1Scale g sk
              let msg := utf8Bytes "transfer 100 ETH to alice"
              let dom := utf8Bytes "zkc.sig.v1"
              let inputs := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr sk, DynVal.bytes msg, DynVal.bytes dom]
              out := out ++ [check "schnorr_example::Signature ideal-RO admitted" cs.ideal?.isSome "ok"]
              match proveDifferential cs M hC empty inputs, proveDifferential cs M hC empty inputs with
              | .ok sig1, .ok sig2 =>
                  out := out ++ [
                    check "schnorr_example::Signature deterministic 64B compact proof (emptySource)"
                      (sig1.length == 64 && sig1 == sig2) s!"{sig1.length}B deterministic"
                  ]
                  match verifyDifferential cs M hC empty inputs sig1 with
                  | .ok none => out := out ++ [check "schnorr_example::Signature honest verify (pure Core IR recovery)" true "accept"]
                  | .ok (some st) => out := out ++ [check "schnorr_example::Signature honest verify" false s!"stopped {reprStr st}"]
                  | .error err => out := out ++ [check "schnorr_example::Signature honest verify" false err]
                  let badMsgInputs := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr sk,
                    DynVal.bytes (utf8Bytes "transfer 999 ETH to mallory"), DynVal.bytes dom]
                  let badDomInputs := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr sk,
                    DynVal.bytes msg, DynVal.bytes (utf8Bytes "zkc.sig.v2")]
                  out := out ++ [
                    checkReject "schnorr_example::Signature reject tampered message context" cs M hC empty badMsgInputs sig1,
                    checkReject "schnorr_example::Signature reject tampered domain context" cs M hC empty badDomInputs sig1,
                    checkReject "schnorr_example::Signature reject flipped challenge byte" cs M hC empty inputs (flipByte sig1 3),
                    checkReject "schnorr_example::Signature reject flipped response byte" cs M hC empty inputs (flipByte sig1 40),
                    checkReject "schnorr_example::Signature reject trailing byte" cs M hC empty inputs (sig1 ++ [0])
                  ]
              | .error err, _ | _, .error err =>
                  out := out ++ [check "schnorr_example::Signature prove" false err]
  return out

/-- 3. `examples/chaum_pedersen.zkc::SameLogProof` (**pure Core IR `HashChain<Keccak256, Fr>`**). -/
def testChaumPedersenExample : IO (List TestResult) := do
  match ← compileFiles #["../../examples/chaum_pedersen.zkc"] with
  | .error err => return [check "chaum_pedersen.zkc compile" false err]
  | .ok state =>
      match deployScheme state "SameLogProof" with
      | .error err => return [check "chaum_pedersen::SameLogProof deploy" false err]
      | .ok cs =>
          match hM : linkedModel? cs.bindings with
          | .error err => return [check "chaum_pedersen::SameLogProof linkedModel?" false err]
          | .ok M =>
              have hC := linkedModel?_carriers hM
              let src := seededSource cs.bindings M hC (utf8Bytes "zkc-chaum-pedersen-seed")
              let g := g1Generator
              let h := g1Scale g 7
              let x : Nat := 0xabcdef0123456789
              let u := g1Scale g x
              let v := g1Scale h x
              let inputs := [DynVal.g1 g, DynVal.g1 h, DynVal.g1 u, DynVal.g1 v, DynVal.fr x]
              let noOpaqueSuiteRows := !(cs.bindings.rows.any fun (k, _) => k.name.startsWith "suite.")
              let mut out : List TestResult := [
                check "chaum_pedersen::SameLogProof pure Core IR HashChain (0 opaque suite.* rows)"
                  noOpaqueSuiteRows s!"{cs.bindings.rows.length} total rows",
                check "chaum_pedersen::SameLogProof ideal-RO admitted" cs.ideal?.isSome "ok"
              ]
              match proveDifferential cs M hC src inputs with
              | .error err => out := out ++ [check "chaum_pedersen::SameLogProof prove" false err]
              | .ok pf =>
                  out := out ++ [
                    check "chaum_pedersen::SameLogProof prove (Core.execute == runClosed, 128B)"
                      (pf.length == 128) s!"{pf.length}B"
                  ]
                  match verifyDifferential cs M hC src inputs pf with
                  | .ok none => out := out ++ [check "chaum_pedersen::SameLogProof honest verify" true "accept"]
                  | .ok (some st) => out := out ++ [check "chaum_pedersen::SameLogProof honest verify" false s!"stopped {reprStr st}"]
                  | .error err => out := out ++ [check "chaum_pedersen::SameLogProof honest verify" false err]
                  let badV := [DynVal.g1 g, DynVal.g1 h, DynVal.g1 u, DynVal.g1 (g1Scale h (x + 1)), DynVal.fr x]
                  out := out ++ [
                    checkReject "chaum_pedersen::SameLogProof reject flipped byte" cs M hC src inputs (flipByte pf 10),
                    checkReject "chaum_pedersen::SameLogProof reject wrong v" cs M hC src badV pf,
                    checkReject "chaum_pedersen::SameLogProof reject trailing byte" cs M hC src inputs (pf ++ [0])
                  ]
              return out

/-- 4. `examples/sigma_or.zkc::Or<G1>`: BOTH `Witness::Left` and `Witness::Right` branches. -/
def testSigmaOrExample : IO (List TestResult) := do
  let wrapper :=
    "module sigma_or_driver\n" ++
    "use sigma_or::{Or}\n" ++
    "use zkc::curves::bls12_381::{G1}\n" ++
    "use zkc::suites::{Merlin3Bls12381}\n" ++
    "scheme OrProof = Or<G1>:\n" ++
    "    construction derived(Merlin3Bls12381)\n"
  match ← compileInline "sigma_or_driver.zkc" wrapper with
  | .error err => return [check "sigma_or wrapper compile" false err]
  | .ok state =>
      match deployScheme state "OrProof" with
      | .error err => return [check "sigma_or::Or<G1> deploy" false err]
      | .ok cs =>
          match hM : linkedModel? cs.bindings with
          | .error err => return [check "sigma_or::Or<G1> linkedModel?" false err]
          | .ok M =>
              have hC := linkedModel?_carriers hM
              let src := seededSource cs.bindings M hC (utf8Bytes "zkc-sigma-or-seed")
              let g := g1Generator
              let w0 : Nat := 1111111
              let w1 : Nat := 2222222
              let x0 := g1Scale g w0
              let x1 := g1Scale g w1
              let inLeft := [DynVal.g1 g, DynVal.g1 x0, DynVal.g1 x1, DynVal.variant 0 (DynVal.fr w0)]
              let inRight := [DynVal.g1 g, DynVal.g1 x0, DynVal.g1 x1, DynVal.variant 1 (DynVal.fr w1)]
              let mut out : List TestResult := [
                check "sigma_or::Or<G1> ideal-RO admitted" cs.ideal?.isSome "ok"
              ]
              match proveDifferential cs M hC src inLeft, proveDifferential cs M hC src inRight with
              | .ok pfL, .ok pfR =>
                  out := out ++ [
                    check "sigma_or::Or<G1> Left & Right proofs identical length (224B)"
                      (pfL.length == 224 && pfR.length == 224) s!"Left={pfL.length}B, Right={pfR.length}B"
                  ]
                  match verifyDifferential cs M hC src inLeft pfL, verifyDifferential cs M hC src inRight pfR with
                  | .ok none, .ok none =>
                      out := out ++ [check "sigma_or::Or<G1> Left & Right honest verify" true "both accept"]
                  | _, _ =>
                      out := out ++ [check "sigma_or::Or<G1> Left & Right honest verify" false "verify failed"]
                  let wrongStmt := [DynVal.g1 g, DynVal.g1 (g1Scale g (w0 + 1)), DynVal.g1 x1,
                    DynVal.variant 0 (DynVal.fr w0)]
                  out := out ++ [
                    checkReject "sigma_or::Or<G1> reject flipped byte" cs M hC src inLeft (flipByte pfL 100),
                    checkReject "sigma_or::Or<G1> reject wrong statement" cs M hC src wrongStmt pfL
                  ]
              | .error err, _ | _, .error err =>
                  out := out ++ [check "sigma_or::Or<G1> prove" false err]
              return out

/-- 5. `examples/sumcheck_example.zkc::Proof` (`Sumcheck<10>` with nested `Reduce` & 10-round loop). -/
def testSumcheckExample : IO (List TestResult) := do
  match ← compileFiles #["../../examples/sumcheck_example.zkc"] with
  | .error err => return [check "sumcheck_example.zkc compile" false err]
  | .ok state =>
      match deployScheme state "Proof" with
      | .error err => return [check "sumcheck_example::Proof deploy" false err]
      | .ok cs =>
          match hM : linkedModel? cs.bindings with
          | .error err => return [check "sumcheck_example::Proof linkedModel?" false err]
          | .ok M =>
              have hC := linkedModel?_carriers hM
              let src := emptySource M
              let tableVals : List Nat := (List.range 1024).map fun i => (i * 3 + 7) % bls12381FrOrder
              let claim : Nat := tableVals.foldl (fun acc x => (acc + x) % bls12381FrOrder) 0
              let inputs := [DynVal.seq (tableVals.map DynVal.fr), DynVal.fr claim]
              let mut out : List TestResult := [
                check "sumcheck_example::Proof ideal-RO admitted" cs.ideal?.isSome "ok"
              ]
              match proveDifferential cs M hC src inputs 500000 with
              | .error err => out := out ++ [check "sumcheck_example::Proof prove" false err]
              | .ok pf =>
                  out := out ++ [
                    check "sumcheck_example::Proof (Sumcheck<10>, 1024 Frs) prove (Core.execute == runClosed, 640B)"
                      (pf.length == 640) s!"{pf.length}B (10 rounds)"
                  ]
                  match verifyDifferential cs M hC src inputs pf 500000 with
                  | .ok none => out := out ++ [check "sumcheck_example::Proof honest verify" true "accept"]
                  | .ok (some st) => out := out ++ [check "sumcheck_example::Proof honest verify" false s!"stopped {reprStr st}"]
                  | .error err => out := out ++ [check "sumcheck_example::Proof honest verify" false err]
                  let badClaim := [DynVal.seq (tableVals.map DynVal.fr), DynVal.fr ((claim + 1) % bls12381FrOrder)]
                  out := out ++ [
                    checkReject "sumcheck_example::Proof reject flipped byte" cs M hC src inputs (flipByte pf 200) 500000,
                    checkReject "sumcheck_example::Proof reject wrong claim" cs M hC src badClaim pf 500000,
                    checkReject "sumcheck_example::Proof reject trailing byte" cs M hC src inputs (pf ++ [0]) 500000
                  ]
              return out

/-- 6. Native `KoalaBear` + `KoalaBear4` scheme deployed with `Poseidon2KoalaBear`. -/
def testPoseidon2KoalaBear : IO (List TestResult) := do
  let srcText :=
    "module poseidon2_kb_test\n" ++
    "use zkc::fields::{KoalaBear, KoalaBear4}\n" ++
    "use zkc::suites::{Poseidon2KoalaBear}\n" ++
    "pub protocol FoldCheck roles(P, V)(\n" ++
    "    tag: KoalaBear @(P, V),\n" ++
    "    a: KoalaBear4 @(P, V),\n" ++
    "    b: KoalaBear4 @(P, V),\n" ++
    "    w: KoalaBear4 @P\n" ++
    "):\n" ++
    "    mask @P <- sample KoalaBear4\n" ++
    "    t <- send a * mask to V\n" ++
    "    c <- draw KoalaBear4 from V to P\n" ++
    "    z <- send mask + c * w to V\n" ++
    "    guard @V a * z == t + b * c\n" ++
    "    guard @V tag == tag\n" ++
    "scheme KbProof = FoldCheck:\n" ++
    "    construction derived(Poseidon2KoalaBear)\n"
  match ← compileInline "poseidon2_kb_test.zkc" srcText with
  | .error err => return [check "Poseidon2KoalaBear compile" false err]
  | .ok state =>
      match deployScheme state "KbProof" with
      | .error err => return [check "Poseidon2KoalaBear deploy" false err]
      | .ok cs =>
          match hM : linkedModel? cs.bindings with
          | .error err => return [check "Poseidon2KoalaBear linkedModel?" false err]
          | .ok M =>
              have hC := linkedModel?_carriers hM
              let src := seededSource cs.bindings M hC (utf8Bytes "zkc-poseidon2-kb-seed")
              let a : List Nat := [11, 22, 33, 44]
              let w : List Nat := [5, 7, 9, 13]
              let b := ext4Mul a w
              let inputs := [DynVal.koala 99, DynVal.koala4 a, DynVal.koala4 b, DynVal.koala4 w]
              let mut out : List TestResult := [
                check "Poseidon2KoalaBear ideal-RO admitted" cs.ideal?.isSome "ok"
              ]
              match proveDifferential cs M hC src inputs with
              | .error err => out := out ++ [check "Poseidon2KoalaBear prove" false err]
              | .ok pf =>
                  out := out ++ [
                    check "Poseidon2KoalaBear prove (native KoalaBear units, Core.execute == runClosed, 32B)"
                      (pf.length == 32) s!"{pf.length}B"
                  ]
                  match verifyDifferential cs M hC src inputs pf with
                  | .ok none => out := out ++ [check "Poseidon2KoalaBear honest verify" true "accept"]
                  | .ok (some st) => out := out ++ [check "Poseidon2KoalaBear honest verify" false s!"stopped {reprStr st}"]
                  | .error err => out := out ++ [check "Poseidon2KoalaBear honest verify" false err]
                  let badB := [DynVal.koala 99, DynVal.koala4 a, DynVal.koala4 (ext4Add b ext4One), DynVal.koala4 w]
                  out := out ++ [
                    checkReject "Poseidon2KoalaBear reject flipped byte" cs M hC src inputs (flipByte pf 4),
                    checkReject "Poseidon2KoalaBear reject wrong b" cs M hC src badB pf,
                    checkReject "Poseidon2KoalaBear reject trailing byte" cs M hC src inputs (pf ++ [0])
                  ]
              return out

/-- 7. Interactive two-party scheme (`construction interactive` + `runInteractiveScheme`). -/
def testInteractiveScheme : IO (List TestResult) := do
  let srcText :=
    "module interactive_test\n" ++
    "use schnorr::{Schnorr}\n" ++
    "use zkc::curves::bls12_381::{G1}\n" ++
    "scheme LiveSchnorr = Schnorr<G1>:\n" ++
    "    construction interactive\n"
  match ← compileInline "interactive_test.zkc" srcText with
  | .error err => return [check "interactive scheme compile" false err]
  | .ok state =>
      match deployScheme state "LiveSchnorr" with
      | .error err => return [check "interactive scheme deploy" false err]
      | .ok cs =>
          match hM : linkedModel? cs.bindings with
          | .error err => return [check "interactive scheme linkedModel?" false err]
          | .ok M =>
              have hC := linkedModel?_carriers hM
              let src := seededSource cs.bindings M hC (utf8Bytes "zkc-interactive-seed")
              let g := g1Generator
              let sk : Nat := 777777
              let pk := g1Scale g sk
              let honest := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr sk]
              let dishonest := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr (sk + 1)]
              match buildRoleInputs cs.bindings M hC 0 cs.deployed.entry.ins honest,
                    buildRoleInputs cs.bindings M hC 1 cs.deployed.entry.ins honest,
                    buildRoleInputs cs.bindings M hC 0 cs.deployed.entry.ins dishonest with
              | .ok pHon, .ok vHon, .ok pBad =>
                  let (oP, oV, _) := runInteractiveScheme M cs.deployed 0 1 pHon vHon src 100000
                  let honOk := match oP, oV with
                    | .ended (.returned _), .ended (.returned _) => true
                    | _, _ => false
                  let (_, oVBad, _) := runInteractiveScheme M cs.deployed 0 1 pBad vHon src 100000
                  let badRejected := match oVBad with
                    | .ended (.stopped (.declared .reject _)) => true
                    | _ => false
                  return [
                    check "Interactive Schnorr: honest two-party run accepts" honOk "both returned",
                    check "Interactive Schnorr: dishonest prover rejected by verifier" badRejected "declared reject"
                  ]
              | _, _, _ => return [check "Interactive Schnorr: input build" false "failed"]

/-- 8. Retry-with-abort BLS12-381 G1 Schnorr protocol (`Core.admit` → `Core.deploy` with
`retry := some (bound, ⟨[], ⟨409⟩⟩)`): attempt 0 sends `A` and derives `c` before aborting on
`attemptIdx == 0` (exercising transcript + proof-buffer rollback), then attempt 1 proves a valid
80B Merlin3 proof that verifies; `bound = 1` exercises identical `.declared .exhausted` stops in
BOTH `Core.execute` (`runDeployed`) and `Core.specialize` + `runClosed` (`runDeployedClosed`). -/
def testRetryWithAbort : IO (List TestResult) := do
  let g1Ty : LinkedType := .nominal (.inl (.group .g1))
  let frTy : LinkedType := .nominal (.inl (.field .bls12381Fr))
  let byteSeqTy : LinkedType := .seq (.fin 256) none
  let stTy : LinkedType := .nominal (.inr (.type (.nominal "suite.merlin3.state") .nil))
  let lawFr : Zkc.Vocabulary.LawKey := .uniform (.nominal (.field .bls12381Fr))
  let pG1 : Parameters := .cons (linkedTypeToParam g1Ty) .nil
  let pFr : Parameters := .cons (linkedTypeToParam frTy) .nil

  let primStart : PrimitiveName := ⟨"suite.merlin3.start", .nil⟩
  let primAbsorb : PrimitiveName := ⟨"suite.merlin3.absorb", .nil⟩
  let primEncG1 : PrimitiveName := ⟨"suite.merlin3.encode", pG1⟩
  let primEncFr : PrimitiveName := ⟨"suite.merlin3.encode", pFr⟩
  let primDerFr : PrimitiveName := ⟨"suite.merlin3.derive", pFr⟩
  let primLayWG1 : PrimitiveName := ⟨"layout.canonical.write", pG1⟩
  let primLayRG1 : PrimitiveName := ⟨"layout.canonical.try_read", pG1⟩
  let primLayEG1 : PrimitiveName := ⟨"layout.canonical.equal", pG1⟩
  let primLayWFr : PrimitiveName := ⟨"layout.canonical.write", pFr⟩
  let primLayRFr : PrimitiveName := ⟨"layout.canonical.try_read", pFr⟩
  let primLayEFr : PrimitiveName := ⟨"layout.canonical.equal", pFr⟩

  let runCase (bound : Nat) : Except String (List TestResult) := do
    let mut b : Bindings := {}
    b ← CfrgVectors.insertBind b primStart [byteSeqTy] [stTy]
    b ← CfrgVectors.insertBind b primAbsorb [stTy, byteSeqTy, byteSeqTy] [stTy]
    b ← CfrgVectors.insertBind b primEncG1 [g1Ty] [byteSeqTy]
    b ← CfrgVectors.insertBind b primEncFr [frTy] [byteSeqTy]
    b ← CfrgVectors.insertBind b primDerFr [stTy, byteSeqTy] [frTy, stTy]
    b ← CfrgVectors.insertBind b primLayWG1 [g1Ty] [byteSeqTy]
    b ← CfrgVectors.insertBind b primLayRG1 [byteSeqTy, .nat] [.bool, g1Ty, .nat]
    b ← CfrgVectors.insertBind b primLayEG1 [g1Ty, g1Ty] [.bool]
    b ← CfrgVectors.insertBind b primLayWFr [frTy] [byteSeqTy]
    b ← CfrgVectors.insertBind b primLayRFr [byteSeqTy, .nat] [.bool, frTy, .nat]
    b ← CfrgVectors.insertBind b primLayEFr [frTy, frTy] [.bool]

    -- Inputs: 0 : base @(0,1), 1 : point @(0,1), 2 : scalar @0
    let protoDef : Definition b.vocabulary :=
      .protocol ⟨1⟩ 2 [⟨g1Ty, [0, 1]⟩, ⟨g1Ty, [0, 1]⟩, ⟨frTy, [0]⟩] []
        (.mk [0, 1, 2] [
          .attempt ⟨409⟩ [0] [] (.mk [50] [
            .op ⟨410⟩ [3] (.event (.given (.coin lawFr) 0 []) frTy) [],
            .op ⟨411⟩ [4] (.compute [0] (.row (.inl (.group .scale (.group .g1))))) [0, 3],
            .op ⟨412⟩ [5] (.event (.flow .message 0 [1]) g1Ty) [4],
            .op ⟨413⟩ [6] (.event (.given (.coin lawFr) 1 [0]) frTy) [],
            .op ⟨414⟩ [20] (.compute [0] (.literal .nat [0])) [],
            .op ⟨415⟩ [21] (.compute [0] (.owned .natEqual [] [])) [50, 20],
            .op ⟨416⟩ [22] (.compute [0] (.owned .boolNot [] [])) [21],
            .guard ⟨417⟩ [0] 22 .abort,
            .op ⟨418⟩ [7] (.compute [0] (.row (.inl (.field .mul .bls12381Fr .all)))) [6, 2],
            .op ⟨419⟩ [8] (.compute [0] (.row (.inl (.field .add .bls12381Fr .all)))) [3, 7],
            .op ⟨420⟩ [9] (.event (.flow .message 0 [1]) frTy) [8],
            .op ⟨421⟩ [10] (.compute [1] (.row (.inl (.group .scale (.group .g1))))) [0, 9],
            .op ⟨422⟩ [11] (.compute [1] (.row (.inl (.group .scale (.group .g1))))) [1, 6],
            .op ⟨423⟩ [12] (.compute [1] (.row (.inl (.group .add (.group .g1))))) [5, 11],
            .op ⟨424⟩ [13] (.compute [1] (.row (.inl (.group .equal (.group .g1))))) [10, 12],
            .guard ⟨425⟩ [1] 13 .reject
          ] [])
        ] [])

    let helpers : List (Definition b.vocabulary) := [
      CfrgVectors.rowWrap b ⟨2⟩ primStart [byteSeqTy] [stTy],
      CfrgVectors.rowWrap b ⟨3⟩ primAbsorb [stTy, byteSeqTy, byteSeqTy] [stTy],
      CfrgVectors.rowWrap b ⟨4⟩ primEncG1 [g1Ty] [byteSeqTy],
      CfrgVectors.rowWrap b ⟨5⟩ primEncFr [frTy] [byteSeqTy],
      CfrgVectors.rowWrap b ⟨6⟩ primDerFr [stTy, byteSeqTy] [frTy, stTy],
      CfrgVectors.rowWrap b ⟨7⟩ primLayWG1 [g1Ty] [byteSeqTy],
      CfrgVectors.readWrap b ⟨8⟩ primLayRG1 g1Ty,
      CfrgVectors.rowWrap b ⟨9⟩ primLayEG1 [g1Ty, g1Ty] [.bool],
      CfrgVectors.rowWrap b ⟨10⟩ primLayWFr [frTy] [byteSeqTy],
      CfrgVectors.readWrap b ⟨11⟩ primLayRFr frTy,
      CfrgVectors.rowWrap b ⟨12⟩ primLayEFr [frTy, frTy] [.bool]
    ]
    let prog : NamedProgram b.vocabulary := ⟨protoDef :: helpers⟩
    let admitted ← match Core.admit prog ⟨[], [], [], [], []⟩ with
      | .ok a => .ok a
      | .error errs => .error s!"retry Core.admit refused ({errs.length})"
    let enc := Project.linkedEncoder b
    let suiteRef : Core.ModuleRef := {
      members := [
        (SuiteSlot.start, ⟨2⟩), (SuiteSlot.absorb, ⟨3⟩),
        (SuiteSlot.encode, ⟨4⟩), (SuiteSlot.encode, ⟨5⟩), (SuiteSlot.derive, ⟨6⟩)
      ]
      lawMembers := [(SuiteSlot.derive, enc.lawKey lawFr, ⟨6⟩)]
    }
    let layoutRef : Core.ModuleRef := {
      members := [
        (LayoutSlot.write, ⟨7⟩), (LayoutSlot.read, ⟨8⟩), (LayoutSlot.equal, ⟨9⟩),
        (LayoutSlot.write, ⟨10⟩), (LayoutSlot.read, ⟨11⟩), (LayoutSlot.equal, ⟨12⟩)
      ]
    }
    let decl : Core.Declaration := {
      key := ⟨100⟩
      entry := ⟨1⟩
      kinds := [.online, .online]
      construction := .derived suiteRef none
      prover := some 0
      layout := some { «module» := layoutRef, carry := [], recover := [] }
      retry := some (bound, ⟨[], ⟨409⟩⟩)
      samples := none
      context := []
      grinds := []
      commits := []
      pins := []
      application := []
    }
    let deployed ← match Core.deploy enc admitted decl with
      | .ok d => .ok d
      | .error errs => .error s!"retry Core.deploy refused ({errs.length})"
    match hM : linkedModel? b with
    | .error err => .error err
    | .ok M =>
        have hC := linkedModel?_carriers hM
        let src := seededSource b M hC (utf8Bytes "zkc-retry-rollback-seed")
        let g := g1Generator
        let sk : Nat := 314159
        let pk := g1Scale g sk
        let inputs := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr sk]
        let pIns ← buildRoleInputs b M hC 0 deployed.entry.ins inputs
        let vIns ← buildRoleInputs b M hC 1 deployed.entry.ins inputs
        match hPT : Stack.Takes (deployed.stack 0), hVT : Stack.Takes (deployed.stack 1) with
        | [], [.seq (.fin 256) none] =>
            let pTaken : HList M.Val (Stack.Takes (deployed.stack 0)) := hPT.symm ▸ .nil
            let (oE, _) := runDeployed M deployed 0 pIns pTaken src 100000
            let (oC, _) := runDeployedClosed M deployed 0 pIns pTaken src 100000
            if bound > 1 then
              let pfE ← extractProofBytes oE
              let pfC ← extractProofBytes oC
              let vTaken : HList M.Val (Stack.Takes (deployed.stack 1)) := hVT.symm ▸ (.cons pfE .nil)
              let (vE, _) := runDeployed M deployed 1 vIns vTaken src 100000
              let (vC, _) := runDeployedClosed M deployed 1 vIns vTaken src 100000
              let vOk := match vE, vC with
                | .ended (.returned _), .ended (.returned _) => true
                | _, _ => false
              return [
                check s!"Retry (bound={bound}): attempt 0 aborts+rolls back, attempt 1 proves (Core.execute == runClosed, 80B)"
                  (pfE.length == 80 && pfE == pfC) s!"{pfE.length}B",
                check s!"Retry (bound={bound}): verifier accepts attempt-1 proof (Core.execute == runClosed)"
                  vOk "accept"
              ]
            else
              let exOk := match oE, oC with
                | .ended (.stopped s1@(.declared .exhausted _)),
                  .ended (.stopped s2@(.declared .exhausted _)) => s1 == s2
                | _, _ => false
              return [
                check s!"Retry (bound={bound}): both Core.execute & runClosed stop with identical .declared .exhausted"
                  exOk "exact Stop match"
              ]
        | _, _ => .error "unexpected retry stack signature"

  let mut out : List TestResult := []
  match runCase 4 with
  | .ok rs => out := out ++ rs
  | .error err => out := out ++ [check "Retry (bound=4)" false err]
  match runCase 1 with
  | .ok rs => out := out ++ rs
  | .error err => out := out ++ [check "Retry (bound=1)" false err]
  return out

/-- 9. `deployProtocolWithSuite`: dynamically deploy `schnorr_example.zkc`'s `Schnorr<G1>` root
with BOTH pure Core IR `HashChain<Sha256, Fr>` AND `CfrgShake128`. -/
def testProtocolRootSuites : IO (List TestResult) := do
  match ← compileFiles #["../../examples/schnorr_example.zkc"] with
  | .error err => return [check "deployProtocolWithSuite compile" false err]
  | .ok state =>
      let mut out : List TestResult := []
      let g := g1Generator
      let sk : Nat := 0x9876543210fedcba
      let pk := g1Scale g sk
      let inputs := [DynVal.g1 g, DynVal.g1 pk, DynVal.fr sk]
      for (label, suite) in [
        ("HashChain<Sha256, Fr>", SuiteSpec.hashChain .sha256 .bls12381Fr),
        ("CFRG SHAKE128", SuiteSpec.cfrgShake128 false)
      ] do
        match deployProtocolWithSuite state "Schnorr" suite with
        | .error err => out := out ++ [check s!"deployProtocolWithSuite ({label})" false err]
        | .ok cs =>
            match hM : linkedModel? cs.bindings with
            | .error err => out := out ++ [check s!"deployProtocolWithSuite ({label}) linkedModel?" false err]
            | .ok M =>
                have hC := linkedModel?_carriers hM
                let src := seededSource cs.bindings M hC (utf8Bytes s!"seed-{label}")
                match proveDifferential cs M hC src inputs with
                | .error err => out := out ++ [check s!"deployProtocolWithSuite ({label}) prove" false err]
                | .ok pf =>
                    match verifyDifferential cs M hC src inputs pf with
                    | .ok none =>
                        out := out ++ [
                          check s!"deployProtocolWithSuite ({label}): prove+verify (Core.execute == runClosed, {pf.length}B)"
                            (pf.length == 80 && cs.ideal?.isSome) "accept + ideal-RO"
                        ]
                    | _ => out := out ++ [check s!"deployProtocolWithSuite ({label}) verify" false "rejected"]
      return out

/-- Run all 9 end-to-end runtime verification example suites. -/
def runExamplesSuite : IO (List TestResult) := do
  let mut all : List TestResult := []
  all := all ++ (← testSchnorrExample)
  all := all ++ (← testChaumPedersenExample)
  all := all ++ (← testSigmaOrExample)
  all := all ++ (← testSumcheckExample)
  all := all ++ (← testPoseidon2KoalaBear)
  all := all ++ (← testInteractiveScheme)
  all := all ++ (← testRetryWithAbort)
  all := all ++ (← testProtocolRootSuites)
  return all

end Zkc.Tests.Runtime
