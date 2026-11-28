import Zkc.Tests.Core.Deployment.Fixtures

/-!
Behavioral and regression checks for:
- Canonical wire formats (`Zkc.Core.Format.Canonical`).
- Standard, multi-draw, compact, authored, branching, subprotocol-apply, looped, retried,
  interactive, and ideal random-oracle deployments (`Core.deploy`, `Core.deployIdeal`, `Core.execute`).
- Distribution-aware `V.LawKey` dispatch in `SuiteSlot.derive` (`ModuleRef.lawMembers`).
- Linear-size DAG-preserving multi-procedure specialization (`Core.specialize` on depth-8 diamond
  DAG with 256 call paths).
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

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
    deployedIdentity schnorrDeployed ≠
      deployedIdentity schnorrTaggedDeployed ∧
    deployedIdentity schnorrTaggedDeployed ≠
      deployedIdentity schnorrTaggedOtherAppDeployed ∧
    deployedIdentity schnorrDeployed ≠
      deployedIdentity schnorrAppCtxDeployed ∧
    deployedIdentity schnorrDeployed ≠
      deployedIdentity schnorrCompactDeployed := by
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

/-- Weak Fiat–Shamir prevention and session-tag + application binding. -/
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
      decide (ps1.getD 0 0 ≠ ps2.getD 0 0) &&
      decide (ps1.getD 0 0 ≠ psApp.getD 0 0) &&
      runVerify schnorrSamplesDeployed 13 ps1 &&
      runVerify schnorrSamplesDeployed 2 ps2 &&
      runVerify schnorrSamplesAppDeployed 13 psApp &&
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

/-! ## Multi-draw, compact layout, and retried attempt execution -/

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

def checkRetrySchnorr : Bool :=
  let sessBytes := 0 :: retrySchnorrDeployed.identity
  match runProve retrySchnorrDeployed 7 13 0,
      runProveSpecialized retrySchnorrDeployed 7 13 0 with
  | some p1, some p2 =>
      let baseHash := mixBytes (mixBytes 7 sessBytes + 13) (encodeSite ⟨[], ⟨410⟩⟩)
      let r0 := baseHash % 11
      let r1 := (baseHash + 17 + 1) % 11
      let commit0 := powMod 2 r0 23
      let commit1 := powMod 2 r1 23
      let rejStmts := ([1, 2, 3, 4].filter fun y => !runVerify retrySchnorrDeployed y p1).length
      decide (p1 = p2) &&
      decide (p1.length = 2) &&
      decide (commit0 ≠ commit1) &&
      decide (p1.getD 0 0 = commit1) &&
      runVerify retrySchnorrDeployed 13 p1 &&
      runVerifySpecialized retrySchnorrDeployed 13 p1 &&
      decide (rejStmts ≥ 3)
  | _, _ => false

theorem retry_schnorr_rollback_and_specialized : checkRetrySchnorr = true := by
  decide +kernel

/-! ## Pure collision-free ideal random-oracle deployment (`deployIdeal`) -/

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

/-! ## Interactive two-role scheduler, trailing-message elision, and identity injectivity -/

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

theorem site_label_through_path_separation :
    msgLabel ⟨[⟨1⟩], ⟨5⟩⟩ ≠ msgLabel ⟨[⟨2⟩], ⟨5⟩⟩ ∧
    msgLabel ⟨[], ⟨5⟩⟩ ≠ msgLabel ⟨[⟨1⟩], ⟨5⟩⟩ ∧
    drawLabel ⟨[⟨1⟩], ⟨5⟩⟩ ≠ drawLabel ⟨[⟨2⟩], ⟨5⟩⟩ ∧
    msgLabel ⟨[⟨1⟩], ⟨5⟩⟩ ≠ drawLabel ⟨[⟨1⟩], ⟨5⟩⟩ := by
  decide +kernel

theorem deployed_identity_determines_declaration
    {a₁ a₂ : Admitted deployVocab} {decl₁ decl₂ : Declaration}
    (d₁ d₂ : Deployed deployVocab)
    (h₁ : deploy deployEncoder a₁ decl₁ = .ok d₁)
    (h₂ : deploy deployEncoder a₂ decl₂ = .ok d₂)
    (h : deployedIdentity d₁ = deployedIdentity d₂) :
    d₁.declaration = d₂.declaration := by
  have hD := (deploy_identity_injective deployEncoder deployEncoder_injective h₁ h₂ h).1
  have hKeep₁ := (deploy_keeps deployEncoder a₁ decl₁ d₁ h₁).2.1
  have hKeep₂ := (deploy_keeps deployEncoder a₂ decl₂ d₂ h₂).2.1
  rw [hKeep₁, hKeep₂, hD]

/-! ## Distribution-aware `V.LawKey` dispatch (`uniform` vs `nonzero` on `.fin 11`) -/

private def tlInputs (insTys : List (LTy twoLawVocab)) (witness statement : Nat) :
    Option (HList (LVal twoLawModel) insTys) :=
  match insTys with
  | [⟨.fin 11, [0]⟩, ⟨.fin 11, [0, 1]⟩] =>
      some (.cons (witness : Nat) (.cons (statement : Nat) .nil))
  | _ => none

private def tlExtractProof : {ts : List (Ty Empty)} → HList twoLawModel.Val ts → Option (List Nat)
  | [.seq (.fin 256) none], .cons bs .nil => some bs
  | _, _ => none

private def tlPackProof (bs : List Nat) : (ts : List (Ty Empty)) → Option (HList twoLawModel.Val ts)
  | [.seq (.fin 256) none] => some (.cons bs .nil)
  | _ => none

private def runTwoLawProve (d : Deployed twoLawVocab) (w y : Nat) : Option (List Nat) :=
  if hEmpty : Stack.Takes (d.stack 0) = [] then
    (tlInputs d.entry.ins w y).bind fun ins =>
      (prove execute d twoLawModel 0 (hideAll twoLawModel 0 ins) hEmpty
        (fun _ _ => none) 128).bind tlExtractProof
  else none

private def runTwoLawProveSpec (d : Deployed twoLawVocab) (w y : Nat) : Option (List Nat) :=
  if hEmpty : Stack.Takes (d.stack 0) = [] then
    (tlInputs d.entry.ins w y).bind fun ins =>
      let cr := specialize d 0
      let p := cr.denote twoLawModel (Defs.fnTable twoLawModel d.admitted.program.defs)
        (hideAll twoLawModel 0 ins) (cast (congrArg (HList twoLawModel.Val) hEmpty.symm) .nil)
      match (runProcess twoLawModel (fun _ _ => none) 0 p 128).1 with
      | .ended (.returned (_, gives)) => tlExtractProof gives
      | _ => none
  else none

private def runTwoLawVerify (d : Deployed twoLawVocab) (y : Nat) (proof : List Nat) : Bool :=
  match tlInputs d.entry.ins 0 y, tlPackProof proof (Stack.Takes (d.stack 1)) with
  | some ins, some taken =>
      (verify execute d twoLawModel 1 (hideAll twoLawModel 1 ins) taken
        (fun _ _ => none) 128).isSome
  | _, _ => false

private def runTwoLawVerifySpec (d : Deployed twoLawVocab) (y : Nat) (proof : List Nat) : Bool :=
  match tlInputs d.entry.ins 0 y, tlPackProof proof (Stack.Takes (d.stack 1)) with
  | some ins, some taken =>
      let cr := specialize d 1
      let p := cr.denote twoLawModel (Defs.fnTable twoLawModel d.admitted.program.defs)
        (hideAll twoLawModel 1 ins) taken
      match (runProcess twoLawModel (fun _ _ => none) 1 p 128).1 with
      | .ended (.returned _) => true
      | _ => false
  | _, _ => false

/-- Verifies law-keyed `SuiteSlot.derive` resolves `.uniform → ⟨104⟩` and `.nonzero → ⟨105⟩` on the
same Core type `.fin 11`, executes end-to-end prove/verify & specialized prove/verify cleanly, and
commits `lawMembers` into `deployedIdentity` (distinct proofs and identities across suites). -/
def checkTwoLawDispatchAndExecution : Bool :=
  let dUnif := (findSuiteDerive twoLawEncoder admittedTwoLaw twoLawSuite .nat .uniform [] tlElem).map (·.hdr.key)
  let dNonZ := (findSuiteDerive twoLawEncoder admittedTwoLaw twoLawSuite .nat .nonzero [] tlElem).map (·.hdr.key)
  match runTwoLawProve twoLawDeployed 4 4, runTwoLawProveSpec twoLawDeployed 4 4,
      runTwoLawProve twoLawSwappedDeployed 4 4 with
  | some p1, some p2, some pSwap =>
      let rejStmts := ([0, 1, 2, 3, 5, 6].filter fun y => !runTwoLawVerify twoLawDeployed y p1).length
      decide (dUnif = some ⟨104⟩) &&
      decide (dNonZ = some ⟨105⟩) &&
      decide (deployedIdentity twoLawDeployed ≠
        deployedIdentity twoLawSwappedDeployed) &&
      decide (p1 = p2) &&
      decide (p1 ≠ pSwap) &&
      runTwoLawVerify twoLawDeployed 4 p1 &&
      runTwoLawVerifySpec twoLawDeployed 4 p1 &&
      decide (rejStmts ≥ 4) &&
      !runTwoLawVerify twoLawDeployed 4 pSwap &&
      runTwoLawVerify twoLawSwappedDeployed 4 pSwap
  | _, _, _ => false

theorem twoLaw_distribution_dispatch_and_execution :
    checkTwoLawDispatchAndExecution = true := by
  decide +kernel

/-! ## Depth-8 diamond-DAG specialization (`2^8 = 256` call paths, linear `astSize`) -/

/-- Verifies that specializing `dagSchnorrDeployed` (depth-8 diamond DAG = 256 dynamic call paths)
deduplicates all 9 subprotocol levels into exactly 9 shared `ClosedProcs` with strictly linear
`astSize < 160` on BOTH prover and verifier, while preserving exact prove/verify behavior. -/
def checkDagLinearSizeAndExecution : Bool :=
  let crP := specialize dagSchnorrDeployed 0
  let crV := specialize dagSchnorrDeployed 1
  match runProve dagSchnorrDeployed 7 13 5, runProveSpecialized dagSchnorrDeployed 7 13 5 with
  | some p1, some p2 =>
      decide (crP.procSigs.length = 9) &&
      decide (crV.procSigs.length = 9) &&
      decide (crP.astSize < 160) &&
      decide (crV.astSize < 160) &&
      decide (p1 = p2) &&
      decide (p1.length = 2) &&
      runVerify dagSchnorrDeployed 13 p1 &&
      runVerifySpecialized dagSchnorrDeployed 13 p1 &&
      !runVerify dagSchnorrDeployed 12 p1
  | _, _ => false

theorem dag_specialize_linear_size_and_execution :
    checkDagLinearSizeAndExecution = true := by
  decide +kernel

end Zkc.Core.Tests.Deployment
