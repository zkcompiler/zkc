import Zkc.Tests.Core.Deployment.Fixtures

/-!
Targeted regression tests and kernel-checked witnesses for deployment hardening:

1. Bound canonical deployment identity under swapped vocabulary encoders (no encoder argument on read).
2. Deploy-time refusal of non-injective encoders on used laws (`deploy` and `deployIdeal`).
3. Strict unambiguous `ModuleRef.lawMembers` resolution (wrong-typed explicit entry refuses instead
   of falling back to a generic default; duplicate explicit and duplicate default entries refuse).
4. Exact caller-mapped recipient sets (`getters = [verifier]`, `hearers = [prover]`), operand-bearing
   prover private coins under `samples`, and `deployIdeal` colliding `serviceKey` refusal.
5. Definition-order-, proof-note-, and dead-definition-invariant canonical identity (`schemeIdentity`).
6. Role-projected dead-procedure elimination in `Core.specialize` (prover-only branch subprotocol
   produces 0 shared procedures in the verifier's `ClosedRole`).
7. Selected-function `Deployed.SuiteLawfulFor` witness (`deploy_complete` succeeds even when a
   shadowed generic default violates an overridden law's support so universal `SuiteLawful` is false).
8. Site-sensitive `Deployed.SamplesLawfulFor` witness (`deploy_complete_samples` succeeds on the
   empty world `fun _ _ => none` even when the sampler returns an invalid value on other sites so
   site-agnostic `SamplesLawful` is false).
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

set_option maxRecDepth 16000

private theorem hCastInj {α β : Type} {h : α = β} {x y : α}
    (heq : cast h x = cast h y) : x = y := by
  subst h; exact heq

/-! ## 1. Bound identity under swapped encoders (no encoder re-supply on read) -/

/-- Alternate injective encoder for `twoLawVocab` that swaps `.uniform` and `.nonzero` bytes. -/
def twoLawEncoderSwapped : VocabEncoder twoLawVocab where
  typeKey k := nomatch k
  rowKey := twoLawEncoder.rowKey
  lawKey
    | .uniform => [1]
    | .nonzero => [0]

def twoLawSwappedEncDeployed : Deployed twoLawVocab :=
  (deploy twoLawEncoderSwapped admittedTwoLaw twoLawDecl).toOption.get (by decide +kernel)

private def hTlInputs (insTys : List (LTy twoLawVocab)) (w y : Nat) :
    Option (HList (LVal twoLawModel) insTys) :=
  match insTys with
  | [⟨.fin 11, [0]⟩, ⟨.fin 11, [0, 1]⟩] => some (.cons (w : Nat) (.cons (y : Nat) .nil))
  | _ => none

private def hTlExtract : {ts : List (Ty Empty)} → HList twoLawModel.Val ts → Option (List Nat)
  | [.seq (.fin 256) none], .cons bs .nil => some bs
  | _, _ => none

private def hTlProve (d : Deployed twoLawVocab) (w y : Nat) : Option (List Nat) :=
  if hEmpty : Stack.Takes (d.stack 0) = [] then
    (hTlInputs d.entry.ins w y).bind fun ins =>
      (prove execute d twoLawModel 0 (hideAll twoLawModel 0 ins) hEmpty
        (fun _ _ => none) 128).bind hTlExtract
  else none

/-- Deploying the exact same `twoLawDecl` under swapped encoders selects `[104, 105]` vs `[105, 104]`
and commits distinct identities directly into `Deployed.identity` (`deployedIdentity d₁ ≠ deployedIdentity d₂`)
without requiring readers to supply an encoder. -/
def checkBoundIdentitySwappedEncoders : Bool :=
  let u1 := (findSuiteDerive twoLawEncoder admittedTwoLaw twoLawSuite .nat .uniform [] tlElem).map (·.hdr.key)
  let n1 := (findSuiteDerive twoLawEncoder admittedTwoLaw twoLawSuite .nat .nonzero [] tlElem).map (·.hdr.key)
  let u2 := (findSuiteDerive twoLawEncoderSwapped admittedTwoLaw twoLawSuite .nat .uniform [] tlElem).map (·.hdr.key)
  let n2 := (findSuiteDerive twoLawEncoderSwapped admittedTwoLaw twoLawSuite .nat .nonzero [] tlElem).map (·.hdr.key)
  match hTlProve twoLawDeployed 4 4, hTlProve twoLawSwappedEncDeployed 4 4 with
  | some p1, some p2 =>
      decide (u1 = some ⟨104⟩) &&
      decide (n1 = some ⟨105⟩) &&
      decide (u2 = some ⟨105⟩) &&
      decide (n2 = some ⟨104⟩) &&
      decide (deployedIdentity twoLawDeployed ≠ deployedIdentity twoLawSwappedEncDeployed) &&
      decide (p1 ≠ p2)
  | _, _ => false

theorem bound_identity_swapped_encoders : checkBoundIdentitySwappedEncoders = true := by
  decide +kernel

/-! ## 2. Non-injective encoder refusal on used laws -/

/-- Non-injective encoder collapsing `.uniform` and `.nonzero` to identical bytes `[0]`. -/
def twoLawEncoderColliding : VocabEncoder twoLawVocab where
  typeKey k := nomatch k
  rowKey := twoLawEncoder.rowKey
  lawKey _ := [0]

private def failsWith {V : Vocabulary} (res : Except (List (ProgramRefusal V)) (Deployed V))
    (r : Rule) : Bool :=
  match res with
  | .error errs => errs.any (fun e => decide (e.rule = r))
  | .ok _ => false

theorem non_injective_encoder_refused :
    failsWith (deploy twoLawEncoderColliding admittedTwoLaw twoLawDecl) .protocol = true ∧
    failsWith (deployIdeal twoLawEncoderColliding idealServiceKey admittedTwoLaw twoLawDecl) .protocol = true := by
  decide +kernel

/-! ## 3. Strict unambiguous `ModuleRef.lawMembers` resolution -/

/-- Suite with a wrong-typed explicit `lawMembers` entry (`⟨102⟩`) alongside a valid generic
default (`⟨104⟩`): must be refused rather than silently falling back to `⟨104⟩`. -/
def twoLawSuiteWrongExplicit : ModuleRef where
  members := twoLawSuite.members ++ [(SuiteSlot.derive, ⟨104⟩)]
  lawMembers := [
    (SuiteSlot.derive, twoLawEncoder.lawKey .nonzero, ⟨102⟩)
  ]

/-- Suite with two valid explicit `lawMembers` entries for `.uniform`: must be refused as ambiguous. -/
def twoLawSuiteDupExplicit : ModuleRef where
  members := twoLawSuite.members
  lawMembers := [
    (SuiteSlot.derive, twoLawEncoder.lawKey .uniform, ⟨104⟩),
    (SuiteSlot.derive, twoLawEncoder.lawKey .uniform, ⟨105⟩),
    (SuiteSlot.derive, twoLawEncoder.lawKey .nonzero, ⟨105⟩)
  ]

/-- Suite with two valid generic default `SuiteSlot.derive` entries in `members`: must be refused. -/
def twoLawSuiteDupDefault : ModuleRef where
  members := twoLawSuite.members ++ [(SuiteSlot.derive, ⟨104⟩), (SuiteSlot.derive, ⟨105⟩)]
  lawMembers := []

theorem strict_lawMembers_resolution_controls :
    failsWith (deploy twoLawEncoder admittedTwoLaw
      { twoLawDecl with construction := .derived twoLawSuiteWrongExplicit none }) .callee = true ∧
    failsWith (deploy twoLawEncoder admittedTwoLaw
      { twoLawDecl with construction := .derived twoLawSuiteDupExplicit none }) .callee = true ∧
    failsWith (deploy twoLawEncoder admittedTwoLaw
      { twoLawDecl with construction := .derived twoLawSuiteDupDefault none }) .callee = true := by
  decide +kernel

/-! ## 4. Exact recipient sets, operand-bearing private coins, and `deployIdeal` `serviceKey` collision -/

private def minimalSuiteDefs : List (Definition deployVocab) :=
  [fnStart, fnAbsorb, fnEncodeScalar, fnEncodePoint, fnDeriveScalar, fnReadScalar, fnReadPoint]

/-- 3-role protocol whose flow sends to `[1, 2]` (verifier + service): must be refused. -/
def multicastFlowProto : Definition deployVocab :=
  .protocol ⟨220⟩ 3 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨2201⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨2202⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨2203⟩ [4] (.event (.flow .message 0 [1, 2]) dPoint) [3],
      .op ⟨2204⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) []] [])

/-- 3-role protocol whose verifier public coin has extra listener `[0, 2]`: must be refused. -/
def multicastCoinProto : Definition deployVocab :=
  .protocol ⟨221⟩ 3 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨2211⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨2212⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨2213⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
      .op ⟨2214⟩ [5] (.event (.given (.coin ()) 1 [0, 2]) dScalar) []] [])

/-- 3-role authored protocol whose flow sends to `[1, 2]`: must be refused. -/
def authoredMulticastProto : Definition deployVocab :=
  .protocol ⟨222⟩ 3 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨2221⟩ [2] (.event (.flow .message 0 [1, 2]) dPoint) [1]] [])

/-- 2-role protocol issuing `.request idealServiceKey`: must be refused by `deployIdeal` for
`idealServiceKey` and accepted for a fresh service key `⟨998⟩`. -/
def collidingReqProto : Definition deployVocab :=
  .protocol ⟨223⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨2231⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨2232⟩ [3] (.compute [0] (.row .base)) [2],
      .op ⟨2233⟩ [4] (.event (.flow .message 0 [1]) dPoint) [3],
      .op ⟨2234⟩ [5] (.event (.given (.coin ()) 1 [0]) dScalar) [],
      .op ⟨2235⟩ [6] (.event (.given (.request idealServiceKey) 1 []) dScalar) [1]] [])

def controlProgram : NamedProgram deployVocab where
  definitions := minimalSuiteDefs ++
    [multicastFlowProto, multicastCoinProto, authoredMulticastProto, collidingReqProto]

private theorem admittedControl_isSome :
    (admit controlProgram noAssociation).toOption.isSome = true := by
  decide +kernel

def admittedControl : Admitted deployVocab :=
  (admit controlProgram noAssociation).toOption.get admittedControl_isSome

private def threeRoleDecl (entry : Key) (con : Construction := .derived toySuite none) : Declaration where
  key := ⟨30⟩
  entry := entry
  kinds := [.online, .online, .offline]
  construction := con
  prover := none
  layout := some ⟨toyLayoutModule, [], []⟩
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

/-- Vocabulary with a 1-operand sampling law (`[fin 256] → fin 256`) to test deterministic `samples`
refusal on operand-bearing prover private coins. -/
def operandCoinVocab : Vocabulary where
  TypeKey := Empty
  RowKey := Empty
  LawKey := Unit
  row r := nomatch r
  law _ := some ⟨[.fin 256], .fin 256⟩
  literal _ _ := true
  decided k := nomatch k

def operandCoinEncoder : VocabEncoder operandCoinVocab where
  typeKey k := nomatch k
  rowKey r := nomatch r
  lawKey _ := [0]

private abbrev ocByte : Ty Empty := .fin 256
private abbrev ocBytes : Ty Empty := .seq ocByte none

def ocFnStart : Definition operandCoinVocab :=
  .fn ⟨100⟩ [ocBytes] [.nat] false none Summary.empty (.mk [0] [
    .op ⟨1⟩ [1] (.literal .nat [0]) []] [1])

def ocFnAbsorb : Definition operandCoinVocab :=
  .fn ⟨101⟩ [.nat, ocBytes, ocBytes] [.nat] false none Summary.empty (.mk [0, 1, 2] [] [0])

def ocFnEncode : Definition operandCoinVocab :=
  .fn ⟨102⟩ [ocByte] [ocBytes] false none Summary.empty (.mk [0] [
    .op ⟨1⟩ [1] (.owned .seqFill [.seq ocByte (some 1)] []) [0],
    .op ⟨2⟩ [2] (.owned .seqUnsized [.seq ocByte (some 1)] []) [1]] [2])

def ocFnRead : Definition operandCoinVocab :=
  .fn ⟨103⟩ [ocBytes, .nat] [ocByte, .nat] true none Summary.empty (.mk [0, 1] [
    .op ⟨1⟩ [2] (.owned .seqLength [ocBytes] []) [0],
    .op ⟨2⟩ [3] (.owned .natLess [] []) [1, 2],
    .guard ⟨3⟩ () 3 .reject,
    .op ⟨4⟩ [4] (.owned .seqAt [ocBytes] []) [0, 1],
    .op ⟨5⟩ [5] (.literal .nat [1]) [],
    .op ⟨6⟩ [6] (.owned .natAdd [] []) [1, 5]] [4, 6])

def ocFnSamples : Definition operandCoinVocab :=
  .fn ⟨109⟩ [ocByte, ocBytes, ocBytes, .nat, .nat] [ocByte] false none Summary.empty
    (.mk [0, 1, 2, 3, 4] [] [0])

def ocProto : Definition operandCoinVocab :=
  .protocol ⟨200⟩ 2 [⟨ocByte, [0, 1]⟩] []
    (.mk [0] [
      .op ⟨10⟩ [1] (.event (.given (.coin ()) 0 []) ocByte) [0],
      .op ⟨11⟩ [2] (.event (.flow .message 0 [1]) ocByte) [1]] [])

def ocProgram : NamedProgram operandCoinVocab where
  definitions := [ocFnStart, ocFnAbsorb, ocFnEncode, ocFnRead, ocFnSamples, ocProto]

private theorem admittedOc_isSome :
    (admit ocProgram noAssociation).toOption.isSome = true := by
  decide +kernel

def admittedOc : Admitted operandCoinVocab :=
  (admit ocProgram noAssociation).toOption.get admittedOc_isSome

def ocDecl : Declaration where
  key := ⟨1⟩
  entry := ⟨200⟩
  kinds := [.online, .online]
  construction := .derived
    ⟨[(SuiteSlot.start, ⟨100⟩), (SuiteSlot.absorb, ⟨101⟩), (SuiteSlot.encode, ⟨102⟩)], []⟩ none
  prover := none
  layout := some ⟨⟨[(LayoutSlot.write, ⟨102⟩), (LayoutSlot.read, ⟨103⟩)], []⟩, [], []⟩
  retry := none
  samples := some ⟨109⟩
  context := []
  grinds := []
  commits := []
  pins := []

theorem exact_recipients_operand_and_serviceKey_refusals :
    -- Multicast flow `[1, 2]` refused by `deploy`, `deployIdeal`, and authored `deploy`
    failsWith (deploy deployEncoder admittedControl (threeRoleDecl ⟨220⟩)) .protocol = true ∧
    failsWith (deployIdeal deployEncoder idealServiceKey admittedControl (threeRoleDecl ⟨220⟩)) .protocol = true ∧
    failsWith (deploy deployEncoder admittedControl (threeRoleDecl ⟨222⟩ .authored)) .protocol = true ∧
    -- Multicast public coin `[0, 2]` refused by `deploy` and `deployIdeal`
    failsWith (deploy deployEncoder admittedControl (threeRoleDecl ⟨221⟩)) .protocol = true ∧
    failsWith (deployIdeal deployEncoder idealServiceKey admittedControl (threeRoleDecl ⟨221⟩)) .protocol = true ∧
    -- Operand-bearing prover private coin under `samples` refused with `Rule.operands`
    failsWith (deploy operandCoinEncoder admittedOc ocDecl) .operands = true ∧
    -- Colliding `idealServiceKey` refused by `deployIdeal`, while fresh `⟨998⟩` succeeds
    failsWith (deployIdeal deployEncoder idealServiceKey admittedControl
      { schnorrDecl with entry := ⟨223⟩ }) .protocol = true ∧
    (deployIdeal deployEncoder ⟨998⟩ admittedControl
      { schnorrDecl with entry := ⟨223⟩ }).isOk = true := by
  decide +kernel

/-! ## 5. Order-, proof-note-, and dead-definition-invariant canonical identity -/

private def fnStartLoop (notes : BodyAnalysis.Annotations (LocalRaw deployVocab)) :
    Definition deployVocab :=
  .fn ⟨100⟩ [dBytes] [.nat] false none Summary.empty (.mk [0] [
    .loop ⟨1⟩ () (.fixed 1) [] [] (.mk [5] [] []),
    .op ⟨2⟩ [1] (.literal .nat [1]) [],
    .op ⟨3⟩ [2] (.row .mix) [1, 0]] [2]) notes

private def fnDeadHelper : Definition deployVocab :=
  .fn ⟨199⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [] [0])

def canonProgA : NamedProgram deployVocab where
  definitions := [fnStartLoop [], fnAbsorb, fnEncodeScalar, fnEncodePoint, fnDeriveScalar,
    fnReadScalar, fnReadPoint, schnorrProto]

def canonProgB : NamedProgram deployVocab where
  definitions := [fnDeadHelper, fnReadPoint, fnReadScalar, fnDeriveScalar,
    fnEncodePoint, fnEncodeScalar, fnAbsorb,
    fnStartLoop [(.instruction .root ⟨1⟩, .invariant [] [])], schnorrProto]

private theorem admittedCanonA_isSome :
    (admit canonProgA noAssociation).toOption.isSome = true := by decide +kernel

private theorem admittedCanonB_isSome :
    (admit canonProgB noAssociation).toOption.isSome = true := by decide +kernel

def admittedCanonA : Admitted deployVocab :=
  (admit canonProgA noAssociation).toOption.get admittedCanonA_isSome

def admittedCanonB : Admitted deployVocab :=
  (admit canonProgB noAssociation).toOption.get admittedCanonB_isSome

def canonDeployedA : Deployed deployVocab :=
  (deploy deployEncoder admittedCanonA schnorrDecl).toOption.get (by decide +kernel)

def canonDeployedB : Deployed deployVocab :=
  (deploy deployEncoder admittedCanonB schnorrDecl).toOption.get (by decide +kernel)

/-- Reordering independent definitions, adding proof-only `BodyAnalysis.Annotation` loop invariants,
and inserting unreachable definitions all produce byte-identical `deployedIdentity` and session bytes. -/
theorem canonical_identity_order_and_note_invariant :
    deployedIdentity canonDeployedA = deployedIdentity canonDeployedB ∧
    (match resolveSessionBytes deployEncoder admittedCanonA schnorrDecl none,
           resolveSessionBytes deployEncoder admittedCanonB schnorrDecl none with
     | .ok ⟨bsA, _⟩, .ok ⟨bsB, _⟩ => decide (bsA = bsB)
     | _, _ => false) = true := by
  decide +kernel

/-! ## 6. Role-projected dead-procedure elimination in `Core.specialize` -/

/-- 1-role subprotocol helper invoked only inside a prover-only `.choose` branch. -/
def proverHelperProto : Definition deployVocab :=
  .protocol ⟨225⟩ 1 [⟨dScalar, [0]⟩] [⟨dScalar, [0]⟩]
    (.mk [0] [
      .op ⟨2251⟩ [1] (.compute [0] (.row .add)) [0, 0]] [1])

/-- Schnorr protocol invoking `proverHelperProto` inside a prover-only `.choose` branch (`[0]`):
`project 1` erases the branch completely, so verifier specialization must emit 0 shared procedures. -/
def proverBranchSubProto : Definition deployVocab :=
  .protocol ⟨224⟩ 2 [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] []
    (.mk [0, 1] [
      .op ⟨2240⟩ [2] (.event (.given (.coin ()) 0 []) dScalar) [],
      .op ⟨2241⟩ [3] (.compute [0] (.row .sameScalar)) [2, 2],
      .choose ⟨2242⟩ [0] 3 [4]
        (.mk [] [.op ⟨2243⟩ [5] (.apply ⟨225⟩ [0]) [2]] [5])
        (.mk [] [] [2]),
      .op ⟨2244⟩ [6] (.compute [0] (.row .base)) [4],
      .op ⟨2245⟩ [7] (.event (.flow .message 0 [1]) dPoint) [6],
      .op ⟨2246⟩ [8] (.event (.given (.coin ()) 1 [0]) dScalar) [],
      .op ⟨2247⟩ [9] (.compute [0] (.row .mul)) [8, 0],
      .op ⟨2248⟩ [10] (.compute [0] (.row .add)) [4, 9],
      .op ⟨2249⟩ [11] (.event (.flow .message 0 [1]) dScalar) [10],
      .op ⟨2250⟩ [12] (.compute [1] (.row .base)) [11],
      .op ⟨2252⟩ [13] (.compute [1] (.row .scale)) [8, 1],
      .op ⟨2253⟩ [14] (.compute [1] (.row .plus)) [7, 13],
      .op ⟨2254⟩ [15] (.compute [1] (.row .same)) [12, 14],
      .guard ⟨2255⟩ [1] 15 .reject] [])

def proverBranchProgram : NamedProgram deployVocab where
  definitions := minimalSuiteDefs ++ [proverHelperProto, proverBranchSubProto]

private theorem admittedProverBranch_isSome :
    (admit proverBranchProgram noAssociation).toOption.isSome = true := by decide +kernel

def admittedProverBranch : Admitted deployVocab :=
  (admit proverBranchProgram noAssociation).toOption.get admittedProverBranch_isSome

def proverBranchDecl : Declaration :=
  { schnorrDecl with key := ⟨24⟩, entry := ⟨224⟩ }

def proverBranchDeployed : Deployed deployVocab :=
  (deploy deployEncoder admittedProverBranch proverBranchDecl).toOption.get (by decide +kernel)

def checkRoleProjectedDeadProcElim : Bool :=
  let crP := specialize proverBranchDeployed 0
  let crV := specialize proverBranchDeployed 1
  match runProve proverBranchDeployed 7 13 5, runProveSpecialized proverBranchDeployed 7 13 5 with
  | some p1, some p2 =>
      let rejStmts := ([1, 2, 3, 4].filter fun y => !runVerify proverBranchDeployed y p1).length
      decide (crP.procSigs.length = 1) &&
      decide (crV.procSigs.length = 0) &&
      decide (p1 = p2) &&
      runVerify proverBranchDeployed 13 p1 &&
      runVerifySpecialized proverBranchDeployed 13 p1 &&
      decide (rejStmts ≥ 3)
  | _, _ => false

theorem specialize_role_projected_dead_proc_eliminated :
    checkRoleProjectedDeadProcElim = true := by
  decide +kernel

/-! ## 7. Selected-function `Deployed.SuiteLawfulFor` witness (`¬ SuiteLawful`, yet `deploy_complete`) -/

private abbrev tlVar {T : Type} {Γ : Ctx T} {a : T} (n : Nat) (h : Γ.find? n = some a := by rfl) :
    Var Γ a := ⟨n, h⟩

private def tlWTStart {fns : List (FnHeader twoLawVocab)} :
    Term (localDialect twoLawVocab fns) (Ctx.positional [tlBytes]) [.nat] :=
  .op ⟨1⟩ (.literal .nat [1] rfl) .nil (.cons 1 .nil) <|
  .op ⟨2⟩ (.row TwoLawRow.mix _ rfl) (.cons (tlVar 1) (.cons (tlVar 0) .nil)) (.cons 2 .nil) <|
  .ret (.cons (tlVar 2) .nil)

private def tlWTAbsorb {fns : List (FnHeader twoLawVocab)} :
    Term (localDialect twoLawVocab fns) (Ctx.positional [.nat, tlBytes, tlBytes]) [.nat] :=
  .op ⟨1⟩ (.row TwoLawRow.mix _ rfl) (.cons (tlVar 0) (.cons (tlVar 1) .nil)) (.cons 3 .nil) <|
  .op ⟨2⟩ (.row TwoLawRow.mix _ rfl) (.cons (tlVar 3) (.cons (tlVar 2) .nil)) (.cons 4 .nil) <|
  .ret (.cons (tlVar 4) .nil)

private def tlWTEncode {fns : List (FnHeader twoLawVocab)} :
    Term (localDialect twoLawVocab fns) (Ctx.positional [tlElem]) [tlBytes] :=
  .op ⟨1⟩ (.row TwoLawRow.fin11ToByte _ rfl) (.cons (tlVar 0) .nil) (.cons 1 .nil) <|
  .op ⟨2⟩ (.owned (.seqFill tlByte 1 rfl)) (.cons (tlVar 1) .nil) (.cons 2 .nil) <|
  .op ⟨3⟩ (.owned (.seqUnsized tlByte 1)) (.cons (tlVar 2) .nil) (.cons 3 .nil) <|
  .ret (.cons (tlVar 3) .nil)

private def tlWTDeriveUniform {fns : List (FnHeader twoLawVocab)} :
    Term (localDialect twoLawVocab fns) (Ctx.positional [.nat, tlBytes]) [tlElem, .nat] :=
  .op ⟨1⟩ (.row TwoLawRow.squeezeUniform _ rfl) (.cons (tlVar 0) (.cons (tlVar 1) .nil))
    (.cons 2 (.cons 3 .nil)) <|
  .ret (.cons (tlVar 2) (.cons (tlVar 3) .nil))

private def tlWTDeriveNonZero {fns : List (FnHeader twoLawVocab)} :
    Term (localDialect twoLawVocab fns) (Ctx.positional [.nat, tlBytes]) [tlElem, .nat] :=
  .op ⟨1⟩ (.row TwoLawRow.squeezeNonZero _ rfl) (.cons (tlVar 0) (.cons (tlVar 1) .nil))
    (.cons 2 (.cons 3 .nil)) <|
  .ret (.cons (tlVar 2) (.cons (tlVar 3) .nil))

private def tlWTRead {fns : List (FnHeader twoLawVocab)} :
    Term (localDialect twoLawVocab fns) (Ctx.positional [tlBytes, .nat]) [tlElem, .nat] :=
  .op ⟨1⟩ (.owned (.seqLength tlByte none rfl)) (.cons (tlVar 0) .nil) (.cons 2 .nil) <|
  .op ⟨2⟩ (.owned .natLess) (.cons (tlVar 1) (.cons (tlVar 2) .nil)) (.cons 3 .nil) <|
  .guard ⟨3⟩ () (tlVar 3) rfl .reject <|
  .op ⟨4⟩ (.owned (.seqAt tlByte none rfl)) (.cons (tlVar 0) (.cons (tlVar 1) .nil)) (.cons 4 .nil) <|
  .op ⟨5⟩ (.owned (.finToNat 256)) (.cons (tlVar 4) .nil) (.cons 5 .nil) <|
  .op ⟨6⟩ (.literal .nat [11] rfl) .nil (.cons 6 .nil) <|
  .op ⟨7⟩ (.owned .natLess) (.cons (tlVar 5) (.cons (tlVar 6) .nil)) (.cons 7 .nil) <|
  .guard ⟨8⟩ () (tlVar 7) rfl .reject <|
  .op ⟨9⟩ (.row TwoLawRow.byteToFin11 _ rfl) (.cons (tlVar 4) .nil) (.cons 8 .nil) <|
  .op ⟨10⟩ (.literal .nat [1] rfl) .nil (.cons 9 .nil) <|
  .op ⟨11⟩ (.owned .natAdd) (.cons (tlVar 1) (.cons (tlVar 9) .nil)) (.cons 10 .nil) <|
  .ret (.cons (tlVar 8) (.cons (tlVar 10) .nil))

/-- Site-sensitive sampler: returns `1` (`∈ support .nonzero`) ONLY when `siteBytes.length` equals
`(encodeSite ⟨[], ⟨10⟩⟩).length`, and `0` (`∉ support .nonzero`) for any other site length. -/
private def tlWTSampleSite {fns : List (FnHeader twoLawVocab)} :
    Term (localDialect twoLawVocab fns)
      (Ctx.positional [tlElem, tlElem, tlBytes, tlBytes, .nat, .nat]) [tlElem] :=
  .op ⟨1⟩ (.owned (.seqLength tlByte none rfl)) (.cons (tlVar 3) .nil) (.cons 6 .nil) <|
  .op ⟨2⟩ (.literal .nat [(encodeSite ⟨[], ⟨10⟩⟩).length] rfl) .nil (.cons 7 .nil) <|
  .op ⟨3⟩ (.owned .natEqual) (.cons (tlVar 6) (.cons (tlVar 7) .nil)) (.cons 8 .nil) <|
  .choose ⟨4⟩ () (tlVar 8) rfl (fun _ _ => trivial)
    (.op ⟨5⟩ (.literal (V := twoLawVocab) tlElem [1] rfl) .nil (.cons 9 .nil)
      (.ret (.cons (tlVar 9) .nil)))
    (.op ⟨6⟩ (.literal (V := twoLawVocab) tlElem [0] rfl) .nil (.cons 10 .nil)
      (.ret (.cons (tlVar 10) .nil)))
    (.cons 11 .nil) <|
  .ret (.cons (tlVar 11) .nil)

private abbrev tlWHdrStart : FnHeader twoLawVocab := ⟨⟨100⟩, [tlBytes], [.nat], false, none, Summary.empty⟩
private abbrev tlWHdrAbsorb : FnHeader twoLawVocab := ⟨⟨101⟩, [.nat, tlBytes, tlBytes], [.nat], false, none, Summary.empty⟩
private abbrev tlWHdrEncode : FnHeader twoLawVocab := ⟨⟨102⟩, [tlElem], [tlBytes], false, none, Summary.empty⟩
private abbrev tlWHdrDerUnif : FnHeader twoLawVocab := ⟨⟨104⟩, [.nat, tlBytes], [tlElem, .nat], false, none, Summary.empty⟩
private abbrev tlWHdrDerNonZ : FnHeader twoLawVocab := ⟨⟨105⟩, [.nat, tlBytes], [tlElem, .nat], false, none, Summary.empty⟩
private abbrev tlWHdrRead : FnHeader twoLawVocab := ⟨⟨106⟩, [tlBytes, .nat], [tlElem, .nat], true, none, Summary.empty⟩
private abbrev tlWHdrSampSite : FnHeader twoLawVocab :=
  ⟨⟨109⟩, [tlElem, tlElem, tlBytes, tlBytes, .nat, .nat], [tlElem], false, none, Summary.empty⟩

private abbrev tlWFnHeaders : List (FnHeader twoLawVocab) :=
  [tlWHdrSampSite, tlWHdrRead, tlWHdrDerNonZ, tlWHdrDerUnif, tlWHdrEncode, tlWHdrAbsorb, tlWHdrStart]

private def tlWFnDefs : Defs twoLawVocab ⟨tlWFnHeaders, []⟩ :=
  .fn tlWHdrSampSite (Names.counting 0 _) tlWTSampleSite
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel), rfl⟩ <|
  .fn tlWHdrRead (Names.counting 0 _) tlWTRead
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel), rfl⟩ <|
  .fn tlWHdrDerNonZ (Names.counting 0 _) tlWTDeriveNonZero
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel), rfl⟩ <|
  .fn tlWHdrDerUnif (Names.counting 0 _) tlWTDeriveUniform
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel), rfl⟩ <|
  .fn tlWHdrEncode (Names.counting 0 _) tlWTEncode
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel), rfl⟩ <|
  .fn tlWHdrAbsorb (Names.counting 0 _) tlWTAbsorb
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel), rfl⟩ <|
  .fn tlWHdrStart (Names.counting 0 _) tlWTStart
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel), rfl⟩ <|
  .nil

private theorem tlW_seqAt_some {V : Vocabulary} (M : Model V) (item : V.Ty)
    (free : Ty.isLinear V item = false) (buf : List (M.Val item)) (off : Nat)
    (hlt : off < buf.length) :
    ownedOp M (.seqAt item none free) (.cons buf (.cons off .nil)) =
      Process.done (.cons (buf[off]'hlt) .nil) := by
  simp only [ownedOp, List.getElem?_eq_getElem hlt]

private theorem tlW_list_split {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs = xs.take i ++ [xs[i]'h] ++ xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => cases h
  | cons a rest ih =>
      cases i with
      | zero => rfl
      | succ k =>
          simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, List.cons_append]
          exact congrArg (a :: ·) (ih k (Nat.lt_of_succ_lt_succ h))

private theorem tlWRead_eval {fns : List (FnHeader twoLawVocab)}
    (fnTable : FnTable twoLawModel fns) (buf : List Nat) (off : Nat) :
    tlWTRead.denote (localSem twoLawModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [tlBytes, .nat]) (.cons buf (.cons off .nil))) =
      if hlt : off < buf.length then
        let b := buf[off]'hlt
        if b < 11 then
          .done (.cons (b % 11) (.cons (off + 1) .nil))
        else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  dsimp only [tlWTRead]
  erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .nat) buf.length .nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .bool) (Nat.blt off buf.length) .nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_guard]
  by_cases hlt : off < buf.length
  · rw [dite_eq_left hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = true := Nat.blt_eq.mpr hlt
    rw [hltB]; dsimp only [cond]
    erw [Term.denote_op]
    change (ownedOp twoLawModel (.seqAt tlByte none rfl) (.cons buf (.cons off .nil))).bind _ = _
    rw [tlW_seqAt_some twoLawModel tlByte rfl buf off hlt]; dsimp only [Process.bind]
    erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .nat) (buf[off]'hlt) .nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .nat) 11 .nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .bool) (Nat.blt (buf[off]'hlt) 11) .nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_guard]
    by_cases hb : buf[off]'hlt < 11
    · rw [ite_eq_left hb]
      change (bif Nat.blt (buf[off]'hlt) 11 then _ else _) = _
      have hbB : Nat.blt (buf[off]'hlt) 11 = true := Nat.blt_eq.mpr hb
      rw [hbB]; rfl
    · rw [ite_eq_right hb]
      change (bif Nat.blt (buf[off]'hlt) 11 then _ else _) = _
      have hbB : Nat.blt (buf[off]'hlt) 11 = false := Bool.eq_false_iff.mpr (fun h => hb (Nat.blt_eq.mp h))
      rw [hbB]; rfl
  · rw [dite_eq_right hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = false := Bool.eq_false_iff.mpr (fun h => hlt (Nat.blt_eq.mp h))
    rw [hltB]; rfl

private theorem tlWFnDefs_read_eval (buf : List Nat) (off : Nat) :
    Defs.fnTable twoLawModel tlWFnDefs tlWHdrRead (Member.tail Member.head)
      (.cons buf (.cons off .nil)) =
      if hlt : off < buf.length then
        let b := buf[off]'hlt
        if b < 11 then
          .done (.cons (b % 11) (.cons (off + 1) .nil))
        else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨3⟩⟩) :=
  tlWRead_eval _ buf off

private theorem tlWSampSite_eval {fns : List (FnHeader twoLawVocab)}
    (fnTable : FnTable twoLawModel fns)
    (w y : Nat) (sess site : List Nat) (att seq : Nat) :
    tlWTSampleSite.denote (localSem twoLawModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [tlElem, tlElem, tlBytes, tlBytes, .nat, .nat])
        (.cons w (.cons y (.cons sess (.cons site (.cons att (.cons seq .nil))))))) =
      .done (.cons (if site.length == (encodeSite ⟨[], ⟨10⟩⟩).length then (1 : Nat) else 0) .nil) := by
  dsimp only [tlWTSampleSite]
  erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .nat) site.length .nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .nat) (encodeSite ⟨[], ⟨10⟩⟩).length .nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_op]; change (Process.done (HList.cons (V := twoLawModel.Val) (a := .bool) (site.length == (encodeSite ⟨[], ⟨10⟩⟩).length) .nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_choose]
  cases h : (site.length == (encodeSite ⟨[], ⟨10⟩⟩).length) <;> rfl

private def tlWMixedProtoTerm {hs : Headers twoLawVocab} :
    Term (protocolDialect twoLawVocab hs) (Ctx.positional [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩]) [] :=
  .op ⟨10⟩ (.flow (τ := tlElem) (H := [0, 1]) .message 0 [1] (by decide) (by decide)) (.cons (tlVar 1) .nil) (.cons 2 .nil) <|
  .op ⟨11⟩ (.given (.coin TwoLaw.uniform) 1 [0] [] tlElem ⟨⟨[], tlElem⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 3 .nil) <|
  .op ⟨12⟩ (.given (.coin TwoLaw.nonzero) 1 [0] [] tlElem ⟨⟨[], tlElem⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 4 .nil) <|
  .op ⟨13⟩ (.compute [0, 1] (.row TwoLawRow.fin11Add _ rfl) [⟨tlElem, [0, 1]⟩, ⟨tlElem, [0, 1]⟩]
      rfl (by decide)) (.cons (tlVar 3) (.cons (tlVar 4) .nil)) (.cons 5 .nil) <|
  .op ⟨14⟩ (.compute [0] (.row TwoLawRow.fin11Add _ rfl) [⟨tlElem, [0, 1]⟩, ⟨tlElem, [0]⟩]
      rfl (by decide)) (.cons (tlVar 5) (.cons (tlVar 0) .nil)) (.cons 6 .nil) <|
  .op ⟨15⟩ (.flow (τ := tlElem) (H := [0]) .message 0 [1] (by decide) (by decide)) (.cons (tlVar 6) .nil) (.cons 7 .nil) <|
  .op ⟨16⟩ (.compute [1] (.owned (.finToNat 11)) [⟨tlElem, [0, 1]⟩] rfl (by decide))
      (.cons (tlVar 4) .nil) (.cons 8 .nil) <|
  .op ⟨17⟩ (.compute [1] (.literal (V := twoLawVocab) .nat [0] rfl) [] rfl (by decide))
      .nil (.cons 9 .nil) <|
  .op ⟨18⟩ (.compute [1] (.owned .natLess) [⟨.nat, [1]⟩, ⟨.nat, [1]⟩] rfl (by decide))
      (.cons (tlVar 9) (.cons (tlVar 8) .nil)) (.cons 10 .nil) <|
  .guard ⟨19⟩ [1] (tlVar 10) ⟨rfl, by decide, by decide⟩ .reject <|
  .op ⟨20⟩ (.compute [1] (.row TwoLawRow.fin11Add _ rfl) [⟨tlElem, [0, 1]⟩, ⟨tlElem, [0, 1]⟩]
      rfl (by decide)) (.cons (tlVar 5) (.cons (tlVar 2) .nil)) (.cons 11 .nil) <|
  .op ⟨21⟩ (.compute [1] (.owned (.finToNat 11)) [⟨tlElem, [0, 1]⟩] rfl (by decide))
      (.cons (tlVar 7) .nil) (.cons 12 .nil) <|
  .op ⟨22⟩ (.compute [1] (.owned (.finToNat 11)) [⟨tlElem, [1]⟩] rfl (by decide))
      (.cons (tlVar 11) .nil) (.cons 13 .nil) <|
  .op ⟨23⟩ (.compute [1] (.owned .natEqual) [⟨.nat, [1]⟩, ⟨.nat, [1]⟩] rfl (by decide))
      (.cons (tlVar 12) (.cons (tlVar 13) .nil)) (.cons 14 .nil) <|
  .guard ⟨24⟩ [1] (tlVar 14) ⟨rfl, by decide, by decide⟩ .reject <|
  .ret .nil

private abbrev tlWMixedHdr : ProtocolHeader twoLawVocab :=
  ⟨⟨200⟩, 2, [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩], [], shapeOf (tlWMixedProtoTerm (hs := ⟨tlWFnHeaders, []⟩))⟩

private def tlWMixedTyped : Typed twoLawVocab :=
  ⟨⟨tlWFnHeaders, [tlWMixedHdr]⟩,
   .protocol tlWMixedHdr (Names.counting 0 _) tlWMixedProtoTerm
     ⟨by simp [Within, ProtocolOp.Within, tlWMixedProtoTerm, tlWMixedHdr],
      by decide,
      by simp [Enclosed, tlWMixedProtoTerm],
      (Term.repeatedAddress_eq_none _).mp (by decide +kernel),
      rfl,
      by unfold Term.UsedOnce; decide +kernel,
      by decide +kernel,
      (Term.rebound_eq_none _ _).mp (by decide +kernel)⟩ tlWFnDefs,
   by decide⟩

/-- Suite using generic default `⟨104⟩` (`squeezeUniform`) in `members` and an explicit override
`⟨105⟩` (`squeezeNonZero`) for `.nonzero` in `lawMembers`. -/
def twoLawMixedSuite : ModuleRef where
  members := [
    (SuiteSlot.start, ⟨100⟩),
    (SuiteSlot.absorb, ⟨101⟩),
    (SuiteSlot.encode, ⟨102⟩),
    (SuiteSlot.derive, ⟨104⟩)
  ]
  lawMembers := [
    (SuiteSlot.derive, twoLawEncoder.lawKey .nonzero, ⟨105⟩)
  ]

def twoLawMixedDecl : Declaration :=
  { twoLawDecl with key := ⟨2⟩, construction := .derived twoLawMixedSuite none }

private theorem tlWMixed_admit_isOk :
    (admit (erase tlWMixedTyped) noAssociation).isOk = true := by decide +kernel

private theorem tlWMixed_deploy_isOk :
    (match admit (erase tlWMixedTyped) noAssociation with
     | .ok a => (deploy twoLawEncoder a twoLawMixedDecl).isOk
     | .error _ => false) = true := by decide +kernel

private theorem tl_member_unique {V : Vocabulary} {p : Typed V} {k : Key}
    {h₁ h₂ : FnHeader V} {f₁ : Member p.headers.fns h₁} {f₂ : Member p.headers.fns h₂}
    (hf₁ : p.find k = some (.fn f₁)) (hf₂ : p.find k = some (.fn f₂)) :
    ∃ e : h₁ = h₂, e ▸ f₁ = f₂ := by
  have hEq : (⟨h₁, f₁⟩ : (h : FnHeader V) × Member p.headers.fns h) = ⟨h₂, f₂⟩ := by
    have h := Option.some.inj (hf₁.symm.trans hf₂)
    cases h; rfl
  cases hEq; exact ⟨rfl, rfl⟩

private theorem tlWMixed_protocol_unfold :
    protocolMeaning twoLawModel tlWMixedTyped Member.head []
      (.cons (4 : Nat) (.cons (4 : Nat) .nil)) =
      (Process.call (GOp.flow .message 0 [1] ⟨[], ⟨10⟩⟩ tlElem (4 : Nat)) fun _ =>
        Process.call (GOp.given (.coin TwoLaw.uniform) 1 [0] ⟨[], ⟨11⟩⟩ [] .nil tlElem) fun (c1 : Nat) =>
          Process.call (GOp.given (.coin TwoLaw.nonzero) 1 [0] ⟨[], ⟨12⟩⟩ [] .nil tlElem) fun (c2 : Nat) =>
            Process.call (GOp.flow .message 0 [1] ⟨[], ⟨15⟩⟩ tlElem (((c1 + c2) % 11 + 4) % 11)) fun _ =>
              ((((bif decide (0 < c2) then
                  bif decide ((((c1 + c2) % 11 + 4) % 11) = (((c1 + c2) % 11 + 4) % 11)) then
                    (Process.done (HList.nil, ()) :
                      Protocol twoLawModel (HList (LVal twoLawModel) [] × Unit))
                  else Process.halt ([1], Stop.declared .reject ⟨[], ⟨24⟩⟩)
                else Process.halt ([1], Stop.declared .reject ⟨[], ⟨19⟩⟩)).map
                fun out => (out.1, ((((c1 + c2) % 11 + 4) % 11), out.2))).map
                fun out => (out.1, (c2, out.2))).map
                fun out => (out.1, (c1, out.2))).map
                fun out => (out.1, ((4 : Nat), out.2))).map
        fun out => (out.1, out.2) := rfl

private theorem tlWMixed_noHalt :
    ∀ source, Lawful twoLawModel source
      (protocolMeaning twoLawModel tlWMixedTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) →
      ∀ e, GExec twoLawModel source
        (protocolMeaning twoLawModel tlWMixedTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) e →
        ∃ out, e = .returned out := by
  intro source hLaw e ⟨_, hRun⟩
  rw [tlWMixed_protocol_unfold] at hLaw hRun
  cases hRun with
  | flow hR1 =>
      cases hR1 with
      | @given _ _ _ _ _ _ _ c1 _ _ _ hS1 hR2 =>
          have hLaw2 := (hLaw c1 hS1).2
          cases hR2 with
          | @given _ _ _ _ _ _ _ c2 _ _ _ hS2 hR3 =>
              obtain ⟨_, sig, hSig, _, _, hSupp⟩ := (hLaw2 c2 hS2).1
              cases Option.some.inj hSig
              have hC2Pos : 0 < c2 := hSupp.1
              cases hR3 with
              | flow hR4 =>
                  have hD1 : decide (0 < c2) = true := decide_eq_true hC2Pos
                  dsimp only [Process.map] at hR4
                  erw [hD1] at hR4
                  simp only [Bool.cond_true, decide_true] at hR4
                  cases hR4
                  exact ⟨_, rfl⟩

private theorem tlWMixed_lp :
    LawfulPrivate twoLawModel (fun _ _ => none)
      (protocolMeaning twoLawModel tlWMixedTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) := by
  rw [tlWMixed_protocol_unfold]
  dsimp only [Process.map, Process.bind, LawfulPrivate, LawfulFor]
  intro (c1 : Nat) _ (c2 : Nat) _
  cases decide (0 < c2) <;> simp [Process.map, LawfulPrivate]

private theorem tlWMixed_fed :
    Fed twoLawModel (fun _ _ => none)
      (protocolMeaning twoLawModel tlWMixedTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) := by
  rw [tlWMixed_protocol_unfold]
  dsimp only [Process.map, Process.bind, Fed, FedFor]
  intro (c1 : Nat) _ (c2 : Nat) _
  cases decide (0 < c2) <;> simp [Process.map, Fed]

seal Zkc.Core.protocolMeaning in
/-- Concrete kernel-checked witness that:
1. Universal `Deployed.SuiteLawful twoLawModel d` is FALSE on `twoLawMixedSuite` (the shadowed
   default `⟨104⟩` returns `0 ∉ support .nonzero` on `(st = 10, lbl = [])`).
2. Selected-function `Deployed.SuiteLawfulFor twoLawEncoder twoLawModel d` is TRUE (never charges
   shadowed default `⟨104⟩` for `.nonzero`), and discharges `deploy_complete` end-to-end! -/
theorem witness_selected_function_suiteLawfulFor :
    ∃ (a : Admitted twoLawVocab) (d : Deployed twoLawVocab)
      (hIns : d.entry.ins = [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      admit (erase tlWMixedTyped) noAssociation = .ok a ∧
      deploy twoLawEncoder a twoLawMixedDecl = .ok d ∧
      ¬ d.SuiteLawful twoLawModel ∧
      d.SuiteLawfulFor twoLawEncoder twoLawModel ∧
      let ins := cast (congrArg (HList (LVal twoLawModel)) hIns.symm)
        (.cons (4 : Nat) (.cons (4 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone twoLawModel (fun _ _ => none) 0
          (d.run twoLawModel 0 (hideAll twoLawModel 0 ins)
            (cast (congrArg (HList twoLawModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone twoLawModel (fun _ _ => none) 1
          (d.run twoLawModel 1 (hideAll twoLawModel 1 ins)
            (cast (congrArg (HList twoLawModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful twoLawModel source'
            (protocolMeaning twoLawModel d.admitted.program d.callee [] ins) ∧
          (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = none) ∧
          GExec twoLawModel source'
            (protocolMeaning twoLawModel d.admitted.program d.callee [] ins) (.returned out) ∧
          outP = hideAll twoLawModel 0 out.1 ∧ outV = hideAll twoLawModel 1 out.1 := by
  have hAdmEx : ∃ a : Admitted twoLawVocab,
      admit (erase tlWMixedTyped) noAssociation = .ok a ∧ a.program = tlWMixedTyped := by
    cases h : admit (erase tlWMixedTyped) noAssociation with
    | error _ => have hOk := tlWMixed_admit_isOk; rw [h] at hOk; cases hOk
    | ok a => exact ⟨a, rfl, admitted_eq_of_readback h rfl⟩
  obtain ⟨a, hAdm, hProg⟩ := hAdmEx
  have hDepEx : ∃ d, deploy twoLawEncoder a twoLawMixedDecl = .ok d := by
    cases h : deploy twoLawEncoder a twoLawMixedDecl with
    | error _ =>
        have hOk := tlWMixed_deploy_isOk
        rw [hAdm] at hOk; dsimp only at hOk; rw [h] at hOk; cases hOk
    | ok d => exact ⟨d, rfl⟩
  obtain ⟨d, hDep⟩ := hDepEx
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps twoLawEncoder a twoLawMixedDecl d hDep
  have hDProg : d.admitted.program = tlWMixedTyped := by rw [hAdmEq, hProg]
  cases d with
  | mk adm decl found stack ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier tlWMixedHdr twoLawMixedDecl = some (0, 1) := by decide +kernel
          obtain ⟨hFirst, hMatched⟩ :=
            deploy_matches twoLawEncoder a twoLawMixedDecl _ hDep 0 1 hRoles
          -- 1. Universal `SuiteLawful` is FALSE: default `⟨104⟩` returns `0` on `(st = 10, lbl = [])`
          --    (`mixBytes 10 [0xFE] = 1595 = 11 * 145`, `1595 % 11 = 0 ∉ support .nonzero`).
          have hNotUniv : ¬ Deployed.SuiteLawful twoLawModel
              ⟨⟨tlWMixedTyped, ann, assoc, assu⟩, twoLawMixedDecl, found, stack, ident⟩ := by
            intro hUniv
            have hDer := (hUniv twoLawMixedSuite none rfl).1
            have hMem104 : (SuiteSlot.derive, (⟨104⟩ : Key)) ∈ twoLawMixedSuite.members := by decide
            let f104 : Member tlWMixedTyped.headers.fns tlWHdrDerUnif :=
              Member.tail (Member.tail (Member.tail Member.head))
            have hFind104 : tlWMixedTyped.find ⟨104⟩ = some (.fn f104) := rfl
            let eNZ : ShapeEvent twoLawVocab :=
              ⟨⟨[], ⟨12⟩⟩, .given (.coin TwoLaw.nonzero) 1 [0], tlElem⟩
            have hENZ : eNZ ∈ tlWMixedHdr.shape.events [] id := by
              simp only [tlWMixedProtoTerm, shapeOf, ProtocolOp.shape, Shape.events, EventClass.rename,
                List.mem_cons, List.not_mem_nil, or_false]
              exact .inr (.inr (.inl rfl))
            have hEval0 : Defs.fnTable twoLawModel tlWMixedTyped.defs tlWHdrDerUnif f104
                (.cons (10 : Nat) (.cons ([] : List Nat) .nil)) =
                .done (.cons (0 : Nat) (.cons (1595 : Nat) .nil)) := rfl
            have hAllow := hDer ⟨104⟩ (.inl hMem104) tlWHdrDerUnif f104 hFind104 .nat []
              eNZ TwoLaw.nonzero 1 0 [] hENZ rfl rfl rfl rfl (10 : Nat) ([] : List Nat) .nil
              (0 : Nat) (1595 : Nat) trivial (fun _ h => nomatch h) trivial hEval0
            obtain ⟨_, sig, hSig, _, _, hSupp⟩ := hAllow
            cases Option.some.inj hSig
            exact Nat.lt_irrefl 0 hSupp.1
          -- 2. Selected-function `SuiteLawfulFor` is TRUE!
          have hSLFor : Deployed.SuiteLawfulFor twoLawEncoder twoLawModel
              ⟨⟨tlWMixedTyped, ann, assoc, assu⟩, twoLawMixedDecl, found, stack, ident⟩ := by
            intro suite sessionTag hCon
            have hSEq : suite = twoLawMixedSuite := (Construction.derived.inj hCon).1.symm
            subst hSEq
            constructor
            · intro e law owner h0 hs drawIns stateTy _ derRef hStart _ _ hLaw hDerFind
                st label payload coin st' _ _ _ hEval
              have hST : stateTy = .nat := by
                have hS0 : findSuiteStart ⟨tlWMixedTyped, ann, assoc, assu⟩ twoLawMixedSuite =
                    some ⟨.nat, ⟨tlWHdrStart, Member.tail (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))),
                      rfl, rfl, rfl, rfl⟩⟩ := rfl
                exact congrArg Sigma.fst (Option.some.inj (hStart.symm.trans hS0))
              subst hST
              cases e with
              | mk eSite eCls eTau =>
                  dsimp only at hLaw hDerFind hEval ⊢
                  cases Option.some.inj hLaw
                  cases payload
                  cases law with
                  | uniform =>
                      have hExp : findSuiteDerive twoLawEncoder ⟨tlWMixedTyped, ann, assoc, assu⟩
                          twoLawMixedSuite .nat TwoLaw.uniform [] tlElem =
                          some ⟨tlWHdrDerUnif, Member.tail (Member.tail (Member.tail Member.head)),
                            rfl, rfl, rfl, rfl⟩ := rfl
                      have hRefEq := Option.some.inj (hDerFind.symm.trans hExp)
                      subst hRefEq
                      have hRun : Defs.fnTable twoLawModel tlWMixedTyped.defs tlWHdrDerUnif
                          (Member.tail (Member.tail (Member.tail Member.head)))
                          (.cons st (.cons label .nil)) =
                          .done (.cons (mixBytes st (0xFE :: label) % 11)
                            (.cons (mixBytes st (0xFE :: label)) .nil)) := rfl
                      change Nat at st coin st'; change List Nat at label
                      erw [hRun] at hEval
                      cases Process.done.inj hEval
                      exact ⟨Nat.mod_lt _ (by decide), ⟨[], tlElem⟩, rfl, rfl, rfl,
                        Nat.mod_lt _ (by decide)⟩
                  | nonzero =>
                      have hExp : findSuiteDerive twoLawEncoder ⟨tlWMixedTyped, ann, assoc, assu⟩
                          twoLawMixedSuite .nat TwoLaw.nonzero [] tlElem =
                          some ⟨tlWHdrDerNonZ, Member.tail (Member.tail Member.head),
                            rfl, rfl, rfl, rfl⟩ := rfl
                      have hRefEq := Option.some.inj (hDerFind.symm.trans hExp)
                      subst hRefEq
                      have hRun : Defs.fnTable twoLawModel tlWMixedTyped.defs tlWHdrDerNonZ
                          (Member.tail (Member.tail Member.head))
                          (.cons st (.cons label .nil)) =
                          .done (.cons (1 + mixBytes st (0xFD :: label) % 10)
                            (.cons (mixBytes st (0xFD :: label)) .nil)) := rfl
                      change Nat at st coin st'; change List Nat at label
                      erw [hRun] at hEval
                      cases Process.done.inj hEval
                      have hMod := Nat.mod_lt (mixBytes st (0xFD :: label)) (show 0 < 10 by decide)
                      refine ⟨?_, ⟨[], tlElem⟩, rfl, rfl, rfl, ?_⟩
                      · show 1 + mixBytes st (0xFD :: label) % 10 < 11; omega
                      · exact ⟨show 0 < 1 + mixBytes st (0xFD :: label) % 10 by omega,
                          show 1 + mixBytes st (0xFD :: label) % 10 < 11 by omega⟩
            · intro eKey hMem hdr f hFind unitTy τ hIn hOut v₁ v₂ u hv₁ hv₂ hEv₁ hEv₂
              have hK : eKey = ⟨102⟩ := by
                simp only [twoLawMixedSuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
                rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | cases h
              subst hK
              have hF102 : tlWMixedTyped.find ⟨102⟩ =
                  some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
              obtain ⟨rfl, rfl⟩ := tl_member_unique hFind hF102
              have hTau : τ = tlElem := (List.cons.inj hIn).1.symm
              have hU : unitTy = tlByte := by
                have hc := (List.cons.inj hOut).1.symm; cases hc; rfl
              subst hTau; subst hU
              cases hIn; cases hOut
              change Nat at v₁ v₂; change List Nat at u
              have hRun : ∀ x : Nat, Defs.fnTable twoLawModel tlWMixedTyped.defs tlWHdrEncode
                  (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))
                  (.cons x .nil) = .done (.cons [x % 256] .nil) := fun _ => rfl
              erw [hRun v₁] at hEv₁; erw [hRun v₂] at hEv₂
              have h1 : [v₁ % 256] = u := congrArg HList.single (Process.done.inj hEv₁)
              have h2 : [v₂ % 256] = u := congrArg HList.single (Process.done.inj hEv₂)
              have hm : v₁ % 256 = v₂ % 256 := (List.cons.inj (h1.trans h2.symm)).1
              change v₁ < 11 at hv₁; change v₂ < 11 at hv₂
              rw [Nat.mod_eq_of_lt (by omega : v₁ < 256), Nat.mod_eq_of_lt (by omega : v₂ < 256)] at hm
              exact hm
          -- 3. `LayoutLawful` on `twoLawLayout`
          have hLL : Deployed.LayoutLawful twoLawModel
              ⟨⟨tlWMixedTyped, ann, assoc, assu⟩, twoLawMixedDecl, found, stack, ident⟩ := by
            intro layout hLay
            have hLEq : layout = ⟨twoLawLayout, [], []⟩ := (Option.some.inj hLay).symm
            subst hLEq
            refine ⟨?_, ?_, ?_⟩
            · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
                v chunk pre post hv _ _ hW
              have hWK : wKey = ⟨102⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
                rcases hwMem with ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | cases h
              have hRK : rKey = ⟨106⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
                rcases hrMem with ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
              subst hWK; subst hRK
              have hF102 : tlWMixedTyped.find ⟨102⟩ =
                  some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
              have hF106 : tlWMixedTyped.find ⟨106⟩ = some (.fn (Member.tail Member.head)) := rfl
              obtain ⟨rfl, rfl⟩ := tl_member_unique hwFind hF102
              obtain ⟨rfl, rfl⟩ := tl_member_unique hrFind hF106
              have hTau : τ = tlElem := (List.cons.inj hwIn).1.symm
              have hU : unitTy = tlByte := by
                have hc := (List.cons.inj hwOut).1.symm; cases hc; rfl
              subst hTau; subst hU
              cases hwIn; cases hwOut; cases hrIn; cases hrOut
              change Nat at v; change v < 11 at hv
              change List Nat at chunk pre post
              have hWRun : Defs.fnTable twoLawModel tlWMixedTyped.defs tlWHdrEncode
                  (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))
                  (.cons v .nil) = .done (.cons [v % 256] .nil) := rfl
              erw [hWRun] at hW
              have hCh : [v % 256] = chunk := congrArg HList.single (Process.done.inj hW)
              subst hCh
              have hV256 : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hV11 : v % 11 = v := Nat.mod_eq_of_lt hv
              have hLt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hAt : (pre ++ [v % 256] ++ post)[pre.length]'hLt = v := by
                have h1 : (pre ++ [v % 256] ++ post)[pre.length]? = some v := by
                  rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
                  simp [hV256]
                rw [List.getElem?_eq_getElem hLt] at h1
                exact Option.some.inj h1
              change Defs.fnTable twoLawModel tlWFnDefs tlWHdrRead (Member.tail Member.head)
                  (.cons (pre ++ [v % 256] ++ post) (.cons pre.length .nil)) = _
              rw [tlWFnDefs_read_eval]
              simp only [hLt, ↓reduceDIte, hAt, hv, ↓reduceIte, hV11]; rfl
            · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
                buf off v nextOff _ _ hR
              have hWK : wKey = ⟨102⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
                rcases hwMem with ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | cases h
              have hRK : rKey = ⟨106⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
                rcases hrMem with ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
              subst hWK; subst hRK
              have hF102 : tlWMixedTyped.find ⟨102⟩ =
                  some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
              have hF106 : tlWMixedTyped.find ⟨106⟩ = some (.fn (Member.tail Member.head)) := rfl
              obtain ⟨rfl, rfl⟩ := tl_member_unique hwFind hF102
              obtain ⟨rfl, rfl⟩ := tl_member_unique hrFind hF106
              have hTau : τ = tlElem := (List.cons.inj hwIn).1.symm
              have hU : unitTy = tlByte := by
                have hc := (List.cons.inj hwOut).1.symm; cases hc; rfl
              subst hTau; subst hU
              cases hwIn; cases hwOut; cases hrIn; cases hrOut
              change List Nat at buf; change Nat at off v nextOff
              erw [tlWFnDefs_read_eval] at hR
              by_cases hlt : off < buf.length
              · simp only [hlt, ↓reduceDIte] at hR
                by_cases hb : buf[off]'hlt < 11
                · simp only [hb, ↓reduceIte] at hR
                  have hPair : (HList.cons (buf[off]'hlt % 11) (.cons (off + 1) .nil) :
                      HList twoLawModel.Val [tlElem, .nat]) = .cons v (.cons nextOff .nil) :=
                    Process.done.inj hR
                  have hvEq : buf[off]'hlt % 11 = v := by cases hPair; rfl
                  have hNextEq : off + 1 = nextOff := by cases hPair; rfl
                  subst hvEq; subst hNextEq
                  have hbMod : buf[off]'hlt % 11 = buf[off]'hlt := Nat.mod_eq_of_lt hb
                  refine ⟨by rw [hbMod]; exact hb, Nat.le_succ off, hlt, [buf[off]'hlt], ?_,
                    tlW_list_split buf off hlt⟩
                  have hMod256 : (buf[off]'hlt % 11) % 256 = buf[off]'hlt := by omega
                  show Defs.fnTable twoLawModel tlWMixedTyped.defs tlWHdrEncode
                    (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))
                    (.cons (buf[off]'hlt % 11) .nil) = .done (.cons [buf[off]'hlt] .nil)
                  change Process.done (HList.cons (V := twoLawModel.Val) (a := tlBytes)
                      [(buf[off]'hlt % 11) % 256] .nil) = _
                  rw [hMod256]
                · simp only [hb, ↓reduceIte] at hR; cases hR
              · simp only [hlt, ↓reduceDIte] at hR; cases hR
            · intro eqKey hMem
              rcases (by simpa [twoLawLayout] using hMem) with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
          have hInsV : (HList.cons (4 : Nat) (.cons (4 : Nat) .nil) :
              HList (LVal twoLawModel) tlWMixedHdr.ins).All (fun a v => twoLawModel.Valid a.ty v) :=
            ⟨show (4 : Nat) < 11 by decide, show (4 : Nat) < 11 by decide, trivial⟩
          have hNoRec : ∀ l, twoLawMixedDecl.layout = some l → l.recover = [] := fun _ h => by
            cases Option.some.inj h; rfl
          exact ⟨a, _, rfl, hFirst, hMatched, hAdm, hDep, hNotUniv, hSLFor,
            deploy_complete twoLawModel twoLawEncoder hAdm hDep rfl rfl rfl hNoRec
              0 1 hRoles hFirst hMatched (.cons (4 : Nat) (.cons (4 : Nat) .nil)) hInsV
              hSLFor hLL tlWMixed_noHalt (fun _ _ => none) tlWMixed_lp tlWMixed_fed⟩

/-! ## 8. Site-sensitive `Deployed.SamplesLawfulFor` witness (`¬ SamplesLawful`, yet `deploy_complete_samples`) -/

private def tlWSiteSampTerm {hs : Headers twoLawVocab} :
    Term (protocolDialect twoLawVocab hs) (Ctx.positional [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩]) [] :=
  .op ⟨10⟩ (.given (.coin TwoLaw.nonzero) 0 [] [] tlElem ⟨⟨[], tlElem⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 2 .nil) <|
  .op ⟨11⟩ (.flow (τ := tlElem) (H := [0]) .message 0 [1] (by decide) (by decide)) (.cons (tlVar 2) .nil) (.cons 3 .nil) <|
  .op ⟨12⟩ (.given (.coin TwoLaw.uniform) 1 [0] [] tlElem ⟨⟨[], tlElem⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 4 .nil) <|
  .op ⟨13⟩ (.compute [0] (.row TwoLawRow.fin11Add _ rfl) [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩]
      rfl (by decide)) (.cons (tlVar 2) (.cons (tlVar 4) .nil)) (.cons 5 .nil) <|
  .op ⟨14⟩ (.flow (τ := tlElem) (H := [0]) .message 0 [1] (by decide) (by decide)) (.cons (tlVar 5) .nil) (.cons 6 .nil) <|
  .op ⟨15⟩ (.compute [1] (.owned (.finToNat 11)) [⟨tlElem, [0, 1]⟩] rfl (by decide))
      (.cons (tlVar 3) .nil) (.cons 7 .nil) <|
  .op ⟨16⟩ (.compute [1] (.literal (V := twoLawVocab) .nat [0] rfl) [] rfl (by decide))
      .nil (.cons 8 .nil) <|
  .op ⟨17⟩ (.compute [1] (.owned .natLess) [⟨.nat, [1]⟩, ⟨.nat, [1]⟩] rfl (by decide))
      (.cons (tlVar 8) (.cons (tlVar 7) .nil)) (.cons 9 .nil) <|
  .guard ⟨18⟩ [1] (tlVar 9) ⟨rfl, by decide, by decide⟩ .reject <|
  .op ⟨19⟩ (.compute [1] (.row TwoLawRow.fin11Add _ rfl) [⟨tlElem, [0, 1]⟩, ⟨tlElem, [0, 1]⟩]
      rfl (by decide)) (.cons (tlVar 3) (.cons (tlVar 4) .nil)) (.cons 10 .nil) <|
  .op ⟨20⟩ (.compute [1] (.owned (.finToNat 11)) [⟨tlElem, [0, 1]⟩] rfl (by decide))
      (.cons (tlVar 6) .nil) (.cons 11 .nil) <|
  .op ⟨21⟩ (.compute [1] (.owned (.finToNat 11)) [⟨tlElem, [1]⟩] rfl (by decide))
      (.cons (tlVar 10) .nil) (.cons 12 .nil) <|
  .op ⟨22⟩ (.compute [1] (.owned .natEqual) [⟨.nat, [1]⟩, ⟨.nat, [1]⟩] rfl (by decide))
      (.cons (tlVar 11) (.cons (tlVar 12) .nil)) (.cons 13 .nil) <|
  .guard ⟨23⟩ [1] (tlVar 13) ⟨rfl, by decide, by decide⟩ .reject <|
  .ret .nil

private abbrev tlWSiteSampHdr : ProtocolHeader twoLawVocab :=
  ⟨⟨210⟩, 2, [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩], [], shapeOf (tlWSiteSampTerm (hs := ⟨tlWFnHeaders, []⟩))⟩

private def tlWSiteSampTyped : Typed twoLawVocab :=
  ⟨⟨tlWFnHeaders, [tlWSiteSampHdr]⟩,
   .protocol tlWSiteSampHdr (Names.counting 0 _) tlWSiteSampTerm
     ⟨by simp [Within, ProtocolOp.Within, tlWSiteSampTerm, tlWSiteSampHdr],
      by decide,
      by simp [Enclosed, tlWSiteSampTerm],
      (Term.repeatedAddress_eq_none _).mp (by decide +kernel),
      rfl,
      by unfold Term.UsedOnce; decide +kernel,
      by decide +kernel,
      (Term.rebound_eq_none _ _).mp (by decide +kernel)⟩ tlWFnDefs,
   by decide⟩

def tlSiteSampDecl : Declaration :=
  { twoLawDecl with key := ⟨3⟩, entry := ⟨210⟩, samples := some ⟨109⟩ }

private theorem tlWSiteSamp_admit_isOk :
    (admit (erase tlWSiteSampTyped) noAssociation).isOk = true := by decide +kernel

private theorem tlWSiteSamp_deploy_isOk :
    (match admit (erase tlWSiteSampTyped) noAssociation with
     | .ok a => (deploy twoLawEncoder a tlSiteSampDecl).isOk
     | .error _ => false) = true := by decide +kernel

private theorem tlWSiteSamp_protocol_unfold :
    protocolMeaning twoLawModel tlWSiteSampTyped Member.head []
      (.cons (4 : Nat) (.cons (4 : Nat) .nil)) =
      (Process.call (GOp.given (.coin TwoLaw.nonzero) 0 [] ⟨[], ⟨10⟩⟩ [] .nil tlElem) fun (r : Nat) =>
        Process.call (GOp.flow .message 0 [1] ⟨[], ⟨11⟩⟩ tlElem r) fun _ =>
          Process.call (GOp.given (.coin TwoLaw.uniform) 1 [0] ⟨[], ⟨12⟩⟩ [] .nil tlElem) fun (c : Nat) =>
            Process.call (GOp.flow .message 0 [1] ⟨[], ⟨14⟩⟩ tlElem ((r + c) % 11)) fun _ =>
              (((bif decide (0 < r) then
                  bif decide ((r + c) % 11 = (r + c) % 11) then
                    (Process.done (HList.nil, ()) :
                      Protocol twoLawModel (HList (LVal twoLawModel) [] × Unit))
                  else Process.halt ([1], Stop.declared .reject ⟨[], ⟨23⟩⟩)
                else Process.halt ([1], Stop.declared .reject ⟨[], ⟨18⟩⟩)).map
                fun out => (out.1, ((r + c) % 11, out.2))).map
                fun out => (out.1, (c, out.2))).map
                fun out => (out.1, (r, out.2))).map
        fun out => (out.1, out.2) := rfl

private theorem tlWSiteSamp_noHalt :
    ∀ source, Lawful twoLawModel source
      (protocolMeaning twoLawModel tlWSiteSampTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) →
      ∀ e, GExec twoLawModel source
        (protocolMeaning twoLawModel tlWSiteSampTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) e →
        ∃ out, e = .returned out := by
  intro source hLaw e ⟨_, hRun⟩
  rw [tlWSiteSamp_protocol_unfold] at hLaw hRun
  cases hRun with
  | @given _ _ _ _ _ _ _ r _ _ _ hSR hR1 =>
      obtain ⟨_, sig, hSig, _, _, hSupp⟩ := (hLaw r hSR).1
      cases Option.some.inj hSig
      have hRPos : 0 < r := hSupp.1
      cases hR1 with
      | flow hR2 =>
          cases hR2 with
          | @given _ _ _ _ _ _ _ c _ _ _ _ hR3 =>
              cases hR3 with
              | flow hR4 =>
                  have hD1 : decide (0 < r) = true := decide_eq_true hRPos
                  dsimp only [Process.map] at hR4
                  erw [hD1] at hR4
                  simp only [Bool.cond_true, decide_true] at hR4
                  cases hR4
                  exact ⟨_, rfl⟩

private theorem tlWSiteSamp_lp :
    LawfulSampled twoLawModel 0 (fun _ _ => none)
      (protocolMeaning twoLawModel tlWSiteSampTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) := by
  rw [tlWSiteSamp_protocol_unfold]
  dsimp only [Process.map, Process.bind, LawfulSampled, LawfulFor]
  rw [ite_eq_left ⟨rfl, rfl⟩]
  intro (r : Nat) _ (c : Nat) _
  cases decide (0 < r) <;> simp [Process.map, LawfulFor]

private theorem tlWSiteSamp_fed :
    FedSampled twoLawModel 0 (fun _ _ => none)
      (protocolMeaning twoLawModel tlWSiteSampTyped Member.head [] (.cons (4 : Nat) (.cons (4 : Nat) .nil))) := by
  rw [tlWSiteSamp_protocol_unfold]
  dsimp only [Process.map, Process.bind, FedSampled, FedFor]
  rw [ite_eq_left ⟨rfl, rfl⟩]
  intro (r : Nat) _ (c : Nat) _
  cases decide (0 < r) <;> simp [Process.map, FedFor]

seal Zkc.Core.protocolMeaning in
/-- Concrete kernel-checked witness that:
1. Site-agnostic `Deployed.SamplesLawful twoLawModel d` is FALSE on `tlWTSampleSite` (passing
   `siteBytes = []` returns `0 ∉ support .nonzero`).
2. Site-bound `Deployed.SamplesLawfulFor twoLawEncoder twoLawModel d` is TRUE (the actual private
   coin site `⟨[], ⟨10⟩⟩` has `encodeSite ⟨[], ⟨10⟩⟩` matching the expected length and returns `1`),
   discharging `deploy_complete_samples` on the completely empty world `fun _ _ => none`! -/
theorem witness_site_sensitive_samplesLawfulFor :
    ∃ (a : Admitted twoLawVocab) (d : Deployed twoLawVocab)
      (hIns : d.entry.ins = [⟨tlElem, [0]⟩, ⟨tlElem, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      admit (erase tlWSiteSampTyped) noAssociation = .ok a ∧
      deploy twoLawEncoder a tlSiteSampDecl = .ok d ∧
      ¬ d.SamplesLawful twoLawModel ∧
      d.SamplesLawfulFor twoLawEncoder twoLawModel ∧
      let ins := cast (congrArg (HList (LVal twoLawModel)) hIns.symm)
        (.cons (4 : Nat) (.cons (4 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone twoLawModel (fun _ _ => none) 0
          (d.run twoLawModel 0 (hideAll twoLawModel 0 ins)
            (cast (congrArg (HList twoLawModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone twoLawModel (fun _ _ => none) 1
          (d.run twoLawModel 1 (hideAll twoLawModel 1 ins)
            (cast (congrArg (HList twoLawModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful twoLawModel source'
            (protocolMeaning twoLawModel d.admitted.program d.callee [] ins) ∧
          (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins ++ d.entry.shape.proverPrivateCoins 0 →
            source' at_ τ = none) ∧
          GExec twoLawModel source'
            (protocolMeaning twoLawModel d.admitted.program d.callee [] ins) (.returned out) ∧
          outP = hideAll twoLawModel 0 out.1 ∧ outV = hideAll twoLawModel 1 out.1 := by
  have hAdmEx : ∃ a : Admitted twoLawVocab,
      admit (erase tlWSiteSampTyped) noAssociation = .ok a ∧ a.program = tlWSiteSampTyped := by
    cases h : admit (erase tlWSiteSampTyped) noAssociation with
    | error _ => have hOk := tlWSiteSamp_admit_isOk; rw [h] at hOk; cases hOk
    | ok a => exact ⟨a, rfl, admitted_eq_of_readback h rfl⟩
  obtain ⟨a, hAdm, hProg⟩ := hAdmEx
  have hDepEx : ∃ d, deploy twoLawEncoder a tlSiteSampDecl = .ok d := by
    cases h : deploy twoLawEncoder a tlSiteSampDecl with
    | error _ =>
        have hOk := tlWSiteSamp_deploy_isOk
        rw [hAdm] at hOk; dsimp only at hOk; rw [h] at hOk; cases hOk
    | ok d => exact ⟨d, rfl⟩
  obtain ⟨d, hDep⟩ := hDepEx
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps twoLawEncoder a tlSiteSampDecl d hDep
  have hDProg : d.admitted.program = tlWSiteSampTyped := by rw [hAdmEq, hProg]
  cases d with
  | mk adm decl found stack ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier tlWSiteSampHdr tlSiteSampDecl = some (0, 1) := by decide +kernel
          obtain ⟨hFirst, hMatched⟩ :=
            deploy_matches twoLawEncoder a tlSiteSampDecl _ hDep 0 1 hRoles
          -- 1. Site-agnostic `SamplesLawful` is FALSE (`siteBytes = []` yields `0 ∉ support .nonzero`)
          have hNotAgnostic : ¬ Deployed.SamplesLawful twoLawModel
              ⟨⟨tlWSiteSampTyped, ann, assoc, assu⟩, tlSiteSampDecl, found, stack, ident⟩ := by
            intro hAg
            let ePriv : ShapeEvent twoLawVocab :=
              ⟨⟨[], ⟨10⟩⟩, .given (.coin TwoLaw.nonzero) 0 [], tlElem⟩
            have hEPriv : ePriv ∈ tlWSiteSampHdr.shape.events [] id := by
              simp only [tlWSiteSampTerm, shapeOf, ProtocolOp.shape, Shape.events, EventClass.rename,
                List.mem_cons, List.not_mem_nil, or_false]
              exact .inl rfl
            have hEval0 : Defs.fnTable twoLawModel tlWSiteSampTyped.defs tlWHdrSampSite Member.head
                (.cons (4 : Nat) (.cons (4 : Nat) (.cons ([] : List Nat) (.cons ([] : List Nat)
                  (.cons (0 : Nat) (.cons (0 : Nat) .nil)))))) =
                .done (.cons (0 : Nat) .nil) := by
              change tlWTSampleSite.denote (localSem twoLawModel tlWSiteSampTyped.headers.fns
                  (Defs.fnTable twoLawModel tlWSiteSampTyped.defs)) []
                  (Env.empty.extend (Names.counting 0 [tlElem, tlElem, tlBytes, tlBytes, .nat, .nat]) _) = _
              erw [tlWSampSite_eval]
              have hNe : (([] : List Nat).length == (encodeSite ⟨[], ⟨10⟩⟩).length) = false := by decide +kernel
              rw [hNe]; rfl
            have hAllow := hAg ⟨109⟩ 0 1 rfl hRoles tlWHdrSampSite Member.head rfl
              ePriv TwoLaw.nonzero [] hEPriv rfl rfl rfl rfl
              (.cons (4 : Nat) (.cons (4 : Nat) .nil)) [] [] 0 0 .nil (0 : Nat)
              ⟨show (4 : Nat) < 11 by decide, show (4 : Nat) < 11 by decide, trivial⟩
              (fun _ h => nomatch h) (fun _ h => nomatch h) trivial hEval0
            obtain ⟨_, sig, hSig, _, _, hSupp⟩ := hAllow
            cases Option.some.inj hSig
            exact Nat.lt_irrefl 0 hSupp.1
          -- 2. Site-bound `SamplesLawfulFor` is TRUE!
          have hSampFor : Deployed.SamplesLawfulFor twoLawEncoder twoLawModel
              ⟨⟨tlWSiteSampTyped, ann, assoc, assu⟩, tlSiteSampDecl, found, stack, ident⟩ := by
            intro sKey prover verifier _ _ sessBytes _ hSamp _ hRoles' _ hdr f hFind e law
              hE hCls hLaw hins houts heldVals att seq coin _ hEval
            have hSK : sKey = ⟨109⟩ := (Option.some.inj hSamp).symm
            subst hSK
            have hPV := Prod.mk.inj (Option.some.inj (hRoles'.symm.trans hRoles))
            obtain ⟨rfl, rfl⟩ := hPV
            obtain ⟨rfl, rfl⟩ := tl_member_unique hFind (rfl : tlWSiteSampTyped.find ⟨109⟩ = some (.fn Member.head))
            have hE10 : e.site = ⟨[], ⟨10⟩⟩ ∧ law = (TwoLaw.nonzero : twoLawVocab.LawKey) ∧ e.τ = tlElem := by
              change e ∈ tlWSiteSampHdr.shape.events [] id at hE
              simp only [tlWSiteSampTerm, shapeOf, ProtocolOp.shape, Shape.events, EventClass.rename,
                List.mem_cons, List.not_mem_nil, or_false] at hE
              rcases hE with rfl | rfl | rfl | rfl <;> cases hCls <;> exact ⟨rfl, rfl, rfl⟩
            obtain ⟨hSiteEq, rfl, hTauEq⟩ := hE10
            cases e with
            | mk eSite eCls eTau =>
                dsimp only at hSiteEq hTauEq houts hEval ⊢
                subst hSiteEq; subst hTauEq
                cases hins; cases houts
                cases heldVals with
                | cons w rest1 =>
                    cases rest1 with
                    | cons y rest2 =>
                        cases rest2
                        change Nat at w y coin
                        have hRun : Defs.fnTable twoLawModel tlWSiteSampTyped.defs tlWHdrSampSite Member.head
                            (.cons w (.cons y (.cons sessBytes (.cons (encodeSite ⟨[], ⟨10⟩⟩)
                              (.cons att (.cons seq .nil)))))) =
                            .done (.cons (1 : Nat) .nil) := by
                          change tlWTSampleSite.denote (localSem twoLawModel tlWSiteSampTyped.headers.fns
                              (Defs.fnTable twoLawModel tlWSiteSampTyped.defs)) []
                              (Env.empty.extend (Names.counting 0 [tlElem, tlElem, tlBytes, tlBytes, .nat, .nat]) _) = _
                          erw [tlWSampSite_eval]
                          have hSelf : ((encodeSite ⟨[], ⟨10⟩⟩).length == (encodeSite ⟨[], ⟨10⟩⟩).length) = true := by
                            decide +kernel
                          rw [hSelf]; rfl
                        erw [hRun] at hEval
                        have hCoin : (1 : Nat) = coin :=
                          congrArg HList.single (Process.done.inj hEval)
                        subst hCoin
                        exact ⟨show (1 : Nat) < 11 by decide, ⟨[], tlElem⟩, rfl, rfl, rfl,
                          ⟨show 0 < (1 : Nat) by decide, show (1 : Nat) < 11 by decide⟩⟩
          -- 3. `SuiteLawfulFor` on `twoLawSuite`
          have hSLFor : Deployed.SuiteLawfulFor twoLawEncoder twoLawModel
              ⟨⟨tlWSiteSampTyped, ann, assoc, assu⟩, tlSiteSampDecl, found, stack, ident⟩ := by
            intro suite _ hCon
            have hSEq : suite = twoLawSuite := (Construction.derived.inj hCon).1.symm
            subst hSEq
            constructor
            · intro e law owner h0 hs drawIns stateTy _ derRef hStart _ _ hLaw hDerFind
                st label payload coin st' _ _ _ hEval
              have hST : stateTy = .nat := by
                have hS0 : findSuiteStart ⟨tlWSiteSampTyped, ann, assoc, assu⟩ twoLawSuite =
                    some ⟨.nat, ⟨tlWHdrStart, Member.tail (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))),
                      rfl, rfl, rfl, rfl⟩⟩ := rfl
                exact congrArg Sigma.fst (Option.some.inj (hStart.symm.trans hS0))
              subst hST
              cases e with
              | mk eSite eCls eTau =>
                  dsimp only at hLaw hDerFind hEval ⊢
                  cases Option.some.inj hLaw
                  cases payload
                  cases law with
                  | uniform =>
                      have hExp : findSuiteDerive twoLawEncoder ⟨tlWSiteSampTyped, ann, assoc, assu⟩
                          twoLawSuite .nat TwoLaw.uniform [] tlElem =
                          some ⟨tlWHdrDerUnif, Member.tail (Member.tail (Member.tail Member.head)),
                            rfl, rfl, rfl, rfl⟩ := rfl
                      have hRefEq := Option.some.inj (hDerFind.symm.trans hExp)
                      subst hRefEq
                      have hRun : Defs.fnTable twoLawModel tlWSiteSampTyped.defs tlWHdrDerUnif
                          (Member.tail (Member.tail (Member.tail Member.head)))
                          (.cons st (.cons label .nil)) =
                          .done (.cons (mixBytes st (0xFE :: label) % 11)
                            (.cons (mixBytes st (0xFE :: label)) .nil)) := rfl
                      change Nat at st coin st'; change List Nat at label
                      erw [hRun] at hEval
                      cases Process.done.inj hEval
                      exact ⟨Nat.mod_lt _ (by decide), ⟨[], tlElem⟩, rfl, rfl, rfl,
                        Nat.mod_lt _ (by decide)⟩
                  | nonzero =>
                      have hExp : findSuiteDerive twoLawEncoder ⟨tlWSiteSampTyped, ann, assoc, assu⟩
                          twoLawSuite .nat TwoLaw.nonzero [] tlElem =
                          some ⟨tlWHdrDerNonZ, Member.tail (Member.tail Member.head),
                            rfl, rfl, rfl, rfl⟩ := rfl
                      have hRefEq := Option.some.inj (hDerFind.symm.trans hExp)
                      subst hRefEq
                      have hRun : Defs.fnTable twoLawModel tlWSiteSampTyped.defs tlWHdrDerNonZ
                          (Member.tail (Member.tail Member.head))
                          (.cons st (.cons label .nil)) =
                          .done (.cons (1 + mixBytes st (0xFD :: label) % 10)
                            (.cons (mixBytes st (0xFD :: label)) .nil)) := rfl
                      change Nat at st coin st'; change List Nat at label
                      erw [hRun] at hEval
                      cases Process.done.inj hEval
                      have hMod := Nat.mod_lt (mixBytes st (0xFD :: label)) (show 0 < 10 by decide)
                      refine ⟨?_, ⟨[], tlElem⟩, rfl, rfl, rfl, ?_⟩
                      · show 1 + mixBytes st (0xFD :: label) % 10 < 11; omega
                      · exact ⟨show 0 < 1 + mixBytes st (0xFD :: label) % 10 by omega,
                          show 1 + mixBytes st (0xFD :: label) % 10 < 11 by omega⟩
            · intro eKey hMem hdr f hFind unitTy τ hIn hOut v₁ v₂ u hv₁ hv₂ hEv₁ hEv₂
              have hK : eKey = ⟨102⟩ := by
                simp only [twoLawSuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
                rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
              subst hK
              have hF102 : tlWSiteSampTyped.find ⟨102⟩ =
                  some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
              obtain ⟨rfl, rfl⟩ := tl_member_unique hFind hF102
              have hTau : τ = tlElem := (List.cons.inj hIn).1.symm
              have hU : unitTy = tlByte := by
                have hc := (List.cons.inj hOut).1.symm; cases hc; rfl
              subst hTau; subst hU
              cases hIn; cases hOut
              change Nat at v₁ v₂; change List Nat at u
              have hRun : ∀ x : Nat, Defs.fnTable twoLawModel tlWSiteSampTyped.defs tlWHdrEncode
                  (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))
                  (.cons x .nil) = .done (.cons [x % 256] .nil) := fun _ => rfl
              erw [hRun v₁] at hEv₁; erw [hRun v₂] at hEv₂
              have h1 : [v₁ % 256] = u := congrArg HList.single (Process.done.inj hEv₁)
              have h2 : [v₂ % 256] = u := congrArg HList.single (Process.done.inj hEv₂)
              have hm : v₁ % 256 = v₂ % 256 := (List.cons.inj (h1.trans h2.symm)).1
              change v₁ < 11 at hv₁; change v₂ < 11 at hv₂
              rw [Nat.mod_eq_of_lt (by omega : v₁ < 256), Nat.mod_eq_of_lt (by omega : v₂ < 256)] at hm
              exact hm
          -- 4. `LayoutLawful` on `twoLawLayout`
          have hLL : Deployed.LayoutLawful twoLawModel
              ⟨⟨tlWSiteSampTyped, ann, assoc, assu⟩, tlSiteSampDecl, found, stack, ident⟩ := by
            intro layout hLay
            have hLEq : layout = ⟨twoLawLayout, [], []⟩ := (Option.some.inj hLay).symm
            subst hLEq
            refine ⟨?_, ?_, ?_⟩
            · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
                v chunk pre post hv _ _ hW
              have hWK : wKey = ⟨102⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
                rcases hwMem with ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | cases h
              have hRK : rKey = ⟨106⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
                rcases hrMem with ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
              subst hWK; subst hRK
              have hF102 : tlWSiteSampTyped.find ⟨102⟩ =
                  some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
              have hF106 : tlWSiteSampTyped.find ⟨106⟩ = some (.fn (Member.tail Member.head)) := rfl
              obtain ⟨rfl, rfl⟩ := tl_member_unique hwFind hF102
              obtain ⟨rfl, rfl⟩ := tl_member_unique hrFind hF106
              have hTau : τ = tlElem := (List.cons.inj hwIn).1.symm
              have hU : unitTy = tlByte := by
                have hc := (List.cons.inj hwOut).1.symm; cases hc; rfl
              subst hTau; subst hU
              cases hwIn; cases hwOut; cases hrIn; cases hrOut
              change Nat at v; change v < 11 at hv
              change List Nat at chunk pre post
              have hWRun : Defs.fnTable twoLawModel tlWSiteSampTyped.defs tlWHdrEncode
                  (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))
                  (.cons v .nil) = .done (.cons [v % 256] .nil) := rfl
              erw [hWRun] at hW
              have hCh : [v % 256] = chunk := congrArg HList.single (Process.done.inj hW)
              subst hCh
              have hV256 : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hV11 : v % 11 = v := Nat.mod_eq_of_lt hv
              have hLt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hAt : (pre ++ [v % 256] ++ post)[pre.length]'hLt = v := by
                have h1 : (pre ++ [v % 256] ++ post)[pre.length]? = some v := by
                  rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
                  simp [hV256]
                rw [List.getElem?_eq_getElem hLt] at h1
                exact Option.some.inj h1
              change Defs.fnTable twoLawModel tlWFnDefs tlWHdrRead (Member.tail Member.head)
                  (.cons (pre ++ [v % 256] ++ post) (.cons pre.length .nil)) = _
              rw [tlWFnDefs_read_eval]
              simp only [hLt, ↓reduceDIte, hAt, hv, ↓reduceIte, hV11]; rfl
            · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
                buf off v nextOff _ _ hR
              have hWK : wKey = ⟨102⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
                rcases hwMem with ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | cases h
              have hRK : rKey = ⟨106⟩ := by
                simp only [twoLawLayout, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
                rcases hrMem with ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
              subst hWK; subst hRK
              have hF102 : tlWSiteSampTyped.find ⟨102⟩ =
                  some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
              have hF106 : tlWSiteSampTyped.find ⟨106⟩ = some (.fn (Member.tail Member.head)) := rfl
              obtain ⟨rfl, rfl⟩ := tl_member_unique hwFind hF102
              obtain ⟨rfl, rfl⟩ := tl_member_unique hrFind hF106
              have hTau : τ = tlElem := (List.cons.inj hwIn).1.symm
              have hU : unitTy = tlByte := by
                have hc := (List.cons.inj hwOut).1.symm; cases hc; rfl
              subst hTau; subst hU
              cases hwIn; cases hwOut; cases hrIn; cases hrOut
              change List Nat at buf; change Nat at off v nextOff
              erw [tlWFnDefs_read_eval] at hR
              by_cases hlt : off < buf.length
              · simp only [hlt, ↓reduceDIte] at hR
                by_cases hb : buf[off]'hlt < 11
                · simp only [hb, ↓reduceIte] at hR
                  have hPair : (HList.cons (buf[off]'hlt % 11) (.cons (off + 1) .nil) :
                      HList twoLawModel.Val [tlElem, .nat]) = .cons v (.cons nextOff .nil) :=
                    Process.done.inj hR
                  have hvEq : buf[off]'hlt % 11 = v := by cases hPair; rfl
                  have hNextEq : off + 1 = nextOff := by cases hPair; rfl
                  subst hvEq; subst hNextEq
                  have hbMod : buf[off]'hlt % 11 = buf[off]'hlt := Nat.mod_eq_of_lt hb
                  refine ⟨by rw [hbMod]; exact hb, Nat.le_succ off, hlt, [buf[off]'hlt], ?_,
                    tlW_list_split buf off hlt⟩
                  have hMod256 : (buf[off]'hlt % 11) % 256 = buf[off]'hlt := by omega
                  show Defs.fnTable twoLawModel tlWSiteSampTyped.defs tlWHdrEncode
                    (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))
                    (.cons (buf[off]'hlt % 11) .nil) = .done (.cons [buf[off]'hlt] .nil)
                  change Process.done (HList.cons (V := twoLawModel.Val) (a := tlBytes)
                      [(buf[off]'hlt % 11) % 256] .nil) = _
                  rw [hMod256]
                · simp only [hb, ↓reduceIte] at hR; cases hR
              · simp only [hlt, ↓reduceDIte] at hR; cases hR
            · intro eqKey hMem
              rcases (by simpa [twoLawLayout] using hMem) with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
          have hInsV : (HList.cons (4 : Nat) (.cons (4 : Nat) .nil) :
              HList (LVal twoLawModel) tlWSiteSampHdr.ins).All (fun a v => twoLawModel.Valid a.ty v) :=
            ⟨show (4 : Nat) < 11 by decide, show (4 : Nat) < 11 by decide, trivial⟩
          have hNoRec : ∀ l, tlSiteSampDecl.layout = some l → l.recover = [] := fun _ h => by
            cases Option.some.inj h; rfl
          exact ⟨a, _, rfl, hFirst, hMatched, hAdm, hDep, hNotAgnostic, hSampFor,
            deploy_complete_samples twoLawModel twoLawEncoder hAdm hDep rfl rfl hNoRec
              0 1 hRoles hFirst hMatched (.cons (4 : Nat) (.cons (4 : Nat) .nil)) hInsV
              hSLFor hLL hSampFor tlWSiteSamp_noHalt (fun _ _ => none) tlWSiteSamp_lp tlWSiteSamp_fed⟩

end Zkc.Core.Tests.Deployment
