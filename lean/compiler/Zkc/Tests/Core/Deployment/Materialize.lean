import Zkc.Core.Scheme.Materialize
import Zkc.Tests.Core.Deployment.Fixtures

/-!
Kernel-checked verification of `Zkc.Core.materializeConstructed` and
`Zkc.Core.materializeSerialized` on the Schnorr deployment fixtures:

1. Re-admission via `Core.admit` for streaming `constructed Core`, compact `constructed Core`,
   and streaming `serialized Core`.
2. Layout binding in `constructed Core`: streaming (`schnorrDecl`) vs compact (`schnorrCompactDecl`)
   produce distinct materialized programs with distinct embedded `sessBytes`.
3. Stage shape invariants (`docs/spec/core/stages.md`):
   - `constructed Core` retains both prover→verifier flows and eliminates all public draws;
   - `serialized Core` eliminates all flows and public draws, prepends the proof input `@[1]`
     and proof output `@[0]`, and preserves the trailing-byte guard key (`finishGuardKey`).
4. Concrete differential equivalence of prover proof bytes and verifier `Outcome` / `Stop`
   (including exact `Reason` and `Occurrence`) across re-admitted `serialized Core`,
   `Core.deploy` (`d.run`), and `Core.specialize` on honest runs and 6 adversarial mutations.
5. Fail-closed refusals on unsupported declarations (`interactiveDecl`, compact layout for
   `materializeSerialized`, `loopSchnorrDecl`).

Note: universal `∀ Y proof` exact `Process` equality, `Reading.read` / `Value.value` preservation,
and `form_of_role` extraction on BOTH re-admitted `constructed Core` and `serialized Core`
verifiers are checked in `lean/formal/checks/ConstructedStage.lean`.
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

/-! ## 1. Materialized Schnorr programs and kernel-checked re-admission -/

theorem schnorr_constructed_isSome :
    (materializeConstructed deployEncoder admittedSuite schnorrDecl).toOption.isSome = true := by
  decide +kernel

def schnorrConstructedProg : NamedProgram deployVocab :=
  (materializeConstructed deployEncoder admittedSuite schnorrDecl).toOption.get
    schnorr_constructed_isSome

theorem schnorr_constructed_ok :
    materializeConstructed deployEncoder admittedSuite schnorrDecl = .ok schnorrConstructedProg :=
  except_toOption_get_ok _ schnorr_constructed_isSome

theorem schnorr_constructed_admit_isSome :
    (admit schnorrConstructedProg noAssociation).toOption.isSome = true := by
  decide +kernel

def schnorrConstructedAdmitted : Admitted deployVocab :=
  (admit schnorrConstructedProg noAssociation).toOption.get schnorr_constructed_admit_isSome

theorem schnorr_constructed_admit_ok :
    admit schnorrConstructedProg noAssociation = .ok schnorrConstructedAdmitted :=
  except_toOption_get_ok _ schnorr_constructed_admit_isSome

theorem schnorr_compact_constructed_isSome :
    (materializeConstructed deployEncoder admittedSuite schnorrCompactDecl).toOption.isSome = true := by
  decide +kernel

def schnorrCompactConstructedProg : NamedProgram deployVocab :=
  (materializeConstructed deployEncoder admittedSuite schnorrCompactDecl).toOption.get
    schnorr_compact_constructed_isSome

theorem schnorr_compact_constructed_admit_isSome :
    (admit schnorrCompactConstructedProg noAssociation).toOption.isSome = true := by
  decide +kernel

def schnorrCompactConstructedAdmitted : Admitted deployVocab :=
  (admit schnorrCompactConstructedProg noAssociation).toOption.get
    schnorr_compact_constructed_admit_isSome

theorem schnorr_serialized_isSome :
    (materializeSerialized deployEncoder admittedSuite schnorrDecl).toOption.isSome = true := by
  decide +kernel

def schnorrSerializedProg : NamedProgram deployVocab :=
  (materializeSerialized deployEncoder admittedSuite schnorrDecl).toOption.get
    schnorr_serialized_isSome

theorem schnorr_serialized_ok :
    materializeSerialized deployEncoder admittedSuite schnorrDecl = .ok schnorrSerializedProg :=
  except_toOption_get_ok _ schnorr_serialized_isSome

theorem schnorr_serialized_admit_isSome :
    (admit schnorrSerializedProg noAssociation).toOption.isSome = true := by
  decide +kernel

def schnorrSerializedAdmitted : Admitted deployVocab :=
  (admit schnorrSerializedProg noAssociation).toOption.get schnorr_serialized_admit_isSome

theorem schnorr_serialized_admit_ok :
    admit schnorrSerializedProg noAssociation = .ok schnorrSerializedAdmitted :=
  except_toOption_get_ok _ schnorr_serialized_admit_isSome

/-! ## 2. Layout binding in `constructed Core` and stage shape invariants -/

/-- Extract the first `[byte]` literal emitted in the entry protocol body (the `sessBytes`
binding passed to `SuiteSlot.start`). -/
private def firstBytesLiteral (prog : NamedProgram deployVocab) : Option (List Nat) :=
  prog.definitions.findSome? fun d =>
    match d with
    | .protocol _ _ _ _ (.mk _ body _) =>
        body.findSome? fun instr =>
          match instr with
          | .op _ _ (.compute _ (.literal (.seq (.fin 256) none) data)) _ => some data
          | _ => none
    | .fn .. => none

/-- Streaming (`schnorrDecl`) vs compact (`schnorrCompactDecl`) materialize to distinct
`constructed Core` programs with distinct embedded `sessBytes` literals (preserving layout
commitment in the transcript session identifier). -/
theorem constructed_layout_binds_sessBytes :
    schnorrConstructedProg ≠ schnorrCompactConstructedProg ∧
    firstBytesLiteral schnorrConstructedProg ≠ firstBytesLiteral schnorrCompactConstructedProg ∧
    (firstBytesLiteral schnorrConstructedProg).isSome = true ∧
    (firstBytesLiteral schnorrCompactConstructedProg).isSome = true := by
  decide +kernel

private def countFlowEvents (events : List (ShapeEvent deployVocab)) : Nat :=
  (events.filter fun e => match e.cls with | .flow .. => true | _ => false).length

private def countPrivateCoins (events : List (ShapeEvent deployVocab)) : Nat :=
  (events.filter fun e => match e.cls with | .given (.coin _) _ [] => true | _ => false).length

/-- Stage shape invariants (`docs/spec/core/stages.md`):
- `constructed Core` retains the 2 flows and 1 private coin, and eliminates all public draws;
- `serialized Core` eliminates all flows and public draws, prepends proof input `@[1]` and proof
  output `@[0]`, and retains only the prover's private coin. -/
def checkMaterializedShapes : Bool :=
  match schnorrConstructedAdmitted.program.findProtocol schnorrDecl.entry,
        schnorrSerializedAdmitted.program.findProtocol schnorrDecl.entry with
  | some ⟨conHdr, _⟩, some ⟨serHdr, _⟩ =>
      let conEvents := conHdr.shape.events [] id
      let serEvents := serHdr.shape.events [] id
      decide (conHdr.ins = ([⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] : List (LTy deployVocab))) &&
      decide (conHdr.outs = ([] : List (LTy deployVocab))) &&
      decide (countFlowEvents conEvents = 2) &&
      decide (countPrivateCoins conEvents = 1) &&
      decide (conHdr.shape.heardCoins = []) &&
      decide (serHdr.ins = ([⟨dBytes, [1]⟩, ⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] : List (LTy deployVocab))) &&
      decide (serHdr.outs = ([⟨dBytes, [0]⟩] : List (LTy deployVocab))) &&
      decide (countFlowEvents serEvents = 0) &&
      decide (countPrivateCoins serEvents = 1) &&
      decide (serHdr.shape.heardCoins = [])
  | _, _ => false

theorem materialized_shapes_ok : checkMaterializedShapes = true := by
  decide +kernel

/-! ## 3. Differential execution: `serialized Core` vs `Core.deploy` vs `Core.specialize` -/

private def runSerializedProver (x Y nonce : Nat) : Option (List Nat) :=
  match schnorrSerializedAdmitted.program.findProtocol schnorrDecl.entry with
  | none => none
  | some ⟨hdr, callee⟩ =>
      if hIns : hdr.ins = [⟨dBytes, [1]⟩, ⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] then
        if hOuts : hdr.outs = [⟨dBytes, [0]⟩] then
          let ins : HList (RV deployModel 0) hdr.ins :=
            cast (congrArg (HList (RV deployModel 0)) hIns.symm)
              (.cons (a := (⟨dBytes, [1]⟩ : LTy deployVocab)) ()
                (.cons (a := (⟨dScalar, [0]⟩ : LTy deployVocab)) (x : Nat)
                  (.cons (a := (⟨dPoint, [0, 1]⟩ : LTy deployVocab)) (Y : Nat) .nil)))
          let proc := (roleMeaning deployModel schnorrSerializedAdmitted.program callee 0 [] ins).map
            (fun out => (out, ()))
          match (runProcess deployModel (fixedNonceSource nonce) 0 proc 512).1 with
          | .ended (.returned (out, _)) =>
              let out' : HList (RV deployModel 0) [⟨dBytes, [0]⟩] :=
                cast (congrArg (HList (RV deployModel 0)) hOuts) out
              match out' with
              | .cons bs .nil => some bs
          | _ => none
        else none
      else none

private def runSerializedVerifierOutcome (Y : Nat) (proof : List Nat) : Option (Option Stop) :=
  match schnorrSerializedAdmitted.program.findProtocol schnorrDecl.entry with
  | none => none
  | some ⟨hdr, callee⟩ =>
      if hIns : hdr.ins = [⟨dBytes, [1]⟩, ⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] then
        let ins : HList (RV deployModel 1) hdr.ins :=
          cast (congrArg (HList (RV deployModel 1)) hIns.symm)
            (.cons (a := (⟨dBytes, [1]⟩ : LTy deployVocab)) proof
              (.cons (a := (⟨dScalar, [0]⟩ : LTy deployVocab)) ()
                (.cons (a := (⟨dPoint, [0, 1]⟩ : LTy deployVocab)) (Y : Nat) .nil)))
        let proc := (roleMeaning deployModel schnorrSerializedAdmitted.program callee 1 [] ins).map
          (fun out => (out, ()))
        match (runProcess deployModel (fixedNonceSource 0) 1 proc 512).1 with
        | .ended (.returned _) => some none
        | .ended (.stopped stop) => some (some stop)
        | _ => none
      else none

private def runDeployedVerifierOutcome (Y : Nat) (proof : List Nat) : Option (Option Stop) :=
  match schnorrInputs schnorrDeployed.entry.ins 0 Y,
        packProofBytes proof (Stack.Takes (schnorrDeployed.stack 1)) with
  | some ins, some taken =>
      match (execute schnorrDeployed deployModel 1 (hideAll deployModel 1 ins) taken
          (fixedNonceSource 0) 512).1 with
      | .ended (.returned _) => some none
      | .ended (.stopped stop) => some (some stop)
      | _ => none
  | _, _ => none

private def runSpecializedVerifierOutcome (Y : Nat) (proof : List Nat) : Option (Option Stop) :=
  match schnorrInputs schnorrDeployed.entry.ins 0 Y,
        packProofBytes proof (Stack.Takes (schnorrDeployed.stack 1)) with
  | some ins, some taken =>
      let cr := specialize schnorrDeployed 1
      let proc := cr.denote deployModel (Defs.fnTable deployModel schnorrDeployed.admitted.program.defs)
        (hideAll deployModel 1 ins) taken
      match (runProcess deployModel (fixedNonceSource 0) 1 proc 512).1 with
      | .ended (.returned _) => some none
      | .ended (.stopped stop) => some (some stop)
      | _ => none
  | _, _ => none

/-- Prover proof bytes and verifier `Outcome` / exact `Stop` (`Reason` + `Occurrence`) agree
bit-for-bit across re-admitted `serialized Core`, `Core.deploy`, and `Core.specialize` on honest
runs and all 6 adversarial proof/statement mutations. -/
def checkSerializedDifferential : Bool :=
  let cases : List (Nat × Nat × Nat) := [(7, 5, 8), (3, 2, 5), (9, 8, 10)]
  cases.all fun (x, nonce, badX) =>
    let Y := powMod 2 x 23
    match runSerializedProver x Y nonce, runProve schnorrDeployed x Y nonce with
    | some pfSer, some pfDep =>
        let samePf := decide (pfSer = pfDep)
        let badY := powMod 2 badX 23
        let rej (k : Nat) : Option Stop := some (.declared .reject ⟨[], ⟨k⟩⟩)
        let probes : List (Nat × List Nat × Option Stop) := [
          (Y, pfSer, none),                       -- honest proof accepts
          (badY, pfSer, rej 21),                  -- wrong statement rejects at guard 21
          (Y, [], rej 3),                         -- empty proof rejects at readPoint bounds guard 3
          (Y, pfSer.take 1, rej 3),               -- truncated proof rejects at readScalar bounds guard 3
          (Y, pfSer ++ [0], rej 29),              -- trailing byte rejects at finishGuardKey 29
          (Y, [23, pfSer.getD 1 0], rej 8),       -- out-of-range point rejects at readPoint range guard 8
          (Y, [pfSer.getD 0 0, 11], rej 8)        -- out-of-range scalar rejects at readScalar range guard 8
        ]
        samePf && probes.all fun (stmt, pf, expected) =>
          let oSer := runSerializedVerifierOutcome stmt pf
          let oDep := runDeployedVerifierOutcome stmt pf
          let oSpec := runSpecializedVerifierOutcome stmt pf
          decide (oSer = some expected) && decide (oSer = oDep) && decide (oDep = oSpec)
    | _, _ => false

theorem serialized_differential_ok : checkSerializedDifferential = true := by
  decide +kernel

/-! ## 4. Fail-closed refusals on out-of-scope declarations -/

private def matFails {V : Vocabulary} (res : Except (List (ProgramRefusal V)) (NamedProgram V)) : Bool :=
  match res with
  | .error (_ :: _) => true
  | _ => false

theorem materialize_fail_closed_refusals :
    matFails (materializeConstructed deployEncoder admittedSuite interactiveDecl) = true ∧
    matFails (materializeSerialized deployEncoder admittedSuite interactiveDecl) = true ∧
    matFails (materializeSerialized deployEncoder admittedSuite schnorrCompactDecl) = true ∧
    matFails (materializeConstructed deployEncoder admittedSuite loopSchnorrDecl) = true ∧
    matFails (materializeSerialized deployEncoder admittedSuite loopSchnorrDecl) = true := by
  decide +kernel

end Zkc.Core.Tests.Deployment
