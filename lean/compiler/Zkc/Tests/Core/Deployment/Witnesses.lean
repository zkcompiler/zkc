import Zkc.Tests.Core.Deployment.Fixtures

/-!
Concrete, non-vacuous, kernel-checked witness instantiations of the Core deployment, completeness,
ideal random-oracle, and handler-specialization theorems:

1. `deploy_statements_instantiated`: all 12 `Statements.*` predicates instantiated on `cDeploy`.
2. `deployModel_canonicalFormat_witness`: concrete `canonicalFormat_lawful` witness.
3. Specialization soundness witnesses:
   - `retrySchnorr_wellNested`, `retrySchnorr_specialize_sound`
   - `schnorrIdeal_specialize_sound`
   - `witness_specialize_dag_sound`: DAG-preserving linear-size specialization (`9` `ClosedProcs`,
     `astSize < 160`) paired with `specialize_deploy_sound` on `dagSchnorrDeployed`.
4. Generalized completeness witnesses (all hypotheses — `SuiteLawfulFor`, `LayoutLawful`,
   `SamplesLawful`, `RecoveryLawful`, honest completeness, `LawfulPrivate`/`Fed` — discharged):
   - `witness_deploy_complete`: streaming Fiat–Shamir completeness (`deploy_complete`).
   - `witness_deploy_complete_samples`: deterministic prover-sampling completeness
     (`deploy_complete_samples`) on the completely empty world `source := fun _ _ => none`.
   - `witness_deploy_complete_compact`: compact carry/recover completeness
     (`deploy_complete_compact`) on prime-order additive group `primeOrderModel`.
   - `witness_deploy_complete_retry`: abort-and-retry completeness (`deploy_complete_retry`) at
     `k = 1`, exercising real prover abort after transcript absorption & proof write, rollback via
     `restoreAgain`, and honest acceptance on attempt `1`.
5. Ideal random-oracle linkage and domain separation witnesses:
   - `witness_idealPath_msgStep_injective`
   - `witness_deployIdeal_link_concrete_ro` (with concrete partial oracle `schnorrIdealRO`)
   - `witness_deployIdeal_queries_nodup` (`qs.Nodup` + `st0` prefix extension on every path)
   - `witness_cross_session_disjoint` (`schnorrDecl` vs `schnorrAppCtxDecl` can never share a query)
   - `witness_cross_statement_disjoint` (`Y₁ = 13` vs `Y₂ = 2` can never share a query)
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

set_option maxRecDepth 16000

/-! ## Top-level `Statements.*`, canonical format, and specialization soundness witnesses -/

/-- Concrete `Functions deployVocab` record instantiating all proved Core statement theorems. -/
def cDeploy : Functions deployVocab where
  elaborate := elaborateProgram
  eraseRole := fun {_} _ {_} {_} _ => .mk [] [] []
  format := canonicalFormat
  admit := admit
  check := check
  deploy := deploy deployEncoder
  identity := deployedIdentity
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
    SchemeStatements.completeStreaming deployEncoder ∧
    SchemeStatements.idealLink deployEncoder ∧
    Statements.executorRuns cDeploy :=
  ⟨canonicalFormat_formats cDeploy rfl,
   deployedIdentity_identityReads deployEncoder cDeploy rfl rfl,
   statements_deployKeeps deployEncoder cDeploy rfl,
   statements_deployFindsRoles deployEncoder cDeploy rfl,
   statements_deployMatches deployEncoder cDeploy rfl,
   statements_deployScoped deployEncoder cDeploy rfl,
   statements_deployFresh deployEncoder cDeploy rfl,
   statements_deployedSafe deployEncoder cDeploy rfl rfl,
   statements_deployCoverage deployEncoder cDeploy rfl,
   statements_completeStreaming deployEncoder cDeploy rfl rfl,
   statements_completeStreamingFor deployEncoder,
   statements_idealLink deployEncoder,
   execute_runs cDeploy rfl⟩

/-- Direct concrete witness of `canonicalFormat_lawful` on `(scalar, point)` in `deployModel`. -/
theorem deployModel_canonicalFormat_witness :
    (canonicalFormat deployModel deployCodecs
      (.tuple (.cons dScalar (.cons dPoint .nil)))).Lawful
      (deployModel.Valid (.tuple (.cons dScalar (.cons dPoint .nil)))) :=
  canonicalFormat_lawful deployModel deployCodecs (.tuple (.cons dScalar (.cons dPoint .nil)))

/-- Direct witnesses of `deploy_wellNestedRetry`, `specialize_deploy_sound`, and
`specialize_deployIdeal_sound` on concrete deployments (including retried and ideal schemes). -/
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
  specialize_deployIdeal_sound deployModel deployEncoder idealServiceKey admittedSuite
    schnorrDecl schnorrIdealDeployed schnorrIdeal_deploy_ok r ins taken

/-- Concrete witness of DAG-preserving multi-procedure specialization: on the depth-8 diamond DAG
(`2^8 = 256` dynamic call paths), `Core.specialize` produces linear-size `ClosedProcs` (`9` shared
procedures, `astSize < 160`) whose denotation equals `dagSchnorrDeployed.run` identically on every
role, input, and taken buffer. -/
theorem witness_specialize_dag_sound :
    (specialize dagSchnorrDeployed 0).procSigs.length = 9 ∧
    (specialize dagSchnorrDeployed 0).astSize < 160 ∧
    ∀ (r : Role)
      (ins : HList (RV deployModel r) dagSchnorrDeployed.entry.ins)
      (taken : HList deployModel.Val (Stack.Takes (dagSchnorrDeployed.stack r))),
      (specialize dagSchnorrDeployed r).denote deployModel
          (Defs.fnTable deployModel dagSchnorrDeployed.admitted.program.defs) ins taken =
        dagSchnorrDeployed.run deployModel r ins taken :=
  ⟨by decide +kernel, by decide +kernel,
   fun r ins taken =>
     specialize_deploy_sound deployModel deployEncoder admittedDag dagSchnorrDecl
       dagSchnorrDeployed dagSchnorr_deploy_ok r ins taken⟩

/-! ## Explicit typed witness programs (connected to `admit` via `admitted_eq_of_readback`) -/

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

/-- Point reader checking `< 11` for prime-order additive group `primeOrderModel`. -/
private def wFnReadPoint11 {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dBytes, .nat]) [dPoint, .nat] :=
  .op ⟨1⟩ (.owned (.seqLength dByte none rfl)) (.cons (wvar 0) .nil) (.cons 2 .nil) <|
  .op ⟨2⟩ (.owned .natLess) (.cons (wvar 1) (.cons (wvar 2) .nil)) (.cons 3 .nil) <|
  .guard ⟨3⟩ () (wvar 3) rfl .reject <|
  .op ⟨4⟩ (.owned (.seqAt dByte none rfl)) (.cons (wvar 0) (.cons (wvar 1) .nil)) (.cons 4 .nil) <|
  .op ⟨5⟩ (.owned (.finToNat 256)) (.cons (wvar 4) .nil) (.cons 5 .nil) <|
  .op ⟨6⟩ (.literal .nat [11] rfl) .nil (.cons 6 .nil) <|
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

private def wFnRecoverCommit {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns) (Ctx.positional [dPoint, dScalar, dScalar]) [dPoint] :=
  .op ⟨1⟩ (.row DeployRow.base _ rfl) (.cons (wvar 2) .nil) (.cons 3 .nil) <|
  .op ⟨2⟩ (.row DeployRow.negScale _ rfl) (.cons (wvar 1) (.cons (wvar 0) .nil)) (.cons 4 .nil) <|
  .op ⟨3⟩ (.row DeployRow.plus _ rfl) (.cons (wvar 3) (.cons (wvar 4) .nil)) (.cons 5 .nil) <|
  .ret (.cons (wvar 5) .nil)

private def wFnSamples {fns : List (FnHeader deployVocab)} :
    Term (localDialect deployVocab fns)
      (Ctx.positional [dScalar, dPoint, dBytes, dBytes, .nat, .nat]) [dScalar] :=
  .op ⟨1⟩ (.row DeployRow.mix _ rfl) (.cons (wvar 4) (.cons (wvar 2) .nil)) (.cons 6 .nil) <|
  .op ⟨2⟩ (.row DeployRow.mix _ rfl) (.cons (wvar 6) (.cons (wvar 3) .nil)) (.cons 7 .nil) <|
  .op ⟨3⟩ (.owned .natAdd) (.cons (wvar 7) (.cons (wvar 5) .nil)) (.cons 8 .nil) <|
  .op ⟨4⟩ (.row DeployRow.natToScalar _ rfl) (.cons (wvar 8) .nil) (.cons 9 .nil) <|
  .ret (.cons (wvar 9) .nil)

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

/-- Body inside `.attempt ⟨409⟩` of `wRetrySchnorrTerm`: does not reference the attempt index `2`
and contains no nested attempts. -/
private def wRetryBody {hs : Headers deployVocab} :
    Term (protocolDialect deployVocab hs)
      ((Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]).extend
        (.cons 2 .nil : Names [LTy.index [0]])) [] :=
  .op ⟨410⟩ (.given (.coin ()) 0 [] [] dScalar ⟨⟨[], dScalar⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 3 .nil) <|
  .op ⟨411⟩ (.compute [0] (.row DeployRow.base _ rfl) [⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 3) .nil) (.cons 4 .nil) <|
  .op ⟨412⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (wvar 4) .nil) (.cons 5 .nil) <|
  .op ⟨414⟩ (.compute [0] (.literal (V := deployVocab) dScalar [0] rfl) [] rfl (by decide)) .nil (.cons 6 .nil) <|
  .op ⟨415⟩ (.compute [0] (.row DeployRow.sameScalar _ rfl) [⟨dScalar, [0]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 3) (.cons (wvar 6) .nil)) (.cons 7 .nil) <|
  .op ⟨416⟩ (.compute [0] (.owned .boolNot) [⟨.bool, [0]⟩] rfl (by decide))
      (.cons (wvar 7) .nil) (.cons 8 .nil) <|
  .guard ⟨417⟩ [0] (wvar 8) ⟨rfl, by decide, by decide⟩ .abort <|
  .op ⟨413⟩ (.given (.coin ()) 1 [0] [] dScalar ⟨⟨[], dScalar⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 9 .nil) <|
  .op ⟨418⟩ (.compute [0] (.row DeployRow.mul _ rfl) [⟨dScalar, [0, 1]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 9) (.cons (wvar 0) .nil)) (.cons 10 .nil) <|
  .op ⟨419⟩ (.compute [0] (.row DeployRow.add _ rfl) [⟨dScalar, [0]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 3) (.cons (wvar 10) .nil)) (.cons 11 .nil) <|
  .op ⟨420⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (wvar 11) .nil) (.cons 12 .nil) <|
  .op ⟨421⟩ (.compute [1] (.row DeployRow.base _ rfl) [⟨dScalar, [0, 1]⟩] rfl (by decide))
      (.cons (wvar 12) .nil) (.cons 13 .nil) <|
  .op ⟨422⟩ (.compute [1] (.row DeployRow.scale _ rfl) [⟨dScalar, [0, 1]⟩, ⟨dPoint, [0, 1]⟩] rfl (by decide))
      (.cons (wvar 9) (.cons (wvar 1) .nil)) (.cons 14 .nil) <|
  .op ⟨423⟩ (.compute [1] (.row DeployRow.plus _ rfl) [⟨dPoint, [0, 1]⟩, ⟨dPoint, [1]⟩] rfl (by decide))
      (.cons (wvar 5) (.cons (wvar 14) .nil)) (.cons 15 .nil) <|
  .op ⟨424⟩ (.compute [1] (.row DeployRow.same _ rfl) [⟨dPoint, [1]⟩, ⟨dPoint, [1]⟩] rfl (by decide))
      (.cons (wvar 13) (.cons (wvar 15) .nil)) (.cons 16 .nil) <|
  .guard ⟨425⟩ [1] (wvar 16) ⟨rfl, by decide, by decide⟩ .reject <|
  .ret .nil

/-- Rejection-sampling Schnorr inside prover-owned `.attempt ⟨409⟩ [0]`: sends commitment `A = g^r`
(writing to both transcript and proof buffer), then aborts when `r = 0` without reading the attempt
index (`AttemptIndexFree`), triggering clean rollback via `restoreAgain` before succeeding on the
next attempt with `r = 5`. -/
private def wRetrySchnorrTerm {hs : Headers deployVocab} :
    Term (protocolDialect deployVocab hs)
      (Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]) [] :=
  .attempt ⟨409⟩ [0] ⟨0, rfl⟩ (.cons 2 .nil) wRetryBody .nil (.ret .nil)

private abbrev wHdrStart : FnHeader deployVocab := ⟨⟨100⟩, [dBytes], [.nat], false, none, Summary.empty⟩
private abbrev wHdrAbsorb : FnHeader deployVocab := ⟨⟨101⟩, [.nat, dBytes, dBytes], [.nat], false, none, Summary.empty⟩
private abbrev wHdrEncScalar : FnHeader deployVocab := ⟨⟨102⟩, [dScalar], [dBytes], false, none, Summary.empty⟩
private abbrev wHdrEncPoint : FnHeader deployVocab := ⟨⟨103⟩, [dPoint], [dBytes], false, none, Summary.empty⟩
private abbrev wHdrDerive : FnHeader deployVocab := ⟨⟨104⟩, [.nat, dBytes], [dScalar, .nat], false, none, Summary.empty⟩
private abbrev wHdrReadScalar : FnHeader deployVocab := ⟨⟨105⟩, [dBytes, .nat], [dScalar, .nat], true, none, Summary.empty⟩
private abbrev wHdrReadPoint : FnHeader deployVocab := ⟨⟨106⟩, [dBytes, .nat], [dPoint, .nat], true, none, Summary.empty⟩
private abbrev wHdrEqScalar : FnHeader deployVocab := ⟨⟨107⟩, [dScalar, dScalar], [.bool], false, none, Summary.empty⟩
private abbrev wHdrRecover : FnHeader deployVocab := ⟨⟨108⟩, [dPoint, dScalar, dScalar], [dPoint], false, none, Summary.empty⟩
private abbrev wHdrSamples : FnHeader deployVocab :=
  ⟨⟨109⟩, [dScalar, dPoint, dBytes, dBytes, .nat, .nat], [dScalar], false, none, Summary.empty⟩

private abbrev wFnHeaders : List (FnHeader deployVocab) :=
  [wHdrSamples, wHdrEqScalar, wHdrReadPoint, wHdrReadScalar, wHdrDerive,
   wHdrEncPoint, wHdrEncScalar, wHdrAbsorb, wHdrStart]

private abbrev wCompactFnHeaders : List (FnHeader deployVocab) :=
  [wHdrRecover, wHdrEqScalar, wHdrReadPoint, wHdrReadScalar, wHdrDerive,
   wHdrEncPoint, wHdrEncScalar, wHdrAbsorb, wHdrStart]

private abbrev wSchnorrHdr : ProtocolHeader deployVocab :=
  ⟨⟨200⟩, 2, [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩], [], shapeOf (wSchnorrTerm (hs := ⟨wFnHeaders, []⟩))⟩

private abbrev wCompactSchnorrHdr : ProtocolHeader deployVocab :=
  ⟨⟨200⟩, 2, [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩], [], shapeOf (wSchnorrTerm (hs := ⟨wCompactFnHeaders, []⟩))⟩

private abbrev wRetrySchnorrHdr : ProtocolHeader deployVocab :=
  ⟨⟨202⟩, 2, [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩], [], shapeOf (wRetrySchnorrTerm (hs := ⟨wFnHeaders, []⟩))⟩

private def wFnDefs : Defs deployVocab ⟨wFnHeaders, []⟩ :=
  .fn wHdrSamples (Names.counting 0 _) wFnSamples
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
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

private def wCompactFnDefs : Defs deployVocab ⟨wCompactFnHeaders, []⟩ :=
  .fn wHdrRecover (Names.counting 0 _) wFnRecoverCommit
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrEqScalar (Names.counting 0 _) wFnEqScalar
    ⟨(Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel, by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel),
     rfl⟩ <|
  .fn wHdrReadPoint (Names.counting 0 _) wFnReadPoint11
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

private def compactWitnessDefs : Defs deployVocab ⟨wCompactFnHeaders, [wCompactSchnorrHdr]⟩ :=
  .protocol wCompactSchnorrHdr (Names.counting 0 _) wSchnorrTerm
    ⟨by simp [Within, ProtocolOp.Within, wSchnorrTerm, wCompactSchnorrHdr],
     by decide,
     by simp [Enclosed, wSchnorrTerm],
     (Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     rfl,
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel)⟩
    wCompactFnDefs

private def retryWitnessDefs : Defs deployVocab ⟨wFnHeaders, [wRetrySchnorrHdr]⟩ :=
  .protocol wRetrySchnorrHdr (Names.counting 0 _) wRetrySchnorrTerm
    ⟨by simp [Within, ProtocolOp.Within, wRetrySchnorrTerm, wRetryBody, wRetrySchnorrHdr],
     by decide,
     by simp [Enclosed, wRetrySchnorrTerm, wRetryBody],
     (Term.repeatedAddress_eq_none _).mp (by decide +kernel),
     rfl,
     by unfold Term.UsedOnce; decide +kernel,
     by decide +kernel,
     (Term.rebound_eq_none _ _).mp (by decide +kernel)⟩
    wFnDefs

private def witnessTyped : Typed deployVocab :=
  ⟨⟨wFnHeaders, [wSchnorrHdr]⟩, witnessDefs, by decide⟩

private def compactWitnessTyped : Typed deployVocab :=
  ⟨⟨wCompactFnHeaders, [wCompactSchnorrHdr]⟩, compactWitnessDefs, by decide⟩

private def retryWitnessTyped : Typed deployVocab :=
  ⟨⟨wFnHeaders, [wRetrySchnorrHdr]⟩, retryWitnessDefs, by decide⟩

/-- Streaming retry declaration (`bound = 4`, `target = ⟨[], ⟨409⟩⟩`, `samples = none`) for
`witness_deploy_complete_retry`. -/
def retryNoSamplesDecl : Declaration :=
  { retrySchnorrDecl with key := ⟨18⟩, samples := none }

/-! ## Admission and deployment existence witnesses -/

private theorem witness_admit_isOk :
    (admit (erase witnessTyped) noAssociation).isOk = true := by
  decide +kernel

private theorem witness_deploy_isOk :
    (match admit (erase witnessTyped) noAssociation with
     | .ok a => (deploy deployEncoder a schnorrDecl).isOk
     | .error _ => false) = true := by
  decide +kernel

private theorem witness_deploySamples_isOk :
    (match admit (erase witnessTyped) noAssociation with
     | .ok a => (deploy deployEncoder a schnorrSamplesDecl).isOk
     | .error _ => false) = true := by
  decide +kernel

private theorem witness_deployIdeal_isOk :
    (match admit (erase witnessTyped) noAssociation with
     | .ok a => (deployIdeal deployEncoder idealServiceKey a schnorrDecl).isOk
     | .error _ => false) = true := by
  decide +kernel

private theorem witness_deployIdealAppCtx_isOk :
    (match admit (erase witnessTyped) noAssociation with
     | .ok a => (deployIdeal deployEncoder idealServiceKey a schnorrAppCtxDecl).isOk
     | .error _ => false) = true := by
  decide +kernel

private theorem compactWitness_admit_isOk :
    (admit (erase compactWitnessTyped) noAssociation).isOk = true := by
  decide +kernel

private theorem compactWitness_deploy_isOk :
    (match admit (erase compactWitnessTyped) noAssociation with
     | .ok a => (deploy deployEncoder a schnorrCompactDecl).isOk
     | .error _ => false) = true := by
  decide +kernel

private theorem retryWitness_admit_isOk :
    (admit (erase retryWitnessTyped) noAssociation).isOk = true := by
  decide +kernel

private theorem retryWitness_deploy_isOk :
    (match admit (erase retryWitnessTyped) noAssociation with
     | .ok a => (deploy deployEncoder a retryNoSamplesDecl).isOk
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

private theorem witness_deploySamples_exists :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      a.program = witnessTyped ∧
      deploy deployEncoder a schnorrSamplesDecl = .ok d := by
  obtain ⟨a, hAdm, hProg⟩ := witness_admit_exists
  cases hDep : deploy deployEncoder a schnorrSamplesDecl with
  | error _ =>
      have hOk := witness_deploySamples_isOk
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

private theorem witness_deployIdealAppCtx_exists :
    ∃ (a : Admitted deployVocab) (dIdeal : Deployed deployVocab),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      a.program = witnessTyped ∧
      deployIdeal deployEncoder idealServiceKey a schnorrAppCtxDecl = .ok dIdeal := by
  obtain ⟨a, hAdm, hProg⟩ := witness_admit_exists
  cases hDep : deployIdeal deployEncoder idealServiceKey a schnorrAppCtxDecl with
  | error _ =>
      have hOk := witness_deployIdealAppCtx_isOk
      rw [hAdm] at hOk; dsimp only at hOk; rw [hDep] at hOk; cases hOk
  | ok dIdeal => exact ⟨a, dIdeal, hAdm, hProg, hDep⟩

private theorem compactWitness_admit_exists :
    ∃ a : Admitted deployVocab,
      admit (erase compactWitnessTyped) noAssociation = .ok a ∧ a.program = compactWitnessTyped := by
  cases h : admit (erase compactWitnessTyped) noAssociation with
  | error _ => have hOk := compactWitness_admit_isOk; rw [h] at hOk; cases hOk
  | ok a => exact ⟨a, rfl, admitted_eq_of_readback h rfl⟩

private theorem compactWitness_deploy_exists :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab),
      admit (erase compactWitnessTyped) noAssociation = .ok a ∧
      a.program = compactWitnessTyped ∧
      deploy deployEncoder a schnorrCompactDecl = .ok d := by
  obtain ⟨a, hAdm, hProg⟩ := compactWitness_admit_exists
  cases hDep : deploy deployEncoder a schnorrCompactDecl with
  | error _ =>
      have hOk := compactWitness_deploy_isOk
      rw [hAdm] at hOk; dsimp only at hOk; rw [hDep] at hOk; cases hOk
  | ok d => exact ⟨a, d, hAdm, hProg, hDep⟩

private theorem retryWitness_admit_exists :
    ∃ a : Admitted deployVocab,
      admit (erase retryWitnessTyped) noAssociation = .ok a ∧ a.program = retryWitnessTyped := by
  cases h : admit (erase retryWitnessTyped) noAssociation with
  | error _ => have hOk := retryWitness_admit_isOk; rw [h] at hOk; cases hOk
  | ok a => exact ⟨a, rfl, admitted_eq_of_readback h rfl⟩

private theorem retryWitness_deploy_exists :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab),
      admit (erase retryWitnessTyped) noAssociation = .ok a ∧
      a.program = retryWitnessTyped ∧
      deploy deployEncoder a retryNoSamplesDecl = .ok d := by
  obtain ⟨a, hAdm, hProg⟩ := retryWitness_admit_exists
  cases hDep : deploy deployEncoder a retryNoSamplesDecl with
  | error _ =>
      have hOk := retryWitness_deploy_isOk
      rw [hAdm] at hOk; dsimp only at hOk; rw [hDep] at hOk; cases hOk
  | ok d => exact ⟨a, d, hAdm, hProg, hDep⟩

/-! ## Function evaluation lemmas and semantic law proofs (`SuiteLawful`, `LayoutLawful`, `SamplesLawful`, `RecoveryLawful`) -/

private theorem member_unique_of_find {V : Vocabulary} {p : Typed V} {k : Key}
    {h₁ h₂ : FnHeader V} {f₁ : Member p.headers.fns h₁} {f₂ : Member p.headers.fns h₂}
    (hf₁ : p.find k = some (.fn f₁)) (hf₂ : p.find k = some (.fn f₂)) :
    ∃ e : h₁ = h₂, e ▸ f₁ = f₂ := by
  have he := Option.some.inj (hf₁.symm.trans hf₂)
  cases he
  exact ⟨rfl, rfl⟩

private theorem cast_inj {α β : Type} {e : α = β} {x y : α} (h : cast e x = cast e y) : x = y := by
  subst e; exact h

private theorem ownedOp_seqAt_some {V : Vocabulary} (M : Model V) (item : V.Ty)
    (free : Ty.isLinear V item = false) (buf : List (M.Val item)) (off : Nat)
    (hlt : off < buf.length) :
    ownedOp M (.seqAt item none free) (.cons buf (.cons off .nil)) =
      Process.done (.cons (buf[off]'hlt) .nil) := by
  simp only [ownedOp, List.getElem?_eq_getElem hlt]

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

-- Concrete `deployModel` evaluators shared by `witnessTyped` and `retryWitnessTyped`
private theorem wfn102_deploy {p : Typed deployVocab}
    (hP : p = witnessTyped ∨ p = retryWitnessTyped) (hdr : FnHeader deployVocab)
    (f : Member p.headers.fns hdr) (hFind : p.find ⟨102⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dScalar]) (hOut : hdr.outs = [dBytes]),
      ∀ (v : Nat),
        Defs.fnTable deployModel p.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons v .nil)) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm) (.cons [v % 256] .nil)) := by
  rcases hP with rfl | rfl
  · have h102 : witnessTyped.find ⟨102⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h102
    subst e; subst he; exact ⟨rfl, rfl, fun _ => rfl⟩
  · have h102 : retryWitnessTyped.find ⟨102⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h102
    subst e; subst he; exact ⟨rfl, rfl, fun _ => rfl⟩

private theorem wfn103_deploy {p : Typed deployVocab}
    (hP : p = witnessTyped ∨ p = retryWitnessTyped) (hdr : FnHeader deployVocab)
    (f : Member p.headers.fns hdr) (hFind : p.find ⟨103⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dPoint]) (hOut : hdr.outs = [dBytes]),
      ∀ (v : Nat),
        Defs.fnTable deployModel p.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons v .nil)) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm) (.cons [v % 256] .nil)) := by
  rcases hP with rfl | rfl
  · have h103 : witnessTyped.find ⟨103⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head)))))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h103
    subst e; subst he; exact ⟨rfl, rfl, fun _ => rfl⟩
  · have h103 : retryWitnessTyped.find ⟨103⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head)))))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h103
    subst e; subst he; exact ⟨rfl, rfl, fun _ => rfl⟩

private theorem wfn104_deploy {p : Typed deployVocab}
    (hP : p = witnessTyped ∨ p = retryWitnessTyped) (hdr : FnHeader deployVocab)
    (f : Member p.headers.fns hdr) (hFind : p.find ⟨104⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [.nat, dBytes]) (hOut : hdr.outs = [dScalar, .nat]),
      ∀ (st : Nat) (lbl : List Nat),
        Defs.fnTable deployModel p.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons st (.cons lbl .nil))) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm)
            (.cons (mixBytes st (0xFF :: lbl) % 11) (.cons (mixBytes st (0xFF :: lbl)) .nil))) := by
  rcases hP with rfl | rfl
  · have h104 : witnessTyped.find ⟨104⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h104
    subst e; subst he; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  · have h104 : retryWitnessTyped.find ⟨104⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h104
    subst e; subst he; exact ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem wFnReadScalar_deploy_eval {fns : List (FnHeader deployVocab)}
    (fnTable : FnTable deployModel fns) (buf : List Nat) (off : Nat) :
    wFnReadScalar.denote (localSem deployModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [dBytes, .nat]) (.cons buf (.cons off .nil))) =
      if hlt : off < buf.length then
        let b := buf[off]'hlt
        if b < 11 then
          .done (.cons (b % 11) (.cons (off + 1) .nil))
        else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
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

private theorem wfn105_deploy {p : Typed deployVocab}
    (hP : p = witnessTyped ∨ p = retryWitnessTyped) (hdr : FnHeader deployVocab)
    (f : Member p.headers.fns hdr) (hFind : p.find ⟨105⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dBytes, .nat]) (hOut : hdr.outs = [dScalar, .nat]),
      ∀ (buf : List Nat) (off : Nat),
        Defs.fnTable deployModel p.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons buf (.cons off .nil))) =
          if hlt : off < buf.length then
            let b := buf[off]'hlt
            if b < 11 then
              .done (cast (congrArg (HList deployModel.Val) hOut.symm)
                (.cons (b % 11) (.cons (off + 1) .nil)))
            else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
          else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  rcases hP with rfl | rfl
  · have h105 : witnessTyped.find ⟨105⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail Member.head)))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h105
    subst e; subst he; exact ⟨rfl, rfl, fun buf off => wFnReadScalar_deploy_eval _ buf off⟩
  · have h105 : retryWitnessTyped.find ⟨105⟩ =
        some (.fn (Member.tail (Member.tail (Member.tail Member.head)))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h105
    subst e; subst he; exact ⟨rfl, rfl, fun buf off => wFnReadScalar_deploy_eval _ buf off⟩

private theorem wFnReadPoint_deploy_eval {fns : List (FnHeader deployVocab)}
    (fnTable : FnTable deployModel fns) (buf : List Nat) (off : Nat) :
    wFnReadPoint.denote (localSem deployModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [dBytes, .nat]) (.cons buf (.cons off .nil))) =
      if hlt : off < buf.length then
        let b := buf[off]'hlt
        if b < 23 then
          .done (.cons (b % 23) (.cons (off + 1) .nil))
        else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
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

private theorem wfn106_deploy {p : Typed deployVocab}
    (hP : p = witnessTyped ∨ p = retryWitnessTyped) (hdr : FnHeader deployVocab)
    (f : Member p.headers.fns hdr) (hFind : p.find ⟨106⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dBytes, .nat]) (hOut : hdr.outs = [dPoint, .nat]),
      ∀ (buf : List Nat) (off : Nat),
        Defs.fnTable deployModel p.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons buf (.cons off .nil))) =
          if hlt : off < buf.length then
            let b := buf[off]'hlt
            if b < 23 then
              .done (cast (congrArg (HList deployModel.Val) hOut.symm)
                (.cons (b % 23) (.cons (off + 1) .nil)))
            else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
          else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  rcases hP with rfl | rfl
  · have h106 : witnessTyped.find ⟨106⟩ = some (.fn (Member.tail (Member.tail Member.head))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h106
    subst e; subst he; exact ⟨rfl, rfl, fun buf off => wFnReadPoint_deploy_eval _ buf off⟩
  · have h106 : retryWitnessTyped.find ⟨106⟩ = some (.fn (Member.tail (Member.tail Member.head))) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h106
    subst e; subst he; exact ⟨rfl, rfl, fun buf off => wFnReadPoint_deploy_eval _ buf off⟩

private theorem wfn107_deploy {p : Typed deployVocab}
    (hP : p = witnessTyped ∨ p = retryWitnessTyped) (hdr : FnHeader deployVocab)
    (f : Member p.headers.fns hdr) (hFind : p.find ⟨107⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dScalar, dScalar]) (hOut : hdr.outs = [.bool]),
      ∀ (a b : Nat),
        Defs.fnTable deployModel p.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm) (.cons a (.cons b .nil))) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm) (.cons (decide (a = b)) .nil)) := by
  rcases hP with rfl | rfl
  · have h107 : witnessTyped.find ⟨107⟩ = some (.fn (Member.tail Member.head)) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h107
    subst e; subst he; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  · have h107 : retryWitnessTyped.find ⟨107⟩ = some (.fn (Member.tail Member.head)) := rfl
    obtain ⟨e, he⟩ := member_unique_of_find hFind h107
    subst e; subst he; exact ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem wFnSamples_deploy_eval {fns : List (FnHeader deployVocab)}
    (fnTable : FnTable deployModel fns)
    (w y : Nat) (sess site : List Nat) (att seq : Nat) :
    wFnSamples.denote (localSem deployModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [dScalar, dPoint, dBytes, dBytes, .nat, .nat])
        (.cons w (.cons y (.cons sess (.cons site (.cons att (.cons seq .nil))))))) =
      .done (.cons ((mixBytes (mixBytes att sess) site + seq) % 11) .nil) := rfl

private theorem wfn109_deploy (hdr : FnHeader deployVocab)
    (f : Member witnessTyped.headers.fns hdr)
    (hFind : witnessTyped.find ⟨109⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dScalar, dPoint, dBytes, dBytes, .nat, .nat]) (hOut : hdr.outs = [dScalar]),
      ∀ (w y : Nat) (sess site : List Nat) (att seq : Nat),
        Defs.fnTable deployModel witnessTyped.defs hdr f
          (cast (congrArg (HList deployModel.Val) hIn.symm)
            (.cons w (.cons y (.cons sess (.cons site (.cons att (.cons seq .nil))))))) =
          .done (cast (congrArg (HList deployModel.Val) hOut.symm)
            (.cons ((mixBytes (mixBytes att sess) site + seq) % 11) .nil)) := by
  have h109 : witnessTyped.find ⟨109⟩ = some (.fn Member.head) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h109
  subst e; subst he
  exact ⟨rfl, rfl, fun w y sess site att seq => wFnSamples_deploy_eval _ w y sess site att seq⟩

-- `SuiteLawful` for any deployment over `witnessTyped` or `retryWitnessTyped` using `toySuite`
private theorem wFnDefs_suiteLawful_of {d : Deployed deployVocab} {tag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived toySuite tag)
    (hProg : d.admitted.program = witnessTyped ∨ d.admitted.program = retryWitnessTyped) :
    d.SuiteLawful deployModel := by
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hCon hProg
          intro suite sessionTag hCon'
          have hSEq : suite = toySuite := (Construction.derived.inj (hCon.symm.trans hCon')).1.symm
          subst hSEq
          constructor
          · intro defKey hMem hdr f hFind stateTy drawIns e law owner h0 hs _ _ hLaw hins houts
              st label payload coin st' _ _ _ hEval
            have hK : defKey = ⟨104⟩ := by
              rcases hMem with hMem | ⟨_, hLM⟩
              · simp only [toySuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
                rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
                · cases h
                · cases h
                · cases h
                · cases h
                · exact h
              · cases hLM
            subst hK
            obtain ⟨hIn, hOut, hEv⟩ := wfn104_deploy hProg hdr f hFind
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
            · obtain ⟨hIn0, hOut0, hEv⟩ := wfn102_deploy hProg hdr f hFind
              have hTau : τ = dScalar := List.cons.inj (hIn.symm.trans hIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hOut.symm.trans hOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v₁ v₂
              change List Nat at u
              have h1 := hEv v₁; have h2 := hEv v₂
              erw [h1] at hEv₁; erw [h2] at hEv₂
              have hd1 : ([v₁ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₁))
              have hd2 : ([v₂ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₂))
              have hMod : v₁ % 256 = v₂ % 256 := List.cons.inj (hd1.trans hd2.symm) |>.1
              have hv1Lt : v₁ < 11 := hv₁
              have hv2Lt : v₂ < 11 := hv₂
              exact (Nat.mod_eq_of_lt (Nat.lt_trans hv1Lt (by decide))).symm.trans
                (hMod.trans (Nat.mod_eq_of_lt (Nat.lt_trans hv2Lt (by decide))))
            · obtain ⟨hIn0, hOut0, hEv⟩ := wfn103_deploy hProg hdr f hFind
              have hTau : τ = dPoint := List.cons.inj (hIn.symm.trans hIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hOut.symm.trans hOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v₁ v₂
              change List Nat at u
              have h1 := hEv v₁; have h2 := hEv v₂
              erw [h1] at hEv₁; erw [h2] at hEv₂
              have hd1 : ([v₁ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₁))
              have hd2 : ([v₂ % 256] : List Nat) = u :=
                congrArg HList.single (cast_inj (Process.done.inj hEv₂))
              have hMod : v₁ % 256 = v₂ % 256 := List.cons.inj (hd1.trans hd2.symm) |>.1
              have hv1Lt : v₁ < 23 := hv₁
              have hv2Lt : v₂ < 23 := hv₂
              exact (Nat.mod_eq_of_lt (Nat.lt_trans hv1Lt (by decide))).symm.trans
                (hMod.trans (Nat.mod_eq_of_lt (Nat.lt_trans hv2Lt (by decide))))

-- `LayoutLawful` for any deployment over `witnessTyped` or `retryWitnessTyped` using `toyLayoutModule`
private theorem wFnDefs_layoutLawful_of {d : Deployed deployVocab} {lay : Layout}
    (hLayDecl : d.declaration.layout = some lay) (hMod : lay.module = toyLayoutModule)
    (hProg : d.admitted.program = witnessTyped ∨ d.admitted.program = retryWitnessTyped) :
    d.LayoutLawful deployModel := by
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hLayDecl hProg
          intro layout hLay
          have hLEq : layout = lay := Option.some.inj (hLay.symm.trans hLayDecl)
          subst hLEq
          refine ⟨?_, ?_, ?_⟩
          · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
              v chunk pre post hv _ _ hW
            rw [hMod] at hwMem hrMem
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
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn102_deploy hProg wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn105_deploy hProg rHdr fR hrFind
              have hTau : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v; change List Nat at chunk pre post
              have hW0 := hEvW v; erw [hW0] at hW
              have hCh : [v % 256] = chunk := congrArg HList.single (cast_inj (Process.done.inj hW))
              subst hCh
              have hR0 := hEvR (pre ++ [v % 256] ++ post) pre.length
              have hvLt : v < 11 := hv
              have hvMod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hlt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hElem : (pre ++ [v % 256] ++ post)[pre.length]'hlt = v := by
                simp [List.append_assoc, hvMod]
              erw [hR0]; rw [dite_eq_left hlt]; dsimp only; rw [hElem, ite_eq_left hvLt]
              have hvm : v % 11 = v := Nat.mod_eq_of_lt hvLt
              erw [hvm]; rfl
            · obtain ⟨hwIn0, _, _⟩ := wfn102_deploy hProg wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn106_deploy hProg rHdr fR hrFind
              have h1 : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dPoint := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, _, _⟩ := wfn103_deploy hProg wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn105_deploy hProg rHdr fR hrFind
              have h1 : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dScalar := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn103_deploy hProg wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn106_deploy hProg rHdr fR hrFind
              have hTau : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v; change List Nat at chunk pre post
              have hW0 := hEvW v; erw [hW0] at hW
              have hCh : [v % 256] = chunk := congrArg HList.single (cast_inj (Process.done.inj hW))
              subst hCh
              have hR0 := hEvR (pre ++ [v % 256] ++ post) pre.length
              have hvLt : v < 23 := hv
              have hvMod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hlt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hElem : (pre ++ [v % 256] ++ post)[pre.length]'hlt = v := by
                simp [List.append_assoc, hvMod]
              erw [hR0]; rw [dite_eq_left hlt]; dsimp only; rw [hElem, ite_eq_left hvLt]
              have hvm : v % 23 = v := Nat.mod_eq_of_lt hvLt
              erw [hvm]; rfl
          · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
              buf off v nextOff _ _ hR
            rw [hMod] at hwMem hrMem
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
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn102_deploy hProg wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn105_deploy hProg rHdr fR hrFind
              have hTau : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change List Nat at buf; change Nat at off v nextOff
              have hR0 := hEvR buf off; erw [hR0] at hR
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
                  erw [hW0]; simp only [hMod256]
                · simp only [hb, ↓reduceIte] at hR; cases hR
              · simp only [hlt, ↓reduceDIte] at hR; cases hR
            · obtain ⟨hwIn0, _, _⟩ := wfn102_deploy hProg wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn106_deploy hProg rHdr fR hrFind
              have h1 : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dPoint := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, _, _⟩ := wfn103_deploy hProg wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := wfn105_deploy hProg rHdr fR hrFind
              have h1 : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have h2 : τ = dScalar := List.cons.inj (hrOut.symm.trans hrOut0) |>.1
              have hContra := h1.symm.trans h2; cases hContra
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := wfn103_deploy hProg wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := wfn106_deploy hProg rHdr fR hrFind
              have hTau : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change List Nat at buf; change Nat at off v nextOff
              have hR0 := hEvR buf off; erw [hR0] at hR
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
                  erw [hW0]; simp only [hMod256]
                · simp only [hb, ↓reduceIte] at hR; cases hR
              · simp only [hlt, ↓reduceDIte] at hR; cases hR
          · intro eqKey hMem eqHdr fEq hFind τ hIn hOut v₁ v₂ b _ _ hEv
            rw [hMod] at hMem
            have hK : eqKey = ⟨107⟩ := by
              simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
              rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
              · cases h
              · cases h
              · cases h
              · cases h
              · exact h
            subst hK
            obtain ⟨hIn0, hOut0, hEv0⟩ := wfn107_deploy hProg eqHdr fEq hFind
            have hTau : τ = dScalar := List.cons.inj (hIn.symm.trans hIn0) |>.1
            subst hTau
            change Nat at v₁ v₂; change Bool at b
            have hEq := hEv0 v₁ v₂; erw [hEq] at hEv
            have hb : decide (v₁ = v₂) = b :=
              congrArg HList.single (cast_inj (Process.done.inj hEv))
            rw [← hb]; exact decide_eq_true_iff

private theorem witness_samplesLawful_of {d : Deployed deployVocab}
    (hDecl : d.declaration = schnorrSamplesDecl) (hProg : d.admitted.program = witnessTyped) :
    d.SamplesLawful deployModel := by
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDecl hProg
          subst hDecl; subst hProg
          intro sKey prover verifier hSamp hRoles hdr f hFind e law drawIns _ _ hLaw
            hins houts heldVals sessBytes siteBytes attemptNum callSeq payload coin _ _ _ _ hEval
          have hSK : sKey = ⟨109⟩ := (Option.some.inj hSamp).symm
          subst hSK
          have hPV : prover = 0 ∧ verifier = 1 := by
            have hR : proverAndVerifier wSchnorrHdr schnorrSamplesDecl = some (0, 1) := by decide +kernel
            exact Prod.mk.inj (Option.some.inj (hRoles.symm.trans hR))
          obtain ⟨rfl, rfl⟩ := hPV
          obtain ⟨hIn0, hOut0, hEv0⟩ := wfn109_deploy hdr f hFind
          cases e with
          | mk eSite eCls eTau =>
              dsimp only at hLaw houts hEval ⊢
              have hTau : eTau = dScalar := (List.cons.inj (hOut0.symm.trans houts)).1.symm
              subst hTau
              cases law
              have hDI : drawIns = [] := by
                have hSig := Option.some.inj hLaw
                cases hSig; rfl
              subst hDI
              cases payload
              cases heldVals with
              | cons w hRest =>
                  cases hRest with
                  | cons y hNil =>
                      cases hNil
                      change Nat at w y coin
                      change List Nat at sessBytes siteBytes
                      have hEv := hEv0 w y sessBytes siteBytes attemptNum callSeq
                      erw [hEv] at hEval
                      have hCoinEq :
                          (mixBytes (mixBytes attemptNum sessBytes) siteBytes + callSeq) % 11 = coin :=
                        congrArg HList.single (cast_inj (Process.done.inj hEval))
                      have hLt : coin < 11 := by
                        rw [← hCoinEq]; exact Nat.mod_lt _ (by decide)
                      exact ⟨hLt, ⟨[], dScalar⟩, rfl, rfl, rfl, hLt⟩

/-! ## Witness 1: Streaming completeness (`deploy_complete`) & ideal path step injectivity -/

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
  have hSL := wFnDefs_suiteLawful_of (by rw [hDeclEq]; rfl) (.inl hDProg)
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

private theorem witness_noHalt :
    ∀ source,
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
      change Nat at vR; change vR < 11 at hrLt
      have hLaw1 := (hLaw _ hSrcR).2
      cases hRun1 with
      | flow hRun2 =>
          cases hRun2 with
          | @given _ _ _ _ _ _ _ vC _ _ _ hSrcC hRun3 =>
              have hcLt : deployModel.Valid dScalar vC := (hLaw1 _ hSrcC).1.1
              change Nat at vC; change vC < 11 at hcLt
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

/-- Concrete non-vacuous instantiation of `deploy_complete` on an admitted & deployed Schnorr
scheme at `(w = 7, Y = 13)`. -/
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
  have hSL := wFnDefs_suiteLawful_of (by rw [hDeclEq]; rfl) (.inl hDProg)
  have hLL := wFnDefs_layoutLawful_of (by rw [hDeclEq]; rfl) rfl (.inl hDProg)
  cases d with
  | mk adm decl found stack _ident =>
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
          exact ⟨a, _, rfl, hFirst, hMatched, hAdm, hDep,
            deploy_complete deployModel deployEncoder hAdm hDep
              rfl rfl rfl hNoRec
              0 1 hRoles hFirst hMatched (.cons (7 : Nat) (.cons (13 : Nat) .nil)) hInsV
              (hSL.toFor deployEncoder deployModel) hLL witness_noHalt (fixedNonceSource 5) hLP hFed⟩

/-! ## Witness 2: Deterministic prover-sampling completeness (`deploy_complete_samples`) on empty world -/

private theorem witness_samples_lawful :
    LawfulSampled deployModel 0 (fun _ _ => none)
      (protocolMeaning deployModel witnessTyped Member.head []
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
  rw [witness_protocol_unfold]
  dsimp only [LawfulSampled, LawfulFor]
  rw [ite_eq_left ⟨rfl, rfl⟩]
  intro (r : Nat) _ (c : Nat) _
  cases decide (powMod 2 ((r + c * 7 % 11) % 11) 23 =
      (powMod 2 r 23 * powMod 13 c 23) % 23) <;> trivial

private theorem witness_samples_fed :
    FedSampled deployModel 0 (fun _ _ => none)
      (protocolMeaning deployModel witnessTyped Member.head []
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
  rw [witness_protocol_unfold]
  dsimp only [FedSampled, FedFor]
  rw [ite_eq_left ⟨rfl, rfl⟩]
  intro (r : Nat) _ (c : Nat) _
  cases decide (powMod 2 ((r + c * 7 % 11) % 11) 23 =
      (powMod 2 r 23 * powMod 13 c 23) % 23) <;> trivial

seal Zkc.Core.protocolMeaning in
/-- Concrete non-vacuous instantiation of `deploy_complete_samples` on `schnorrSamplesDecl` with the
completely empty randomness source `fun _ _ => none` (proving deterministic proving requires zero
external private randomness). -/
theorem witness_deploy_complete_samples :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab)
      (hIns : d.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      deploy deployEncoder a schnorrSamplesDecl = .ok d ∧
      let ins := cast (congrArg (HList (LVal deployModel)) hIns.symm)
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone deployModel (fun _ _ => none) 0
          (d.run deployModel 0 (hideAll deployModel 0 ins)
            (cast (congrArg (HList deployModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone deployModel (fun _ _ => none) 1
          (d.run deployModel 1 (hideAll deployModel 1 ins)
            (cast (congrArg (HList deployModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins) ∧
          (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins ++ d.entry.shape.proverPrivateCoins 0 →
            source' at_ τ = none) ∧
          GExec deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins)
            (.returned out) ∧
          outP = hideAll deployModel 0 out.1 ∧ outV = hideAll deployModel 1 out.1 := by
  obtain ⟨a, d, hAdm, hProg, hDep⟩ := witness_deploySamples_exists
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps deployEncoder a schnorrSamplesDecl d hDep
  have hDProg : d.admitted.program = witnessTyped := by rw [hAdmEq, hProg]
  have hSL := wFnDefs_suiteLawful_of (by rw [hDeclEq]; rfl) (.inl hDProg)
  have hLL := wFnDefs_layoutLawful_of (by rw [hDeclEq]; rfl) rfl (.inl hDProg)
  have hSampL := witness_samplesLawful_of hDeclEq hDProg
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier wSchnorrHdr schnorrSamplesDecl = some (0, 1) := by
            decide +kernel
          obtain ⟨hFirst, hMatched⟩ :=
            deploy_matches deployEncoder a schnorrSamplesDecl _ hDep 0 1 hRoles
          have hInsV : (HList.cons (7 : Nat) (.cons (13 : Nat) .nil) :
              HList (LVal deployModel) wSchnorrHdr.ins).All (fun a v => deployModel.Valid a.ty v) :=
            ⟨show (7 : Nat) < 11 by decide, show (13 : Nat) < 23 by decide, trivial⟩
          have hNoRec : ∀ l, schnorrSamplesDecl.layout = some l → l.recover = [] := fun _ h => by
            cases Option.some.inj h; rfl
          exact ⟨a, _, rfl, hFirst, hMatched, hAdm, hDep,
            deploy_complete_samples deployModel deployEncoder hAdm hDep
              rfl rfl hNoRec
              0 1 hRoles hFirst hMatched (.cons (7 : Nat) (.cons (13 : Nat) .nil)) hInsV
              (hSL.toFor deployEncoder deployModel) hLL (hSampL.toFor deployEncoder deployModel)
              witness_noHalt (fun _ _ => none) witness_samples_lawful witness_samples_fed⟩

/-! ## Witness 3: Compact carry/recover completeness (`deploy_complete_compact`) on `primeOrderModel` -/

private theorem cwfn102_prime (hdr : FnHeader deployVocab)
    (f : Member compactWitnessTyped.headers.fns hdr)
    (hFind : compactWitnessTyped.find ⟨102⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dScalar]) (hOut : hdr.outs = [dBytes]),
      ∀ (v : Nat),
        Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
          (cast (congrArg (HList primeOrderModel.Val) hIn.symm) (.cons v .nil)) =
          .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm) (.cons [v % 256] .nil)) := by
  have h102 : compactWitnessTyped.find ⟨102⟩ =
      some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h102
  subst e; subst he
  exact ⟨rfl, rfl, fun _ => rfl⟩

private theorem cwfn103_prime (hdr : FnHeader deployVocab)
    (f : Member compactWitnessTyped.headers.fns hdr)
    (hFind : compactWitnessTyped.find ⟨103⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dPoint]) (hOut : hdr.outs = [dBytes]),
      ∀ (v : Nat),
        Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
          (cast (congrArg (HList primeOrderModel.Val) hIn.symm) (.cons v .nil)) =
          .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm) (.cons [v % 256] .nil)) := by
  have h103 : compactWitnessTyped.find ⟨103⟩ =
      some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head)))))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h103
  subst e; subst he
  exact ⟨rfl, rfl, fun _ => rfl⟩

private theorem cwfn104_prime (hdr : FnHeader deployVocab)
    (f : Member compactWitnessTyped.headers.fns hdr)
    (hFind : compactWitnessTyped.find ⟨104⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [.nat, dBytes]) (hOut : hdr.outs = [dScalar, .nat]),
      ∀ (st : Nat) (lbl : List Nat),
        Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
          (cast (congrArg (HList primeOrderModel.Val) hIn.symm) (.cons st (.cons lbl .nil))) =
          .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm)
            (.cons (mixBytes st (0xFF :: lbl) % 11) (.cons (mixBytes st (0xFF :: lbl)) .nil))) := by
  have h104 : compactWitnessTyped.find ⟨104⟩ =
      some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h104
  subst e; subst he
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem wFnReadScalar_prime_eval {fns : List (FnHeader deployVocab)}
    (fnTable : FnTable primeOrderModel fns) (buf : List Nat) (off : Nat) :
    wFnReadScalar.denote (localSem primeOrderModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [dBytes, .nat]) (.cons buf (.cons off .nil))) =
      if hlt : off < buf.length then
        let b := buf[off]'hlt
        if b < 11 then
          .done (.cons (b % 11) (.cons (off + 1) .nil))
        else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  dsimp only [wFnReadScalar]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .nat) buf.length HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .bool) (Nat.blt off buf.length) HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_guard]
  by_cases hlt : off < buf.length
  · rw [dite_eq_left hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = true := Nat.blt_eq.mpr hlt
    rw [hltB]; dsimp only [cond]
    erw [Term.denote_op]
    change (ownedOp primeOrderModel (.seqAt dByte none rfl) (.cons buf (.cons off .nil))).bind _ = _
    rw [ownedOp_seqAt_some primeOrderModel dByte rfl buf off hlt]; dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .nat) (buf[off]'hlt) HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .nat) 11 HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .bool) (Nat.blt (buf[off]'hlt) 11) HList.nil)).bind _ = _
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

private theorem cwfn105_prime (hdr : FnHeader deployVocab)
    (f : Member compactWitnessTyped.headers.fns hdr)
    (hFind : compactWitnessTyped.find ⟨105⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dBytes, .nat]) (hOut : hdr.outs = [dScalar, .nat]),
      ∀ (buf : List Nat) (off : Nat),
        Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
          (cast (congrArg (HList primeOrderModel.Val) hIn.symm) (.cons buf (.cons off .nil))) =
          if hlt : off < buf.length then
            let b := buf[off]'hlt
            if b < 11 then
              .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm)
                (.cons (b % 11) (.cons (off + 1) .nil)))
            else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
          else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  have h105 : compactWitnessTyped.find ⟨105⟩ =
      some (.fn (Member.tail (Member.tail (Member.tail Member.head)))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h105
  subst e; subst he
  exact ⟨rfl, rfl, fun buf off => wFnReadScalar_prime_eval _ buf off⟩

private theorem wFnReadPoint11_prime_eval {fns : List (FnHeader deployVocab)}
    (fnTable : FnTable primeOrderModel fns) (buf : List Nat) (off : Nat) :
    wFnReadPoint11.denote (localSem primeOrderModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [dBytes, .nat]) (.cons buf (.cons off .nil))) =
      if hlt : off < buf.length then
        let b := buf[off]'hlt
        if b < 11 then
          .done (.cons (b % 11) (.cons (off + 1) .nil))
        else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  dsimp only [wFnReadPoint11]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .nat) buf.length HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_op]
  change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .bool) (Nat.blt off buf.length) HList.nil)).bind _ = _
  dsimp only [Process.bind]
  erw [Term.denote_guard]
  by_cases hlt : off < buf.length
  · rw [dite_eq_left hlt]
    change (bif Nat.blt off buf.length then _ else _) = _
    have hltB : Nat.blt off buf.length = true := Nat.blt_eq.mpr hlt
    rw [hltB]; dsimp only [cond]
    erw [Term.denote_op]
    change (ownedOp primeOrderModel (.seqAt dByte none rfl) (.cons buf (.cons off .nil))).bind _ = _
    rw [ownedOp_seqAt_some primeOrderModel dByte rfl buf off hlt]; dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .nat) (buf[off]'hlt) HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .nat) 11 HList.nil)).bind _ = _
    dsimp only [Process.bind]
    erw [Term.denote_op]
    change (Process.done (HList.cons (V := primeOrderModel.Val) (a := .bool) (Nat.blt (buf[off]'hlt) 11) HList.nil)).bind _ = _
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

private theorem cwfn106_prime (hdr : FnHeader deployVocab)
    (f : Member compactWitnessTyped.headers.fns hdr)
    (hFind : compactWitnessTyped.find ⟨106⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dBytes, .nat]) (hOut : hdr.outs = [dPoint, .nat]),
      ∀ (buf : List Nat) (off : Nat),
        Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
          (cast (congrArg (HList primeOrderModel.Val) hIn.symm) (.cons buf (.cons off .nil))) =
          if hlt : off < buf.length then
            let b := buf[off]'hlt
            if b < 11 then
              .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm)
                (.cons (b % 11) (.cons (off + 1) .nil)))
            else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
          else .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  have h106 : compactWitnessTyped.find ⟨106⟩ = some (.fn (Member.tail (Member.tail Member.head))) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h106
  subst e; subst he
  exact ⟨rfl, rfl, fun buf off => wFnReadPoint11_prime_eval _ buf off⟩

private theorem cwfn107_prime (hdr : FnHeader deployVocab)
    (f : Member compactWitnessTyped.headers.fns hdr)
    (hFind : compactWitnessTyped.find ⟨107⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dScalar, dScalar]) (hOut : hdr.outs = [.bool]),
      ∀ (a b : Nat),
        Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
          (cast (congrArg (HList primeOrderModel.Val) hIn.symm) (.cons a (.cons b .nil))) =
          .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm) (.cons (decide (a = b)) .nil)) := by
  have h107 : compactWitnessTyped.find ⟨107⟩ = some (.fn (Member.tail Member.head)) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h107
  subst e; subst he
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem wFnRecover_prime_eval {fns : List (FnHeader deployVocab)}
    (fnTable : FnTable primeOrderModel fns) (y c z : Nat) :
    wFnRecoverCommit.denote (localSem primeOrderModel fns fnTable) []
      (Env.empty.extend (Names.counting 0 [dPoint, dScalar, dScalar]) (.cons y (.cons c (.cons z .nil)))) =
      .done (.cons ((z % 11 + ((11 - c % 11) % 11 * y) % 11) % 11) .nil) := rfl

private theorem cwfn108_prime (hdr : FnHeader deployVocab)
    (f : Member compactWitnessTyped.headers.fns hdr)
    (hFind : compactWitnessTyped.find ⟨108⟩ = some (.fn f)) :
    ∃ (hIn : hdr.ins = [dPoint, dScalar, dScalar]) (hOut : hdr.outs = [dPoint]),
      ∀ (y c z : Nat),
        Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
          (cast (congrArg (HList primeOrderModel.Val) hIn.symm) (.cons y (.cons c (.cons z .nil)))) =
          .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm)
            (.cons ((z % 11 + ((11 - c % 11) % 11 * y) % 11) % 11) .nil)) := by
  have h108 : compactWitnessTyped.find ⟨108⟩ = some (.fn Member.head) := rfl
  obtain ⟨e, he⟩ := member_unique_of_find hFind h108
  subst e; subst he
  exact ⟨rfl, rfl, fun y c z => wFnRecover_prime_eval _ y c z⟩

private theorem compact_suiteLawful_of {d : Deployed deployVocab}
    (hDecl : d.declaration = schnorrCompactDecl) (hProg : d.admitted.program = compactWitnessTyped) :
    d.SuiteLawful primeOrderModel := by
  cases d with
  | mk adm decl found stack _ident =>
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
              rcases hMem with hMem | ⟨_, hLM⟩
              · simp only [toySuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
                rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
                · cases h
                · cases h
                · cases h
                · cases h
                · exact h
              · cases hLM
            subst hK
            obtain ⟨hIn, hOut, hEv⟩ := cwfn104_prime hdr f hFind
            have hST : stateTy = .nat ∧ drawIns = [] := by
              have hc := hIn.symm.trans hins
              injection hc with h1 h2
              injection h2 with _ h3
              exact ⟨h1.symm, h3.symm⟩
            obtain ⟨rfl, rfl⟩ := hST
            cases e with
            | mk eSite eCls eTau =>
                dsimp only at hLaw houts hEval ⊢
                have hTau : eTau = dScalar := (List.cons.inj (hOut.symm.trans houts)).1.symm
                subst hTau
                cases payload; cases law
                change Nat at st coin st'; change List Nat at label
                have hEv' := hEv st label; erw [hEv'] at hEval
                have hCoinEq : mixBytes st (0xFF :: label) % 11 = coin := by
                  have hc2 : (.cons (mixBytes st (0xFF :: label) % 11) (.cons (mixBytes st (0xFF :: label)) .nil) :
                      HList primeOrderModel.Val [dScalar, .nat]) = .cons coin (.cons st' .nil) :=
                    cast_inj (Process.done.inj hEval)
                  cases hc2; rfl
                have hCoinLt : coin < 11 := by rw [← hCoinEq]; exact Nat.mod_lt _ (by decide)
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
            · obtain ⟨hIn0, hOut0, hEv⟩ := cwfn102_prime hdr f hFind
              have hTau : τ = dScalar := List.cons.inj (hIn.symm.trans hIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hOut.symm.trans hOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v₁ v₂; change List Nat at u
              erw [hEv v₁] at hEv₁; erw [hEv v₂] at hEv₂
              have hd1 : ([v₁ % 256] : List Nat) = u := congrArg HList.single (cast_inj (Process.done.inj hEv₁))
              have hd2 : ([v₂ % 256] : List Nat) = u := congrArg HList.single (cast_inj (Process.done.inj hEv₂))
              have hMod : v₁ % 256 = v₂ % 256 := List.cons.inj (hd1.trans hd2.symm) |>.1
              have hv1Lt : v₁ < 11 := hv₁; have hv2Lt : v₂ < 11 := hv₂
              exact (Nat.mod_eq_of_lt (Nat.lt_trans hv1Lt (by decide))).symm.trans
                (hMod.trans (Nat.mod_eq_of_lt (Nat.lt_trans hv2Lt (by decide))))
            · obtain ⟨hIn0, hOut0, hEv⟩ := cwfn103_prime hdr f hFind
              have hTau : τ = dPoint := List.cons.inj (hIn.symm.trans hIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hOut.symm.trans hOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v₁ v₂; change List Nat at u
              erw [hEv v₁] at hEv₁; erw [hEv v₂] at hEv₂
              have hd1 : ([v₁ % 256] : List Nat) = u := congrArg HList.single (cast_inj (Process.done.inj hEv₁))
              have hd2 : ([v₂ % 256] : List Nat) = u := congrArg HList.single (cast_inj (Process.done.inj hEv₂))
              have hMod : v₁ % 256 = v₂ % 256 := List.cons.inj (hd1.trans hd2.symm) |>.1
              have hv1Lt : v₁ < 11 := hv₁; have hv2Lt : v₂ < 11 := hv₂
              exact (Nat.mod_eq_of_lt (Nat.lt_trans hv1Lt (by decide))).symm.trans
                (hMod.trans (Nat.mod_eq_of_lt (Nat.lt_trans hv2Lt (by decide))))

private theorem compact_layoutLawful_of {d : Deployed deployVocab}
    (hDecl : d.declaration = schnorrCompactDecl) (hProg : d.admitted.program = compactWitnessTyped) :
    d.LayoutLawful primeOrderModel := by
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDecl hProg
          subst hDecl; subst hProg
          intro layout hLay
          have hLEq : layout = ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩], [(⟨[], ⟨12⟩⟩, ⟨108⟩)]⟩ :=
            Option.some.inj hLay.symm
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
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := cwfn102_prime wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := cwfn105_prime rHdr fR hrFind
              have hTau : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v; change List Nat at chunk pre post
              erw [hEvW v] at hW
              have hCh : [v % 256] = chunk := congrArg HList.single (cast_inj (Process.done.inj hW))
              subst hCh
              have hvLt : v < 11 := hv
              have hvMod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hlt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hElem : (pre ++ [v % 256] ++ post)[pre.length]'hlt = v := by
                simp [List.append_assoc, hvMod]
              erw [hEvR (pre ++ [v % 256] ++ post) pre.length]
              rw [dite_eq_left hlt]; dsimp only; rw [hElem, ite_eq_left hvLt]
              have hvm : v % 11 = v := Nat.mod_eq_of_lt hvLt
              erw [hvm]; rfl
            · obtain ⟨hwIn0, _, _⟩ := cwfn102_prime wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := cwfn106_prime rHdr fR hrFind
              have hContra := (List.cons.inj (hwIn.symm.trans hwIn0)).1.symm.trans
                (List.cons.inj (hrOut.symm.trans hrOut0)).1
              cases hContra
            · obtain ⟨hwIn0, _, _⟩ := cwfn103_prime wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := cwfn105_prime rHdr fR hrFind
              have hContra := (List.cons.inj (hwIn.symm.trans hwIn0)).1.symm.trans
                (List.cons.inj (hrOut.symm.trans hrOut0)).1
              cases hContra
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := cwfn103_prime wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := cwfn106_prime rHdr fR hrFind
              have hTau : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change Nat at v; change List Nat at chunk pre post
              erw [hEvW v] at hW
              have hCh : [v % 256] = chunk := congrArg HList.single (cast_inj (Process.done.inj hW))
              subst hCh
              have hvLt : v < 11 := hv
              have hvMod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
              have hlt : pre.length < (pre ++ [v % 256] ++ post).length := by simp
              have hElem : (pre ++ [v % 256] ++ post)[pre.length]'hlt = v := by
                simp [List.append_assoc, hvMod]
              erw [hEvR (pre ++ [v % 256] ++ post) pre.length]
              rw [dite_eq_left hlt]; dsimp only; rw [hElem, ite_eq_left hvLt]
              have hvm : v % 11 = v := Nat.mod_eq_of_lt hvLt
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
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := cwfn102_prime wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := cwfn105_prime rHdr fR hrFind
              have hTau : τ = dScalar := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change List Nat at buf; change Nat at off v nextOff
              erw [hEvR buf off] at hR
              by_cases hlt : off < buf.length
              · simp only [hlt, ↓reduceDIte] at hR
                by_cases hb : buf[off]'hlt < 11
                · simp only [hb, ↓reduceIte] at hR
                  have hPair : (HList.cons (buf[off]'hlt % 11) (.cons (off + 1) .nil) :
                      HList primeOrderModel.Val [dScalar, .nat]) = .cons v (.cons nextOff .nil) :=
                    cast_inj (Process.done.inj hR)
                  have hvEq : buf[off]'hlt % 11 = v := by cases hPair; rfl
                  have hNextEq : off + 1 = nextOff := by cases hPair; rfl
                  subst hvEq; subst hNextEq
                  have hbMod : buf[off]'hlt % 11 = buf[off]'hlt := Nat.mod_eq_of_lt hb
                  refine ⟨by rw [hbMod]; exact hb, Nat.le_succ off, hlt, [buf[off]'hlt], ?_,
                    list_take_elem_drop buf off hlt⟩
                  have hMod256 : (buf[off]'hlt % 11) % 256 = buf[off]'hlt := by omega
                  erw [hEvW (buf[off]'hlt % 11)]; simp only [hMod256]
                · simp only [hb, ↓reduceIte] at hR; cases hR
              · simp only [hlt, ↓reduceDIte] at hR; cases hR
            · obtain ⟨hwIn0, _, _⟩ := cwfn102_prime wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := cwfn106_prime rHdr fR hrFind
              have hContra := (List.cons.inj (hwIn.symm.trans hwIn0)).1.symm.trans
                (List.cons.inj (hrOut.symm.trans hrOut0)).1
              cases hContra
            · obtain ⟨hwIn0, _, _⟩ := cwfn103_prime wHdr fW hwFind
              obtain ⟨_, hrOut0, _⟩ := cwfn105_prime rHdr fR hrFind
              have hContra := (List.cons.inj (hwIn.symm.trans hwIn0)).1.symm.trans
                (List.cons.inj (hrOut.symm.trans hrOut0)).1
              cases hContra
            · obtain ⟨hwIn0, hwOut0, hEvW⟩ := cwfn103_prime wHdr fW hwFind
              obtain ⟨hrIn0, hrOut0, hEvR⟩ := cwfn106_prime rHdr fR hrFind
              have hTau : τ = dPoint := List.cons.inj (hwIn.symm.trans hwIn0) |>.1
              have hU : unitTy = dByte := by
                have hc := List.cons.inj (hwOut.symm.trans hwOut0) |>.1; injection hc
              subst hTau; subst hU
              change List Nat at buf; change Nat at off v nextOff
              erw [hEvR buf off] at hR
              by_cases hlt : off < buf.length
              · simp only [hlt, ↓reduceDIte] at hR
                by_cases hb : buf[off]'hlt < 11
                · simp only [hb, ↓reduceIte] at hR
                  have hPair : (HList.cons (buf[off]'hlt % 11) (.cons (off + 1) .nil) :
                      HList primeOrderModel.Val [dPoint, .nat]) = .cons v (.cons nextOff .nil) :=
                    cast_inj (Process.done.inj hR)
                  have hvEq : buf[off]'hlt % 11 = v := by cases hPair; rfl
                  have hNextEq : off + 1 = nextOff := by cases hPair; rfl
                  subst hvEq; subst hNextEq
                  have hbMod : buf[off]'hlt % 11 = buf[off]'hlt := Nat.mod_eq_of_lt hb
                  refine ⟨by rw [hbMod]; exact hb, Nat.le_succ off, hlt, [buf[off]'hlt], ?_,
                    list_take_elem_drop buf off hlt⟩
                  have hMod256 : (buf[off]'hlt % 11) % 256 = buf[off]'hlt := by omega
                  erw [hEvW (buf[off]'hlt % 11)]; simp only [hMod256]
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
            obtain ⟨hIn0, hOut0, hEv0⟩ := cwfn107_prime eqHdr fEq hFind
            have hTau : τ = dScalar := List.cons.inj (hIn.symm.trans hIn0) |>.1
            subst hTau
            change Nat at v₁ v₂; change Bool at b
            erw [hEv0 v₁ v₂] at hEv
            have hb : decide (v₁ = v₂) = b :=
              congrArg HList.single (cast_inj (Process.done.inj hEv))
            rw [← hb]; exact decide_eq_true_iff

private theorem compact_protocol_unfold (w y : Nat) :
    protocolMeaning primeOrderModel compactWitnessTyped Member.head []
      (.cons w (.cons y .nil)) =
      Process.call (GOp.given (.coin ()) 0 [] ⟨[], ⟨10⟩⟩ [] .nil dScalar) fun (r : Nat) =>
        Process.call (GOp.flow .message 0 [1] ⟨[], ⟨12⟩⟩ dPoint (r % 11)) fun _ =>
          Process.call (GOp.given (.coin ()) 1 [0] ⟨[], ⟨13⟩⟩ [] .nil dScalar) fun (c : Nat) =>
            Process.call (GOp.flow .message 0 [1] ⟨[], ⟨16⟩⟩ dScalar ((r + (c * w) % 11) % 11))
              fun _ =>
                ((((bif decide (((r + (c * w) % 11) % 11) % 11 =
                    (r % 11 + (c * y) % 11) % 11) then
                  (Process.done (HList.nil, ()) :
                    Protocol primeOrderModel (HList (LVal primeOrderModel) [] × Unit))
                else
                  Process.halt ([1], Stop.declared .reject ⟨[], ⟨21⟩⟩)).map
                  fun out => (out.1, (((r + (c * w) % 11) % 11), out.2))).map
                  fun out => (out.1, (c, out.2))).map
                  fun out => (out.1, (r % 11, out.2))).map
                  fun out => (out.1, out.2) := rfl

private theorem primeOrder_recover_identity (a y c : Nat) (ha : a < 11) (hy : y < 11) (hc : c < 11) :
    ((a + (c * y) % 11) % 11 + ((11 - c % 11) % 11 * y) % 11) % 11 = a := by
  have hAll : ∀ a' y' c' : Fin 11,
      ((a'.1 + (c'.1 * y'.1) % 11) % 11 + ((11 - c'.1 % 11) % 11 * y'.1) % 11) % 11 = a'.1 := by
    decide +kernel
  exact hAll ⟨a, ha⟩ ⟨y, hy⟩ ⟨c, hc⟩

private theorem compact_recoveryLawful_of {d : Deployed deployVocab}
    (hDecl : d.declaration = schnorrCompactDecl) (hProg : d.admitted.program = compactWitnessTyped) :
    d.RecoveryLawful primeOrderModel := by
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDecl hProg
          subst hDecl; subst hProg
          intro layout prover verifier hLay hRoles ins hIns source evs out hLaw hRun
            args kind getters at_ τ x recKey hEvIn hVin hLk hdr f hFind hIn hOut
          have hLEq : layout = ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩], [(⟨[], ⟨12⟩⟩, ⟨108⟩)]⟩ :=
            Option.some.inj hLay.symm
          subst hLEq
          have hPV : prover = 0 ∧ verifier = 1 := by
            have hR : proverAndVerifier wCompactSchnorrHdr schnorrCompactDecl = some (0, 1) := by
              decide +kernel
            exact Prod.mk.inj (Option.some.inj (hRoles.symm.trans hR))
          obtain ⟨rfl, rfl⟩ := hPV
          cases ins with
          | cons w ins1 =>
              cases ins1 with
              | cons y ins2 =>
                  cases ins2
                  change Nat at w y
                  have hwLt : w < 11 := hIns.1
                  have hyLt : y < 11 := hIns.2.1
                  change Lawful primeOrderModel source
                    (protocolMeaning primeOrderModel compactWitnessTyped Member.head []
                      (.cons w (.cons y .nil))) at hLaw
                  change GRun primeOrderModel source
                    (protocolMeaning primeOrderModel compactWitnessTyped Member.head []
                      (.cons w (.cons y .nil))) evs (.returned out) at hRun
                  rw [compact_protocol_unfold w y] at hLaw hRun
                  cases hRun with
                  | @given _ _ _ _ _ _ _ r _ _ _ hSrcR hRun1 =>
                      have hrLt : primeOrderModel.Valid dScalar r := (hLaw _ hSrcR).1.1
                      change Nat at r; change r < 11 at hrLt
                      have hLaw1 := (hLaw _ hSrcR).2
                      cases hRun1 with
                      | flow hRun2 =>
                          cases hRun2 with
                          | @given _ _ _ _ _ _ _ c _ _ _ hSrcC hRun3 =>
                              have hcLt : primeOrderModel.Valid dScalar c := (hLaw1 _ hSrcC).1.1
                              change Nat at c; change c < 11 at hcLt
                              cases hRun3 with
                              | flow hRun4 =>
                                  dsimp only at hRun4
                                  cases hDec : decide (((r + (c * w) % 11) % 11) % 11 =
                                      (r % 11 + (c * y) % 11) % 11) with
                                  | false =>
                                      erw [hDec] at hRun4; cases hRun4
                                  | true =>
                                      have hGuard : ((r + (c * w) % 11) % 11) % 11 =
                                          (r % 11 + (c * y) % 11) % 11 := of_decide_eq_true hDec
                                      erw [hDec] at hRun4
                                      cases hRun4
                                      -- `evs` has exactly the 4 events in run order; only `⟨[], ⟨12⟩⟩` is in `recover`
                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hEvIn
                                      rcases hEvIn with hE | hE | hE | hE
                                      · cases hE
                                      · cases hE
                                        have hRecK : recKey = ⟨108⟩ := (Option.some.inj hLk).symm
                                        subst hRecK
                                        obtain ⟨hIn0, hOut0, hEv0⟩ := cwfn108_prime hdr f hFind
                                        have hEv := hEv0 y c ((r + (c * w) % 11) % 11)
                                        have hId := primeOrder_recover_identity (r % 11) y c
                                          (Nat.mod_lt r (by decide)) hyLt hcLt
                                        change Defs.fnTable primeOrderModel compactWitnessTyped.defs hdr f
                                            (cast (congrArg (HList primeOrderModel.Val) hIn.symm)
                                              (.cons y (.cons c (.cons ((r + (c * w) % 11) % 11) .nil)))) =
                                            .done (cast (congrArg (HList primeOrderModel.Val) hOut.symm)
                                              (.cons (r % 11) .nil))
                                        erw [hEv]
                                        rw [hGuard]
                                        erw [hId]
                                        rfl
                                      · cases hE
                                      · cases hE
                                        cases hLk

private def primeFixedNonceSource (nonce : Nat) : Source primeOrderModel := fun _ τ =>
  match τ with
  | .nominal .scalar => some (nonce % 11)
  | _ => none

/-- Concrete non-vacuous instantiation of `deploy_complete_compact` on `primeOrderModel` (`G = ℤ_11`)
with `schnorrCompactDecl` (`carry = [c]`, `recover = [(A, fnRecoverCommit)]`), discharging
`SuiteLawfulFor`, `LayoutLawful`, and `RecoveryLawful` across all valid inputs. -/
theorem witness_deploy_complete_compact :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab)
      (hIns : d.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      admit (erase compactWitnessTyped) noAssociation = .ok a ∧
      deploy deployEncoder a schnorrCompactDecl = .ok d ∧
      let ins := cast (congrArg (HList (LVal primeOrderModel)) hIns.symm)
        (.cons (7 : Nat) (.cons (7 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone primeOrderModel (primeFixedNonceSource 5) 0
          (d.run primeOrderModel 0 (hideAll primeOrderModel 0 ins)
            (cast (congrArg (HList primeOrderModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone primeOrderModel (primeFixedNonceSource 5) 1
          (d.run primeOrderModel 1 (hideAll primeOrderModel 1 ins)
            (cast (congrArg (HList primeOrderModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful primeOrderModel source'
            (protocolMeaning primeOrderModel d.admitted.program d.callee [] ins) ∧
          (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins →
            source' at_ τ = primeFixedNonceSource 5 at_ τ) ∧
          GExec primeOrderModel source'
            (protocolMeaning primeOrderModel d.admitted.program d.callee [] ins)
            (.returned out) ∧
          outP = hideAll primeOrderModel 0 out.1 ∧ outV = hideAll primeOrderModel 1 out.1 := by
  obtain ⟨a, d, hAdm, hProg, hDep⟩ := compactWitness_deploy_exists
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps deployEncoder a schnorrCompactDecl d hDep
  have hDProg : d.admitted.program = compactWitnessTyped := by rw [hAdmEq, hProg]
  have hSL := compact_suiteLawful_of hDeclEq hDProg
  have hLL := compact_layoutLawful_of hDeclEq hDProg
  have hRL := compact_recoveryLawful_of hDeclEq hDProg
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier wCompactSchnorrHdr schnorrCompactDecl = some (0, 1) := by
            decide +kernel
          obtain ⟨hFirst, hMatched⟩ :=
            deploy_matches deployEncoder a schnorrCompactDecl _ hDep 0 1 hRoles
          have hInsV : (HList.cons (7 : Nat) (.cons (7 : Nat) .nil) :
              HList (LVal primeOrderModel) wCompactSchnorrHdr.ins).All
              (fun a v => primeOrderModel.Valid a.ty v) :=
            ⟨show (7 : Nat) < 11 by decide, show (7 : Nat) < 11 by decide, trivial⟩
          have hNoHalt : ∀ source,
              Lawful primeOrderModel source
                (protocolMeaning primeOrderModel compactWitnessTyped Member.head []
                  (.cons (7 : Nat) (.cons (7 : Nat) .nil))) →
              ∀ e,
                GExec primeOrderModel source
                  (protocolMeaning primeOrderModel compactWitnessTyped Member.head []
                    (.cons (7 : Nat) (.cons (7 : Nat) .nil))) e →
                ∃ out, e = .returned out := by
            intro source hLaw e ⟨_, hRun⟩
            rw [compact_protocol_unfold 7 7] at hLaw hRun
            cases hRun with
            | @given _ _ _ _ _ _ _ vR _ _ _ hSrcR hRun1 =>
                have hrLt : primeOrderModel.Valid dScalar vR := (hLaw _ hSrcR).1.1
                change Nat at vR; change vR < 11 at hrLt
                have hLaw1 := (hLaw _ hSrcR).2
                cases hRun1 with
                | flow hRun2 =>
                    cases hRun2 with
                    | @given _ _ _ _ _ _ _ vC _ _ _ hSrcC hRun3 =>
                        have hcLt : primeOrderModel.Valid dScalar vC := (hLaw1 _ hSrcC).1.1
                        change Nat at vC; change vC < 11 at hcLt
                        cases hRun3 with
                        | flow hRun4 =>
                            dsimp only at hRun4
                            have hEq : ((vR + (vC * 7) % 11) % 11) % 11 =
                                (vR % 11 + (vC * 7) % 11) % 11 := by omega
                            have hDec : decide (((vR + (vC * 7) % 11) % 11) % 11 =
                                (vR % 11 + (vC * 7) % 11) % 11) = true := decide_eq_true hEq
                            erw [hDec] at hRun4
                            cases hRun4
                            exact ⟨_, rfl⟩
          have hLP : LawfulPrivate primeOrderModel (primeFixedNonceSource 5)
              (protocolMeaning primeOrderModel compactWitnessTyped Member.head []
                (.cons (7 : Nat) (.cons (7 : Nat) .nil))) := by
            rw [compact_protocol_unfold 7 7]
            intro v hv
            cases Option.some.inj hv
            refine ⟨⟨show (5 % 11 : Nat) < 11 by decide,
              ⟨[], dScalar⟩, rfl, rfl, rfl, show (5 % 11 : Nat) < 11 by decide⟩, ?_⟩
            intro (c : Nat) _
            dsimp only [LawfulPrivate]
            cases decide (((5 % 11 + (c * 7) % 11) % 11) % 11 =
                ((5 % 11) % 11 + (c * 7) % 11) % 11) <;> trivial
          have hFed : Fed primeOrderModel (primeFixedNonceSource 5)
              (protocolMeaning primeOrderModel compactWitnessTyped Member.head []
                (.cons (7 : Nat) (.cons (7 : Nat) .nil))) := by
            rw [compact_protocol_unfold 7 7]
            refine ⟨(5 : Nat), rfl, fun (c : Nat) _ => ?_⟩
            dsimp only [Fed]
            cases decide (((5 + (c * 7) % 11) % 11) % 11 =
                (5 % 11 + (c * 7) % 11) % 11) <;> trivial
          refine ⟨a, _, rfl, hFirst, hMatched, hAdm, hDep, ?_⟩
          exact deploy_complete_compact primeOrderModel deployEncoder hAdm hDep
            rfl rfl rfl rfl rfl
            0 1 hRoles hFirst hMatched (.cons (7 : Nat) (.cons (7 : Nat) .nil)) hInsV
            (hSL.toFor deployEncoder primeOrderModel) hLL hRL hNoHalt
            (primeFixedNonceSource 5) hLP hFed

/-! ## Witness 4: Abort-and-retry completeness (`deploy_complete_retry`) at `k = 1` -/

/-- Randomness source returning `0` on attempt `0` (triggering real prover abort after emitting
commitment `A` and mutating transcript & proof buffer) and `5` on attempt `1` (succeeding cleanly
after rollback via `restoreAgain`). -/
private def retryAbortThenSucceedSource : Source deployModel := fun at_ τ =>
  match τ with
  | .nominal .scalar =>
      if at_ = ⟨[.attempt ⟨409⟩ 0], ⟨410⟩⟩ then some (0 : Nat)
      else some (5 : Nat)
  | _ => none

private theorem retry_protocol_unfold_gen
    (fnTable : FnTable deployModel wFnHeaders) (gTable : GTable deployModel []) :
    Term.observe deployModel fnTable gTable (wRetrySchnorrTerm (hs := ⟨wFnHeaders, []⟩)) []
      (Env.empty.extend (Names.counting 0 ([⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] : List (LTy deployVocab)))
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))) =
      Process.call (GOp.given (.coin ()) 0 [] ⟨[], ⟨410⟩⟩ [] .nil dScalar) fun (r : Nat) =>
        Process.call (GOp.flow .message 0 [1] ⟨[], ⟨412⟩⟩ dPoint (powMod 2 r 23)) fun _ =>
          ((bif !decide (r = 0) then
              Process.call (GOp.given (.coin ()) 1 [0] ⟨[], ⟨413⟩⟩ [] .nil dScalar) fun (c : Nat) =>
                Process.call (GOp.flow .message 0 [1] ⟨[], ⟨420⟩⟩ dScalar ((r + (c * 7) % 11) % 11))
                  fun _ =>
                    (((bif decide (powMod 2 ((r + (c * 7) % 11) % 11) 23 =
                        (powMod 2 r 23 * powMod 13 c 23) % 23) then
                      (Process.done (HList.nil, ()) :
                        Protocol deployModel (HList (LVal deployModel) [] × Unit))
                    else
                      Process.halt ([1], Stop.declared .reject ⟨[], ⟨425⟩⟩)).map
                      fun out => (out.1, (((r + (c * 7) % 11) % 11), out.2))).map
                      fun out => (out.1, (c, out.2)))
            else
              Process.halt ([0], Stop.declared .abort ⟨[], ⟨417⟩⟩)).map
              fun out => (out.1, (powMod 2 r 23, out.2))).bind (fun inner =>
                (Process.done (HList.nil, ()) :
                  Protocol deployModel (HList (LVal deployModel) [] × Unit)).map
                    fun rest => (rest.1, (inner.2.1, inner.2.2.1, inner.2.2.2.1, ()))) := by
  unfold wRetrySchnorrTerm wRetryBody
  simp only [Term.observe, observeOp, protocolOp, localOp, ownedOp,
    asBool, computeArgs, liftLocal, Process.bind, Process.map]
  rfl

private theorem retry_protocol_unfold :
    protocolMeaning deployModel retryWitnessTyped Member.head []
      (.cons (7 : Nat) (.cons (13 : Nat) .nil)) =
      (Process.call (GOp.given (.coin ()) 0 [] ⟨[], ⟨410⟩⟩ [] .nil dScalar) fun (r : Nat) =>
        Process.call (GOp.flow .message 0 [1] ⟨[], ⟨412⟩⟩ dPoint (powMod 2 r 23)) fun _ =>
          ((bif !decide (r = 0) then
              Process.call (GOp.given (.coin ()) 1 [0] ⟨[], ⟨413⟩⟩ [] .nil dScalar) fun (c : Nat) =>
                Process.call (GOp.flow .message 0 [1] ⟨[], ⟨420⟩⟩ dScalar ((r + (c * 7) % 11) % 11))
                  fun _ =>
                    (((bif decide (powMod 2 ((r + (c * 7) % 11) % 11) 23 =
                        (powMod 2 r 23 * powMod 13 c 23) % 23) then
                      (Process.done (HList.nil, ()) :
                        Protocol deployModel (HList (LVal deployModel) [] × Unit))
                    else
                      Process.halt ([1], Stop.declared .reject ⟨[], ⟨425⟩⟩)).map
                      fun out => (out.1, (((r + (c * 7) % 11) % 11), out.2))).map
                      fun out => (out.1, (c, out.2)))
            else
              Process.halt ([0], Stop.declared .abort ⟨[], ⟨417⟩⟩)).map
              fun out => (out.1, (powMod 2 r 23, out.2))).bind (fun inner =>
                (Process.done (HList.nil, ()) :
                  Protocol deployModel (HList (LVal deployModel) [] × Unit)).map
                    fun rest => (rest.1, (inner.2.1, inner.2.2.1, inner.2.2.2.1, ())))).map
        fun out => (out.1, out.2) :=
  congrArg (fun p => p.map fun out => (out.1, out.2)) (retry_protocol_unfold_gen _ _)

private def Term.straightNoName {D : Dialect} (bad : Name) :
    {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Bool
  | _, _, .ret exit => !decide (bad ∈ HList.names exit)
  | _, _, .op _ _ operands _ rest =>
      !decide (bad ∈ HList.names operands) && Term.straightNoName bad rest
  | _, _, .guard _ _ c _ _ rest =>
      decide (c.name ≠ bad) && Term.straightNoName bad rest
  | _, _, _ => false

private theorem term_denote_agree_except {D : Dialect} (sem : Semantics D) (bad : Name) :
    ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs),
      Term.straightNoName bad t = true →
      ∀ (path : List Frame) (env₁ env₂ : Env sem.Val Γ),
        (∀ name, name ≠ bad → ∀ σ found, env₁ name σ found = env₂ name σ found) →
        t.denote sem path env₁ = t.denote sem path env₂
  | _, _, .ret exit, ht, _, env₁, env₂, hAg => by
      dsimp only [Term.straightNoName] at ht
      have hNot : bad ∉ HList.names exit := by
        intro hm; rw [decide_eq_true hm] at ht; cases ht
      show Process.done (env₁.all exit) = Process.done (env₂.all exit)
      exact congrArg Process.done (Env.all_same exit fun name hmem =>
        hAg name (fun h => hNot (h ▸ hmem)))
  | _, _, .op _ _ operands results rest, ht, path, env₁, env₂, hAg => by
      dsimp only [Term.straightNoName] at ht
      obtain ⟨hOps, hRest⟩ := Bool.and_eq_true_iff.mp ht
      have hNot : bad ∉ HList.names operands := by
        intro hm; rw [decide_eq_true hm] at hOps; cases hOps
      have hAll : env₁.all operands = env₂.all operands :=
        Env.all_same operands fun name hmem => hAg name (fun h => hNot (h ▸ hmem))
      rw [Term.denote_step, Term.denote_step, Instr.denote_op, Instr.denote_op, hAll]
      refine congrArg (Process.bind _) (funext fun vals => ?_)
      exact term_denote_agree_except sem bad rest hRest path _ _
        (fun name hne => Env.extend_same_at env₁ env₂ results vals name (.inr (hAg name hne)))
  | _, _, .guard _ _ c ok _ rest, ht, path, env₁, env₂, hAg => by
      dsimp only [Term.straightNoName] at ht
      obtain ⟨hC, hRest⟩ := Bool.and_eq_true_iff.mp ht
      have hNe : c.name ≠ bad := of_decide_eq_true hC
      have hGet : env₁.get c = env₂.get c := Env.get_same c (hAg c.name hNe)
      rw [Term.denote_guard, Term.denote_guard, hGet]
      cases sem.holds ok (env₂.get c) with
      | true => exact term_denote_agree_except sem bad rest hRest path env₁ env₂ hAg
      | false => rfl
  | _, _, .choose .., ht, _, _, _, _ => by cases ht
  | _, _, .cases .., ht, _, _, _, _ => by cases ht
  | _, _, .loop .., ht, _, _, _, _ => by cases ht
  | _, _, .block .., ht, _, _, _, _ => by cases ht
  | _, _, .attempt .., ht, _, _, _, _ => by cases ht

private def Program.NoBegin {B : Type} : Program deployModel B → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.begin _) _ => False
  | .call _ cont => ∀ r, Program.NoBegin (cont r)

private theorem noBegin_attemptIndexFree {B : Type} (target : Site) (j : Nat) :
    ∀ {p : Program deployModel B}, Program.NoBegin p → Program.AttemptIndexFree deployModel target j p
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.begin _) _, h => False.elim h
  | .call (.give ..) _, h => fun r => noBegin_attemptIndexFree target j (h r)
  | .call (.get ..) _, h => fun r => noBegin_attemptIndexFree target j (h r)
  | .call (.own ..) _, h => fun r => noBegin_attemptIndexFree target j (h r)
  | .call (.hear ..) _, h => fun r => noBegin_attemptIndexFree target j (h r)
  | .call (.settle _) _, h => fun r => noBegin_attemptIndexFree target j (h r)

private theorem noBegin_bind {A B : Type} {f : A → Program deployModel B} :
    ∀ {p : Program deployModel A}, Program.NoBegin p →
      (∀ a, Program.NoBegin (f a)) → Program.NoBegin (p.bind f)
  | .done a, _, hf => hf a
  | .halt _, _, _ => trivial
  | .call (.begin _) _, hp, _ => False.elim hp
  | .call (.give ..) _, hp, hf => fun r => noBegin_bind (hp r) hf
  | .call (.get ..) _, hp, hf => fun r => noBegin_bind (hp r) hf
  | .call (.own ..) _, hp, hf => fun r => noBegin_bind (hp r) hf
  | .call (.hear ..) _, hp, hf => fun r => noBegin_bind (hp r) hf
  | .call (.settle _) _, hp, hf => fun r => noBegin_bind (hp r) hf

private theorem noBegin_map {A B : Type} (f : A → B) :
    ∀ {p : Program deployModel A}, Program.NoBegin p → Program.NoBegin (p.map f)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.begin _) _, hp => False.elim hp
  | .call (.give ..) _, hp => fun r => noBegin_map f (hp r)
  | .call (.get ..) _, hp => fun r => noBegin_map f (hp r)
  | .call (.own ..) _, hp => fun r => noBegin_map f (hp r)
  | .call (.hear ..) _, hp => fun r => noBegin_map f (hp r)
  | .call (.settle _) _, hp => fun r => noBegin_map f (hp r)

private theorem noBegin_liftLocal {A : Type} :
    ∀ (p : Local A), Program.NoBegin (liftLocal (S := RSig deployModel) id p)
  | .done _ => trivial
  | .halt _ => trivial
  | .call op _ => nomatch op

private theorem noBegin_roleOp (fnTable : FnTable deployModel wFnHeaders)
    (rTable : RTable deployModel []) (key : Key) {ins res : List (LTy deployVocab)}
    (o : RoleOp deployVocab ⟨wFnHeaders, []⟩ 0 ins res) (path : List Frame)
    (vs : HList (RV deployModel 0) ins) :
    Program.NoBegin (roleOp deployModel 0 fnTable rTable key o path vs) := by
  cases o with
  | compute _ _ _ _ _ _ => exact noBegin_map _ (noBegin_liftLocal _)
  | absent _ _ => trivial
  | give _ _ _ => cases vs with | cons _ r => cases r; exact fun _ => trivial
  | get _ _ _ _ _ _ => exact fun _ => trivial
  | keep _ _ => cases vs with | cons _ r => cases r; trivial
  | own _ _ _ _ _ _ => exact fun _ => trivial
  | hear _ _ _ _ _ => exact fun _ => trivial
  | apply callee => exact nomatch callee

private theorem term_straight_noBegin (fnTable : FnTable deployModel wFnHeaders)
    (rTable : RTable deployModel []) (bad : Name) :
    ∀ {Γ : Ctx (LTy deployVocab)} {outs : List (LTy deployVocab)}
      (t : Term (roleDialect deployVocab ⟨wFnHeaders, []⟩ 0) Γ outs),
      Term.straightNoName bad t = true →
      ∀ (path : List Frame) (env : Env (RV deployModel 0) Γ),
        Program.NoBegin (t.denote (roleSem deployModel 0 fnTable rTable) path env)
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .op key o operands results rest, ht, path, env => by
      dsimp only [Term.straightNoName] at ht
      obtain ⟨_, hRest⟩ := Bool.and_eq_true_iff.mp ht
      rw [Term.denote_step, Instr.denote_op]
      exact noBegin_bind (noBegin_roleOp fnTable rTable key o path (env.all operands))
        fun vals => term_straight_noBegin fnTable rTable bad rest hRest path (env.extend results vals)
  | _, _, .guard _ _ c ok _ rest, ht, path, env => by
      dsimp only [Term.straightNoName] at ht
      obtain ⟨_, hRest⟩ := Bool.and_eq_true_iff.mp ht
      rw [Term.denote_guard]
      cases (roleSem deployModel 0 fnTable rTable).holds ok (env.get c) with
      | true => exact term_straight_noBegin fnTable rTable bad rest hRest path env
      | false => trivial
  | _, _, .choose .., ht, _, _ => by cases ht
  | _, _, .cases .., ht, _, _ => by cases ht
  | _, _, .loop .., ht, _, _ => by cases ht
  | _, _, .block .., ht, _, _ => by cases ht
  | _, _, .attempt .., ht, _, _ => by cases ht

private theorem attempt_attemptIndexFree
    (fnTable : FnTable deployModel wFnHeaders) (rTable : RTable deployModel []) (j : Nat)
    (body : Term (protocolDialect deployVocab ⟨wFnHeaders, []⟩)
      ((Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]).extend
        (.cons 2 .nil : Names [LTy.index [0]])) [])
    (hBody : Term.straightNoName 2 (project 0 body) = true) :
    Program.AttemptIndexFree deployModel ⟨[], ⟨409⟩⟩ j
      ((project 0 (.attempt ⟨409⟩ [0] ⟨0, rfl⟩ (.cons 2 .nil) body .nil (.ret .nil) :
          Term (protocolDialect deployVocab ⟨wFnHeaders, []⟩)
            (Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]) [])).denote
        (roleSem deployModel 0 fnTable rTable) []
        (Env.empty.extend (Names.counting 0 ([⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] : List (LTy deployVocab)))
          (hideAll deployModel 0 (.cons (7 : Nat) (.cons (13 : Nat) .nil) :
            HList (LVal deployModel) [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])))) := by
  let env0 : Env (RV deployModel 0) (Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]) :=
    Env.empty.extend (Names.counting 0 ([⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] : List (LTy deployVocab)))
      (hideAll deployModel 0 (.cons (7 : Nat) (.cons (13 : Nat) .nil) :
        HList (LVal deployModel) [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]))
  change Program.AttemptIndexFree deployModel ⟨[], ⟨409⟩⟩ j
    (Process.call (ROp.begin ⟨[], ⟨409⟩⟩) fun (n : Nat) =>
      (((project 0 body).denote (roleSem deployModel 0 fnTable rTable) []
        (env0.insert 2 (hide deployModel 0 (LTy.index [0]) n))).bind
        fun out => Process.call (ROp.settle ⟨[], ⟨409⟩⟩) fun _ => Process.done out).bind
      fun _ => (Process.done HList.nil : Program deployModel (HList (RV deployModel 0) [])))
  dsimp only [Program.AttemptIndexFree]
  refine ⟨fun _ => ?_, fun n => ?_⟩
  · have hEq :
        (project 0 body).denote (roleSem deployModel 0 fnTable rTable) []
          (env0.insert 2 (hide deployModel 0 (LTy.index [0]) j)) =
        (project 0 body).denote (roleSem deployModel 0 fnTable rTable) []
          (env0.insert 2 (hide deployModel 0 (LTy.index [0]) 0)) :=
      term_denote_agree_except (roleSem deployModel 0 fnTable rTable) 2 (project 0 body) hBody [] _ _
        (fun name hne σ found =>
          (Env.insert_at_other env0 2 (hide deployModel 0 (LTy.index [0]) j) hne found).trans
            (Env.insert_at_other env0 2 (hide deployModel 0 (LTy.index [0]) 0) hne found).symm)
    rw [hEq]
  · exact noBegin_attemptIndexFree ⟨[], ⟨409⟩⟩ j
      (noBegin_bind
        (noBegin_bind
          (term_straight_noBegin fnTable rTable 2 (project 0 body) hBody []
            (env0.insert 2 (hide deployModel 0 (LTy.index [0]) n)))
          (fun _ _ => trivial))
        (fun _ => trivial))

private theorem retry_prover_attemptIndexFree (j : Nat) :
    Program.AttemptIndexFree deployModel ⟨[], ⟨409⟩⟩ j
      (roleMeaning deployModel retryWitnessTyped Member.head 0 []
        (hideAll deployModel 0 (.cons (7 : Nat) (.cons (13 : Nat) .nil)))) :=
  attempt_attemptIndexFree _ _ j wRetryBody (by decide +kernel)

/-- Concrete non-vacuous instantiation of `deploy_complete_retry` at `k = 1` (`bound = 4`): attempt 0
draws `r = 0`, emits `A = 1` (modifying both sponge state and proof buffer), and aborts at guard
`⟨417⟩`; `attempts` rolls back cleanly via `restoreAgain`; attempt 1 draws `r = 5`, succeeds, and
the verifier accepts its proof. -/
theorem witness_deploy_complete_retry :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab)
      (hIns : d.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      admit (erase retryWitnessTyped) noAssociation = .ok a ∧
      deploy deployEncoder a retryNoSamplesDecl = .ok d ∧
      let ins := cast (congrArg (HList (LVal deployModel)) hIns.symm)
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone deployModel retryAbortThenSucceedSource 0
          (d.run deployModel 0 (hideAll deployModel 0 ins)
            (cast (congrArg (HList deployModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone deployModel retryAbortThenSucceedSource 1
          (d.run deployModel 1 (hideAll deployModel 1 ins)
            (cast (congrArg (HList deployModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins) ∧
          (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
            source' at' τ' = shiftAttemptSource deployModel
              (d.entry.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
              (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource at' τ') ∧
          GExec deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins)
            (.returned out) ∧
          outP = hideAll deployModel 0 out.1 ∧ outV = hideAll deployModel 1 out.1 := by
  obtain ⟨a, d, hAdm, hProg, hDep⟩ := retryWitness_deploy_exists
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps deployEncoder a retryNoSamplesDecl d hDep
  have hDProg : d.admitted.program = retryWitnessTyped := by rw [hAdmEq, hProg]
  have hSL := wFnDefs_suiteLawful_of (by rw [hDeclEq]; rfl) (.inr hDProg)
  have hLL := wFnDefs_layoutLawful_of (by rw [hDeclEq]; rfl) rfl (.inr hDProg)
  cases d with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier wRetrySchnorrHdr retryNoSamplesDecl = some (0, 1) := by
            decide +kernel
          obtain ⟨hFirst, hMatched⟩ :=
            deploy_matches deployEncoder a retryNoSamplesDecl _ hDep 0 1 hRoles
          have hInsV : (HList.cons (7 : Nat) (.cons (13 : Nat) .nil) :
              HList (LVal deployModel) wRetrySchnorrHdr.ins).All
              (fun a v => deployModel.Valid a.ty v) :=
            ⟨show (7 : Nat) < 11 by decide, show (13 : Nat) < 23 by decide, trivial⟩
          have hNoRec : ∀ l, retryNoSamplesDecl.layout = some l → l.recover = [] := fun _ h => by
            cases Option.some.inj h; rfl
          have hFnsNoAb : Defs.fnsNoAbort retryWitnessTyped.defs = true := by decide +kernel
          have hOnce : wRetrySchnorrHdr.shape.retryAtMostOnce ⟨[], ⟨409⟩⟩ [] = true := by decide +kernel
          have hOwned : wRetrySchnorrHdr.shape.retryOwnedBy 0 ⟨[], ⟨409⟩⟩ [] = true := by decide +kernel
          have hExcl : wRetrySchnorrHdr.shape.attemptCoinsExclusive 0 ⟨[], ⟨409⟩⟩ = true := by decide +kernel
          have hVNoAtt : wRetrySchnorrHdr.shape.hasAttemptFor 1 ⟨[], ⟨409⟩⟩ [] = false := by decide +kernel
          have hShift0 :
              shiftAttemptSource deployModel
                (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                (.attempt ⟨409⟩ 0) retryAbortThenSucceedSource ⟨[], ⟨410⟩⟩ dScalar = some (0 : Nat) := by
            have hIn : (⟨[], ⟨410⟩⟩ : Site) ∈
                wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false := by decide +kernel
            unfold shiftAttemptSource; dsimp only [Occurrence.site, Frame.applications]
            erw [ite_eq_left hIn]; rfl
          have hShift1 :
              shiftAttemptSource deployModel
                (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource ⟨[], ⟨410⟩⟩ dScalar = some (5 : Nat) := by
            have hIn : (⟨[], ⟨410⟩⟩ : Site) ∈
                wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false := by decide +kernel
            unfold shiftAttemptSource; dsimp only [Occurrence.site, Frame.applications]
            erw [ite_eq_left hIn]; rfl
          have hNotHeard410 : (⟨[], ⟨410⟩⟩ : Site) ∉ wRetrySchnorrHdr.shape.heardCoins := by
            decide +kernel
          have hLPAb : ∀ j, j < 1 →
              LawfulPrivate deployModel
                (shiftAttemptSource deployModel
                  (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                  (.attempt ⟨409⟩ j) retryAbortThenSucceedSource)
                (protocolMeaning deployModel retryWitnessTyped Member.head []
                  (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
            intro j hj
            have hj0 : j = 0 := Nat.lt_one_iff.mp hj
            subst hj0
            rw [retry_protocol_unfold]
            dsimp only [Process.map, Process.bind, LawfulPrivate]
            intro v hv
            rw [hShift0] at hv
            cases Option.some.inj hv
            exact ⟨⟨show (0 : Nat) < 11 by decide, ⟨[], dScalar⟩, rfl, rfl, rfl,
              show (0 : Nat) < 11 by decide⟩, trivial⟩
          have hFedAb : ∀ j, j < 1 →
              Fed deployModel
                (shiftAttemptSource deployModel
                  (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                  (.attempt ⟨409⟩ j) retryAbortThenSucceedSource)
                (protocolMeaning deployModel retryWitnessTyped Member.head []
                  (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
            intro j hj
            have hj0 : j = 0 := Nat.lt_one_iff.mp hj
            subst hj0
            rw [retry_protocol_unfold]
            dsimp only [Process.map, Process.bind, Fed]
            exact ⟨(0 : Nat), hShift0, trivial⟩
          have hAborts : ∀ j, j < 1 →
              ∀ source₁, Lawful deployModel source₁
                (protocolMeaning deployModel retryWitnessTyped Member.head []
                  (.cons (7 : Nat) (.cons (13 : Nat) .nil))) →
                AllFed deployModel source₁
                  (protocolMeaning deployModel retryWitnessTyped Member.head []
                    (.cons (7 : Nat) (.cons (13 : Nat) .nil))) →
                (∀ at' τ', at'.site ∉ wRetrySchnorrHdr.shape.heardCoins →
                  source₁ at' τ' = shiftAttemptSource deployModel
                    (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                    (.attempt ⟨409⟩ j) retryAbortThenSucceedSource at' τ') →
                ∃ evs who why,
                  GRun deployModel source₁
                    (protocolMeaning deployModel retryWitnessTyped Member.head []
                      (.cons (7 : Nat) (.cons (13 : Nat) .nil))) evs (.stopped who why) ∧
                  0 ∈ who ∧ why.isAbort = true := by
            intro j hj source₁ _ _ hAg
            have hj0 : j = 0 := Nat.lt_one_iff.mp hj
            subst hj0
            have hS410 : source₁ ⟨[], ⟨410⟩⟩ dScalar = some (0 : Nat) :=
              (hAg ⟨[], ⟨410⟩⟩ dScalar hNotHeard410).trans hShift0
            rw [retry_protocol_unfold]
            dsimp only [Process.map, Process.bind]
            exact ⟨[Event.given (.coin ()) 0 [] ⟨[], ⟨410⟩⟩ dScalar (0 : Nat),
              Event.flow .message 0 [1] ⟨[], ⟨412⟩⟩ dPoint (powMod 2 0 23)],
              [0], Stop.declared .abort ⟨[], ⟨417⟩⟩,
              .given hS410 (.flow .halt), List.mem_cons_self, rfl⟩
          have hLPK : LawfulPrivate deployModel
              (shiftAttemptSource deployModel
                (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource)
              (protocolMeaning deployModel retryWitnessTyped Member.head []
                (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
            rw [retry_protocol_unfold]
            dsimp only [Process.map, Process.bind, LawfulPrivate]
            intro v hv
            rw [hShift1] at hv
            cases Option.some.inj hv
            refine ⟨⟨show (5 : Nat) < 11 by decide, ⟨[], dScalar⟩, rfl, rfl, rfl,
              show (5 : Nat) < 11 by decide⟩, ?_⟩
            intro (c : Nat) _
            dsimp only [Process.map, Process.bind, LawfulPrivate]
            cases decide (powMod 2 ((5 + c * 7 % 11) % 11) 23 =
                (powMod 2 5 23 * powMod 13 c 23) % 23) <;> trivial
          have hFedK : Fed deployModel
              (shiftAttemptSource deployModel
                (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource)
              (protocolMeaning deployModel retryWitnessTyped Member.head []
                (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
            rw [retry_protocol_unfold]
            dsimp only [Process.map, Process.bind, Fed]
            refine ⟨(5 : Nat), hShift1, fun (c : Nat) _ => ?_⟩
            dsimp only [Process.map, Process.bind, Fed]
            cases decide (powMod 2 ((5 + c * 7 % 11) % 11) 23 =
                (powMod 2 5 23 * powMod 13 c 23) % 23) <;> trivial
          have hNoHaltK : ∀ source₁,
              Lawful deployModel source₁
                (protocolMeaning deployModel retryWitnessTyped Member.head []
                  (.cons (7 : Nat) (.cons (13 : Nat) .nil))) →
              (∀ at' τ', at'.site ∉ wRetrySchnorrHdr.shape.heardCoins →
                source₁ at' τ' = shiftAttemptSource deployModel
                  (wRetrySchnorrHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                  (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource at' τ') →
              ∀ e, GExec deployModel source₁
                (protocolMeaning deployModel retryWitnessTyped Member.head []
                  (.cons (7 : Nat) (.cons (13 : Nat) .nil))) e →
              ∃ out, e = .returned out := by
            intro source₁ hLaw hAg e ⟨_, hRun⟩
            have hS410 : source₁ ⟨[], ⟨410⟩⟩ dScalar = some (5 : Nat) :=
              (hAg ⟨[], ⟨410⟩⟩ dScalar hNotHeard410).trans hShift1
            rw [retry_protocol_unfold] at hLaw hRun
            dsimp only [Process.map, Process.bind] at hLaw hRun
            cases hRun with
            | @given _ _ _ _ _ _ _ vR _ _ _ hSrcR hRun1 =>
                change Nat at vR
                have hrEq : vR = 5 := Option.some.inj (hSrcR.symm.trans hS410)
                subst hrEq
                have hLaw1 := (hLaw _ hSrcR).2
                cases hRun1 with
                | flow hRun2 =>
                    dsimp only [Bool.not_false, cond, Process.map, Process.bind] at hLaw1 hRun2
                    cases hRun2 with
                    | @given _ _ _ _ _ _ _ vC _ _ _ hSrcC hRun3 =>
                        have hcLt : deployModel.Valid dScalar vC := (hLaw1 _ hSrcC).1.1
                        change Nat at vC; change vC < 11 at hcLt
                        cases hRun3 with
                        | flow hRun4 =>
                            have hEq := schnorr_group_law_w7 5 vC (by decide) hcLt
                            have hAdd : ∀ r c : Nat, (r + c * 7 % 11) % 11 = (r + c * 7) % 11 :=
                              fun r c => by omega
                            have hDec : decide (powMod 2 ((5 + vC * 7 % 11) % 11) 23 =
                                (powMod 2 5 23 * powMod 13 vC 23) % 23) = true :=
                              decide_eq_true (by rw [hAdd, hEq])
                            erw [hDec] at hRun4
                            cases hRun4
                            exact ⟨_, rfl⟩
          refine ⟨a, _, rfl, hFirst, hMatched, hAdm, hDep, ?_⟩
          exact deploy_complete_retry deployModel deployEncoder hAdm retryNoSamplesDecl _ hDep
            rfl rfl rfl hNoRec
            (hSL.toFor deployEncoder deployModel) hLL hRoles hFirst hMatched
            (.cons (7 : Nat) (.cons (13 : Nat) .nil)) hInsV
            retryAbortThenSucceedSource 1 (by decide)
            hFnsNoAb hOnce hOwned hExcl hVNoAtt
            (fun j _ => retry_prover_attemptIndexFree j)
            hLPAb hFedAb hAborts hLPK hFedK hNoHaltK

/-! ## Witness 5: Ideal RO verifier linkage (`deployIdeal_link`) with concrete partial oracle -/

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
  | mk adm decl found stack _ident =>
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
                  simp [Stack.Takes, hUL]
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

/-- Concrete non-vacuous instantiation of `deployIdeal_link` through concrete partial oracle
`schnorrIdealRO`, proof bytes `[9, 0]`, statement `Y = 13`, and `fixedNonceSource 5`. -/
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

/-! ## Witnesses 6–8: Ideal RO query uniqueness, cross-session, and cross-statement separation -/

/-- Concrete witness of `deployIdeal_queries_nodup`: on EVERY execution path and EVERY proof buffer
(honest or malicious), the emitted `idealServiceKey` queries are strictly duplicate-free (`qs.Nodup`)
and every query extends the canonical initial path `st0`. -/
theorem witness_deployIdeal_queries_nodup :
    ∃ (a : Admitted deployVocab) (dIdeal : Deployed deployVocab)
      (hIns : dIdeal.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (st0 : deployModel.Val (LayerBuild.idealPathTy dByte)),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      deployIdeal deployEncoder idealServiceKey a schnorrDecl = .ok dIdeal ∧
      let vIns := hideAll deployModel 1
        (cast (congrArg (HList (LVal deployModel)) hIns.symm)
          (.cons (0 : Nat) (.cons (13 : Nat) .nil)))
      ∀ (taken : HList deployModel.Val (Stack.Takes (dIdeal.stack 1)))
        (qs : List (deployModel.Val (LayerBuild.idealQueryTy dByte))),
        (dIdeal.run deployModel 1 vIns taken).ServiceQueries deployModel dByte idealServiceKey qs →
        qs.Nodup ∧ ∀ q ∈ qs, st0.1 <+: q.1.1 ∧ st0.2.1 <+: q.1.2.1 := by
  obtain ⟨a, dIdeal, hAdm, hProg, hDep⟩ := witness_deployIdeal_exists
  obtain ⟨w, hWEq⟩ := deployIdeal_ok_elim deployEncoder idealServiceKey a schnorrDecl dIdeal hDep
  have hAdmEq : dIdeal.admitted = a := by rw [hWEq]
  have hDeclEq : dIdeal.declaration = schnorrDecl := by rw [hWEq]
  have hDProg : dIdeal.admitted.program = witnessTyped := by rw [hAdmEq, hProg]
  cases dIdeal with
  | mk adm decl found stack _ident =>
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
          obtain ⟨suiteUnitTy, _, _, _, st0, hUnit, _, _, hAll⟩ :=
            deployIdeal_queries_nodup deployModel deployEncoder idealServiceKey
              hDep rfl rfl hRoles vIns hVInsV
          have hSU : suiteUnitTy = dByte := by
            cases a with
            | mk progA annA assocA assuA =>
                dsimp only at hProg; subst hProg
                have hExp : findSuiteUnit ⟨witnessTyped, annA, assocA, assuA⟩ toySuite =
                    some ⟨dByte, ⟨rfl⟩⟩ := rfl
                exact congrArg Sigma.fst (Option.some.inj (hUnit.symm.trans hExp))
          subst hSU
          exact ⟨a, _, rfl, st0, hAdm, hDep, hAll⟩

/-- Concrete witness of `deployIdeal_cross_session_disjoint`: `schnorrDecl` (`application = []`) and
`schnorrAppCtxDecl` (`application = [42, 7, 3]`) can NEVER share any random-oracle query `q` on any
proofs, inputs, or rounds. -/
theorem witness_cross_session_disjoint :
    ∃ (a : Admitted deployVocab)
      (sess₁ sess₂ : List Nat) (hS₁ : ∀ b, b ∈ sess₁ → b < 256) (hS₂ : ∀ b, b ∈ sess₂ → b < 256)
      (st₁ st₂ : deployModel.Val (LayerBuild.idealPathTy dByte)),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      resolveSessionBytes deployEncoder a schnorrDecl none = .ok ⟨sess₁, hS₁⟩ ∧
      resolveSessionBytes deployEncoder a schnorrAppCtxDecl none = .ok ⟨sess₂, hS₂⟩ ∧
      idealInitialPath deployModel a toySuite dByte 0 1 sess₁
        (hideAll deployModel 1 (.cons (0 : Nat) (.cons (13 : Nat) .nil) :
          HList (LVal deployModel) wSchnorrHdr.ins)) = some st₁ ∧
      idealInitialPath deployModel a toySuite dByte 0 1 sess₂
        (hideAll deployModel 1 (.cons (0 : Nat) (.cons (13 : Nat) .nil) :
          HList (LVal deployModel) wSchnorrHdr.ins)) = some st₂ ∧
      ∀ q : deployModel.Val (LayerBuild.idealQueryTy dByte),
        ¬ (st₁.1 <+: q.1.1 ∧ st₂.1 <+: q.1.1) := by
  obtain ⟨a, d₁, hAdm, hProg, hDep₁⟩ := witness_deployIdeal_exists
  obtain ⟨a', d₂, hAdm', hProg', hDep₂⟩ := witness_deployIdealAppCtx_exists
  have hAA : a' = a := Except.ok.inj (hAdm'.symm.trans hAdm)
  subst a'
  obtain ⟨w₁, hEq₁⟩ := deployIdeal_ok_elim deployEncoder idealServiceKey a schnorrDecl d₁ hDep₁
  obtain ⟨w₂, hEq₂⟩ := deployIdeal_ok_elim deployEncoder idealServiceKey a schnorrAppCtxDecl d₂ hDep₂
  have hAdm₁ : d₁.admitted = a := by rw [hEq₁]
  have hDecl₁ : d₁.declaration = schnorrDecl := by rw [hEq₁]
  have hAdm₂ : d₂.admitted = a := by rw [hEq₂]
  have hDecl₂ : d₂.declaration = schnorrAppCtxDecl := by rw [hEq₂]
  cases d₁ with
  | mk adm₁ decl₁ found₁ stack₁ _ident₁ =>
      cases d₂ with
      | mk adm₂ decl₂ found₂ stack₂ _ident₂ =>
          dsimp only at hAdm₁ hDecl₁ hAdm₂ hDecl₂
          subst hAdm₁; subst hDecl₁; subst hAdm₂; subst hDecl₂
          cases adm₂ with
          | mk progA annA assocA assuA =>
              dsimp only at hProg; subst hProg
              let a0 : Admitted deployVocab := ⟨witnessTyped, annA, assocA, assuA⟩
              have hRoles₁ : proverAndVerifier wSchnorrHdr schnorrDecl = some (0, 1) := by decide +kernel
              have hRoles₂ : proverAndVerifier wSchnorrHdr schnorrAppCtxDecl = some (0, 1) := by decide +kernel
              let vIns : HList (RV deployModel 1) wSchnorrHdr.ins :=
                hideAll deployModel 1 (.cons (0 : Nat) (.cons (13 : Nat) .nil))
              have hVInsV : vIns.All (RV.Valid deployModel 1) :=
                hideAll_valid deployModel 1 _
                  ⟨show (0 : Nat) < 11 by decide, show (13 : Nat) < 23 by decide, trivial⟩
              obtain ⟨u₁, _, sess₁, hS₁, st₁, hU₁, hRes₁, hInit₁, _⟩ :=
                deployIdeal_queries_nodup deployModel deployEncoder idealServiceKey
                  hDep₁ rfl rfl hRoles₁ vIns hVInsV
              obtain ⟨u₂, _, sess₂, hS₂, st₂, hU₂, hRes₂, hInit₂, _⟩ :=
                deployIdeal_queries_nodup deployModel deployEncoder idealServiceKey
                  hDep₂ rfl rfl hRoles₂ vIns hVInsV
              have hSU₁ : u₁ = dByte :=
                congrArg Sigma.fst (Option.some.inj (hU₁.symm.trans (rfl : findSuiteUnit a0 toySuite = some ⟨dByte, ⟨rfl⟩⟩)))
              have hSU₂ : u₂ = dByte :=
                congrArg Sigma.fst (Option.some.inj (hU₂.symm.trans (rfl : findSuiteUnit a0 toySuite = some ⟨dByte, ⟨rfl⟩⟩)))
              subst hSU₁; subst hSU₂
              refine ⟨a0, sess₁, sess₂, hS₁, hS₂, st₁, st₂, hAdm, hRes₁, hRes₂, hInit₁, hInit₂, ?_⟩
              intro q ⟨hP₁, hP₂⟩
              have hEqDecl := (deployIdeal_cross_session_disjoint deployModel deployEncoder
                deployEncoder_injective hRes₁ hRes₂ hInit₁ hInit₂ hP₁ hP₂).2.1
              have hAppEq : ([] : List Nat) = [42, 7, 3] := congrArg Declaration.application hEqDecl
              cases hAppEq

/-- Concrete witness of `deployIdeal_cross_statement_disjoint`: valid statements `Y₁ = 13` and
`Y₂ = 2` on the same ideal Schnorr deployment can NEVER share any random-oracle query `q`. -/
theorem witness_cross_statement_disjoint :
    ∃ (a : Admitted deployVocab) (dIdeal : Deployed deployVocab)
      (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
      (st₁ st₂ : deployModel.Val (LayerBuild.idealPathTy dByte)),
      admit (erase witnessTyped) noAssociation = .ok a ∧
      deployIdeal deployEncoder idealServiceKey a schnorrDecl = .ok dIdeal ∧
      resolveSessionBytes deployEncoder a schnorrDecl none = .ok ⟨sessBytes, hSess⟩ ∧
      idealInitialPath deployModel a toySuite dByte 0 1 sessBytes
        (hideAll deployModel 1 (.cons (0 : Nat) (.cons (13 : Nat) .nil) :
          HList (LVal deployModel) wSchnorrHdr.ins)) = some st₁ ∧
      idealInitialPath deployModel a toySuite dByte 0 1 sessBytes
        (hideAll deployModel 1 (.cons (0 : Nat) (.cons (2 : Nat) .nil) :
          HList (LVal deployModel) wSchnorrHdr.ins)) = some st₂ ∧
      ∀ q : deployModel.Val (LayerBuild.idealQueryTy dByte),
        ¬ (st₁.2.1 <+: q.1.2.1 ∧ st₂.2.1 <+: q.1.2.1) := by
  obtain ⟨a, dIdeal, hAdm, hProg, hDep⟩ := witness_deployIdeal_exists
  obtain ⟨w, hWEq⟩ := deployIdeal_ok_elim deployEncoder idealServiceKey a schnorrDecl dIdeal hDep
  have hAdmEq : dIdeal.admitted = a := by rw [hWEq]
  have hDeclEq : dIdeal.declaration = schnorrDecl := by rw [hWEq]
  have hDProg : dIdeal.admitted.program = witnessTyped := by rw [hAdmEq, hProg]
  have hSL := wFnDefs_suiteLawful_of (by rw [hDeclEq]; rfl) (.inl hDProg)
  cases dIdeal with
  | mk adm decl found stack _ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq hAdmEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier wSchnorrHdr schnorrDecl = some (0, 1) := by decide +kernel
          let vIns₁ : HList (RV deployModel 1) wSchnorrHdr.ins :=
            hideAll deployModel 1 (.cons (0 : Nat) (.cons (13 : Nat) .nil))
          let vIns₂ : HList (RV deployModel 1) wSchnorrHdr.ins :=
            hideAll deployModel 1 (.cons (0 : Nat) (.cons (2 : Nat) .nil))
          have hV₁ : vIns₁.All (RV.Valid deployModel 1) :=
            hideAll_valid deployModel 1 _
              ⟨show (0 : Nat) < 11 by decide, show (13 : Nat) < 23 by decide, trivial⟩
          have hV₂ : vIns₂.All (RV.Valid deployModel 1) :=
            hideAll_valid deployModel 1 _
              ⟨show (0 : Nat) < 11 by decide, show (2 : Nat) < 23 by decide, trivial⟩
          obtain ⟨u₁, _, sessBytes, hSess, st₁, hU₁, hRes, hInit₁, _⟩ :=
            deployIdeal_queries_nodup deployModel deployEncoder idealServiceKey
              hDep rfl rfl hRoles vIns₁ hV₁
          obtain ⟨u₂, _, sessBytes₂, _, st₂, hU₂, hRes₂, hInit₂, _⟩ :=
            deployIdeal_queries_nodup deployModel deployEncoder idealServiceKey
              hDep rfl rfl hRoles vIns₂ hV₂
          have hSU₁ : u₁ = dByte := by
            cases a with
            | mk progA annA assocA assuA =>
                dsimp only at hProg; subst hProg
                have hExp : findSuiteUnit ⟨witnessTyped, annA, assocA, assuA⟩ toySuite =
                    some ⟨dByte, ⟨rfl⟩⟩ := rfl
                exact congrArg Sigma.fst (Option.some.inj (hU₁.symm.trans hExp))
          have hSU₂ : u₂ = dByte := by
            cases a with
            | mk progA annA assocA assuA =>
                dsimp only at hProg; subst hProg
                have hExp : findSuiteUnit ⟨witnessTyped, annA, assocA, assuA⟩ toySuite =
                    some ⟨dByte, ⟨rfl⟩⟩ := rfl
                exact congrArg Sigma.fst (Option.some.inj (hU₂.symm.trans hExp))
          subst hSU₁; subst hSU₂
          have hSessEq : sessBytes₂ = sessBytes := by
            have hEq := hRes₂.symm.trans hRes
            cases hEq
            rfl
          subst sessBytes₂
          have hInit₁' : idealInitialPath deployModel ⟨witnessTyped, ann, assoc, assu⟩
              toySuite dByte 0 1 sessBytes vIns₁ = some st₁ := by
            rw [← hAdmEq] at hInit₁; exact hInit₁
          have hInit₂' : idealInitialPath deployModel ⟨witnessTyped, ann, assoc, assu⟩
              toySuite dByte 0 1 sessBytes vIns₂ = some st₂ := by
            rw [← hAdmEq] at hInit₂; exact hInit₂
          refine ⟨a, _, sessBytes, hSess, st₁, st₂, hAdm, hDep, hRes, hInit₁, hInit₂, ?_⟩
          intro q ⟨hD₁, hD₂⟩
          have hStmtEq := deployIdeal_cross_statement_disjoint deployModel deployEncoder
            (d := ⟨⟨witnessTyped, ann, assoc, assu⟩, schnorrDecl, found, stack, _ident⟩)
            (hCon := rfl) (hSuite := hSL.toFor deployEncoder deployModel)
            hV₁ hV₂ hInit₁' hInit₂' hD₁ hD₂
          have hMem : (⟨0, 0, dPoint, rfl⟩ : LayerBuild.StmtPos deployVocab 1 wSchnorrHdr.ins) ∈
              LayerBuild.statementPositions 1 0 1 (.inr rfl) wSchnorrHdr.ins :=
            List.mem_cons_self
          have hValEq := hStmtEq ⟨0, 0, dPoint, rfl⟩ hMem
          change (13 : Nat) = 2 at hValEq
          cases hValEq

/-! ## Witness 9: Post-challenge abort-and-retry completeness (`deploy_complete_retry` via `AllFed`) -/

/-- Post-challenge rejection-sampling body inside `.attempt ⟨409⟩ [0]`: draws private nonce `r`,
sends commitment `A = g^r`, draws verifier public challenge `c` (`⟨413⟩`), and ONLY AFTER hearing
`c` checks `r ≠ 0` (`guard ⟨417⟩ [0] .abort`). Discharging `hAborts` on this protocol requires the
`AllFed` hypothesis of `deploy_complete_retry` to supply `c` at `⟨413⟩`. -/
private def wPostChRetryBody {hs : Headers deployVocab} :
    Term (protocolDialect deployVocab hs)
      ((Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]).extend
        (.cons 2 .nil : Names [LTy.index [0]])) [] :=
  .op ⟨410⟩ (.given (.coin ()) 0 [] [] dScalar ⟨⟨[], dScalar⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 3 .nil) <|
  .op ⟨411⟩ (.compute [0] (.row DeployRow.base _ rfl) [⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 3) .nil) (.cons 4 .nil) <|
  .op ⟨412⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (wvar 4) .nil) (.cons 5 .nil) <|
  .op ⟨413⟩ (.given (.coin ()) 1 [0] [] dScalar ⟨⟨[], dScalar⟩, rfl, rfl, rfl⟩
      (fun _ h => nomatch h) (by decide)) .nil (.cons 9 .nil) <|
  .op ⟨414⟩ (.compute [0] (.literal (V := deployVocab) dScalar [0] rfl) [] rfl (by decide)) .nil (.cons 6 .nil) <|
  .op ⟨415⟩ (.compute [0] (.row DeployRow.sameScalar _ rfl) [⟨dScalar, [0]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 3) (.cons (wvar 6) .nil)) (.cons 7 .nil) <|
  .op ⟨416⟩ (.compute [0] (.owned .boolNot) [⟨.bool, [0]⟩] rfl (by decide))
      (.cons (wvar 7) .nil) (.cons 8 .nil) <|
  .guard ⟨417⟩ [0] (wvar 8) ⟨rfl, by decide, by decide⟩ .abort <|
  .op ⟨418⟩ (.compute [0] (.row DeployRow.mul _ rfl) [⟨dScalar, [0, 1]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 9) (.cons (wvar 0) .nil)) (.cons 10 .nil) <|
  .op ⟨419⟩ (.compute [0] (.row DeployRow.add _ rfl) [⟨dScalar, [0]⟩, ⟨dScalar, [0]⟩] rfl (by decide))
      (.cons (wvar 3) (.cons (wvar 10) .nil)) (.cons 11 .nil) <|
  .op ⟨420⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (wvar 11) .nil) (.cons 12 .nil) <|
  .op ⟨421⟩ (.compute [1] (.row DeployRow.base _ rfl) [⟨dScalar, [0, 1]⟩] rfl (by decide))
      (.cons (wvar 12) .nil) (.cons 13 .nil) <|
  .op ⟨422⟩ (.compute [1] (.row DeployRow.scale _ rfl) [⟨dScalar, [0, 1]⟩, ⟨dPoint, [0, 1]⟩] rfl (by decide))
      (.cons (wvar 9) (.cons (wvar 1) .nil)) (.cons 14 .nil) <|
  .op ⟨423⟩ (.compute [1] (.row DeployRow.plus _ rfl) [⟨dPoint, [0, 1]⟩, ⟨dPoint, [1]⟩] rfl (by decide))
      (.cons (wvar 5) (.cons (wvar 14) .nil)) (.cons 15 .nil) <|
  .op ⟨424⟩ (.compute [1] (.row DeployRow.same _ rfl) [⟨dPoint, [1]⟩, ⟨dPoint, [1]⟩] rfl (by decide))
      (.cons (wvar 13) (.cons (wvar 15) .nil)) (.cons 16 .nil) <|
  .guard ⟨425⟩ [1] (wvar 16) ⟨rfl, by decide, by decide⟩ .reject <|
  .ret .nil

private def wPostChRetryTerm {hs : Headers deployVocab} :
    Term (protocolDialect deployVocab hs)
      (Ctx.positional [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩]) [] :=
  .attempt ⟨409⟩ [0] ⟨0, rfl⟩ (.cons 2 .nil) wPostChRetryBody .nil (.ret .nil)

private abbrev wPostChRetryHdr : ProtocolHeader deployVocab :=
  ⟨⟨202⟩, 2, [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩], [], shapeOf (wPostChRetryTerm (hs := ⟨wFnHeaders, []⟩))⟩

private def postChRetryTyped : Typed deployVocab :=
  ⟨⟨wFnHeaders, [wPostChRetryHdr]⟩,
   .protocol wPostChRetryHdr (Names.counting 0 _) wPostChRetryTerm
     ⟨by simp [Within, ProtocolOp.Within, wPostChRetryTerm, wPostChRetryBody, wPostChRetryHdr],
      by decide,
      by simp [Enclosed, wPostChRetryTerm, wPostChRetryBody],
      (Term.repeatedAddress_eq_none _).mp (by decide +kernel),
      rfl,
      by unfold Term.UsedOnce; decide +kernel,
      by decide +kernel,
      (Term.rebound_eq_none _ _).mp (by decide +kernel)⟩ wFnDefs,
   by decide⟩

private theorem postChRetry_admit_isOk :
    (admit (erase postChRetryTyped) noAssociation).isOk = true := by decide +kernel

private theorem postChRetry_deploy_isOk :
    (match admit (erase postChRetryTyped) noAssociation with
     | .ok a => (deploy deployEncoder a retryNoSamplesDecl).isOk
     | .error _ => false) = true := by decide +kernel

private theorem postChRetry_protocol_unfold_gen
    (fnTable : FnTable deployModel wFnHeaders) (gTable : GTable deployModel []) :
    Term.observe deployModel fnTable gTable (wPostChRetryTerm (hs := ⟨wFnHeaders, []⟩)) []
      (Env.empty.extend (Names.counting 0 ([⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] : List (LTy deployVocab)))
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))) =
      Process.call (GOp.given (.coin ()) 0 [] ⟨[], ⟨410⟩⟩ [] .nil dScalar) fun (r : Nat) =>
        Process.call (GOp.flow .message 0 [1] ⟨[], ⟨412⟩⟩ dPoint (powMod 2 r 23)) fun _ =>
          ((Process.call (GOp.given (.coin ()) 1 [0] ⟨[], ⟨413⟩⟩ [] .nil dScalar) fun (c : Nat) =>
              ((bif !decide (r = 0) then
                  Process.call (GOp.flow .message 0 [1] ⟨[], ⟨420⟩⟩ dScalar ((r + (c * 7) % 11) % 11))
                    fun _ =>
                      ((bif decide (powMod 2 ((r + (c * 7) % 11) % 11) 23 =
                          (powMod 2 r 23 * powMod 13 c 23) % 23) then
                        (Process.done (HList.nil, ()) :
                          Protocol deployModel (HList (LVal deployModel) [] × Unit))
                      else
                        Process.halt ([1], Stop.declared .reject ⟨[], ⟨425⟩⟩)).map
                        fun out => (out.1, (((r + (c * 7) % 11) % 11), out.2)))
                else
                  Process.halt ([0], Stop.declared .abort ⟨[], ⟨417⟩⟩)).map
                fun out => (out.1, (c, out.2)))).map
            fun out => (out.1, (powMod 2 r 23, out.2))).bind (fun inner =>
              (Process.done (HList.nil, ()) :
                Protocol deployModel (HList (LVal deployModel) [] × Unit)).map
                  fun rest => (rest.1, (inner.2.1, inner.2.2.1, inner.2.2.2.1, ()))) := by
  unfold wPostChRetryTerm wPostChRetryBody
  simp only [Term.observe, observeOp, protocolOp, localOp, ownedOp,
    asBool, computeArgs, liftLocal, Process.bind, Process.map]
  rfl

private theorem postChRetry_protocol_unfold :
    protocolMeaning deployModel postChRetryTyped Member.head []
      (.cons (7 : Nat) (.cons (13 : Nat) .nil)) =
      (Process.call (GOp.given (.coin ()) 0 [] ⟨[], ⟨410⟩⟩ [] .nil dScalar) fun (r : Nat) =>
        Process.call (GOp.flow .message 0 [1] ⟨[], ⟨412⟩⟩ dPoint (powMod 2 r 23)) fun _ =>
          ((Process.call (GOp.given (.coin ()) 1 [0] ⟨[], ⟨413⟩⟩ [] .nil dScalar) fun (c : Nat) =>
              ((bif !decide (r = 0) then
                  Process.call (GOp.flow .message 0 [1] ⟨[], ⟨420⟩⟩ dScalar ((r + (c * 7) % 11) % 11))
                    fun _ =>
                      ((bif decide (powMod 2 ((r + (c * 7) % 11) % 11) 23 =
                          (powMod 2 r 23 * powMod 13 c 23) % 23) then
                        (Process.done (HList.nil, ()) :
                          Protocol deployModel (HList (LVal deployModel) [] × Unit))
                      else
                        Process.halt ([1], Stop.declared .reject ⟨[], ⟨425⟩⟩)).map
                        fun out => (out.1, (((r + (c * 7) % 11) % 11), out.2)))
                else
                  Process.halt ([0], Stop.declared .abort ⟨[], ⟨417⟩⟩)).map
                fun out => (out.1, (c, out.2)))).map
            fun out => (out.1, (powMod 2 r 23, out.2))).bind (fun inner =>
              (Process.done (HList.nil, ()) :
                Protocol deployModel (HList (LVal deployModel) [] × Unit)).map
                  fun rest => (rest.1, (inner.2.1, inner.2.2.1, inner.2.2.2.1, ())))).map
        fun out => (out.1, out.2) :=
  congrArg (fun p => p.map fun out => (out.1, out.2)) (postChRetry_protocol_unfold_gen _ _)

/-- Concrete non-vacuous witness of `deploy_complete_retry` on a **post-challenge abort** protocol:
attempt 0 sends commitment `A`, derives the Fiat–Shamir challenge `c` (`⟨413⟩`), and ONLY THEN
aborts at guard `⟨417⟩` (using `AllFed` to supply `c` in `hAborts`), rolls back transcript state and
proof buffer, and succeeds honestly on attempt 1. -/
theorem witness_post_challenge_abort_retry :
    ∃ (a : Admitted deployVocab) (d : Deployed deployVocab)
      (hIns : d.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩])
      (hFirst : Stack.Takes (d.stack 0) = [])
      (hMatched : Stack.Gives (d.stack 0) = Stack.Takes (d.stack 1)),
      admit (erase postChRetryTyped) noAssociation = .ok a ∧
      deploy deployEncoder a retryNoSamplesDecl = .ok d ∧
      let ins := cast (congrArg (HList (LVal deployModel)) hIns.symm)
        (.cons (7 : Nat) (.cons (13 : Nat) .nil))
      ∃ outP gives recordP outV givesV recordV,
        Alone deployModel retryAbortThenSucceedSource 0
          (d.run deployModel 0 (hideAll deployModel 0 ins)
            (cast (congrArg (HList deployModel.Val) hFirst.symm) .nil))
          recordP (.returned (outP, gives)) ∧
        Alone deployModel retryAbortThenSucceedSource 1
          (d.run deployModel 1 (hideAll deployModel 1 ins)
            (cast (congrArg (HList deployModel.Val) hMatched) gives))
          recordV (.returned (outV, givesV)) ∧
        ∃ source' out,
          Lawful deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins) ∧
          (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
            source' at' τ' = shiftAttemptSource deployModel
              (d.entry.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
              (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource at' τ') ∧
          GExec deployModel source'
            (protocolMeaning deployModel d.admitted.program d.callee [] ins)
            (.returned out) ∧
          outP = hideAll deployModel 0 out.1 ∧ outV = hideAll deployModel 1 out.1 := by
  have hAdmEx : ∃ a : Admitted deployVocab,
      admit (erase postChRetryTyped) noAssociation = .ok a ∧ a.program = postChRetryTyped := by
    cases h : admit (erase postChRetryTyped) noAssociation with
    | error _ => have hOk := postChRetry_admit_isOk; rw [h] at hOk; cases hOk
    | ok a => exact ⟨a, rfl, admitted_eq_of_readback h rfl⟩
  obtain ⟨a, hAdm, hProg⟩ := hAdmEx
  have hDepEx : ∃ d, deploy deployEncoder a retryNoSamplesDecl = .ok d := by
    cases h : deploy deployEncoder a retryNoSamplesDecl with
    | error _ =>
        have hOk := postChRetry_deploy_isOk
        rw [hAdm] at hOk; dsimp only at hOk; rw [h] at hOk; cases hOk
    | ok d => exact ⟨d, rfl⟩
  obtain ⟨d, hDep⟩ := hDepEx
  obtain ⟨hAdmEq, hDeclEq, _⟩ := deploy_keeps deployEncoder a retryNoSamplesDecl d hDep
  have hDProg : d.admitted.program = postChRetryTyped := by rw [hAdmEq, hProg]
  cases d with
  | mk adm decl found stack ident =>
      cases adm with
      | mk prog ann assoc assu =>
          dsimp only at hDProg hDeclEq
          subst hDProg; subst hDeclEq
          have hRoles : proverAndVerifier wPostChRetryHdr retryNoSamplesDecl = some (0, 1) := by
            decide +kernel
          obtain ⟨hFirst, hMatched⟩ :=
            deploy_matches deployEncoder a retryNoSamplesDecl _ hDep 0 1 hRoles
          -- Reuse `wFnDefs` semantic laws via `retryWitness_deploy_exists` (definitionally identical `wFnHeaders`/`wFnDefs`)
          obtain ⟨_, dR, _, hProgR, hDepR⟩ := retryWitness_deploy_exists
          obtain ⟨hAdmR, hDeclR, _⟩ := deploy_keeps deployEncoder _ retryNoSamplesDecl dR hDepR
          have hDProgR : dR.admitted.program = retryWitnessTyped := by rw [hAdmR, hProgR]
          have hSLR := wFnDefs_suiteLawful_of (by rw [hDeclR]; rfl) (.inr hDProgR)
          have hLLR := wFnDefs_layoutLawful_of (by rw [hDeclR]; rfl) rfl (.inr hDProgR)
          cases dR with
          | mk admR declR foundR stackR identR =>
              cases admR with
              | mk progR annR assocR assuR =>
                  dsimp only at hDProgR hDeclR
                  subst hDProgR; subst hDeclR
                  have hFindMap : ∀ k, (k = ⟨102⟩ ∨ k = ⟨103⟩ ∨ k = ⟨104⟩ ∨ k = ⟨105⟩ ∨ k = ⟨106⟩ ∨ k = ⟨107⟩) →
                      ∀ {hdr} {f : Member wFnHeaders hdr},
                        postChRetryTyped.find k = some (.fn f) → retryWitnessTyped.find k = some (.fn f) := by
                    intro k hk hdr f hFind
                    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
                    · obtain ⟨rfl, rfl⟩ := member_unique_of_find hFind
                        (rfl : postChRetryTyped.find ⟨102⟩ = some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))))))
                      rfl
                    · obtain ⟨rfl, rfl⟩ := member_unique_of_find hFind
                        (rfl : postChRetryTyped.find ⟨103⟩ = some (.fn (Member.tail (Member.tail (Member.tail (Member.tail (Member.tail Member.head)))))))
                      rfl
                    · obtain ⟨rfl, rfl⟩ := member_unique_of_find hFind
                        (rfl : postChRetryTyped.find ⟨104⟩ = some (.fn (Member.tail (Member.tail (Member.tail (Member.tail Member.head))))))
                      rfl
                    · obtain ⟨rfl, rfl⟩ := member_unique_of_find hFind
                        (rfl : postChRetryTyped.find ⟨105⟩ = some (.fn (Member.tail (Member.tail (Member.tail Member.head)))))
                      rfl
                    · obtain ⟨rfl, rfl⟩ := member_unique_of_find hFind
                        (rfl : postChRetryTyped.find ⟨106⟩ = some (.fn (Member.tail (Member.tail Member.head))))
                      rfl
                    · obtain ⟨rfl, rfl⟩ := member_unique_of_find hFind
                        (rfl : postChRetryTyped.find ⟨107⟩ = some (.fn (Member.tail Member.head)))
                      rfl
                  have hSL : Deployed.SuiteLawful deployModel
                      ⟨⟨postChRetryTyped, ann, assoc, assu⟩, retryNoSamplesDecl, found, stack, ident⟩ := by
                    intro suite _ hCon
                    have hSEq : suite = toySuite := (Construction.derived.inj hCon).1.symm
                    subst hSEq
                    have hW := hSLR toySuite _ rfl
                    constructor
                    · intro defKey hMem hdr f hFind stateTy drawIns e law owner h0 hs _ _ hLaw hins houts
                        st lbl pay coin st' hStV hLblV hPayV hEval
                      have hK : defKey = ⟨104⟩ := by
                        rcases hMem with hMem | ⟨_, hLM⟩
                        · simp only [toySuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
                          rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
                        · cases hLM
                      subst hK
                      cases law
                      have hF' := hFindMap ⟨104⟩ (.inr (.inr (.inl rfl))) hFind
                      cases e with
                      | mk eSite eCls eTau =>
                          dsimp only at hLaw houts hEval ⊢
                          cases Option.some.inj hLaw
                          exact hW.1 ⟨104⟩ hMem hdr f hF' stateTy []
                            ⟨⟨[], ⟨413⟩⟩, .given (.coin ()) 1 [0], dScalar⟩ () 1 0 []
                            (show (⟨⟨[], ⟨413⟩⟩, .given (.coin ()) 1 [0], dScalar⟩ : ShapeEvent deployVocab) ∈
                              wRetrySchnorrHdr.shape.events [] id by
                                simp [wRetrySchnorrTerm, wRetryBody, shapeOf, ProtocolOp.shape, Shape.events, EventClass.rename])
                            rfl rfl hins houts st lbl pay coin st' hStV hLblV hPayV hEval
                    · intro eKey hMem hdr f hFind unitTy τ hIn hOut v₁ v₂ u hv₁ hv₂ hEv₁ hEv₂
                      have hK : eKey = ⟨102⟩ ∨ eKey = ⟨103⟩ := by
                        simp only [toySuite, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
                        rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;>
                          first | exact .inl h | exact .inr h | cases h
                      rcases hK with rfl | rfl
                      · exact hW.2 ⟨102⟩ hMem hdr f (hFindMap ⟨102⟩ (.inl rfl) hFind) unitTy τ hIn hOut v₁ v₂ u hv₁ hv₂ hEv₁ hEv₂
                      · exact hW.2 ⟨103⟩ hMem hdr f (hFindMap ⟨103⟩ (.inr (.inl rfl)) hFind) unitTy τ hIn hOut v₁ v₂ u hv₁ hv₂ hEv₁ hEv₂
                  have hLL : Deployed.LayoutLawful deployModel
                      ⟨⟨postChRetryTyped, ann, assoc, assu⟩, retryNoSamplesDecl, found, stack, ident⟩ := by
                    intro layout hLay
                    have hLEq : layout = ⟨toyLayoutModule, [], []⟩ := (Option.some.inj hLay).symm
                    subst hLEq
                    have hW := hLLR ⟨toyLayoutModule, [], []⟩ rfl
                    refine ⟨?_, ?_, ?_⟩
                    · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
                        v chunk pre post hv hPre hPost hWRun
                      have hWK : wKey = ⟨102⟩ ∨ wKey = ⟨103⟩ := by
                        simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
                        rcases hwMem with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
                          first | exact .inl h | exact .inr h | cases h
                      have hRK : rKey = ⟨105⟩ ∨ rKey = ⟨106⟩ := by
                        simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
                        rcases hrMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;>
                          first | exact .inl h | exact .inr h | cases h
                      have hFW' : retryWitnessTyped.find wKey = some (.fn fW) := by
                        rcases hWK with rfl | rfl
                        · exact hFindMap ⟨102⟩ (.inl rfl) hwFind
                        · exact hFindMap ⟨103⟩ (.inr (.inl rfl)) hwFind
                      have hFR' : retryWitnessTyped.find rKey = some (.fn fR) := by
                        rcases hRK with rfl | rfl
                        · exact hFindMap ⟨105⟩ (.inr (.inr (.inr (.inl rfl)))) hrFind
                        · exact hFindMap ⟨106⟩ (.inr (.inr (.inr (.inr (.inl rfl))))) hrFind
                      exact hW.1 wKey rKey hwMem hrMem wHdr rHdr fW fR hFW' hFR' unitTy τ hwIn hwOut hrIn hrOut
                        v chunk pre post hv hPre hPost hWRun
                    · intro wKey rKey hwMem hrMem wHdr rHdr fW fR hwFind hrFind unitTy τ hwIn hwOut hrIn hrOut
                        buf off v nextOff hBuf hRRun
                      have hWK : wKey = ⟨102⟩ ∨ wKey = ⟨103⟩ := by
                        simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwMem
                        rcases hwMem with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
                          first | exact .inl h | exact .inr h | cases h
                      have hRK : rKey = ⟨105⟩ ∨ rKey = ⟨106⟩ := by
                        simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrMem
                        rcases hrMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;>
                          first | exact .inl h | exact .inr h | cases h
                      have hFW' : retryWitnessTyped.find wKey = some (.fn fW) := by
                        rcases hWK with rfl | rfl
                        · exact hFindMap ⟨102⟩ (.inl rfl) hwFind
                        · exact hFindMap ⟨103⟩ (.inr (.inl rfl)) hwFind
                      have hFR' : retryWitnessTyped.find rKey = some (.fn fR) := by
                        rcases hRK with rfl | rfl
                        · exact hFindMap ⟨105⟩ (.inr (.inr (.inr (.inl rfl)))) hrFind
                        · exact hFindMap ⟨106⟩ (.inr (.inr (.inr (.inr (.inl rfl))))) hrFind
                      exact hW.2.1 wKey rKey hwMem hrMem wHdr rHdr fW fR hFW' hFR' unitTy τ hwIn hwOut hrIn hrOut
                        buf off v nextOff hBuf hRRun
                    · intro eqKey hMem hdr f hFind τ hIn hOut v₁ v₂ b hv₁ hv₂ hEv
                      have hEK : eqKey = ⟨107⟩ := by
                        simp only [toyLayoutModule, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
                        rcases hMem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
                      subst hEK
                      exact hW.2.2 ⟨107⟩ hMem hdr f (hFindMap ⟨107⟩ (.inr (.inr (.inr (.inr (.inr rfl))))) hFind) τ hIn hOut v₁ v₂ b hv₁ hv₂ hEv
                  have hInsV : (HList.cons (7 : Nat) (.cons (13 : Nat) .nil) :
                      HList (LVal deployModel) wPostChRetryHdr.ins).All
                      (fun a v => deployModel.Valid a.ty v) :=
                    ⟨show (7 : Nat) < 11 by decide, show (13 : Nat) < 23 by decide, trivial⟩
                  have hNoRec : ∀ l, retryNoSamplesDecl.layout = some l → l.recover = [] := fun _ h => by
                    cases Option.some.inj h; rfl
                  have hFnsNoAb : Defs.fnsNoAbort postChRetryTyped.defs = true := by decide +kernel
                  have hOnce : wPostChRetryHdr.shape.retryAtMostOnce ⟨[], ⟨409⟩⟩ [] = true := by decide +kernel
                  have hOwned : wPostChRetryHdr.shape.retryOwnedBy 0 ⟨[], ⟨409⟩⟩ [] = true := by decide +kernel
                  have hExcl : wPostChRetryHdr.shape.attemptCoinsExclusive 0 ⟨[], ⟨409⟩⟩ = true := by decide +kernel
                  have hVNoAtt : wPostChRetryHdr.shape.hasAttemptFor 1 ⟨[], ⟨409⟩⟩ [] = false := by decide +kernel
                  have hShift0 :
                      shiftAttemptSource deployModel
                        (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                        (.attempt ⟨409⟩ 0) retryAbortThenSucceedSource ⟨[], ⟨410⟩⟩ dScalar = some (0 : Nat) := by
                    have hIn : (⟨[], ⟨410⟩⟩ : Site) ∈
                        wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false := by decide +kernel
                    unfold shiftAttemptSource; dsimp only [Occurrence.site, Frame.applications]
                    erw [ite_eq_left hIn]; rfl
                  have hShift1 :
                      shiftAttemptSource deployModel
                        (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                        (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource ⟨[], ⟨410⟩⟩ dScalar = some (5 : Nat) := by
                    have hIn : (⟨[], ⟨410⟩⟩ : Site) ∈
                        wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false := by decide +kernel
                    unfold shiftAttemptSource; dsimp only [Occurrence.site, Frame.applications]
                    erw [ite_eq_left hIn]; rfl
                  have hNotHeard410 : (⟨[], ⟨410⟩⟩ : Site) ∉ wPostChRetryHdr.shape.heardCoins := by
                    decide +kernel
                  have hLPAb : ∀ j, j < 1 →
                      LawfulPrivate deployModel
                        (shiftAttemptSource deployModel
                          (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                          (.attempt ⟨409⟩ j) retryAbortThenSucceedSource)
                        (protocolMeaning deployModel postChRetryTyped Member.head []
                          (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
                    intro j hj
                    have hj0 : j = 0 := Nat.lt_one_iff.mp hj; subst hj0
                    rw [postChRetry_protocol_unfold]
                    dsimp only [Process.map, Process.bind, LawfulPrivate]
                    intro v hv; rw [hShift0] at hv; cases Option.some.inj hv
                    exact ⟨⟨show (0 : Nat) < 11 by decide, ⟨[], dScalar⟩, rfl, rfl, rfl,
                      show (0 : Nat) < 11 by decide⟩, fun _ _ => trivial⟩
                  have hFedAb : ∀ j, j < 1 →
                      Fed deployModel
                        (shiftAttemptSource deployModel
                          (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                          (.attempt ⟨409⟩ j) retryAbortThenSucceedSource)
                        (protocolMeaning deployModel postChRetryTyped Member.head []
                          (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
                    intro j hj
                    have hj0 : j = 0 := Nat.lt_one_iff.mp hj; subst hj0
                    rw [postChRetry_protocol_unfold]
                    dsimp only [Process.map, Process.bind, Fed]
                    exact ⟨(0 : Nat), hShift0, fun _ _ => trivial⟩
                  -- HERE `hAF : AllFed` is genuinely used to obtain the challenge `vC` at `⟨413⟩`!
                  have hAborts : ∀ j, j < 1 →
                      ∀ source₁, Lawful deployModel source₁
                        (protocolMeaning deployModel postChRetryTyped Member.head []
                          (.cons (7 : Nat) (.cons (13 : Nat) .nil))) →
                        AllFed deployModel source₁
                          (protocolMeaning deployModel postChRetryTyped Member.head []
                            (.cons (7 : Nat) (.cons (13 : Nat) .nil))) →
                        (∀ at' τ', at'.site ∉ wPostChRetryHdr.shape.heardCoins →
                          source₁ at' τ' = shiftAttemptSource deployModel
                            (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                            (.attempt ⟨409⟩ j) retryAbortThenSucceedSource at' τ') →
                        ∃ evs who why,
                          GRun deployModel source₁
                            (protocolMeaning deployModel postChRetryTyped Member.head []
                              (.cons (7 : Nat) (.cons (13 : Nat) .nil))) evs (.stopped who why) ∧
                          0 ∈ who ∧ why.isAbort = true := by
                    intro j hj source₁ _ hAF hAg
                    have hj0 : j = 0 := Nat.lt_one_iff.mp hj; subst hj0
                    have hS410 : source₁ ⟨[], ⟨410⟩⟩ dScalar = some (0 : Nat) :=
                      (hAg ⟨[], ⟨410⟩⟩ dScalar hNotHeard410).trans hShift0
                    rw [postChRetry_protocol_unfold] at hAF ⊢
                    dsimp only [Process.map, Process.bind, AllFed] at hAF ⊢
                    obtain ⟨vR, hSrcR, hAF1⟩ := hAF
                    change Nat at vR
                    have hrEq : vR = 0 := Option.some.inj (hSrcR.symm.trans hS410)
                    subst hrEq
                    obtain ⟨vC, hSrcC, _⟩ := hAF1
                    exact ⟨[Event.given (.coin ()) 0 [] ⟨[], ⟨410⟩⟩ dScalar (0 : Nat),
                      Event.flow .message 0 [1] ⟨[], ⟨412⟩⟩ dPoint (powMod 2 0 23),
                      Event.given (.coin ()) 1 [0] ⟨[], ⟨413⟩⟩ dScalar vC],
                      [0], Stop.declared .abort ⟨[], ⟨417⟩⟩,
                      .given hS410 (.flow (.given hSrcC .halt)), List.mem_cons_self, rfl⟩
                  have hLPK : LawfulPrivate deployModel
                      (shiftAttemptSource deployModel
                        (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                        (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource)
                      (protocolMeaning deployModel postChRetryTyped Member.head []
                        (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
                    rw [postChRetry_protocol_unfold]
                    dsimp only [Process.map, Process.bind, LawfulPrivate]
                    intro v hv; rw [hShift1] at hv; cases Option.some.inj hv
                    refine ⟨⟨show (5 : Nat) < 11 by decide, ⟨[], dScalar⟩, rfl, rfl, rfl,
                      show (5 : Nat) < 11 by decide⟩, fun (c : Nat) _ => ?_⟩
                    cases decide (powMod 2 ((5 + c * 7 % 11) % 11) 23 =
                        (powMod 2 5 23 * powMod 13 c 23) % 23) <;> trivial
                  have hFedK : Fed deployModel
                      (shiftAttemptSource deployModel
                        (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                        (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource)
                      (protocolMeaning deployModel postChRetryTyped Member.head []
                        (.cons (7 : Nat) (.cons (13 : Nat) .nil))) := by
                    rw [postChRetry_protocol_unfold]
                    dsimp only [Process.map, Process.bind, Fed]
                    refine ⟨(5 : Nat), hShift1, fun (c : Nat) _ => ?_⟩
                    cases decide (powMod 2 ((5 + c * 7 % 11) % 11) 23 =
                        (powMod 2 5 23 * powMod 13 c 23) % 23) <;> trivial
                  have hNoHaltK : ∀ source₁,
                      Lawful deployModel source₁
                        (protocolMeaning deployModel postChRetryTyped Member.head []
                          (.cons (7 : Nat) (.cons (13 : Nat) .nil))) →
                      (∀ at' τ', at'.site ∉ wPostChRetryHdr.shape.heardCoins →
                        source₁ at' τ' = shiftAttemptSource deployModel
                          (wPostChRetryHdr.shape.attemptPrivateCoins 0 ⟨[], ⟨409⟩⟩ [] false)
                          (.attempt ⟨409⟩ 1) retryAbortThenSucceedSource at' τ') →
                      ∀ e, GExec deployModel source₁
                        (protocolMeaning deployModel postChRetryTyped Member.head []
                          (.cons (7 : Nat) (.cons (13 : Nat) .nil))) e →
                      ∃ out, e = .returned out := by
                    intro source₁ hLaw hAg e ⟨_, hRun⟩
                    have hS410 : source₁ ⟨[], ⟨410⟩⟩ dScalar = some (5 : Nat) :=
                      (hAg ⟨[], ⟨410⟩⟩ dScalar hNotHeard410).trans hShift1
                    rw [postChRetry_protocol_unfold] at hLaw hRun
                    dsimp only [Process.map, Process.bind] at hLaw hRun
                    cases hRun with
                    | @given _ _ _ _ _ _ _ vR _ _ _ hSrcR hRun1 =>
                        change Nat at vR
                        have hrEq : vR = 5 := Option.some.inj (hSrcR.symm.trans hS410)
                        subst hrEq
                        have hLaw1 := (hLaw _ hSrcR).2
                        cases hRun1 with
                        | flow hRun2 =>
                            cases hRun2 with
                            | @given _ _ _ _ _ _ _ vC _ _ _ hSrcC hRun3 =>
                                have hcLt : deployModel.Valid dScalar vC := (hLaw1 _ hSrcC).1.1
                                change Nat at vC; change vC < 11 at hcLt
                                dsimp only [Bool.not_false, cond, Process.map, Process.bind] at hRun3
                                cases hRun3 with
                                | flow hRun4 =>
                                    have hEq := schnorr_group_law_w7 5 vC (by decide) hcLt
                                    have hAdd : ∀ r c : Nat, (r + c * 7 % 11) % 11 = (r + c * 7) % 11 :=
                                      fun r c => by omega
                                    have hDec : decide (powMod 2 ((5 + vC * 7 % 11) % 11) 23 =
                                        (powMod 2 5 23 * powMod 13 vC 23) % 23) = true :=
                                      decide_eq_true (by rw [hAdd, hEq])
                                    erw [hDec] at hRun4
                                    cases hRun4
                                    exact ⟨_, rfl⟩
                  refine ⟨a, _, rfl, hFirst, hMatched, hAdm, hDep, ?_⟩
                  exact deploy_complete_retry deployModel deployEncoder hAdm retryNoSamplesDecl _ hDep
                    rfl rfl rfl hNoRec
                    (hSL.toFor deployEncoder deployModel) hLL hRoles hFirst hMatched
                    (.cons (7 : Nat) (.cons (13 : Nat) .nil)) hInsV
                    retryAbortThenSucceedSource 1 (by decide)
                    hFnsNoAb hOnce hOwned hExcl hVNoAtt
                    (fun j _ => attempt_attemptIndexFree _ _ j wPostChRetryBody (by decide +kernel))
                    hLPAb hFedAb hAborts hLPK hFedK hNoHaltK

end Zkc.Core.Tests.Deployment
