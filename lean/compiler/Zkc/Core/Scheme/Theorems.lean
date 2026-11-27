module

public import Zkc.Core.Scheme.DeployElim
public import Zkc.Core.Scheme.Safety
public import Zkc.Core.Scheme.Completeness
public import Zkc.Core.Scheme.IdealLink
public import Zkc.Core.Format.Canonical
public import Zkc.Core.Statements

@[expose] public section

/-!
Top-level `Statements` proofs for canonical wire formats, deployed-scheme identity,
and non-interactive / ideal random-oracle deployment.

The underlying proofs are split across focused modules:
- `Zkc.Core.Scheme.DeployElim`: elimination witnesses and structural theorems
  (`deploy_keeps`, `deploy_findsRoles`, `deploy_matches`, `deploy_scoped`,
  `deploy_wellNestedRetry`, `deploy_fresh`, and their `deployIdeal_*` counterparts)
- `Zkc.Core.Scheme.Safety`: validity safety (`deploy_safe`, `deployIdeal_safe`)
  and effect coverage (`deploy_coverage`, `deployIdeal_verifier_covered`)
- `Zkc.Core.Scheme.Completeness`: streaming completeness (`deploy_complete`)
- `Zkc.Core.Scheme.IdealLink`: ideal random-oracle verifier linkage (`deployIdeal_link`),
  pure ideal-path step injectivity, and compact proof wire-layout canonicality
  (`buildCompactParse_written`, `compactLayoutVStart_written`)
-/

namespace Zkc.Core

section StatementTheorems

variable {V : Vocabulary}

/-- `canonicalFormat` satisfies `Statements.formats`. -/
theorem canonicalFormat_formats (c : Functions V)
    (hfmt : c.format = fun M codecs τ => canonicalFormat M codecs τ) :
    Statements.formats c := by
  intro M codecs τ
  rw [hfmt]
  exact canonicalFormat_lawful M codecs τ

/-- `deployedIdentity` satisfies `Statements.identityReads`. -/
theorem deployedIdentity_identityReads (enc : VocabEncoder V) (c : Functions V)
    (hid : c.identity = deployedIdentity enc) :
    Statements.identityReads c := by
  intro d d' hdecl hdefs
  rw [hid]
  exact deployedIdentity_reads enc d d' hdecl hdefs

/-- `deploy` satisfies `Statements.deployKeeps`. -/
theorem statements_deployKeeps (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployKeeps c := by
  intro a declaration d h
  rw [hdep] at h
  exact deploy_keeps enc a declaration d h

/-- `deploy` satisfies `Statements.deployFindsRoles`. -/
theorem statements_deployFindsRoles (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployFindsRoles c := by
  intro a declaration d h hNonInt
  rw [hdep] at h
  exact deploy_findsRoles enc a declaration d h hNonInt

/-- `deploy` satisfies `Statements.deployMatches`. -/
theorem statements_deployMatches (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployMatches c := by
  intro a declaration d h prover verifier hRoles
  rw [hdep] at h
  exact deploy_matches enc a declaration d h prover verifier hRoles

/-- `deploy` satisfies `Statements.deployScoped`. -/
theorem statements_deployScoped (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployScoped c := by
  intro a declaration d h
  rw [hdep] at h
  exact deploy_scoped enc a declaration d h

/-- `deploy` satisfies `Statements.deployFresh`. -/
theorem statements_deployFresh (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployFresh c := by
  intro a declaration d h
  rw [hdep] at h
  exact deploy_fresh enc a declaration d h

/-- `deploy` satisfies `Statements.deployedSafe`. -/
theorem statements_deployedSafe (enc : VocabEncoder V) (c : Functions V)
    (hadm : c.admit = admit) (hdep : c.deploy = deploy enc) : Statements.deployedSafe c := by
  intro named assoc a hA decl d hD M r ins taken hIns hTaken
  rw [hadm] at hA; rw [hdep] at hD
  exact deploy_safe M enc hA hD r ins taken hIns hTaken

/-- `deploy` satisfies `Statements.deployCoverage`. -/
theorem statements_deployCoverage (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployCoverage c := by
  intro _ _ _ _ decl d hD hni
  rw [hdep] at hD
  exact deploy_coverage enc hD hni

/-- `deploy` satisfies `Statements.completeStreaming`. -/
theorem statements_completeStreaming (enc : VocabEncoder V) (c : Functions V)
    (hadm : c.admit = admit) (hdep : c.deploy = deploy enc) : Statements.completeStreaming c := by
  intro named assoc a hA decl d hD hNI hNR hNS hRec p v hR first matched M ins hIns hSL hLL hNH src hLP hFed
  rw [hadm] at hA; rw [hdep] at hD
  exact deploy_complete M enc hA hD hNI hNR hNS hRec p v hR first matched ins hIns hSL hLL hNH src hLP hFed

/-- `deployIdeal` satisfies `Statements.idealLink`. -/
theorem statements_idealLink (enc : VocabEncoder V) : Statements.idealLink enc := by
  intro M serviceKey a decl suite sessionTag layout dIdeal hDep hCon hLay hNoRetry hNoCarry hNoRec
    prover verifier hRoles ins hIns
  exact deployIdeal_link M enc serviceKey hDep hCon hLay hNoRetry hNoCarry hNoRec
    prover verifier hRoles ins hIns

end StatementTheorems

end Zkc.Core
