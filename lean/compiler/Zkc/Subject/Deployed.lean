module

public import Zkc.Subject.Package
public import Zkc.Core.Scheme.Theorems
public import Zkc.Core.Run.Specialize.Sound

@[expose] public section
set_option autoImplicit false

/-!
The typed subject of a deployed scheme (`DeployedScheme`) and its ideal random-oracle counterpart
(`IdealDeployedScheme`), built directly over `Zkc.Subject.Package`.

Unites the written-stage subject boundary (`Zkc.Subject.Package`) with Core deployment
(`Core.deploy`, `Core.deployIdeal`), handler specialization (`Core.specialize_deploy_sound`),
safety/coverage (`deploy_safe`, `deploy_coverage`), and ideal random-oracle linkage and query
separation (`deployIdeal_link`, `deployIdeal_queries_nodup`), with zero duplicate package
representations and strictly within the two-axiom policy (`propext`, `Quot.sound`).
-/

namespace Zkc.Subject

open Zkc.Core

/-- A deployed scheme over an admitted `Zkc.Subject.Package`: carries the Core `Declaration` and
evidence that `Core.deploy` succeeds on any admission of `pkg`. -/
structure DeployedScheme {V : Vocabulary} (enc : VocabEncoder V) (pkg : Package V) where
  declaration : Declaration
  deployAccepts : ∀ {a : Admitted V}, admit pkg.stored pkg.association = .ok a →
    (deploy enc a declaration).isOk = true

namespace DeployedScheme

variable {V : Vocabulary} {enc : VocabEncoder V} {pkg : Package V} (s : DeployedScheme enc pkg)

/-- Every admission of `pkg` yields a deployed scheme `d` with `d.admitted = a` and
`d.declaration = s.declaration`. -/
theorem deploy_exists_of {a : Admitted V} (hAdm : admit pkg.stored pkg.association = .ok a) :
    ∃ d : Deployed V, deploy enc a s.declaration = .ok d ∧
      d.admitted = a ∧ d.declaration = s.declaration ∧ d.admitted.program = pkg.installed := by
  have hOk := s.deployAccepts hAdm
  cases hDep : deploy enc a s.declaration with
  | error _ => rw [hDep] at hOk; cases hOk
  | ok d =>
      have hK := deploy_keeps enc a s.declaration d hDep
      exact ⟨d, rfl, hK.1, hK.2.1, hK.1 ▸ pkg.readback hAdm⟩

/-- At least one admitted and deployed pair `(a, d)` exists for `s`. -/
theorem deployed_exists :
    ∃ (a : Admitted V) (d : Deployed V),
      admit pkg.stored pkg.association = .ok a ∧
      deploy enc a s.declaration = .ok d ∧
      d.admitted.program = pkg.installed := by
  obtain ⟨a, hAdm⟩ := pkg.admitted_exists
  obtain ⟨d, hDep, _, _, hProg⟩ := s.deploy_exists_of hAdm
  exact ⟨a, d, hAdm, hDep, hProg⟩

/-- Every deployed instance of `s` is safe: no valid input and permitted replies can reach
`Stop.undefined`. -/
theorem safe {a : Admitted V} {d : Deployed V}
    (hAdm : admit pkg.stored pkg.association = .ok a)
    (hDep : deploy enc a s.declaration = .ok d)
    (M : Model V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r)))
    (hIns : ins.All (RV.Valid M r)) (hTaken : taken.All M.Valid) :
    (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined) :=
  deploy_safe M enc hAdm hDep r ins taken hIns hTaken

/-- Every deployed instance of `s` commits the canonical identity of `(enc, a, s.declaration)`. -/
theorem identity_eq {a : Admitted V} {d : Deployed V}
    (_hAdm : admit pkg.stored pkg.association = .ok a)
    (hDep : deploy enc a s.declaration = .ok d) :
    deployedIdentity d = schemeIdentity enc a s.declaration :=
  deploy_identity enc a s.declaration d hDep

/-- Handler specialization soundness for every deployed instance of `s`:
`(specialize d r).denote = d.run` for every role `r`. -/
theorem specialize_sound {a : Admitted V} {d : Deployed V}
    (_hAdm : admit pkg.stored pkg.association = .ok a)
    (hDep : deploy enc a s.declaration = .ok d)
    (M : Model V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_deploy_sound M enc a s.declaration d hDep r ins taken

/-- Package-rooted existence corollary uniting admission of `pkg`, deployment of `s`, bound
canonical identity, safety, and specialization soundness. -/
theorem deployed_specialize_sound (M : Model V) :
    ∃ (a : Admitted V) (d : Deployed V),
      admit pkg.stored pkg.association = .ok a ∧
      deploy enc a s.declaration = .ok d ∧
      d.admitted.program = pkg.installed ∧
      deployedIdentity d = schemeIdentity enc a s.declaration ∧
      (∀ r ins taken, ins.All (RV.Valid M r) → taken.All M.Valid →
        (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined)) ∧
      (∀ r ins taken,
        (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
          d.run M r ins taken) := by
  obtain ⟨a, d, hAdm, hDep, hProg⟩ := s.deployed_exists
  exact ⟨a, d, hAdm, hDep, hProg, s.identity_eq hAdm hDep,
    fun r ins taken hIns hTaken => s.safe hAdm hDep M r ins taken hIns hTaken,
    fun r ins taken => s.specialize_sound hAdm hDep M r ins taken⟩

end DeployedScheme

/-- An ideal random-oracle deployed scheme over an admitted `Zkc.Subject.Package`, bridging
written-stage subjects directly to `deployIdeal_link` and `deployIdeal_queries_nodup`. -/
structure IdealDeployedScheme {V : Vocabulary} (enc : VocabEncoder V) (pkg : Package V) where
  serviceKey : Key
  declaration : Declaration
  idealAccepts : ∀ {a : Admitted V}, admit pkg.stored pkg.association = .ok a →
    (deployIdeal enc serviceKey a declaration).isOk = true

namespace IdealDeployedScheme

variable {V : Vocabulary} {enc : VocabEncoder V} {pkg : Package V} (s : IdealDeployedScheme enc pkg)

/-- Every admission of `pkg` yields an ideal deployed scheme `d` with `d.admitted.program = pkg.installed`. -/
theorem ideal_exists_of {a : Admitted V} (hAdm : admit pkg.stored pkg.association = .ok a) :
    ∃ d : Deployed V, deployIdeal enc s.serviceKey a s.declaration = .ok d ∧
      d.admitted = a ∧ d.declaration = s.declaration ∧ d.admitted.program = pkg.installed := by
  have hOk := s.idealAccepts hAdm
  cases hDep : deployIdeal enc s.serviceKey a s.declaration with
  | error _ => rw [hDep] at hOk; cases hOk
  | ok d =>
      let ⟨_, hEq⟩ := deployIdeal_ok_elim enc s.serviceKey a s.declaration d hDep
      subst hEq
      exact ⟨_, rfl, rfl, rfl, pkg.readback hAdm⟩

/-- At least one admitted and ideal-deployed pair `(a, d)` exists for `s`. -/
theorem ideal_exists :
    ∃ (a : Admitted V) (d : Deployed V),
      admit pkg.stored pkg.association = .ok a ∧
      deployIdeal enc s.serviceKey a s.declaration = .ok d ∧
      d.admitted.program = pkg.installed := by
  obtain ⟨a, hAdm⟩ := pkg.admitted_exists
  obtain ⟨d, hDep, _, _, hProg⟩ := s.ideal_exists_of hAdm
  exact ⟨a, d, hAdm, hDep, hProg⟩

/-- Every ideal-deployed instance of `s` is safe: no valid input and permitted replies can reach
`Stop.undefined`. -/
theorem safe {a : Admitted V} {d : Deployed V}
    (hAdm : admit pkg.stored pkg.association = .ok a)
    (hDep : deployIdeal enc s.serviceKey a s.declaration = .ok d)
    (M : Model V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r)))
    (hIns : ins.All (RV.Valid M r)) (hTaken : taken.All M.Valid) :
    (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined) :=
  deployIdeal_safe M enc s.serviceKey hAdm hDep r ins taken hIns hTaken

/-- Every ideal-deployed instance of `s` commits the canonical identity of `(enc, a, s.declaration)`. -/
theorem identity_eq {a : Admitted V} {d : Deployed V}
    (_hAdm : admit pkg.stored pkg.association = .ok a)
    (hDep : deployIdeal enc s.serviceKey a s.declaration = .ok d) :
    deployedIdentity d = schemeIdentity enc a s.declaration :=
  deployIdeal_identity enc s.serviceKey a s.declaration d hDep

/-- Every ideal-deployed instance of `s` automatically has a fresh `serviceKey` disjoint from
all request service keys in `d.entry.shape`. -/
theorem serviceKey_fresh {a : Admitted V} {d : Deployed V}
    (_hAdm : admit pkg.stored pkg.association = .ok a)
    (hDep : deployIdeal enc s.serviceKey a s.declaration = .ok d) :
    ServiceKeyFresh d.entry.shape s.serviceKey :=
  deployIdeal_serviceKey_fresh enc s.serviceKey a s.declaration d hDep

/-- Handler specialization soundness for every ideal-deployed instance of `s`. -/
theorem specialize_sound {a : Admitted V} {d : Deployed V}
    (_hAdm : admit pkg.stored pkg.association = .ok a)
    (hDep : deployIdeal enc s.serviceKey a s.declaration = .ok d)
    (M : Model V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_deployIdeal_sound M enc s.serviceKey a s.declaration d hDep r ins taken

/-- Package-rooted existence corollary uniting admission of `pkg`, ideal random-oracle deployment
of `s`, bound canonical identity, automatic `serviceKey` freshness, safety, and specialization
soundness. -/
theorem ideal_specialize_sound (M : Model V) :
    ∃ (a : Admitted V) (d : Deployed V),
      admit pkg.stored pkg.association = .ok a ∧
      deployIdeal enc s.serviceKey a s.declaration = .ok d ∧
      d.admitted.program = pkg.installed ∧
      deployedIdentity d = schemeIdentity enc a s.declaration ∧
      ServiceKeyFresh d.entry.shape s.serviceKey ∧
      (∀ r ins taken, ins.All (RV.Valid M r) → taken.All M.Valid →
        (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined)) ∧
      (∀ r ins taken,
        (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
          d.run M r ins taken) := by
  obtain ⟨a, d, hAdm, hDep, hProg⟩ := s.ideal_exists
  exact ⟨a, d, hAdm, hDep, hProg, s.identity_eq hAdm hDep, s.serviceKey_fresh hAdm hDep,
    fun r ins taken hIns hTaken => s.safe hAdm hDep M r ins taken hIns hTaken,
    fun r ins taken => s.specialize_sound hAdm hDep M r ins taken⟩

end IdealDeployedScheme

end Zkc.Subject
