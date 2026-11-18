module

public import Zkc.Core.Facts.Contracts.OutsideProjection
public import Zkc.Core.Facts.Contracts.RoleSetting
public import Zkc.Core.Facts.Body.Traversal
public import Zkc.Core.Facts.Body.Verdicts
public import Zkc.Core.Projection.Addresses
public import Zkc.Core.Facts.Body.RoleChecking

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts

variable {V : Vocabulary} {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
variable (header : ProtocolHeader V) {inputs : Names header.ins} (body : RoleP V hs r header inputs)

/-- A successful role check applies to the original role process, at every invocation path
and every permitted reply, including execution after a projected protocol call. -/
theorem checkRole_safe (summary : Contract (RoleRaw V)) (lemmas : List (Lemma (LTy V) (RoleRaw V)))
    (notes : Annotations (RoleRaw V)) {bounds}
    (accepted : checkRole catalog r header body summary lemmas notes = .ok bounds)
    (distinct : (body.addresses []).Nodup)
    (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) (rcallees : RCallees M roles)
    (sound : ∀ l ∈ lemmas, l.Valid (RoleRuns M r fns roles) (roleReading M r)
      (TypedValue (roleSem M r fns roles) (RoleValueValid M r)))
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p,b) ∈ F → p.definition = header.key → p.role = some r → (p,b) ∈ bounds)
    (path : List Frame) (values : HList (RV M r) header.ins) :
    let σ := setting catalog r header.key lemmas M fns roles notes F
    σ.AllValid values →
    (∀ e ∈ summary.requires, e.Holds σ.Runs σ.R (σ.sem.dyns values)) →
    Term.EveryFact σ .root body path (Env.empty.extend inputs values) →
    body.EveryLoop σ.sem σ.permitted σ.Bounded path [] (Env.empty.extend inputs values) ∧
      (body.denote σ.sem path (Env.empty.extend inputs values)).Every (Permitted M)
        (fun ys => σ.AllValid ys ∧ ∀ e ∈ summary.ensures, e.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns ys))
        (fun stop => stop ≠ .undefined) := by
  intro σ valid req facts
  have ⟨loops, returns⟩ := checkFacts_safe σ
    (settingLawful catalog r _ _ M fns roles _ _ callees rcallees sound)
    (readerLawful catalog r _ _ M fns roles _ _ callees)
    summary inputs body bounds accepted distinct recorded path values valid req facts
  exact ⟨loops, returns⟩

/-- An elaborated protocol supplies address uniqueness for its projection. With an empty role
contract and no annotations, only validity of the actual inputs and the callees is required. -/
theorem checkedProjection (source : Prot V hs header inputs) (ok : ProtocolConditions header source)
    {bounds} (accepted : checkRole catalog r header (project r source) = .ok bounds)
    (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) (rcallees : RCallees M roles)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p,b) ∈ F → p.definition = header.key → p.role = some r → (p,b) ∈ bounds)
    (path : List Frame) (values : HList (RV M r) header.ins) (valid : values.All (RV.Valid M r)) :
    (project r source).EveryLoop (roleSem M r fns roles) (Permitted M) (Annotation.Bounded ⟨F⟩ header.key (some r))
      path [] (Env.empty.extend inputs values) ∧
    ((project r source).denote (roleSem M r fns roles) path (Env.empty.extend inputs values)).Every
      (Permitted M) (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) := by
  let σ := setting catalog r header.key [] M fns roles [] F
  obtain ⟨loops, run⟩ := checkRole_safe catalog r header (project r source) ⟨[],[]⟩ [] [] accepted
    (projectedAddresses_nodup r source ok.distinct) M fns roles callees rcallees (by simp)
    F recorded path values (((roleSem M r fns roles).dyns_valid_iff values).mpr valid)
    (by simp [Contract.requires]) (noGivenFacts σ rfl _ _ _)
  refine ⟨loops, ?_⟩
  exact Process.every_mono _ _ (fun ys kept => ((roleSem M r fns roles).dyns_valid_iff ys).mp kept.1)
    (fun _ h => h) run

/-- An elaborated protocol supplies address uniqueness for its projection. With an empty role
contract and no annotations, only validity of the actual inputs and the callees is required. -/
theorem checkedProjection_safe (source : Prot V hs header inputs) (ok : ProtocolConditions header source)
    {bounds} (accepted : checkRole catalog r header (project r source) = .ok bounds)
    (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) (rcallees : RCallees M roles)
    (path : List Frame) (values : HList (RV M r) header.ins) (valid : values.All (RV.Valid M r)) :
    ((project r source).denote (roleSem M r fns roles) path (Env.empty.extend inputs values)).Every
      (Permitted M) (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) :=
  (checkedProjection catalog r header source ok accepted M fns roles callees rcallees []
    (by simp) path values valid).2

#print axioms checkedProjection_safe
#print axioms checkRole_safe
end Zkc.Core.BodyAnalysis.RoleContracts
