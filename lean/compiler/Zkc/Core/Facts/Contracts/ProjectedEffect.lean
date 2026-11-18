module

public import Zkc.Core.Facts.Contracts.ProjectedOperations

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts
open HeaderContracts

variable {V : Vocabulary} {hs : Headers V} (M : Model V) (r : Role)
variable (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (catalog : FunctionContracts hs.fns)

/-- A projected call fits the actual ports, runs the callee at the inverse role map and
returns the valid results to the caller at its mapped output ports. -/
theorem application_safe (rcallees : RCallees M roles) {hdr : ProtocolHeader V}
    (callee : Member hs.protocols hdr) (peers : List Role) (distinct : peers.Nodup)
    (covers : peers.length = hdr.roles) (operands : List (LTy V))
    (fits : Fits operands (hdr.ins.map (LTy.map (RoleMap.ofList peers distinct).to)))
    (key : Key) (path : List Frame) (args : HList (RV M r) operands) (valid : args.All (RV.Valid M r)) :
    ((roleSem M r fns roles).op key (.apply callee peers distinct covers operands fits) path args).Every
      (Permitted M) (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) := by
  let roleMap := RoleMap.ofList peers distinct
  change Process.Every (S := RSig M) (Permitted M) _ _ ((mapR M roleMap.to
    (roles _ callee (roleMap.back r) (path ++ [.application key])
      (enterAll M roleMap r (fitAllRV M fits args)))).map (leaveAll M roleMap r))
  rw [every_map, every_mapR]
  exact Process.every_mono _ _ (fun ys v => leaveAll_valid M roleMap r ys v) (fun _ h => h)
    (rcallees _ callee _ _ _ (enterAll_valid M roleMap r _ (fitAllRV_valid M fits args valid)))

theorem effect (callees : Callees M fns) (rcallees : RCallees M roles)
    {ins outs} (op : RoleOp V hs r ins outs) (ordered : roleShared op = false)
    (key : Key) (path : List Frame) (args : HList (RV M r) ins)
    (valid : ∀ v ∈ (roleSem M r fns roles).dyns args, RoleValueValid M r v)
    (required : (rules catalog r).Required (roleSem M r fns roles) (roleReading M r)
      (RoleReturns M r fns roles) (RoleValueValid M r) op args) :
    let sem := roleSem M r fns roles
    (sem.op key op path args).Every (Permitted M)
      (fun ys => (∀ v ∈ sem.dyns ys, RoleValueValid M r v) ∧
        (rules catalog r).Ensured sem (roleReading M r) (RoleReturns M r fns roles)
          (RoleValueValid M r) op args ys)
      (· ≠ .undefined) := by
  dsimp only
  cases op with
  | absent | keep => cases ordered
  | compute R op ins types mine here =>
    subst types
    have c := compute_corr M r fns roles here args
    have eff := (catalog.lawful M fns callees (fun _ _ => True)).effect op ordered key path _
      ((corr_valid c).mp valid) (localRequired mine c required)
    change Process.Every _ _ _ (localOp M fns op (HList.ofLocated M (revealAll M here args))) at eff
    change Process.Every _ _ _ ((liftLocal id (localOp M fns op
      (HList.ofLocated M (revealAll M here args)))).map _)
    cases ran : localOp M fns op (HList.ofLocated M (revealAll M here args)) with
    | done returned =>
      rw [ran] at eff
      obtain ⟨ok, ens⟩ := eff
      have c' : Corr M r ((roleSem M r fns roles).dyns (hideAll M r (HList.located M R returned)))
          ((localSem M hs.fns fns).dyns returned) := by
        rw [located_outputs]
        exact corr_liftAt mine _
      exact ⟨(corr_valid c').mpr ok, roleEnsured mine (corr_append c c') ens⟩
    | halt stop => rw [ran] at eff; exact eff
    | call impossible => cases impossible
  | give kind getters here =>
    obtain ⟨v, rfl⟩ := HList.one args
    intro _ _
    refine ⟨?_, fun _ h => nomatch h⟩
    intro d m
    obtain rfl := List.mem_singleton.mp m
    exact (valid_hide M r (Holders.mem_ofList.mpr (List.mem_append_right _ here)) _).mpr
      (valid _ (List.mem_singleton.mpr rfl) here)
  | get τ H kind giver getters mine =>
    intro x permitted
    refine ⟨?_, fun _ h => nomatch h⟩
    intro d m
    obtain rfl := List.mem_singleton.mp m
    exact (valid_hide M r (Holders.mem_ofList.mpr (List.mem_append_left _ mine)) _).mpr permitted
  | own kind hearers operands τ typed here =>
    intro x permitted
    refine ⟨?_, fun _ h => nomatch h⟩
    intro d m
    obtain rfl := List.mem_singleton.mp m
    apply (valid_hide M r (Holders.mem_ofList.mpr (List.mem_cons_self ..)) _).mpr
    cases kind with
    | request => exact permitted
    | coin => exact permitted.1
  | hear kind owner hearers τ mine =>
    intro x permitted
    refine ⟨?_, fun _ h => nomatch h⟩
    intro d m
    obtain rfl := List.mem_singleton.mp m
    exact (valid_hide M r (Holders.mem_ofList.mpr (List.mem_cons_of_mem _ mine)) _).mpr permitted
  | apply callee peers distinct covers operands fits =>
    exact Process.every_mono _ _ (fun ys v => ⟨((roleSem M r fns roles).dyns_valid_iff ys).mpr v,
      fun _ h => nomatch h⟩) (fun _ h => h)
      (application_safe M r fns roles rcallees callee peers distinct covers _ fits key path args
        (((roleSem M r fns roles).dyns_valid_iff args).mp valid))

end Zkc.Core.BodyAnalysis.RoleContracts
