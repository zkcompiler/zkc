module

public import Zkc.Core.Run.Specialize.AttemptSound
public import Zkc.Core.Scheme.Deploy.Structural

@[expose] public section

/-!
End-to-end soundness of DAG-preserving multi-procedure handler specialization (`specialize_sound`).

Proves:
- CPS soundness for every term constructor (`specializeTerm_sound`, `specializeArms_sound`);
- soundness of inline + DAG-shared protocol specialization (`specializeProtocolInDefs_sound`) and
  bottom-up shared-procedure construction (`buildSharedProcs_sound`);
- soundness of layer-stack specialization (`specializeClauses_sound`, `specializeStack_sound`,
  `stackAgain_eval`, `stackInit_denote`, `stackFinish_denote`);
- top-level theorems `specialize_sound`, `specialize_sound_noRetry`, `specialize_deploy_sound`,
  and `specialize_deployIdeal_sound`.
-/

namespace Zkc.Core

section Soundness
variable {V : Vocabulary} (M : Model V)

/-! ## Level 1: Per-operation CPS soundness (`specializeTerm_sound_*`) -/

private theorem specializeTerm_sound_compute {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = fnTable hdr f)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {insOp outsOp : List V.Ty} {outsTerm : List (LTy V)}
    (key : Key) (R : Holders) (lo : LocalOp V hs.fns insOp outsOp)
    (opTys : List (LTy V)) (types : opTys.map LTy.ty = insOp) (mine : r ∈ R)
    (here : ∀ a ∈ opTys, r ∈ a.holders)
    (operands : HList (Var Γ) opTys) (results : Names (outsOp.map fun τ => ⟨τ, R⟩))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outsTerm)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend results) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.compute R lo opTys types mine here) operands results rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  rw [Term.denote_op]
  conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply (((liftLocal id (localOp M fnTable lo (computeArgs M types (revealAll M here (env.all operands))))).map
      fun outs => hideAll M r (HList.located M R outs)).bind fun vs =>
        rest.denote (roleSem M r fnTable rTable) path (env.extend results vs))).bind cont) s = _
  rw [mapR_bind, mapR_map, mapR_liftLocal, Process.bind_assoc, Process.bind_map,
    handler_run_liftLocal]
  have hArgs : cenv.all (cast (congrArg (HList (Var Δ)) types) (varsAllHeld hCtx here operands)) =
      computeArgs M types (revealAll M here (env.all operands)) := by
    unfold computeArgs
    rw [← env_all_varsAllHeld M hEnv here operands]
    have hc : ∀ {ts₁ ts₂ : List V.Ty} (e : ts₁ = ts₂) (xs : HList (Var Δ) ts₁),
        cenv.all (cast (congrArg (HList (Var Δ)) e) xs) =
          cast (congrArg (HList M.Val) e) (cenv.all xs) := by
      intro _ _ e _; subst e; rfl
    exact hc types _
  rw [hArgs, localOp_lift_eq M fnTable fullTable fnLift hLift, Process.bind_assoc]
  congr 1; funext vs
  have hRest' := hRest path
    (env.extend results (hideAll M r (HList.located M R vs)))
    (cenv.extend (heldNames r results) (heldValues M r (hideAll M r (HList.located M R vs))))
    s cont (hEnv.extend M results _) hPR hWNRest
  rw [hRest']
  have hRes : held r (outsOp.map fun τ => ⟨τ, R⟩) = outsOp := held_map_holders r R mine outsOp
  have hVs : cast (congrArg (HList M.Val) hRes) (heldValues M r (hideAll M r (HList.located M R vs))) = vs := by
    rw [heldValues_hideAll_located M r R mine vs, cast_cast, cast_eq]
  conv => rhs; rw [← hVs, closedTerm_denote_castExt M fullTable procTable hRes (heldNames r results)]

private theorem specializeTerm_sound_absent {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (items : List (LTy V)) (out : ∀ a ∈ items, r ∉ a.holders)
    (results : Names items) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend results) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.absent items out) .nil results rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  rw [Term.denote_op]
  conv => rhs; rw [specializeTerm]; dsimp only
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path (env.extend results (nothings M out)))).bind cont) s = _
  have hEmpty : held r items = [] := held_all_out r items out
  have hExt : Δ.extend (heldNames r results) = Δ := by
    have hNil : cast (congrArg Names hEmpty) (heldNames r results) = .nil := by
      cases cast (congrArg Names hEmpty) (heldNames r results); rfl
    rw [← ctx_extend_cast Δ hEmpty (heldNames r results), hNil]; rfl
  have hCenv : cast (congrArg (Env M.Val) hExt.symm) cenv =
      cenv.extend (heldNames r results) (heldValues M r (nothings M out)) := by
    have hNilN : cast (congrArg Names hEmpty) (heldNames r results) = .nil := by
      cases cast (congrArg Names hEmpty) (heldNames r results); rfl
    have hHeq : HEq (cenv.extend (heldNames r results) (heldValues M r (nothings M out))) cenv := by
      rw [heldValues_nothings M r out]
      have h1 := env_extend_cast cenv hEmpty (heldNames r results)
        (cast (congrArg (HList M.Val) hEmpty.symm) .nil)
      rw [hNilN, cast_cast, cast_eq] at h1
      exact h1.symm
    exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
  rw [closedTerm_denote_castCT, Process.bind_map, hCenv]
  exact hRest path (env.extend results (nothings M out)) _ s cont (hEnv.extend M results _) hPR hWNRest

private theorem specializeTerm_sound_give {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    (hSpec : SpecOpSoundOn M fullTable procTable h specOp pathRel)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} {τ : V.Ty} {H : Holders}
    (key : Key) (kind : FlowKind) (getters : List Role) (here : r ∈ H)
    (x : Var Γ ⟨τ, H⟩) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (getters ++ H)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.give (τ := τ) (H := H) kind getters here) (.cons x .nil) (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  have hIn : r ∈ Holders.ofList (getters ++ H) :=
    Holders.mem_ofList.mpr (List.mem_append_right _ here)
  have hRes : held r [⟨τ, Holders.ofList (getters ++ H)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hExt : Δ.extend (heldNames r (.cons (a := ⟨τ, Holders.ofList (getters ++ H)⟩) resName .nil)) =
      Δ.insert resName τ := by
    rw [heldNames_cons_pos hIn,
      ctx_extend_cast Δ (held_cons_pos r ⟨τ, Holders.ofList (getters ++ H)⟩ [] hIn).symm]; rfl
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through perm r hCtx
        (.op key (.give (τ := τ) (H := H) kind getters here) (.cons x .nil) (.cons resName .nil) rest)).denote
        M fullTable procTable path cenv s =
      ((specOp through key ((ResidualOp.give kind getters τ).mapPeers perm.apply) (.cons (varHeld hCtx x here) .nil)).denote
        M fullTable procTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through perm r
            (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl).denote
          M fullTable procTable path ((cenv.extend .nil out.1).insert resName ((cenv.extend .nil out.1).get (varHeld hCtx x here))) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply ((Process.call (ROp.give kind getters ⟨path, key⟩ τ (reveal M (a := ⟨τ, H⟩) here (env.get x)))
      fun _ => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ (reveal M (a := ⟨τ, H⟩) here (env.get x))) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecG := hSpec through key ((ResidualOp.give kind getters τ).mapPeers perm.apply)
    (.cons (varHeld hCtx x here) .nil) path cenv s hPR
  rw [hSpecG, Process.bind_assoc, Process.bind_map]
  change _ = ((h.clause (ROp.give kind (getters.map perm.apply) ⟨path, key⟩ τ (cenv.get (varHeld hCtx x here))) s).bind fun a =>
    (((specializeTerm specOp fnLift specApply retryCfg through perm r
        (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl).denote
      M fullTable procTable path (cenv.insert resName (cenv.get (varHeld hCtx x here))) a.2).bind
      fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2)
  rw [env_get_varHeld M hEnv x here]
  congr 1; funext out
  have hCenvEq : cast (congrArg (Env M.Val) hExt.symm) (cenv.insert resName (reveal M (a := ⟨τ, H⟩) here (env.get x))) =
      cenv.extend (heldNames r (.cons resName .nil))
        (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ (reveal M (a := ⟨τ, H⟩) here (env.get x))) .nil)) := by
    have hHeq : HEq
        (cenv.extend (heldNames r (.cons resName .nil))
          (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ (reveal M (a := ⟨τ, H⟩) here (env.get x))) .nil)))
        (cenv.insert resName (reveal M (a := ⟨τ, H⟩) here (env.get x))) := by
      rw [heldNames_cons_pos hIn, heldValues_cons_pos M hIn, reveal_hide]
      exact env_extend_cast cenv hRes.symm (HList.cons resName .nil)
        (HList.cons (reveal M (a := ⟨τ, H⟩) here (env.get x)) .nil)
    exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
  rw [closedTerm_denote_castCT, Process.bind_map, hCenvEq]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPR hWNRest

private theorem specializeTerm_sound_get {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    (hSpec : SpecOpSoundOn M fullTable procTable h specOp pathRel)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (τ : V.Ty) (H : Holders)
    (kind : FlowKind) (giver : Role) (getters : List Role) (mine : r ∈ getters)
    (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (getters ++ H)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.get τ H kind giver getters mine) .nil (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  have hIn : r ∈ Holders.ofList (getters ++ H) :=
    Holders.mem_ofList.mpr (List.mem_append_left _ mine)
  have hRes : held r [⟨τ, Holders.ofList (getters ++ H)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through perm r hCtx
        (.op key (.get τ H kind giver getters mine) .nil (.cons resName .nil) rest)).denote
        M fullTable procTable path cenv s =
      ((specOp through key ((ResidualOp.get kind giver τ).mapPeers perm.apply) .nil).denote
        M fullTable procTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through perm r
            (hCtx.extend (.cons resName .nil)) rest).castCT
          (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl).denote
          M fullTable procTable path
          (cenv.extend (cast (congrArg Names hRes) (heldNames r (.cons resName .nil))) out.1) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply ((Process.call (ROp.get kind giver ⟨path, key⟩ τ)
      fun v => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ v) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecG := hSpec through key ((ResidualOp.get kind giver τ).mapPeers perm.apply)
    .nil path cenv s hPR
  rw [hSpecG, Process.bind_assoc, Process.bind_map]
  dsimp only [ResidualOp.mapPeers, ResidualOp.toROp, Env.all, ResidualOp.replyOf]
  congr 1; funext out
  have hOutEq : cast (congrArg (HList M.Val) hRes)
      (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ out.1) .nil)) =
      .cons out.1 .nil := by
    rw [heldValues_cons_pos M hIn, reveal_hide, cast_cast]; rfl
  conv => rhs; rw [← hOutEq, closedTerm_denote_castExt M fullTable procTable hRes (heldNames r (.cons resName .nil))]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPR hWNRest

private theorem specializeTerm_sound_keep {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} {τ : V.Ty} {H : Holders}
    (key : Key) (H' : Holders) (same : r ∈ H ↔ r ∈ H')
    (x : Var Γ ⟨τ, H⟩) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, H'⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.keep (τ := τ) (H := H) H' same) (.cons x .nil) (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  rw [Term.denote_op]
  conv => rhs; rw [specializeTerm]; dsimp only
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path
      (env.extend (.cons resName .nil) (.cons (carry M same (env.get x)) .nil)))).bind cont) s = _
  by_cases hIn : r ∈ H
  · rw [dite_eq_left hIn]
    conv => rhs; rw [ClosedTerm.denote]
    have hIn' : r ∈ H' := same.mp hIn
    have hExt : Δ.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil)) = Δ.insert resName τ := by
      rw [heldNames_cons_pos hIn', ctx_extend_cast Δ (held_cons_pos r ⟨τ, H'⟩ [] hIn').symm]; rfl
    have hRevCarry : reveal M hIn' (carry M same (env.get x)) = reveal M hIn (env.get x) := by
      simp [reveal, carry]
    have hCenvEq : cast (congrArg (Env M.Val) hExt.symm) (cenv.insert resName (cenv.get (varHeld hCtx x hIn))) =
        cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
          (heldValues M r (.cons (carry M same (env.get x)) .nil)) := by
      rw [env_get_varHeld M hEnv x hIn, ← hRevCarry]
      have hHeq : HEq
          (cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
            (heldValues M r (.cons (carry M same (env.get x)) .nil)))
          (cenv.insert resName (reveal M hIn' (carry M same (env.get x)))) := by
        rw [heldNames_cons_pos hIn', heldValues_cons_pos M hIn']
        exact env_extend_cast cenv (held_cons_pos r ⟨τ, H'⟩ [] hIn').symm (HList.cons resName .nil)
          (HList.cons (reveal M hIn' (carry M same (env.get x))) .nil)
      exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
    rw [closedTerm_denote_castCT, Process.bind_map, hCenvEq]
    exact hRest path _ _ s cont (hEnv.extend M (.cons resName .nil) _) hPR hWNRest
  · rw [dite_eq_right hIn]
    have hOut' : r ∉ H' := fun m => hIn (same.mpr m)
    have hExt : Δ.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil)) = Δ := by
      rw [heldNames_cons_neg hOut', ctx_extend_cast Δ (held_cons_neg r ⟨τ, H'⟩ [] hOut').symm]; rfl
    have hCenvEq : cast (congrArg (Env M.Val) hExt.symm) cenv =
        cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
          (heldValues M r (.cons (carry M same (env.get x)) .nil)) := by
      have hHeq : HEq
          (cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
            (heldValues M r (.cons (carry M same (env.get x)) .nil))) cenv := by
        rw [heldNames_cons_neg hOut', heldValues_cons_neg M hOut']
        exact env_extend_cast cenv (held_cons_neg r ⟨τ, H'⟩ [] hOut').symm .nil .nil
      exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
    rw [closedTerm_denote_castCT, Process.bind_map, hCenvEq]
    exact hRest path _ _ s cont (hEnv.extend M (.cons resName .nil) _) hPR hWNRest

private theorem specializeTerm_sound_own {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    (hSpec : SpecOpSoundOn M fullTable procTable h specOp pathRel)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (kind : GivenKind V) (hearers : List Role)
    (opTys : List (LTy V)) (τ : V.Ty) (typed : kind.Typed (opTys.map LTy.ty) τ)
    (here : ∀ a ∈ opTys, r ∈ a.holders) (operands : HList (Var Γ) opTys) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (r :: hearers)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.own kind hearers opTys τ typed here) operands (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  have hIn : r ∈ Holders.ofList (r :: hearers) := Holders.mem_ofList.mpr List.mem_cons_self
  have hRes : held r [⟨τ, Holders.ofList (r :: hearers)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through perm r hCtx
        (.op key (.own kind hearers opTys τ typed here) operands (.cons resName .nil) rest)).denote
        M fullTable procTable path cenv s =
      ((specOp through key ((ResidualOp.own kind hearers (opTys.map LTy.ty) τ).mapPeers perm.apply)
          (varsAllHeld hCtx here operands)).denote
        M fullTable procTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through perm r
            (hCtx.extend (.cons resName .nil)) rest).castCT
          (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl).denote
          M fullTable procTable path
          (cenv.extend (cast (congrArg Names hRes) (heldNames r (.cons resName .nil))) out.1) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply ((Process.call (ROp.own kind hearers ⟨path, key⟩ (opTys.map LTy.ty)
        (HList.ofLocated M (revealAll M here (env.all operands))) τ)
      fun v => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (r :: hearers)⟩ v) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecO := hSpec through key
    ((ResidualOp.own kind hearers (opTys.map LTy.ty) τ).mapPeers perm.apply)
    (varsAllHeld hCtx here operands) path cenv s hPR
  rw [hSpecO, Process.bind_assoc, Process.bind_map]
  dsimp only [ResidualOp.mapPeers, ResidualOp.toROp, ResidualOp.replyOf]
  rw [env_all_varsAllHeld M hEnv here operands]
  congr 1; funext out
  have hOutEq : cast (congrArg (HList M.Val) hRes)
      (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (r :: hearers)⟩ out.1) .nil)) =
      .cons out.1 .nil := by
    rw [heldValues_cons_pos M hIn, reveal_hide, cast_cast]; rfl
  conv => rhs; rw [← hOutEq, closedTerm_denote_castExt M fullTable procTable hRes (heldNames r (.cons resName .nil))]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPR hWNRest

private theorem specializeTerm_sound_hear {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    (hSpec : SpecOpSoundOn M fullTable procTable h specOp pathRel)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (kind : GivenKind V) (owner : Role) (hearers : List Role)
    (τ : V.Ty) (mine : r ∈ hearers) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (owner :: hearers)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.hear kind owner hearers τ mine) .nil (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  have hIn : r ∈ Holders.ofList (owner :: hearers) :=
    Holders.mem_ofList.mpr (List.mem_cons_of_mem _ mine)
  have hRes : held r [⟨τ, Holders.ofList (owner :: hearers)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through perm r hCtx
        (.op key (.hear kind owner hearers τ mine) .nil (.cons resName .nil) rest)).denote
        M fullTable procTable path cenv s =
      ((specOp through key ((ResidualOp.hear kind owner τ).mapPeers perm.apply) .nil).denote
        M fullTable procTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through perm r
            (hCtx.extend (.cons resName .nil)) rest).castCT
          (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl).denote
          M fullTable procTable path
          (cenv.extend (cast (congrArg Names hRes) (heldNames r (.cons resName .nil))) out.1) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply ((Process.call (ROp.hear kind owner ⟨path, key⟩ τ)
      fun v => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (owner :: hearers)⟩ v) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecH := hSpec through key ((ResidualOp.hear kind owner τ).mapPeers perm.apply)
    .nil path cenv s hPR
  rw [hSpecH, Process.bind_assoc, Process.bind_map]
  dsimp only [ResidualOp.mapPeers, ResidualOp.toROp, Env.all, ResidualOp.replyOf]
  congr 1; funext out
  have hOutEq : cast (congrArg (HList M.Val) hRes)
      (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (owner :: hearers)⟩ out.1) .nil)) =
      .cons out.1 .nil := by
    rw [heldValues_cons_pos M hIn, reveal_hide, cast_cast]; rfl
  conv => rhs; rw [← hOutEq, closedTerm_denote_castExt M fullTable procTable hRes (heldNames r (.cons resName .nil))]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPR hWNRest

private theorem specializeTerm_sound_apply {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ)
    (pathRel : List Key → List Frame → Prop) (hPRClosed : PathRelClosed pathRel)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (retryAllowed : Option (Nat × Site × StackAgain V fullFns σ) → Prop)
    (hApply : SpecApplySound M fullTable procTable h pathRel retryAllowed rTable specApply)
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    (hRC : RetryCfgOk M fullTable h retryCfg)
    (hRAllow : retryAllowed retryCfg)
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} {hdr : ProtocolHeader V}
    (key : Key) (callee : Member hs.protocols hdr) (roles : List Role)
    (distinct : roles.Nodup) (covers : roles.length = hdr.roles)
    (opTys : List (LTy V)) (fits : Fits opTys (hdr.ins.map (LTy.map (RoleMap.ofList roles distinct).to)))
    (operands : HList (Var Γ) opTys)
    (results : Names (hdr.outs.map (LTy.map (RoleMap.ofList roles distinct).to)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend results) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.op key (.apply callee roles distinct covers opTys fits) operands results rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩
  rw [Term.denote_op]
  let rm := RoleMap.ofList roles distinct
  let perm' := perm.comp (FinPerm.ofList roles distinct)
  have hPermEq : ∀ q, perm'.apply q = perm.apply (rm.to q) := fun q => by
    dsimp only [perm', rm]
    rw [FinPerm.apply_comp, FinPerm.apply_ofList]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply (((mapR M rm.to (rTable hdr callee (rm.back r) (path ++ [Frame.application key])
      (enterAll M rm r (fitAllRV M fits (env.all operands))))).map (leaveAll M rm r)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend results vs))).bind cont) s = _
  rw [mapR_bind, mapR_map, mapR_comp, Process.bind_assoc, Process.bind_map,
    ← mapR_congr M hPermEq]
  have hPR' : pathRel (through ++ [key]) (path ++ [Frame.application key]) := hPRClosed.app through key path hPR
  have hCalWN : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications (path ++ [Frame.application key]) = through ++ [key] ∧
        Shape.noNestedAttempt site (through ++ [key]) hdr.shape = true :=
    fun b site ag hc => ⟨by rw [Frame.applications_append, (hWN b site ag hc).1]; rfl, (hWN b site ag hc).2.1⟩
  have hApp := hApply retryCfg hRC hRAllow callee (through ++ [key]) perm' (rm.back r)
    (path ++ [Frame.application key]) (enterAll M rm r (fitAllRV M fits (env.all operands))) s
    (fun a => (mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path
      (env.extend results (leaveAll M rm r a)))).bind cont) hPR' hCalWN
  rw [hApp]
  conv => rhs; rw [specializeTerm]; dsimp only
  have hOut : held r (hdr.outs.map (LTy.map rm.to)) = held (rm.back r) hdr.outs :=
    held_map_roleMap rm r hdr.outs
  have hTail : ∀ (out : HList M.Val (held (rm.back r) hdr.outs) × HList M.Val σ),
      h.run (retryOfCfg M retryCfg)
        ((mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path
          (env.extend results (leaveAll M rm r (unheldValues M (rm.back r) out.1))))).bind cont) out.2 =
      (((specializeTerm specOp fnLift specApply retryCfg through perm r (hCtx.extend results) rest).castCT
          (ctx_extend_cast Δ hOut (heldNames r results)).symm rfl).denote
        M fullTable procTable path (cenv.extend (cast (congrArg Names hOut) (heldNames r results)) out.1) out.2).bind
        fun out2 => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out2.1)) out2.2 := by
    intro out
    have hLeave : cast (congrArg (HList M.Val) hOut)
        (heldValues M r (leaveAll M rm r (unheldValues M (rm.back r) out.1))) = out.1 := by
      rw [heldValues_leaveAll, heldValues_unheldValues, cast_cast, cast_eq]
    conv => rhs; rw [← hLeave, closedTerm_denote_castExt M fullTable procTable hOut (heldNames r results)]
    exact hRest path (env.extend results (leaveAll M rm r (unheldValues M (rm.back r) out.1)))
      _ out.2 cont (hEnv.extend M results _) hPR hWNRest
  cases hTgt : specApply retryCfg callee (through ++ [key]) perm' (rm.back r) with
  | shared mem =>
      dsimp only
      rw [ClosedTerm.denote, env_all_fitVars M hEnv rm fits operands, Process.bind_assoc]
      congr 1; funext out; exact hTail out
  | inlined calleeIns calleeBody =>
      dsimp only
      rw [ClosedTerm.denote, env_all_fitVars M hEnv rm fits operands, Process.bind_assoc]
      congr 1; funext out; exact hTail out

private theorem specializeTerm_sound_choose {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (pathRel : List Key → List Frame → Prop)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs mid : List (LTy V)} {t : LTy V}
    (key : Key) (w : Holders) (c : Var Γ t) (ok : t.ty = .bool ∧ r ∈ t.holders ∧ r ∈ w)
    (gives : ∀ a, a ∈ mid → (roleDialect V hs r).Gives w a)
    (onTrue onFalse : Term (roleDialect V hs r) Γ mid)
    (results : Names mid) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hTrue : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx onTrue)
    (hFalse : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx onFalse)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend results) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.choose key w c ok gives onTrue onFalse results rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  rw [Term.denote_choose]
  conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M perm.apply ((bif asBool M ok.1 (reveal M ok.2.1 (env.get c)) then
      onTrue.denote (roleSem M r fnTable rTable) path env
    else onFalse.denote (roleSem M r fnTable rTable) path env).bind
      fun mids => rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s = _
  have hBool : cenv.get (cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)) =
      asBool M ok.1 (reveal M ok.2.1 (env.get c)) := by
    unfold asBool
    rw [← env_get_varHeld M hEnv c ok.2.1]
    have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
        cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
      intro _ _ e _; subst e; rfl
    exact hc ok.1 _
  rw [hBool, mapR_bind, Process.bind_assoc, Process.bind_assoc]
  cases asBool M ok.1 (reveal M ok.2.1 (env.get c)) with
  | false =>
      dsimp only [cond]
      rw [hFalse path env cenv s _ hEnv hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2.1⟩)]
      congr 1; funext out
      have hEx := hEnv.extend M results (unheldValues M r out.1)
      rw [heldValues_unheldValues] at hEx
      exact hRest path _ _ out.2 cont hEx hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2.2⟩)
  | true =>
      dsimp only [cond]
      rw [hTrue path env cenv s _ hEnv hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.1⟩)]
      congr 1; funext out
      have hEx := hEnv.extend M results (unheldValues M r out.1)
      rw [heldValues_unheldValues] at hEx
      exact hRest path _ _ out.2 cont hEx hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2.2⟩)

private theorem specializeTerm_sound_loop {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ)
    (pathRel : List Key → List Frame → Prop) (hPRClosed : PathRelClosed pathRel)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
    (through : List Key) (perm : FinPerm) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs carried each : List (LTy V)}
    (key : Key) (ps : Holders) (times : Times (roleDialect V hs r) ps Γ)
    (gives : ∀ a, a ∈ carried ++ each → (roleDialect V hs r).Gives ps a)
    (initial : HList (Var Γ) carried)
    (idxNm : Name) (carriedInNames : Names carried)
    (body : Term (roleDialect V hs r) (Γ.extend (.cons (a := LTy.index ps) idxNm carriedInNames)) (carried ++ each))
    (results : Names (carried ++ each.map (LTy.collected times.size)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hBody : ∀ {ΔB : Ctx V.Ty} (hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index ps) idxNm carriedInNames)) ΔB),
      SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
        through perm r retryCfg hCtxB body)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg (hCtx.extend results) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
      through perm r retryCfg hCtx
      (.loop key ps times gives initial (.cons idxNm carriedInNames) body results rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  rw [Term.denote_loop]
  conv => rhs; rw [specializeTerm]; dsimp only
  rw [mapR_bind, Process.bind_assoc]
  have hTimesEq : (specializeTimes hCtx times).eval M cenv =
      (roleSem M r fnTable rTable).times times env := by
    cases times with
    | fixed _ => rfl
    | value cnt ok =>
        dsimp only [specializeTimes, ClosedTimes.eval, Semantics.times, roleSem, asNat]
        rw [← env_get_varHeld M hEnv cnt ok.2.1]
        have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
            cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
          intro _ _ e _; subst e; rfl
        exact hc ok.1 _
  have hSize : (specializeTimes hCtx times).size = times.size := specializeTimes_size hCtx times
  have hBodyOut : held r (carried ++ each) = held r carried ++ held r each :=
    held_append r carried each
  have hResTy : held r (carried ++ each.map (LTy.collected times.size)) =
      held r carried ++ (held r each).map (fun τ => .seq τ (specializeTimes hCtx times).size) := by
    rw [held_append, held_map_collected, hSize]
  have hLoopProof : ∀ (idxOpt : Option Name)
      (hCtxB : CtxRel r (Γ.extend (.cons idxNm carriedInNames))
        (loopBodyCtx Δ idxOpt (heldNames r carriedInNames)))
      (hEnvStep : ∀ (i : Nat) (cv : HList (RV M r) carried),
        EnvRel M r hCtxB
          (env.extend (.cons idxNm carriedInNames) (.cons (hide M r (LTy.index ps) i) cv))
          (loopBodyEnv M cenv idxOpt i (heldNames r carriedInNames) (heldValues M r cv))),
      h.run (retryOfCfg M retryCfg)
        ((mapR M perm.apply (Process.iterate ((roleSem M r fnTable rTable).times times env)
            ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
              (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
              key path env)
            0 (env.all initial, HList.empties each))).bind fun ls =>
          (mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path
            (env.extend results (ls.1.append ((roleSem M r fnTable rTable).collected times.size ls.2))))).bind cont) s =
      ((ClosedTerm.loop key (specializeTimes hCtx times) (varsHeld hCtx initial) idxOpt
          (heldNames r carriedInNames)
          ((specializeTerm specOp fnLift specApply retryCfg through perm r hCtxB body).castCT rfl hBodyOut)
          (cast (congrArg Names hResTy) (heldNames r results))
          ((specializeTerm specOp fnLift specApply retryCfg through perm r (hCtx.extend results) rest).castCT
            (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl)).denote
        M fullTable procTable path cenv s).bind fun out =>
        h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2 := by
    intro idxOpt hCtxB hEnvStep
    conv => rhs; rw [ClosedTerm.denote]
    rw [hTimesEq, env_all_varsHeld M hEnv initial, ← heldAcc_empties M r each, Process.bind_assoc]
    let n0 := (roleSem M r fnTable rTable).times times env
    suffices hIter : ∀ (n i : Nat)
        (ls : HList (RV M r) carried × HList (fun a => List (RV M r a)) each)
        (st0 : HList M.Val σ),
        h.run (retryOfCfg M retryCfg)
          ((mapR M perm.apply (Process.iterate n
              ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
                (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
                key path env)
              i ls)).bind fun lsEnd =>
            (mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path
              (env.extend results (lsEnd.1.append ((roleSem M r fnTable rTable).collected times.size lsEnd.2))))).bind cont) st0 =
        (Process.iterate n
            (fun j (cls : (HList M.Val (held r carried) × HList (fun τ => List (M.Val τ)) (held r each)) × HList M.Val σ) =>
              (((specializeTerm specOp fnLift specApply retryCfg through perm r hCtxB body).castCT rfl hBodyOut).denote
                  M fullTable procTable (path ++ [Frame.iteration key j])
                  (loopBodyEnv M cenv idxOpt j (heldNames r carriedInNames) cls.1.1) cls.2).bind fun out =>
                let sp := HList.split (held r carried) out.1
                .done ((sp.1, cls.1.2.push sp.2), out.2))
            i ((heldValues M r ls.1, heldAcc M r ls.2), st0)).bind fun clsEnd =>
          (((specializeTerm specOp fnLift specApply retryCfg through perm r (hCtx.extend results) rest).castCT
              (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl).denote
            M fullTable procTable path
            (cenv.extend (cast (congrArg Names hResTy) (heldNames r results))
              (clsEnd.1.1.append (closedCollected M (specializeTimes hCtx times).size clsEnd.1.2)))
            clsEnd.2).bind fun out =>
            h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2 from
      hIter n0 0 (env.all initial, HList.empties each) s
    intro n
    induction n with
    | zero =>
        intro i ls st0
        dsimp only [Process.iterate, mapR, Process.bind]
        have hValEq : cast (congrArg (HList M.Val) hResTy)
            (heldValues M r (ls.1.append ((roleSem M r fnTable rTable).collected times.size ls.2))) =
            (heldValues M r ls.1).append (closedCollected M (specializeTimes hCtx times).size (heldAcc M r ls.2)) := by
          rw [heldValues_append, heldValues_collected M fnTable rTable]
          have hValCast : ∀ {s1 s2 : Option Nat} (hs : s2 = s1)
              {ts1 ts2 : List V.Ty}
              (h1 : ts1 = held r carried ++ ts2)
              (h2 : ts2 = (held r each).map (fun τ => .seq τ s1))
              (hr : ts1 = held r carried ++ (held r each).map (fun τ => .seq τ s2))
              (x : HList M.Val (held r carried)) (y : HList (fun τ => List (M.Val τ)) (held r each)),
              cast (congrArg (HList M.Val) hr)
                (cast (congrArg (HList M.Val) h1.symm)
                  (x.append (cast (congrArg (HList M.Val) h2.symm) (closedCollected M s1 y)))) =
                x.append (closedCollected M s2 y) := by
            intro _ _ hs _ _ h1 h2 hr _ _; subst hs; subst h2; subst h1; rfl
          exact hValCast hSize (held_append _ _ _) (held_map_collected _ _ _) hResTy _ _
        rw [← hValEq, closedTerm_denote_castExt M fullTable procTable hResTy (heldNames r results)]
        exact hRest path _ _ st0 cont (hEnv.extend M results _) hPR
          (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩)
    | succ m ihM =>
        intro i ls st0
        dsimp only [Process.iterate, Semantics.loopStep]
        change h.run (retryOfCfg M retryCfg)
          ((mapR M perm.apply (((body.denote (roleSem M r fnTable rTable) (path ++ [Frame.iteration key i])
              (env.extend (.cons idxNm carriedInNames) (.cons (hide M r (LTy.index ps) i) ls.1))).bind
            fun a => Process.done ((HList.split carried a).1, ls.2.push (HList.split carried a).2)).bind
            fun a2 => Process.iterate m
              ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
                (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
                key path env) (i + 1) a2)).bind fun lsEnd =>
            (mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path
              (env.extend results (lsEnd.1.append ((roleSem M r fnTable rTable).collected times.size lsEnd.2))))).bind cont) st0 = _
        rw [mapR_bind, mapR_bind, Process.bind_assoc, Process.bind_assoc, Process.bind_assoc,
          closedTerm_denote_castCT, cast_eq, Process.bind_map, Process.bind_assoc]
        have hPRI : pathRel through (path ++ [Frame.iteration key i]) := hPRClosed.iter through key i path hPR
        have hStepBody := hBody hCtxB (path ++ [Frame.iteration key i])
          (env.extend (.cons idxNm carriedInNames) (.cons (hide M r (LTy.index ps) i) ls.1))
          (loopBodyEnv M cenv idxOpt i (heldNames r carriedInNames) (heldValues M r ls.1)) st0
          (fun a =>
            (mapR M perm.apply (Process.done ((HList.split carried a).1, ls.2.push (HList.split carried a).2))).bind fun a2 =>
              (mapR M perm.apply (Process.iterate m
                ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
                  (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
                  key path env) (i + 1) a2)).bind fun lsEnd =>
                (mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path
                  (env.extend results (lsEnd.1.append ((roleSem M r fnTable rTable).collected times.size lsEnd.2))))).bind cont)
          (hEnvStep i ls.1) hPRI
          (fun b site ag hc => ⟨by rw [Frame.applications_append, (hWN b site ag hc).1]; exact List.append_nil _, (hWN b site ag hc).2.1⟩)
        rw [hStepBody]
        congr 1; funext out
        dsimp only [mapR, Process.bind]
        have hSp := heldValues_split M r (unheldValues M r out.1)
        rw [heldValues_unheldValues] at hSp
        rw [hSp.1, hSp.2, ← heldAcc_push M r ls.2]
        exact ihM (i + 1) _ out.2
  by_cases hIn : r ∈ ps
  · rw [dite_eq_left hIn]
    refine hLoopProof (some idxNm) _ fun i cv => ?_
    have h1 := (hEnv.insert_held M idxNm (a := LTy.index ps) hIn (hide M r (LTy.index ps) i)).extend M carriedInNames cv
    rw [reveal_hide] at h1
    exact h1
  · rw [dite_eq_right hIn]
    refine hLoopProof none _ fun i cv => ?_
    exact (hEnv.insert_unheld M idxNm (a := LTy.index ps) hIn (hide M r (LTy.index ps) i)).extend M carriedInNames cv

mutual
  theorem specializeTerm_sound {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
      (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
      {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
      (specOp : EffectSpecializer V fullFns procs σ)
      (pathRel : List Key → List Frame → Prop) (hPRClosed : PathRelClosed pathRel)
      (hSpec : SpecOpSoundOn M fullTable procTable h specOp pathRel)
      {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
      (hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = fnTable hdr f)
      (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
        {hdr : ProtocolHeader V} → Member hs.protocols hdr →
        List Key → FinPerm → (r : Role) →
        ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
      (retryAllowed : Option (Nat × Site × StackAgain V fullFns σ) → Prop)
      (hRAllowNone : retryAllowed none)
      (hApply : SpecApplySound M fullTable procTable h pathRel retryAllowed rTable specApply)
      (through : List Key) (perm : FinPerm) (r : Role) :
      ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
        RetryCfgOk M fullTable h retryCfg →
        retryAllowed retryCfg →
        ∀ {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
          {outs : List (LTy V)} (t : Term (roleDialect V hs r) Γ outs),
          SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
            through perm r retryCfg hCtx t
    | retryCfg, _, _, Γ, Δ, hCtx, _, .ret exit => fun path env cenv s _ cont hEnv _ _ => by
        rw [Term.denote_ret, specializeTerm, ClosedTerm.denote]
        dsimp only [mapR, Process.bind]
        rw [env_all_varsHeld M hEnv exit, unheldValues_heldValues]
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.compute R lo opTys types mine here) operands results rest =>
        specializeTerm_sound_compute M fullTable procTable h specOp pathRel fnTable rTable fnLift hLift specApply
          through perm r retryCfg hCtx key R lo opTys types mine here operands results rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend results) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.absent items out) .nil results rest =>
        specializeTerm_sound_absent M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key items out results rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend results) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.give kind getters here) (.cons x .nil) (.cons resName .nil) rest =>
        specializeTerm_sound_give M fullTable procTable h specOp pathRel hSpec fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key kind getters here x resName rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend (.cons resName .nil)) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.get τ H kind giver getters mine) .nil (.cons resName .nil) rest =>
        specializeTerm_sound_get M fullTable procTable h specOp pathRel hSpec fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key τ H kind giver getters mine resName rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend (.cons resName .nil)) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.keep H' same) (.cons x .nil) (.cons resName .nil) rest =>
        specializeTerm_sound_keep M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key H' same x resName rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend (.cons resName .nil)) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.own kind hearers opTys τ typed here) operands (.cons resName .nil) rest =>
        specializeTerm_sound_own M fullTable procTable h specOp pathRel hSpec fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key kind hearers opTys τ typed here operands resName rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend (.cons resName .nil)) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.hear kind owner hearers τ mine) .nil (.cons resName .nil) rest =>
        specializeTerm_sound_hear M fullTable procTable h specOp pathRel hSpec fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key kind owner hearers τ mine resName rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend (.cons resName .nil)) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .op key (.apply callee roles distinct covers opTys fits) operands results rest =>
        specializeTerm_sound_apply M fullTable procTable h specOp pathRel hPRClosed fnTable rTable fnLift
          specApply retryAllowed hApply
          through perm r retryCfg hRC hRAllow hCtx key callee roles distinct covers opTys fits operands results rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend results) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .guard key w c ok why rest => fun path env cenv s _ cont hEnv hPR hWN => by
        rw [Term.denote_guard]
        conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
        change h.run (retryOfCfg M retryCfg)
          ((mapR M perm.apply (bif asBool M ok.1 (reveal M ok.2.1 (env.get c)) then
            rest.denote (roleSem M r fnTable rTable) path env
          else Process.halt (.declared why ⟨path, key⟩))).bind cont) s = _
        have hBool : cenv.get (cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)) =
            asBool M ok.1 (reveal M ok.2.1 (env.get c)) := by
          unfold asBool
          rw [← env_get_varHeld M hEnv c ok.2.1]
          have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
              cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
            intro _ _ e _; subst e; rfl
          exact hc ok.1 _
        rw [hBool]
        cases asBool M ok.1 (reveal M ok.2.1 (env.get c)) with
        | false => rfl
        | true =>
            exact specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
              specApply retryAllowed hRAllowNone hApply
              through perm r retryCfg hRC hRAllow hCtx rest path env cenv s cont hEnv hPR hWN
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .choose key w c ok gives onTrue onFalse results rest =>
        specializeTerm_sound_choose M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key w c ok gives onTrue onFalse results rest
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow hCtx onTrue)
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow hCtx onFalse)
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend results) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .cases (t := t) (payloads := payloads) key ps x ok gives arms results rest =>
        fun path env cenv s _ cont hEnv hPR hWN => by
        rw [Term.denote_cases]
        conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
        change h.run (retryOfCfg M retryCfg)
          ((mapR M perm.apply ((arms.denote (roleSem M r fnTable rTable) path env (rolePick M r ok (env.get x))).bind
            fun mids => rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s = _
        rw [mapR_bind, Process.bind_assoc, Process.bind_assoc]
        have hv : ∃ k alts, t.ty = .variant k alts ∧ payloads = alts.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨k, alts, he, hp, _⟩ := ok; exact ⟨k, alts, he, hp⟩
        have hEq : t.ty = .variant t.ty.variantKey t.ty.alternatives := Ty.eq_variant hv
        have hPay : payloads = t.ty.alternatives.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨_, alts, he, hp⟩ := hv; rw [Ty.alternatives_of he, hp]
        have hrT : r ∈ t.holders := by obtain ⟨_, _, _, _, h1, _⟩ := ok; exact h1
        have hrPs : r ∈ ps := by obtain ⟨_, _, _, _, _, h2⟩ := ok; exact h2
        have hVal : cenv.get (cast (congrArg (Var Δ) hEq) (varHeld hCtx x hrT)) =
            cast (congrArg M.Val hEq) (reveal M hrT (env.get x)) := by
          rw [← env_get_varHeld M hEnv x hrT]
          have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
              cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
            intro _ _ e _; subst e; rfl
          exact hc hEq _
        rw [hVal]
        have hPickEq : rolePick M r ok (env.get x) =
            cast (congrArg (Pick (RV M r)) hPay.symm)
              (liftPick M r ps (Tys.pick M t.ty.alternatives
                (cast (congrArg M.Val hEq) (reveal M hrT (env.get x))))) := by
          dsimp only [rolePick, locatedPick]
          rw [pickAt_eq_liftPick M r ps]
        rw [hPickEq]
        rw [specializeArms_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
          specApply retryAllowed hRAllowNone hApply
          through perm r retryCfg hRC hRAllow ps hrPs hCtx arms hPay path env cenv s _ _ hEnv hPR
          (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.1⟩)]
        congr 1; funext out
        have hEx := hEnv.extend M results (unheldValues M r out.1)
        rw [heldValues_unheldValues] at hEx
        exact specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
          specApply retryAllowed hRAllowNone hApply
          through perm r retryCfg hRC hRAllow (hCtx.extend results) rest path _ _ out.2 cont
          hEx hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .loop key ps times gives initial (.cons idxNm carriedInNames) body results rest =>
        specializeTerm_sound_loop M fullTable procTable h specOp pathRel hPRClosed fnTable rTable fnLift specApply
          through perm r retryCfg hCtx key ps times gives initial idxNm carriedInNames body results rest
          (fun hCtxB => specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow hCtxB body)
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend results) rest)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .block key number body results rest =>
        fun path env cenv s _ cont hEnv hPR hWN => by
        rw [Term.denote_block]
        conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
        rw [mapR_bind, Process.bind_assoc, Process.bind_assoc]
        have hPRB : pathRel through (path ++ [Frame.iteration key number]) := hPRClosed.iter through key number path hPR
        have hBodyS := specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
          specApply retryAllowed hRAllowNone hApply
          through perm r retryCfg hRC hRAllow hCtx body (path ++ [Frame.iteration key number]) env cenv s
          (fun a => (mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path (env.extend results a))).bind cont)
          hEnv hPRB (fun b site ag hc => ⟨by rw [Frame.applications_append, (hWN b site ag hc).1]; exact List.append_nil _, (hWN b site ag hc).2.1⟩)
        rw [hBodyS]
        congr 1; funext out
        have hEx := hEnv.extend M results (unheldValues M r out.1)
        rw [heldValues_unheldValues] at hEx
        exact specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
          specApply retryAllowed hRAllowNone hApply
          through perm r retryCfg hRC hRAllow (hCtx.extend results) rest path _ _ out.2 cont
          hEx hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2⟩)
    | retryCfg, hRC, hRAllow, Γ, Δ, hCtx, _, .attempt key w owns (.cons idxNm .nil) body results rest =>
        specializeTerm_sound_attempt M fullTable procTable h specOp pathRel hSpec fnTable rTable fnLift specApply
          through perm r retryCfg hRC hCtx key w owns idxNm body results rest
          (fun hCtxB => specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow hCtxB body)
          (fun hCtxB => specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r none trivial hRAllowNone hCtxB body)
          (specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
            specApply retryAllowed hRAllowNone hApply
            through perm r retryCfg hRC hRAllow (hCtx.extend results) rest)

  theorem specializeArms_sound {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
      (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
      {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
      (specOp : EffectSpecializer V fullFns procs σ)
      (pathRel : List Key → List Frame → Prop) (hPRClosed : PathRelClosed pathRel)
      (hSpec : SpecOpSoundOn M fullTable procTable h specOp pathRel)
      {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
      (hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = fnTable hdr f)
      (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
        {hdr : ProtocolHeader V} → Member hs.protocols hdr →
        List Key → FinPerm → (r : Role) →
        ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))
      (retryAllowed : Option (Nat × Site × StackAgain V fullFns σ) → Prop)
      (hRAllowNone : retryAllowed none)
      (hApply : SpecApplySound M fullTable procTable h pathRel retryAllowed rTable specApply)
      (through : List Key) (perm : FinPerm) (r : Role) :
      ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
        RetryCfgOk M fullTable h retryCfg →
        retryAllowed retryCfg →
        ∀ (ps : Holders) (hrPs : r ∈ ps)
          {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
          {mid payloads : List (LTy V)} (arms : Arms (roleDialect V hs r) Γ mid payloads)
          {alts : List V.Ty} (hPay : payloads = alts.map fun τ => ⟨τ, ps⟩)
          (path : List Frame) (env : Env (RV M r) Γ) (cenv : Env M.Val Δ) (s : HList M.Val σ)
          (pkVal : Pick M.Val alts)
          {B : Type} (cont : HList (RV M r) mid → Program M B),
          EnvRel M r hCtx env cenv →
          pathRel through path →
          (∀ b site ag, retryCfg = some (b, site, ag) →
            Frame.applications path = through ∧ RoleArmsWellNested M fnTable rTable r site through arms) →
          h.run (retryOfCfg M retryCfg)
            ((mapR M perm.apply (arms.denote (roleSem M r fnTable rTable) path env
              (cast (congrArg (Pick (RV M r)) hPay.symm) (liftPick M r ps pkVal)))).bind cont) s =
            ((specializeArms specOp fnLift specApply retryCfg through perm r ps hrPs hCtx arms hPay).denote
              M fullTable procTable path cenv s pkVal).bind
              fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2
    | _, _, _, _, _, _, _, _, _, _, .nil, [], _, _, _, _, _, pkVal, _, _, _, _, _ => nomatch pkVal
    | _, _, _, _, _, _, _, _, _, _, .nil, _ :: _, hPay, _, _, _, _, _, _, _, _, _, _ => nomatch hPay
    | _, _, _, _, _, _, _, _, _, _, .cons _ _ _, [], hPay, _, _, _, _, _, _, _, _, _, _ => nomatch hPay
    | retryCfg, hRC, hRAllow, ps, hrPs, Γ, Δ, hCtx, _, a :: restP,
        .cons (.cons nm .nil) arm more, τ :: altsRest, hPay, path, env, cenv, s, pkVal, _, cont,
        hEnv, hPR, hWNA => by
        have hHead : a = ⟨τ, ps⟩ := (List.cons.inj hPay).1
        have hTail : restP = altsRest.map (fun τ => ⟨τ, ps⟩) := (List.cons.inj hPay).2
        cases pkVal with
        | here v =>
            have hCtxA : CtxRel r (Γ.extend (.cons (a := a) nm .nil))
                (Δ.extend (.cons (a := τ) nm .nil)) := by
              rw [show Γ.extend (.cons (a := a) nm .nil) = Γ.insert nm ⟨τ, ps⟩ by rw [Ctx.extend, Ctx.extend, hHead]]
              exact hCtx.insert_held nm (a := ⟨τ, ps⟩)
            have hPickH : cast (congrArg (Pick (RV M r)) hPay.symm) (liftPick M r ps (.here v)) =
                Pick.here (cast (congrArg (RV M r) hHead.symm) (hide M r ⟨τ, ps⟩ v)) := by
              cases hHead; cases hTail; rfl
            rw [hPickH]
            dsimp only [Arms.denote]
            conv => rhs; rw [specializeArms]; dsimp only; rw [ClosedArms.denote]
            have hInsEnv : EnvRel M r hCtxA
                (env.extend (.cons (a := a) nm .nil)
                  (.cons (cast (congrArg (RV M r) hHead.symm) (hide M r ⟨τ, ps⟩ v)) .nil))
                (cenv.extend (.cons (a := τ) nm .nil) (.cons v .nil)) := by
              intro name' b hΓ hrb
              have hBase := hEnv.insert_held M nm hrPs (hide M r ⟨τ, ps⟩ v)
              rw [reveal_hide] at hBase
              have hEqEnv : HEq
                  (env.extend (.cons (a := a) nm .nil)
                    (.cons (cast (congrArg (RV M r) hHead.symm) (hide M r ⟨τ, ps⟩ v)) .nil))
                  (env.insert nm (hide M r ⟨τ, ps⟩ v)) := by
                cases hHead; exact HEq.rfl
              have hCtxEq : Γ.extend (.cons (a := a) nm .nil) = Γ.insert nm ⟨τ, ps⟩ := by
                rw [Ctx.extend, Ctx.extend, hHead]
              have hGet : ∀ {Γ₁ Γ₂ : Ctx (LTy V)} (e : Γ₁ = Γ₂) (e1 : Env (RV M r) Γ₁) (e2 : Env (RV M r) Γ₂),
                  HEq e1 e2 → ∀ (p1 : Γ₁.find? name' = some b) (p2 : Γ₂.find? name' = some b),
                    e1 name' b p1 = e2 name' b p2 := by
                intro _ _ e e1 e2 he p1 p2; subst e; cases eq_of_heq he; rfl
              have hΓ' : (Γ.insert nm ⟨τ, ps⟩).find? name' = some b := by rw [← hCtxEq]; exact hΓ
              rw [hGet hCtxEq _ _ hEqEnv hΓ hΓ']
              exact hBase name' b hΓ' hrb
            exact specializeTerm_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
              specApply retryAllowed hRAllowNone hApply
              through perm r retryCfg hRC hRAllow hCtxA arm path _ _ s cont hInsEnv hPR
              (fun b site ag hc => ⟨(hWNA b site ag hc).1, (hWNA b site ag hc).2.1⟩)
        | there pk' =>
            have hPickT : cast (congrArg (Pick (RV M r)) hPay.symm) (liftPick M r ps (.there pk')) =
                Pick.there (cast (congrArg (Pick (RV M r)) hTail.symm) (liftPick M r ps pk')) := by
              cases hHead; cases hTail; rfl
            rw [hPickT]
            dsimp only [Arms.denote]
            conv => rhs; rw [specializeArms]; dsimp only; rw [ClosedArms.denote]
            exact specializeArms_sound fullTable procTable h specOp pathRel hPRClosed hSpec fnTable rTable fnLift hLift
              specApply retryAllowed hRAllowNone hApply
              through perm r retryCfg hRC hRAllow ps hrPs hCtx more hTail path env cenv s pk' cont hEnv hPR
              (fun b site ag hc => ⟨(hWNA b site ag hc).1, (hWNA b site ag hc).2.2⟩)
end

/-! ## Level 1.5: Protocol specialization and DAG-shared procedure soundness -/

/-- Soundness invariant for a `sharedLookup` table over `defs` at any subtree-free call path. -/
def SharedLookupSound {procs : List (ClosedProcSig V)}
    {σ : List V.Ty} (procTable : ClosedProcTable M procs)
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (freeCond : List Frame → Prop) {hs : Headers V} (defs : Defs V hs)
    (lookup : {hdr : ProtocolHeader V} → Member hs.protocols hdr → FinPerm → (r : Role) →
      Option (Member procs ⟨σ, held r hdr.ins, held r hdr.outs⟩)) : Prop :=
  ∀ {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr) (perm : FinPerm) (r : Role)
    (mem : Member procs ⟨σ, held r hdr.ins, held r hdr.outs⟩),
    lookup callee perm r = some mem →
    ∀ (path : List Frame) (ins : HList (RV M r) hdr.ins) (s : HList M.Val σ),
      freeCond path →
      h.run (retryOf M none) (mapR M perm.apply (Defs.rTable M defs hdr callee r path ins)) s =
        (procTable _ mem path (heldValues M r ins) s).map fun out =>
          (unheldValues M r out.1, out.2)

/-- Helper: bridge a `SharedLookupSound` hit into a CPS equation under an arbitrary `retryCfg`
when `retrySite` is not in the subtree (or `retryCfg = none`). -/
private theorem shared_hit_cps {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    {σ : List V.Ty} (procTable : ClosedProcTable M procs)
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    {hs : Headers V} (defs : Defs V hs) {hdr : ProtocolHeader V}
    (callee : Member hs.protocols hdr) (perm : FinPerm) (r : Role)
    (mem : Member procs ⟨σ, held r hdr.ins, held r hdr.outs⟩)
    (path : List Frame) (ins : HList (RV M r) hdr.ins) (s : HList M.Val σ)
    {B : Type} (cont : HList (RV M r) hdr.outs → Program M B)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    (hNoBeg : ∀ b site ag, retryCfg = some (b, site, ag) →
      ¬ ((Frame.applications path).isPrefixOf site.through = true))
    (hRun : h.run (retryOf M none) (mapR M perm.apply (Defs.rTable M defs hdr callee r path ins)) s =
      (procTable _ mem path (heldValues M r ins) s).map fun out =>
        (unheldValues M r out.1, out.2)) :
    h.run (retryOfCfg M retryCfg)
      ((mapR M perm.apply (Defs.rTable M defs hdr callee r path ins)).bind cont) s =
      (procTable _ mem path (heldValues M r ins) s).bind fun out =>
        h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2 := by
  have hNB : NoBeginFor M (retryOfCfg M retryCfg)
      (mapR M perm.apply (Defs.rTable M defs hdr callee r path ins)) := by
    cases retryCfg with
    | none =>
        have hAll : ∀ {A : Type} (p : Program M A), NoBeginFor M (retryOf M none) p := by
          intro A p
          induction p with
          | done _ => trivial
          | halt _ => trivial
          | call _ _ ih => exact ⟨rfl, ih⟩
        exact hAll _
    | some cfg =>
        cases cfg with
        | mk b sr =>
            cases sr with
            | mk site ag =>
                refine noBeginFor_mapR M (fun ρ op ho => by cases op <;> exact ho) perm.apply ?_
                exact noBeginFor_retryOf_defs M defs b site callee r path ins (hNoBeg b site ag rfl)
  rw [handler_run_bind_noBegin M h (retryOfCfg M retryCfg) _ hNB cont s, hRun, Process.bind_map]

/-- Middle-level soundness: `specializeProtocolInDefs` matches `Defs.rTable` under `Handler.run`
for any sound `sharedLookup` table and any closed `pathRel`. -/
theorem specializeProtocolInDefs_sound {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns procs σ) (activeSites : List Site)
    (pathRel : List Key → List Frame → Prop) (hPRClosed : PathRelClosed pathRel)
    (hSpec : SpecOpSoundOn M fullTable procTable h specOp pathRel)
    (freeCond : List Frame → Prop)
    (hFreeImplies : ∀ th path, pathRel th path → subtreeFree activeSites th = true → freeCond path) :
    ∀ {hs : Headers V} (defs : Defs V hs)
      (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
      (_hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = Defs.fnTable M defs hdr f)
      (sharedLookup : {hdr : ProtocolHeader V} → Member hs.protocols hdr → FinPerm → (r : Role) →
        Option (Member procs ⟨σ, held r hdr.ins, held r hdr.outs⟩))
      (_hShared : SharedLookupSound M procTable h freeCond defs sharedLookup)
      (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
      (_hRC : RetryCfgOk M fullTable h retryCfg)
      (_hRetryIn : ∀ b site ag, retryCfg = some (b, site, ag) → site ∈ activeSites)
      {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr)
      (through : List Key) (perm : FinPerm) (r : Role)
      (path : List Frame) (ins : HList (RV M r) hdr.ins)
      (s : HList M.Val σ) {B : Type} (cont : HList (RV M r) hdr.outs → Program M B),
      pathRel through path →
      (∀ b site ag, retryCfg = some (b, site, ag) →
        Frame.applications path = through ∧ Shape.noNestedAttempt site through hdr.shape = true) →
      h.run (retryOfCfg M retryCfg) ((mapR M perm.apply (Defs.rTable M defs hdr callee r path ins)).bind cont) s =
        ((specializeProtocolInDefs specOp activeSites defs fnLift sharedLookup retryCfg callee through perm r).2.denote
          M fullTable procTable path
          (Env.empty.extend
            (specializeProtocolInDefs specOp activeSites defs fnLift sharedLookup retryCfg callee through perm r).1
            (heldValues M r ins)) s).bind
          fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2
  | _, .nil, _, _, _, _, _, _, _, _, m, _, _, _, _, _, _, _, _, _, _ => nomatch m
  | _, .fn _ _ _ _ rest _, fnLift, hLift, sharedLookup, hShared, retryCfg, hRC, hRetryIn, _, m,
      through, perm, r, path, ins, s, _, cont, hPR, hWN =>
      specializeProtocolInDefs_sound fullTable procTable h specOp activeSites pathRel hPRClosed hSpec
        freeCond hFreeImplies rest (fun f => fnLift (.tail f))
        (fun hdr f => hLift hdr (.tail f)) sharedLookup hShared retryCfg hRC hRetryIn m
        through perm r path ins s cont hPR hWN
  | _, .protocol (hs := hsRest) hdrP inputsP bodyP okP rest, fnLift, hLift, sharedLookup, hShared,
      retryCfg, hRC, hRetryIn, _, .head, through, perm, r, path, ins, s, _, cont, hPR, hWN => by
      let restLookup : {hdr' : ProtocolHeader V} → Member hsRest.protocols hdr' → FinPerm → (r' : Role) →
          Option (Member procs ⟨σ, held r' hdr'.ins, held r' hdr'.outs⟩) :=
        fun m' p' r' => sharedLookup (.tail m') p' r'
      have hRestShared : SharedLookupSound M procTable h freeCond rest restLookup :=
        fun m' p' r' mem hEq path' ins' s' hFr => hShared (.tail m') p' r' mem hEq path' ins' s' hFr
      let specApply : Option (Nat × Site × StackAgain V fullFns σ) →
          {hdr' : ProtocolHeader V} → Member hsRest.protocols hdr' →
          List Key → FinPerm → (r' : Role) →
          ApplyTarget V fullFns procs σ (held r' hdr'.ins) (held r' hdr'.outs) :=
        fun rc {_} m' th' p' r' =>
          if subtreeFree activeSites th' then
            match restLookup m' p' r' with
            | some mem => .shared mem
            | none =>
                let res := specializeProtocolInDefs specOp activeSites rest fnLift restLookup rc m' th' p' r'
                .inlined res.1 res.2
          else
            let res := specializeProtocolInDefs specOp activeSites rest fnLift restLookup rc m' th' p' r'
            .inlined res.1 res.2
      have hApplySound : SpecApplySound M fullTable procTable h pathRel
          (fun rc => ∀ b site ag, rc = some (b, site, ag) → site ∈ activeSites)
          (Defs.rTable M rest) specApply := by
        intro rc hRC' hRIn' hdr' m' th' p' r' path' ins' s' B' cont' hPR' hWN'
        dsimp only [specApply]
        by_cases hFr : subtreeFree activeSites th' = true
        · rw [ite_eq_left hFr]
          cases hLook : restLookup m' p' r' with
          | some mem =>
              dsimp only
              have hNoBeg : ∀ b site ag, rc = some (b, site, ag) →
                  ¬ ((Frame.applications path').isPrefixOf site.through = true) := by
                intro b site ag hc
                rw [(hWN' b site ag hc).1]
                exact subtreeFree_not_mem activeSites th' hFr (hRIn' b site ag hc)
              exact shared_hit_cps M procTable h rest m' p' r' mem path' ins' s' cont' rc hNoBeg
                (hRestShared m' p' r' mem hLook path' ins' s' (hFreeImplies th' path' hPR' hFr))
          | none =>
              dsimp only
              exact specializeProtocolInDefs_sound fullTable procTable h specOp activeSites pathRel hPRClosed
                hSpec freeCond hFreeImplies rest fnLift hLift restLookup hRestShared rc hRC' hRIn' m' th'
                p' r' path' ins' s' cont' hPR' hWN'
        · rw [ite_eq_right hFr]
          exact specializeProtocolInDefs_sound fullTable procTable h specOp activeSites pathRel hPRClosed
            hSpec freeCond hFreeImplies rest fnLift hLift restLookup hRestShared rc hRC' hRIn' m' th'
            p' r' path' ins' s' cont' hPR' hWN'
      dsimp only [specializeProtocolInDefs, Defs.rTable]
      refine specializeTerm_sound M fullTable procTable h specOp pathRel hPRClosed hSpec
        (Defs.fnTable M rest) (Defs.rTable M rest) fnLift hLift
        specApply (fun rc => ∀ b site ag, rc = some (b, site, ag) → site ∈ activeSites)
        (fun _ _ _ hc => nomatch hc) hApplySound
        through perm r retryCfg hRC hRetryIn ((CtxRel.empty r).extend inputsP) (project r bodyP)
        path (Env.empty.extend inputsP ins) _ s cont
        ((EnvRel.empty M r).extend M inputsP ins) hPR ?_
      intro b site ag hc
      refine ⟨(hWN b site ag hc).1, ?_⟩
      have hSh := (hWN b site ag hc).2
      rw [okP.shaped] at hSh
      exact roleTermWellNested_of_shape M rest site r through bodyP hSh
  | _, .protocol _ _ _ _ rest, fnLift, hLift, sharedLookup, hShared, retryCfg, hRC, hRetryIn, _, .tail m,
      through, perm, r, path, ins, s, _, cont, hPR, hWN =>
      specializeProtocolInDefs_sound fullTable procTable h specOp activeSites pathRel hPRClosed hSpec
        freeCond hFreeImplies rest fnLift hLift (fun m' p' r' => sharedLookup (.tail m') p' r')
        (fun m' p' r' mem hEq path' ins' s' hFr => hShared (.tail m') p' r' mem hEq path' ins' s' hFr)
        retryCfg hRC hRetryIn m through perm r path ins s cont hPR hWN

/-- Soundness of appending deduplicated shared procedures for a single protocol level `hdrP`. -/
private theorem addSharedForProto_sound {fullFns : List (FnHeader V)} {σ : List V.Ty}
    (fullTable : FnTable M fullFns)
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (freeCond : List Frame → Prop)
    (hPRFree : PathRelClosed (fun _ path => freeCond path))
    (hUnhandled : ∀ {procs : List (ClosedProcSig V)} (procTable : ClosedProcTable M procs),
      SpecOpSoundOn M fullTable procTable h (unhandledSpecOp σ) (fun _ path => freeCond path))
    {hsRest : Headers V} (hdrP : ProtocolHeader V) (inputsP : Names hdrP.ins)
    (bodyP : Term (protocolDialect V hsRest) (Ctx.empty.extend inputsP) hdrP.outs)
    (okP : ProtocolConditions hdrP bodyP)
    (rest : Defs V hsRest)
    (fnLift : ∀ {hdr}, Member hsRest.fns hdr → Member fullFns hdr)
    (hLift : ∀ hdr (f : Member hsRest.fns hdr), fullTable hdr (fnLift f) = Defs.fnTable M rest hdr f)
    (restPool : SharedPool V fullFns hsRest.protocols σ)
    (hRestPool : SharedLookupSound M (restPool.procs.denote M fullTable) h freeCond rest restPool.lookup) :
    ∀ (keys : List (FinPerm × Role)),
      let res := addSharedForProto hdrP inputsP bodyP rest fnLift restPool keys
      (∀ {sig} (m : Member restPool.sigs sig),
        res.2.1.denote M fullTable sig (res.2.2.1 m) = restPool.procs.denote M fullTable sig m) ∧
      (∀ (perm : FinPerm) (r : Role)
        (mem : Member res.1 ⟨σ, held r hdrP.ins, held r hdrP.outs⟩),
        res.2.2.2 perm r = some mem →
        ∀ (path : List Frame) (ins : HList (RV M r) hdrP.ins) (s : HList M.Val σ),
          freeCond path →
          h.run (retryOf M none)
              (mapR M perm.apply (Defs.rTable M (.protocol hdrP inputsP bodyP okP rest) hdrP .head r path ins)) s =
            (res.2.1.denote M fullTable _ mem path (heldValues M r ins) s).map fun out =>
              (unheldValues M r out.1, out.2))
  | [] => ⟨fun _ => rfl, fun _ _ _ hEq => nomatch hEq⟩
  | (perm0, r0) :: more => by
      have ih := addSharedForProto_sound fullTable h freeCond hPRFree hUnhandled
        hdrP inputsP bodyP okP rest fnLift hLift restPool hRestPool more
      dsimp only [addSharedForProto] at ih ⊢
      obtain ⟨hEmbedPrev, hHeadPrev⟩ := ih
      let prev := addSharedForProto hdrP inputsP bodyP rest fnLift restPool more
      refine ⟨fun m => hEmbedPrev m, ?_⟩
      intro perm r mem hEq path ins s hFree
      by_cases hHit : perm = perm0 ∧ r = r0
      · obtain ⟨rfl, rfl⟩ := hHit
        rw [dite_eq_left ⟨rfl, rfl⟩] at hEq
        cases hEq
        dsimp only [ClosedProcs.denote, Defs.rTable]
        let curProcs := prev.2.1
        let embed : ∀ {sig}, Member restPool.sigs sig → Member prev.1 sig := prev.2.2.1
        have hLiftedRest : SharedLookupSound M (curProcs.denote M fullTable) h freeCond rest
            (fun m2 p2 r2 => (restPool.lookup m2 p2 r2).map embed) := by
          intro hdr2 m2 p2 r2 mem2 hLook2 path2 ins2 s2 hFr2
          cases hOrig : restPool.lookup m2 p2 r2 with
          | none => simp [hOrig] at hLook2
          | some mem0 =>
              simp only [hOrig, Option.map_some, Option.some.injEq] at hLook2
              subst hLook2
              rw [hEmbedPrev mem0]
              exact hRestPool m2 p2 r2 mem0 hOrig path2 ins2 s2 hFr2
        let specApply : Option (Nat × Site × StackAgain V fullFns σ) →
            {hdr' : ProtocolHeader V} → Member hsRest.protocols hdr' →
            List Key → FinPerm → (r'' : Role) →
            ApplyTarget V fullFns prev.1 σ (held r'' hdr'.ins) (held r'' hdr'.outs) :=
          fun rc {_} m' th' p' r'' =>
            match restPool.lookup m' p' r'' with
            | some mem0 => .shared (embed mem0)
            | none =>
                let res := specializeProtocolInDefs (unhandledSpecOp σ) [] rest fnLift
                  (fun m2 p2 r2 => (restPool.lookup m2 p2 r2).map embed) rc m' th' p' r''
                .inlined res.1 res.2
        have hApplySound : SpecApplySound M fullTable (curProcs.denote M fullTable) h
            (fun _ path' => freeCond path') (fun rc => rc = none) (Defs.rTable M rest) specApply := by
          intro rc _ hRCNone hdr' m' th' p' r'' path' ins' s' B' cont' hPR' hWN'
          subst hRCNone
          dsimp only [specApply]
          cases hLook : restPool.lookup m' p' r'' with
          | some mem0 =>
              dsimp only
              refine shared_hit_cps M (curProcs.denote M fullTable) h rest m' p' r'' (embed mem0)
                path' ins' s' cont' none (fun _ _ _ hc => nomatch hc) ?_
              rw [hEmbedPrev mem0]
              exact hRestPool m' p' r'' mem0 hLook path' ins' s' hPR'
          | none =>
              dsimp only
              exact specializeProtocolInDefs_sound M fullTable (curProcs.denote M fullTable) h
                (unhandledSpecOp σ) [] (fun _ p => freeCond p) hPRFree
                (hUnhandled (curProcs.denote M fullTable)) freeCond (fun _ _ hp _ => hp)
                rest fnLift hLift (fun m2 p2 r2 => (restPool.lookup m2 p2 r2).map embed)
                hLiftedRest none trivial (fun _ _ _ hc => nomatch hc)
                m' th' p' r'' path' ins' s' cont' hPR' hWN'
        have hTerm := specializeTerm_sound M fullTable (curProcs.denote M fullTable) h
          (unhandledSpecOp σ) (fun _ p => freeCond p) hPRFree
          (hUnhandled (curProcs.denote M fullTable))
          (Defs.fnTable M rest) (Defs.rTable M rest) fnLift hLift
          specApply (fun rc => rc = none) rfl hApplySound
          [] perm r none trivial rfl ((CtxRel.empty r).extend inputsP) (project r bodyP)
          path (Env.empty.extend inputsP ins)
          (Env.empty.extend (heldNames r inputsP) (heldValues M r ins)) s
          Process.done ((EnvRel.empty M r).extend M inputsP ins) hFree (fun _ _ _ hc => nomatch hc)
        rw [Process.bind_pure] at hTerm
        dsimp only [retryOfCfg, Handler.run] at hTerm
        exact hTerm.trans (Process.map_eq_bind _ _).symm
      · rw [dite_eq_right hHit] at hEq
        obtain ⟨memPrev, hPrev, hTailEq⟩ := Option.map_eq_some_iff.mp hEq
        subst hTailEq
        exact hHeadPrev perm r memPrev hPrev path ins s hFree

/-- Soundness of bottom-up topological `buildSharedProcs` across all protocols in `defs`. -/
private theorem buildSharedProcs_sound {fullFns : List (FnHeader V)} {σ : List V.Ty}
    (fullTable : FnTable M fullFns)
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (freeCond : List Frame → Prop)
    (hPRFree : PathRelClosed (fun _ path => freeCond path))
    (hUnhandled : ∀ {procs : List (ClosedProcSig V)} (procTable : ClosedProcTable M procs),
      SpecOpSoundOn M fullTable procTable h (unhandledSpecOp σ) (fun _ path => freeCond path)) :
    ∀ {hs : Headers V} (defs : Defs V hs)
      (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
      (_hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = Defs.fnTable M defs hdr f)
      (demands : List (SharedDemand V hs.protocols)),
      let pool := buildSharedProcs σ defs fnLift demands
      SharedLookupSound M (pool.procs.denote M fullTable) h freeCond defs pool.lookup
  | _, .nil, _, _, _ => fun {_} m => nomatch m
  | _, .fn (hs := hsRest) _ _ _ _ rest _, fnLift, hLift, demands =>
      buildSharedProcs_sound fullTable h freeCond hPRFree hUnhandled (hs := hsRest) rest
        (fun f => fnLift (.tail f)) (fun hdr f => hLift hdr (.tail f)) demands
  | _, .protocol (hs := hsRest) hdrP inputsP bodyP okP rest, fnLift, hLift, demands => by
      dsimp only [buildSharedProcs]
      let part := partitionDemands demands
      let subDemands := part.1.flatMap fun (perm, r') => collectDirectAppliesTerm perm r' (project r' bodyP)
      let restPool := buildSharedProcs σ (hs := hsRest) rest fnLift (subDemands ++ part.2)
      have hRestPool : SharedLookupSound M (restPool.procs.denote M fullTable) h freeCond rest restPool.lookup :=
        buildSharedProcs_sound fullTable h freeCond hPRFree hUnhandled (hs := hsRest) rest fnLift hLift (subDemands ++ part.2)
      obtain ⟨hEmbed, hHead⟩ := addSharedForProto_sound M fullTable h freeCond hPRFree hUnhandled
        hdrP inputsP bodyP okP rest fnLift hLift restPool hRestPool part.1
      intro callee perm r mem hLook path ins s hFree
      cases callee with
      | head => exact hHead perm r mem hLook path ins s hFree
      | tail m =>
          obtain ⟨mem0, hOrig, hEm⟩ := Option.map_eq_some_iff.mp hLook
          subst hEm
          rw [hEmbed mem0]
          exact hRestPool m perm r mem0 hOrig path ins s hFree

/-! ## Level 2: Layer-stack specialization soundness (`specializeClauses`, `specializeStack`, `Stack*`) -/

private theorem specializeClauses_sound {hs : Headers V} (defs : Defs V hs) {r_top : Role} {state : V.Ty}
    {σ_rest : List V.Ty}
    (hBelow : Handler (RSig M) (RSig M) Stop (HList M.Val σ_rest))
    (specBelow : EffectSpecializer V hs.fns [] σ_rest)
    (hSpecBelow : SpecOpSound M (Defs.fnTable M defs) (ClosedProcTable.empty M) hBelow specBelow)
    (through : List Key) (key : Key) {ins res : List V.Ty} (op : ResidualOp V ins res)
    {Δ : Ctx V.Ty} (args : HList (Var Δ) ins) (path : List Frame) (cenv : Env M.Val Δ)
    (mine : M.Val state) (below : HList M.Val σ_rest) (hPath : Frame.applications path = through) :
    ∀ (cs : List (Clause V hs r_top state)),
      (specializeClauses defs specBelow through key op args cs).denote M (Defs.fnTable M defs)
          (ClosedProcTable.empty M) path cenv (.cons mine below) =
        (((hBelow.answer (Clause.answer M (Defs.fnTable M defs) (Defs.rTable M defs) cs
              (op.toROp M ⟨path, key⟩ (cenv.all args)) mine) mine below).mapHalt
            fun stop => (stop.1, .cons stop.2.1 stop.2.2)).map
          fun out => (op.replyOf M ⟨path, key⟩ (cenv.all args) out.1.1, .cons out.1.2 out.2))
  | [] => by
      change (((specBelow through key op args).denote M (Defs.fnTable M defs) (ClosedProcTable.empty M) path cenv below).mapHalt
          fun stop => (stop.1, HList.cons mine stop.2)).map (fun out => (out.1, HList.cons mine out.2)) = _
      rw [hSpecBelow through key op args path cenv below hPath, Clause.answer, Handler.answer]
      dsimp only [Handler.answer]
      rw [mapHalt_map, Process.map_map, mapHalt_bind, mapHalt_mapHalt, Process.map_bind]
      simp only [Process.map_eq_bind]
      rfl
  | c :: cs => by
      dsimp only [specializeClauses, Clause.answer]
      let rop := op.toROp M ⟨path, key⟩ (cenv.all args)
      have hSiteEq : (ROp.occurrence M rop).site = ⟨through, key⟩ := by
        rw [op.toROp_occurrence M ⟨path, key⟩ (cenv.all args)]
        simp [Occurrence.site, hPath]
      have hPartEq : ROp.part M rop = op.part := op.toROp_part M ⟨path, key⟩ (cenv.all args)
      have hTakesEq : ROp.takes M rop = ins := op.toROp_takes M ⟨path, key⟩ (cenv.all args)
      have hGivesEq : ROp.gives M rop = res := op.toROp_gives M ⟨path, key⟩ (cenv.all args)
      have hIff : (c.site.site = ⟨through, key⟩ ∧ some c.site.part = op.part ∧
            c.site.takes = ins ∧ c.site.gives = res) ↔
          (c.site.site = (ROp.occurrence M rop).site ∧ some c.site.part = ROp.part M rop ∧
            c.site.takes = ROp.takes M rop ∧ c.site.gives = ROp.gives M rop) := by
        rw [hSiteEq, hPartEq, hTakesEq, hGivesEq]
      by_cases hM : c.site.site = ⟨through, key⟩ ∧ some c.site.part = op.part ∧
          c.site.takes = ins ∧ c.site.gives = res
      · have hM' := hIff.mp hM
        rw [dite_eq_left hM, dite_eq_left hM']
        have hPosEq : Ctx.positional (c.site.takes ++ [state]) =
            Ctx.empty.extend (Names.counting 0 (ins ++ [state])) := by
          unfold Ctx.positional; rw [hM.2.2.1]
        change Process.map (fun out => let sp := HList.split res out.1; (sp.1, HList.cons sp.2.single out.2))
            (Process.mapHalt (fun stop => (stop.1, HList.cons mine stop.2))
              (((specializeTerm specBelow id
                  (fun rc {_} m th perm' r' =>
                    let r0 := specializeProtocolInDefs specBelow [] defs id (fun _ _ _ => none) rc m th perm' r'
                    .inlined r0.1 r0.2)
                  none through FinPerm.identity r_top
                  (CtxRel.positional_alone r_top (c.site.takes ++ [state]))
                  c.code).castCT hPosEq (by rw [held_alone, hM.2.2.2])).denote
                M (Defs.fnTable M defs) (ClosedProcTable.empty M) path
                (Env.empty.extend (Names.counting 0 (ins ++ [state])) ((cenv.all args).append (.cons mine .nil)))
                below)) = _
        rw [closedTerm_denote_castCT, mapHalt_map, Process.map_map]
        have hPathClause : (ROp.occurrence M rop).path = path := by
          rw [op.toROp_occurrence M ⟨path, key⟩ (cenv.all args)]
        have hPayload : cast (congrArg (HList M.Val) hM'.2.2.1.symm) (ROp.payload M rop) =
            cast (congrArg (HList M.Val) hM.2.2.1.symm) (cenv.all args) := by
          have hP := op.toROp_payload M ⟨path, key⟩ (cenv.all args)
          rw [← hP, cast_cast]
        have hEnvPos : EnvRel M r_top (CtxRel.positional_alone r_top (c.site.takes ++ [state]))
            (Env.positional (aloneIn M r_top (HList.append
              (cast (congrArg (HList M.Val) hM'.2.2.1.symm) (ROp.payload M rop)) (.cons mine .nil))))
            (cast (congrArg (Env M.Val) hPosEq.symm)
              (Env.empty.extend (Names.counting 0 (ins ++ [state])) ((cenv.all args).append (.cons mine .nil)))) := by
          rw [hPayload]
          have hBase := EnvRel.positional_alone M r_top
            (HList.append (cast (congrArg (HList M.Val) hM.2.2.1.symm) (cenv.all args)) (.cons mine .nil))
          have hEqEnv : cast (congrArg (Env M.Val) hPosEq.symm)
              (Env.empty.extend (Names.counting 0 (ins ++ [state])) ((cenv.all args).append (.cons mine .nil))) =
              Env.positional (HList.append (cast (congrArg (HList M.Val) hM.2.2.1.symm) (cenv.all args)) (.cons mine .nil)) := by
            have hT := hM.2.2.1
            generalize hPosEq = hp
            generalize hT = ht at hp ⊢
            subst ht
            rfl
          rw [hEqEnv]
          exact hBase
        have hEmptyShared : SharedLookupSound M (ClosedProcTable.empty M) hBelow (fun _ => True) defs
            (fun _ _ _ => none) := fun _ _ _ _ hEq => nomatch hEq
        have hCode := specializeTerm_sound M (Defs.fnTable M defs) (ClosedProcTable.empty M)
          hBelow specBelow (fun th p => Frame.applications p = th) pathRelClosed_exact hSpecBelow
          (Defs.fnTable M defs) (Defs.rTable M defs) id (fun _ _ => rfl)
          (fun rc {_} m th perm' r' =>
            let r0 := specializeProtocolInDefs specBelow [] defs id (fun _ _ _ => none) rc m th perm' r'
            .inlined r0.1 r0.2)
          (fun rc => rc = none) rfl
          (fun rc _ hRCNone {_} callee' th' perm' r' path' ins' s' _ cont' hP' hWN' => by
            subst hRCNone
            exact specializeProtocolInDefs_sound M (Defs.fnTable M defs) (ClosedProcTable.empty M)
              hBelow specBelow [] (fun th p => Frame.applications p = th) pathRelClosed_exact
              hSpecBelow (fun _ => True) (fun _ _ _ _ => trivial)
              defs id (fun _ _ => rfl) (fun _ _ _ => none) hEmptyShared
              none trivial (fun _ _ _ hc => nomatch hc)
              callee' th' perm' r' path' ins' s' cont' hP' hWN')
          through FinPerm.identity r_top none trivial rfl
          (CtxRel.positional_alone r_top (c.site.takes ++ [state])) c.code
          path _ _ below Process.done hEnvPos hPath (fun _ _ _ hc => nomatch hc)
        rw [mapR_congr M (ρ₂ := id) FinPerm.apply_identity, mapR_id, Process.bind_pure] at hCode
        dsimp only [retryOfCfg] at hCode
        have hAnsMap : ∀ {T U : Sig} {H τ X Y E : Type} (hb : Handler T U H τ)
            (f : X → Y) (p : Process T (H × E) X) (e : E) (t : τ),
            hb.answer (p.map f) e t = (hb.answer p e t).map fun out => (f out.1, out.2) := by
          intro _ _ _ _ _ _ _ hb f p e t
          induction p generalizing t with
          | done _ => rfl
          | halt _ => rfl
          | call op k ih =>
              simp only [Process.map, Handler.answer, Process.map_bind]
              congr 1; funext out; exact ih out.1 out.2
        rw [hPathClause, hAnsMap, handler_answer_mapHalt_const, mapHalt_map, mapHalt_mapHalt,
          Process.map_map, hCode, Process.map_eq_bind, Process.map_eq_bind, mapHalt_bind,
          Process.bind_assoc]
        congr 1; funext out
        dsimp only [Handler.run, Process.bind, Process.mapHalt]
        congr 1
        have hAlone : aloneOut M r_top (unheldValues M r_top out.1) =
            cast (congrArg (HList M.Val) (held_alone r_top (c.site.gives ++ [state]))) out.1 := by
          rw [aloneOut_eq_heldValues, heldValues_unheldValues]
        rw [hAlone]
        have hSplitCast : ∀ {g₁ g₂ : List V.Ty} (eg : g₁ = g₂)
            (es : held r_top (alone r_top (g₁ ++ [state])) = g₁ ++ [state])
            (v : HList M.Val (held r_top (alone r_top (g₁ ++ [state])))),
            let s1 := HList.split g₂ (cast (congrArg (HList M.Val) (by rw [es, eg])) v)
            let s2 := HList.split g₁ (cast (congrArg (HList M.Val) es) v)
            s1.1 = cast (congrArg (HList M.Val) eg) s2.1 ∧ s1.2.single = s2.2.single := by
          intro g₁ g₂ eg es v
          subst eg
          exact ⟨rfl, rfl⟩
        have hSC := hSplitCast hM.2.2.2 (held_alone r_top (c.site.gives ++ [state])) out.1
        have hRep : op.replyOf M ⟨path, key⟩ (cenv.all args)
            (ROp.reply M rop (cast (congrArg (HList M.Val) hM'.2.2.2)
              (HList.split c.site.gives (cast (congrArg (HList M.Val) (held_alone r_top (c.site.gives ++ [state]))) out.1)).1)) =
            (HList.split res (cast (congrArg (HList M.Val) (by rw [held_alone, hM.2.2.2])) out.1)).1 := by
          rw [hSC.1]
          have h1 := op.replyOf_reply M ⟨path, key⟩ (cenv.all args)
            (cast (congrArg (HList M.Val) hM.2.2.2)
              (HList.split c.site.gives (cast (congrArg (HList M.Val) (held_alone r_top (c.site.gives ++ [state]))) out.1)).1)
          simpa [rop, cast_cast] using h1
        rw [hRep, hSC.2]
      · have hNM' : ¬ (c.site.site = (ROp.occurrence M rop).site ∧ some c.site.part = ROp.part M rop ∧
            c.site.takes = ROp.takes M rop ∧ c.site.gives = ROp.gives M rop) := fun h' => hM (hIff.mpr h')
        rw [dite_eq_right hM, dite_eq_right hNM']
        exact specializeClauses_sound defs hBelow specBelow hSpecBelow through key op args path cenv mine below hPath cs

private theorem specializeStack_sound {hs : Headers V} (defs : Defs V hs) {r_top : Role}
    {ins_top : List (LTy V)} :
    ∀ (layers : List (Layer V hs r_top ins_top)),
      SpecOpSound M (Defs.fnTable M defs) (ClosedProcTable.empty M)
        (Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) layers)
        (specializeStack defs layers)
  | [] => by
      intro through key ins res op Δ args path cenv s hPath
      cases s
      rfl
  | l :: rest => by
      intro through key ins res op Δ args path cenv s hPath
      cases s with
      | cons mine below =>
          change (specializeClauses defs (specializeStack defs rest) through key op args l.clauses).denote
              M (Defs.fnTable M defs) (ClosedProcTable.empty M) path cenv (HList.cons mine below) =
            Process.map (fun out => (op.replyOf M ⟨path, key⟩ (cenv.all args) out.1, out.2))
              (Process.map (fun out => (out.1, HList.cons out.2.1 out.2.2))
                (Process.mapHalt (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
                  ((Process.mapHalt (fun stop => (stop.1, stop.2.1, stop.2.2))
                    ((Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) rest).answer
                      (Clause.answer M (Defs.fnTable M defs) (Defs.rTable M defs) l.clauses
                        (op.toROp M ⟨path, key⟩ (cenv.all args)) mine) mine below)).bind
                    fun out => Process.done (out.1.1, out.1.2, out.2))))
          rw [specializeClauses_sound M defs
            (Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) rest)
            (specializeStack defs rest)
            (specializeStack_sound defs rest)
            through key op args path cenv mine below hPath l.clauses]
          rw [mapHalt_bind, mapHalt_mapHalt, Process.map_bind, Process.map_eq_bind, Process.map_eq_bind,
            Process.bind_assoc]
          rfl

private theorem stackAgain_eval_cons {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (l : Layer V hs r ins) (rest : List (Layer V hs r ins))
    (i : Nat) (e t : M.Val l.state) (es ts : HList M.Val (Stack.States rest))
    (hRec : StackAgain.eval M fnTable (stackAgain rest) i es ts =
      (Stack.handler M fnTable rTable rest).again i es ts) :
    StackAgain.eval M fnTable (stackAgain (l :: rest)) i (.cons e es) (.cons t ts) =
      (Stack.handler M fnTable rTable (l :: rest)).again i (.cons e es) (.cons t ts) := by
  change StackAgain.eval M fnTable (HList.cons l.again (stackAgain rest)) i (.cons e es) (.cons t ts) =
    (((Layer.handler M fnTable rTable l).over (Stack.handler M fnTable rTable rest)).again
      i (e, es) (t, ts)).map fun next => .cons next.1 next.2
  rw [StackAgain.eval, hRec]
  dsimp only [Handler.over, Layer.handler]
  cases l.again.denote (localSem M hs.fns fnTable) []
      (Env.positional (.cons (i : Nat) (.cons e (.cons t .nil)))) with
  | done res =>
      cases res with
      | cons next rNil =>
          cases rNil
          cases (Stack.handler M fnTable rTable rest).again i es ts <;> rfl
  | halt why => rfl
  | call op _ => nomatch op

private theorem stackAgain_eval {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)} :
    ∀ (layers : List (Layer V hs r ins)),
      StackAgain.eval M fnTable (stackAgain layers) =
        (Stack.handler M fnTable rTable layers).again
  | [] => by
      funext i entry stop
      cases entry; cases stop; rfl
  | l :: rest => by
      funext i entry stop
      cases entry with
      | cons e es =>
          cases stop with
          | cons t ts =>
              exact stackAgain_eval_cons M fnTable rTable l rest i e t es ts
                (congrFun (congrFun (congrFun (stackAgain_eval fnTable rTable rest) i) es) ts)

private theorem stackInit_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} :
    ∀ (layers : List (Layer V hs r ins)) (inputVals : HList (RV M r) ins)
      (takenVals : HList M.Val (Stack.Takes layers)),
      (stackInit layers).denote M fnTable (heldValues M r inputVals) takenVals =
        Stack.start M fnTable layers inputVals takenVals
  | [], _, .nil => rfl
  | l :: rest, inputVals, takenVals => by
      change (liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
          (Env.positional ((HList.split l.takes takenVals).1.append (heldValues M r inputVals))))).bind
          (fun first => ((stackInit rest).denote M fnTable (heldValues M r inputVals)
            (HList.split l.takes takenVals).2).map fun others => HList.cons first.single others) =
        (liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
          (Env.positional ((HList.split l.takes takenVals).1.append (heldValues M r inputVals))))).bind
          (fun first => (Stack.start M fnTable rest inputVals
            (HList.split l.takes takenVals).2).map fun others => HList.cons first.single others)
      congr 1; funext first
      rw [stackInit_denote fnTable rest inputVals (HList.split l.takes takenVals).2]

private theorem stackFinish_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} :
    ∀ (layers : List (Layer V hs r ins)) (states : HList M.Val (Stack.States layers)),
      (stackFinish layers).denote M fnTable states = Stack.finish M fnTable layers states
  | [], .nil => rfl
  | l :: rest, .cons s states => by
      change (liftLocal id (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil)))).bind
          (fun mine => ((stackFinish rest).denote M fnTable states).map fun others => HList.append mine others) =
        (liftLocal id (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil)))).bind
          (fun mine => (Stack.finish M fnTable rest states).map fun others => HList.append mine others)
      congr 1; funext mine
      rw [stackFinish_denote fnTable rest states]

unseal roleMeaning in
private theorem roleMeaning_eq_rTable (p : Typed V) {hdr : ProtocolHeader V}
    (x : Member p.headers.protocols hdr) (r : Role) (path : List Frame)
    (ins : HList (RV M r) hdr.ins) :
    roleMeaning M p x r path ins = Defs.rTable M p.defs hdr x r path ins := rfl

private theorem closedRole_denote_eq {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins outs : List (LTy V)} {takes gives : List V.Ty}
    (cr : ClosedRole V fns r ins outs takes gives)
    (inputVals : HList (RV M r) ins) (takenVals : HList M.Val takes) :
    cr.denote M fnTable inputVals takenVals =
      ((cr.start.denote M fnTable (heldValues M r inputVals) takenVals).bind fun st0 =>
        ((cr.body.denote M fnTable (cr.procs.denote M fnTable) []
            (Env.empty.extend cr.inputs (heldValues M r inputVals)) st0).mapHalt Prod.fst).bind
          fun out => (cr.finish.denote M fnTable out.2).map fun g => (out.1, g)).map
        fun out => (unheldValues M r out.1, out.2) := rfl

private theorem deployed_run_unfold (d : Deployed V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    d.run M r ins taken =
      (Stack.start M (Defs.fnTable M d.admitted.program.defs) (d.stack r) ins taken).bind fun first =>
        (((Stack.handler M (Defs.fnTable M d.admitted.program.defs) (Defs.rTable M d.admitted.program.defs)
            (d.stack r)).run (retryOf M d.retry) (roleMeaning M d.admitted.program d.callee r [] ins) first).mapHalt
          Prod.fst).bind fun out =>
          (Stack.finish M (Defs.fnTable M d.admitted.program.defs) (d.stack r) out.2).map
            fun gives => (out.1, gives) := rfl

private theorem subtreeFree_clauses_of_active {hs : Headers V} {r : Role} {ins : List (LTy V)}
    (layers : List (Layer V hs r ins)) (retry : Option (Nat × Site)) (th : List Key)
    (h : subtreeFree (stackActiveSites layers retry) th = true) :
    subtreeFree (stackClauseSites layers) th = true := by
  cases retry with
  | none => exact h
  | some bs =>
      unfold stackActiveSites at h
      unfold subtreeFree at h ⊢
      rw [List.all_cons, Bool.and_eq_true] at h
      exact h.2

/-! ## Main soundness theorems (`specialize_sound`, `specialize_deploy_sound`, `specialize_deployIdeal_sound`) -/

/-- **Handler specialization soundness (with DAG-preserving multi-procedure sharing).**
For any deployed scheme `d` with well-nested retry (satisfied whenever `d.retry = none`
and for every scheme returned by `deploy` or `deployIdeal`), the specialized `ClosedRole`
has the exact same denotation as `d.run` on every model `M`, role `r`, inputs `ins`, and
taken values `taken`. -/
theorem specialize_sound (d : Deployed V) (r : Role)
    (hRetry : d.WellNestedRetry)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken := by
  let defs := d.admitted.program.defs
  let fnTable := Defs.fnTable M defs
  let layers := d.stack r
  let σ := Stack.States layers
  let activeSites := stackActiveSites layers d.retry
  let rootDemands := collectEntryDemands activeSites defs d.callee [] FinPerm.identity r
  let pool := buildSharedProcs σ defs id rootDemands
  let retryCfg := d.retry.map fun (bound, site) => (bound, site, stackAgain layers)
  have hInit : (stackInit layers).denote M fnTable (heldValues M r ins) taken =
      Stack.start M fnTable layers ins taken :=
    stackInit_denote M fnTable layers ins taken
  rw [closedRole_denote_eq, deployed_run_unfold]
  dsimp only [specialize]
  erw [hInit, Process.map_bind]
  congr 1; funext st0
  rw [Process.map_bind]
  let hStack := Stack.handler M fnTable (Defs.rTable M defs) layers
  let procTable := pool.procs.denote M fnTable
  have hSpec : SpecOpSound M fnTable procTable hStack
      ((specializeStack defs layers).liftProcs emptyProcLift) :=
    specOpSound_liftProcs_nil M fnTable procTable hStack (specializeStack defs layers)
      (specializeStack_sound M defs layers)
  have hShared : SharedLookupSound M procTable hStack
      (fun path => subtreeFree (stackClauseSites layers) (Frame.applications path) = true)
      defs pool.lookup :=
    buildSharedProcs_sound M fnTable hStack
      (fun path => subtreeFree (stackClauseSites layers) (Frame.applications path) = true)
      (pathRelClosed_free (stackClauseSites layers))
      (fun pt => unhandledSpecOp_sound_on_free M defs pt layers)
      defs id (fun _ _ => rfl) rootDemands
  have hRC : RetryCfgOk M fnTable hStack retryCfg := by
    cases hR : d.retry with
    | none => simp [retryCfg, hR, RetryCfgOk]
    | some bs =>
        simp only [retryCfg, hR, Option.map_some, RetryCfgOk]
        exact stackAgain_eval M fnTable (Defs.rTable M defs) layers
  have hRetryIn : ∀ b site ag, retryCfg = some (b, site, ag) → site ∈ activeSites := by
    intro b site ag hc
    cases hR : d.retry with
    | none => simp [retryCfg, hR] at hc
    | some bs =>
        cases bs with
        | mk b0 s0 =>
            simp only [retryCfg, hR, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨_, rfl, _⟩ := hc
            simp [activeSites, stackActiveSites, hR]
  have hRetEq : retryOfCfg M retryCfg = retryOf M d.retry := by
    cases hR : d.retry <;> simp [retryCfg, hR, retryOfCfg, retryOf]
  have hWN : ∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications [] = [] ∧ Shape.noNestedAttempt site [] d.entry.shape = true := by
    intro b site ag hc
    cases hR : d.retry with
    | none => simp [retryCfg, hR] at hc
    | some bs =>
        cases bs with
        | mk b0 s0 =>
            simp only [retryCfg, hR, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨_, rfl, _⟩ := hc
            exact ⟨rfl, hRetry b0 s0 hR⟩
  have hBody := specializeProtocolInDefs_sound M fnTable procTable hStack
    ((specializeStack defs layers).liftProcs emptyProcLift) activeSites
    (fun th path => Frame.applications path = th) pathRelClosed_exact hSpec
    (fun path => subtreeFree (stackClauseSites layers) (Frame.applications path) = true)
    (fun th path hP hFr => by rw [hP]; exact subtreeFree_clauses_of_active layers d.retry th hFr)
    defs id (fun _ _ => rfl) pool.lookup hShared retryCfg hRC hRetryIn
    d.callee [] FinPerm.identity r [] ins st0 Process.done rfl hWN
  rw [mapR_congr M (ρ₂ := id) FinPerm.apply_identity, mapR_id, Process.bind_pure, hRetEq,
    ← roleMeaning_eq_rTable] at hBody
  have hBodyMap : (hStack.run (retryOf M d.retry) (roleMeaning M d.admitted.program d.callee r [] ins) st0).mapHalt Prod.fst =
      (((specializeProtocolInDefs ((specializeStack defs layers).liftProcs emptyProcLift)
            activeSites defs id pool.lookup retryCfg d.callee [] FinPerm.identity r).2.denote
          M fnTable procTable []
          (Env.empty.extend
            (specializeProtocolInDefs ((specializeStack defs layers).liftProcs emptyProcLift)
              activeSites defs id pool.lookup retryCfg d.callee [] FinPerm.identity r).1
            (heldValues M r ins)) st0).mapHalt Prod.fst).map fun out => (unheldValues M r out.1, out.2) := by
    rw [hBody]
    dsimp only [Handler.run]
    rw [← Process.map_eq_bind, mapHalt_map]
  rw [hBodyMap, Process.bind_map]
  congr 1; funext out
  rw [stackFinish_denote M fnTable layers out.2, Process.map_map]

/-- Corollary of `specialize_sound` for deployments without retry (`d.retry = none`). -/
theorem specialize_sound_noRetry (d : Deployed V) (r : Role) (hNoRetry : d.retry = none)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_sound M d r (fun _ _ h => by rw [hNoRetry] at h; cases h) ins taken

/-- **Handler specialization soundness for every scheme returned by `deploy`.**
Because `deploy` rejects nested self-retry in `checkNonInteractiveScope` and forbids retry in
`checkInteractiveScope`, every deployed scheme satisfies `Deployed.WellNestedRetry`. -/
theorem specialize_deploy_sound (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (hDep : deploy enc a declaration = .ok d) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_sound M d r (deploy_wellNestedRetry enc a declaration d hDep) ins taken

/-- **Handler specialization soundness for every scheme returned by `deployIdeal`.** -/
theorem specialize_deployIdeal_sound (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (hDep : deployIdeal enc serviceKey a declaration = .ok d) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_sound M d r (deployIdeal_wellNestedRetry enc serviceKey a declaration d hDep) ins taken

end Soundness

end Zkc.Core
