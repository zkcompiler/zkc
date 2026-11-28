module

public import Zkc.Core.Run.Specialize.CoreLemmas

@[expose] public section

/-!
Soundness of structured bounded retry lowering (`ClosedTerm.retry`) in handler specialization.

Proves the correspondence between `Handler.inside` / `attempts` and `retryAttempts`, and establishes
`specializeTerm_sound_attempt` for both retried and non-retried `.attempt` terms.
-/

namespace Zkc.Core

section AttemptSoundness
variable {V : Vocabulary} (M : Model V)

theorem handler_inside_settle_bind {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (bound : Nat) (site : Site) (i : Nat) {A B : Type}
    (p : Program M A) (hp : NoSettleAt M site p)
    (at_ : Occurrence) (hAt : at_.site = site)
    (k : A → Program M B) (s : HList M.Val σ) :
    h.inside (retryOf M (some (bound, site))) i
        (p.bind fun a => .call (.settle at_) fun _ => k a) s =
      ((Process.markOwn M (.attempt site.key i) (h.run (retryOf M none) p s)).mapHalt
          fun stop => ((true, stop.1), stop.2)).bind fun out =>
        (h.run (retryOf M (some (bound, site))) (k out.1) out.2).mapHalt
          fun stop => ((false, stop.1), stop.2) := by
  induction p generalizing s with
  | done a =>
      simp only [Process.bind, Handler.inside, retryOf, hAt, ↓reduceIte, Handler.run,
        Process.markOwn, Process.mapHalt]
  | halt why => rfl
  | call op next ih =>
      have hNotEnd : (retryOf M (some (bound, site))).ends op = none := by
        cases op with
        | settle at2 =>
            dsimp only [retryOf]
            rw [ite_eq_right hp.1]
        | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | «begin» _ => rfl
      rw [Process.bind, Handler.inside, Handler.run, hNotEnd]
      dsimp only [retryOf]
      rw [markOwn_bind, mapHalt_bind, Process.bind_assoc]
      congr 1; funext out
      exact ih out.1 (hp.2 out.1) out.2

theorem attempts_bind_settle {σ : List V.Ty} {A B : Type}
    (exhausted : Stop)
    (again : Nat → HList M.Val σ → HList M.Val σ → Except Stop (HList M.Val σ))
    (body : Nat → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ))
    (after : A → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (B × HList M.Val σ))
    (entry : HList M.Val σ) :
    ∀ (n i : Nat) (s : HList M.Val σ),
      attempts Stop.isAbort exhausted again
          (fun j s' => ((body j s').mapHalt fun stop => ((true, stop.1), stop.2)).bind fun out =>
            (after out.1 out.2).mapHalt fun stop => ((false, stop.1), stop.2))
          entry n i s =
        (retryAttempts M exhausted again body entry n i s).bind fun out => after out.1 out.2
  | 0, _, _ => rfl
  | 1, i, s => by
      dsimp only [attempts, retryAttempts]
      generalize body i s = P
      induction P with
      | done out =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          exact recover_mapHalt_false Stop.isAbort (fun stop => .halt (exhausted, stop.2)) (after out.1 out.2)
      | halt stop =>
          simp only [Process.mapHalt, Process.bind, Process.recover, Bool.true_and]
          cases Stop.isAbort stop.1 <;> rfl
      | call op k ih =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          congr 1; funext reply; exact ih reply
  | m + 2, i, s => by
      conv => lhs; rw [attempts]
      conv => rhs; rw [retryAttempts]
      dsimp only
      generalize body i s = P
      induction P with
      | done out =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          exact recover_mapHalt_false Stop.isAbort _ (after out.1 out.2)
      | halt stop =>
          simp only [Process.mapHalt, Process.bind, Process.recover, Bool.true_and]
          cases Stop.isAbort stop.1
          · rfl
          · cases again (i + 1) entry stop.2 with
            | error why => rfl
            | ok next => exact attempts_bind_settle exhausted again body after entry (m + 1) (i + 1) next
      | call op k ih =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          congr 1; funext reply; exact ih reply

theorem specializeTerm_sound_attempt {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
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
    (hRC : RetryCfgOk M fullTable h retryCfg)
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs mid : List (LTy V)} (key : Key) (w : Holders) (owns : (roleDialect V hs r).Attempt w)
    (idxNm : Name)
    (body : Term (roleDialect V hs r) (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) mid)
    (results : Names mid) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hBody : ∀ {ΔB : Ctx V.Ty} (hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) ΔB),
      SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply through perm r retryCfg hCtxB body)
    (hBodyNone : ∀ {ΔB : Ctx V.Ty} (hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) ΔB),
      SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply through perm r none hCtxB body)
    (hRest : SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply through perm r retryCfg
      (hCtx.extend results) rest) :
    SpecTermHyp M fullTable procTable h specOp pathRel fnTable rTable fnLift specApply through perm r retryCfg hCtx
      (.attempt key w owns (.cons idxNm .nil) body results rest) := by
  intro path env cenv s _ cont hEnv hPR hWN
  rw [Term.denote_attempt]
  conv => rhs; rw [specializeTerm]; dsimp only
  rw [mapR_bind, Process.bind_assoc]
  by_cases hw : r ∈ w
  · have hBeg : (roleSem M r fnTable rTable).begin w key path =
        Process.call (ROp.begin ⟨path, key⟩) fun n => Process.done (hide M r (LTy.index w) n) := by
      dsimp only [roleSem]; exact ite_eq_left hw
    have hSet : (roleSem M r fnTable rTable).settle w key path =
        Process.call (ROp.settle ⟨path, key⟩) fun _ => Process.done () := by
      dsimp only [roleSem]; exact ite_eq_left hw
    rw [hBeg, hSet, dite_eq_left hw]
    dsimp only [mapR, Process.bind]
    have hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil))
        (Δ.extend (.cons (a := Ty.nat) idxNm .nil)) :=
      hCtx.insert_held idxNm (a := LTy.index w)
    have hNonRetry : ∀ (hNotBeg : (retryOfCfg M retryCfg).begins (.begin ⟨path, key⟩) = none),
        h.run (retryOfCfg M retryCfg)
          (.call (.begin ⟨path, key⟩) fun n =>
            (mapR M perm.apply (body.denote (roleSem M r fnTable rTable) path
              (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) n) .nil)))).bind
              fun mids => .call (.settle ⟨path, key⟩) fun _ =>
                (mapR M perm.apply (rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s =
        ((ClosedTerm.letBind
            (.letBind (specOp through key .begin .nil) (.cons (a := Ty.nat) idxNm .nil)
              (.seq (specializeTerm specOp fnLift specApply retryCfg through perm r hCtxB body)
                (specOp through key .settle .nil)))
            (heldNames r results)
            (specializeTerm specOp fnLift specApply retryCfg through perm r (hCtx.extend results) rest)).denote
          M fullTable procTable path cenv s).bind fun out =>
          h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2 := by
      intro hNotBeg
      rw [handler_run_call_nonBegin M h _ _ hNotBeg]
      dsimp only [ClosedTerm.denote]
      rw [hSpec through key .begin .nil path cenv s hPR, Process.bind_assoc,
        Process.bind_assoc, Process.bind_map]
      dsimp only [ResidualOp.toROp, Env.all, ResidualOp.replyOf]
      congr 1; funext outB
      have hInsEnv : EnvRel M r hCtxB
          (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) outB.1) .nil))
          (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons outB.1 .nil)) := by
        have h1 := hEnv.insert_held M idxNm hw (hide M r (LTy.index w) outB.1)
        rw [reveal_hide] at h1
        exact h1
      rw [Process.bind_assoc,
        hBody hCtxB path _ _ outB.2 _ hInsEnv hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2.1⟩)]
      congr 1; funext outM
      rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial),
        hSpec through key .settle .nil path _ outM.2 hPR,
        Process.bind_map, Process.bind_map]
      dsimp only [ResidualOp.toROp, Env.all, ResidualOp.replyOf]
      congr 1; funext outS
      have hEx := hEnv.extend M results (unheldValues M r outM.1)
      rw [heldValues_unheldValues] at hEx
      exact hRest path _ _ outS.2 cont hEx hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2.2⟩)
    cases retryCfg with
    | none =>
        dsimp only
        simpa only [mapR_bind, mapR, Process.bind_assoc, Process.bind] using hNonRetry rfl
    | some cfg =>
        cases cfg with
        | mk bound sr =>
            cases sr with
            | mk retrySite again =>
                dsimp only
                have hPath : Frame.applications path = through := (hWN bound retrySite again rfl).1
                by_cases hSite : (⟨through, key⟩ : Site) = retrySite
                · rw [ite_eq_left hSite]
                  have hOccSite : (⟨path, key⟩ : Occurrence).site = retrySite := by
                    simpa [Occurrence.site, hPath] using hSite
                  have hBegHit : (retryOf M (some (bound, retrySite))).begins (.begin ⟨path, key⟩) =
                      some (.declared .exhausted ⟨path, key⟩, fun i => i) := by
                    dsimp only [retryOf]; exact ite_eq_left hOccSite
                  dsimp only [ClosedTerm.denote, retryOfCfg]
                  conv => lhs; rw [Handler.run, hBegHit]
                  dsimp only
                  have hRetr : (retryOf M (some (bound, retrySite))).retriable = Stop.isAbort := rfl
                  have hBnd : (retryOf M (some (bound, retrySite))).bound = bound := rfl
                  rw [hRetr, hBnd]
                  dsimp only [RetryCfgOk] at hRC
                  rw [← hRC]
                  have hKeyEq : retrySite.key = key := by cases hSite; rfl
                  have hBodyEq : ∀ (i : Nat) (s' : HList M.Val σ),
                      h.inside (retryOf M (some (bound, retrySite))) i
                        ((mapR M perm.apply ((body.denote (roleSem M r fnTable rTable) path
                            (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil))).bind
                          fun mids => .call (.settle ⟨path, key⟩) fun _ =>
                            rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s' =
                      ((Process.markOwn M (.attempt key i)
                          ((specializeTerm specOp fnLift specApply none through perm r hCtxB body).denote
                            M fullTable procTable path (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (i : Nat) .nil)) s')).mapHalt
                          fun stop => ((true, stop.1), stop.2)).bind fun outM =>
                        (((specializeTerm specOp fnLift specApply (some (bound, retrySite, again))
                            through perm r (hCtx.extend results) rest).denote
                          M fullTable procTable path (cenv.extend (heldNames r results) outM.1) outM.2).bind fun outR =>
                          h.run (retryOf M (some (bound, retrySite))) (cont (unheldValues M r outR.1)) outR.2).mapHalt
                          fun stop => ((false, stop.1), stop.2) := by
                    intro i s'
                    rw [mapR_bind, Process.bind_assoc]
                    dsimp only [mapR, Process.bind]
                    have hNoS : NoSettleAt M retrySite
                        (mapR M perm.apply (body.denote (roleSem M r fnTable rTable) path
                          (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil)))) :=
                      noSettleAt_mapR M perm.apply ((hWN bound retrySite again rfl).2.1 hw hSite path _ hPath)
                    rw [handler_inside_settle_bind M h bound retrySite i _ hNoS ⟨path, key⟩ hOccSite _ s',
                      hKeyEq]
                    have hInsEnv : EnvRel M r hCtxB
                        (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil))
                        (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (i : Nat) .nil)) := by
                      have h1 := hEnv.insert_held M idxNm hw (hide M r (LTy.index w) i)
                      rw [reveal_hide] at h1
                      exact h1
                    have hBodyPure := hBodyNone hCtxB path _ _ s'
                      Process.done hInsEnv hPR (fun _ _ _ hc => nomatch hc)
                    rw [Process.bind_pure] at hBodyPure
                    dsimp only [retryOfCfg] at hBodyPure
                    rw [hBodyPure, markOwn_bind, mapHalt_bind, Process.bind_assoc]
                    congr 1; funext outM
                    dsimp only [Handler.run, Process.markOwn, Process.mapHalt, Process.bind, mapR]
                    congr 1
                    have hEx := hEnv.extend M results (unheldValues M r outM.1)
                    rw [heldValues_unheldValues] at hEx
                    exact hRest path _ _ outM.2 cont hEx hPR (fun b' s' ag' hc => by
                      cases hc; exact ⟨hPath, (hWN bound retrySite again rfl).2.2.2⟩)
                  have hFun : (fun i s' => h.inside (retryOf M (some (bound, retrySite))) i
                      ((mapR M perm.apply ((body.denote (roleSem M r fnTable rTable) path
                          (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil))).bind
                        fun mids => .call (.settle ⟨path, key⟩) fun _ =>
                          rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s') =
                      (fun i s' => ((Process.markOwn M (.attempt key i)
                          ((specializeTerm specOp fnLift specApply none through perm r hCtxB body).denote
                            M fullTable procTable path (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (i : Nat) .nil)) s')).mapHalt
                          fun stop => ((true, stop.1), stop.2)).bind fun outM =>
                        (((specializeTerm specOp fnLift specApply (some (bound, retrySite, again))
                            through perm r (hCtx.extend results) rest).denote
                          M fullTable procTable path (cenv.extend (heldNames r results) outM.1) outM.2).bind fun outR =>
                          h.run (retryOf M (some (bound, retrySite))) (cont (unheldValues M r outR.1)) outR.2).mapHalt
                          fun stop => ((false, stop.1), stop.2)) := by
                    funext i s'; exact hBodyEq i s'
                  rw [hFun, Process.bind_assoc]
                  exact attempts_bind_settle M (.declared .exhausted ⟨path, key⟩)
                    (StackAgain.eval M fullTable again)
                    (fun j s' => Process.markOwn M (.attempt key j)
                      ((specializeTerm specOp fnLift specApply none through perm r hCtxB body).denote
                        M fullTable procTable path (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (j : Nat) .nil)) s'))
                    (fun a st => ((specializeTerm specOp fnLift specApply (some (bound, retrySite, again))
                        through perm r (hCtx.extend results) rest).denote
                      M fullTable procTable path (cenv.extend (heldNames r results) a) st).bind fun outR =>
                      h.run (retryOf M (some (bound, retrySite))) (cont (unheldValues M r outR.1)) outR.2)
                    s bound 0 s
                · rw [ite_eq_right hSite]
                  have hOccNe : (⟨path, key⟩ : Occurrence).site ≠ retrySite := by
                    simpa [Occurrence.site, hPath] using hSite
                  have hNotBeg : (retryOfCfg M (some (bound, retrySite, again))).begins (.begin ⟨path, key⟩) = none := by
                    dsimp only [retryOfCfg, retryOf]
                    exact ite_eq_right hOccNe
                  simpa only [mapR_bind, mapR, Process.bind_assoc, Process.bind] using hNonRetry hNotBeg
  · have hBeg : (roleSem M r fnTable rTable).begin w key path =
        Process.done (hide M r (LTy.index w) 0) := by
      dsimp only [roleSem]; exact ite_eq_right hw
    have hSet : (roleSem M r fnTable rTable).settle w key path = Process.done () := by
      dsimp only [roleSem]; exact ite_eq_right hw
    rw [hBeg, hSet, dite_eq_right hw]
    conv => rhs; rw [ClosedTerm.denote]
    dsimp only [mapR, Process.bind]
    rw [mapR_bind, Process.bind_assoc, Process.bind_assoc]
    have hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) Δ :=
      hCtx.insert_unheld idxNm (a := LTy.index w) hw
    have hInsEnv : EnvRel M r hCtxB
        (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) (0 : Nat)) .nil)) cenv :=
      hEnv.insert_unheld M idxNm hw (hide M r (LTy.index w) (0 : Nat))
    rw [hBody hCtxB path _ cenv s _ hInsEnv hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2.1⟩)]
    congr 1; funext outM
    have hEx := hEnv.extend M results (unheldValues M r outM.1)
    rw [heldValues_unheldValues] at hEx
    exact hRest path _ _ outM.2 cont hEx hPR (fun b site ag hc => ⟨(hWN b site ag hc).1, (hWN b site ag hc).2.2.2⟩)

end AttemptSoundness

end Zkc.Core
