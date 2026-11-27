module

public import Zkc.Core.Program.Sites
public import Zkc.Core.Run.Specialize.Compiler

@[expose] public section

/-!
Core process, handler, nesting, and subtree-freedom lemmas for handler specialization soundness.

Provides:
- `Process` / `mapHalt` / `markOwn` / `mapR` / `Handler` algebra lemmas;
- `NoBeginAt` and `handler_run_bind_noBegin`, linking retried runs to non-retried runs on
  subtree-free shared protocol calls;
- `NoSettleAt` and `RoleTermWellNested` derived from `Shape.attemptSites` / `Shape.noNestedAttempt`;
- `SpecOpSoundOn` (unifying full `specializeStack` and subtree-free `unhandledSpecOp`),
  `unhandledSpecOp_sound_on_free`, and the CPS induction hypothesis `SpecTermHyp`.
-/

namespace Zkc.Core

section CoreSpecLemmas
variable {V : Vocabulary} (M : Model V)

/-! ## `Process`, `mapR`, `markOwn`, and `Handler` algebra -/

theorem mapHalt_bind {S : Sig} {H H' A B : Type} (f : H → H')
    (p : Process S H A) (k : A → Process S H B) :
    (p.bind k).mapHalt f = (p.mapHalt f).bind fun a => (k a).mapHalt f := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      simp only [Process.bind, Process.mapHalt]
      congr 1; funext reply; exact ih reply

theorem mapHalt_map {S : Sig} {H H' A B : Type} (f : H → H') (g : A → B)
    (p : Process S H A) :
    (p.map g).mapHalt f = (p.mapHalt f).map g := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      simp only [Process.map, Process.mapHalt]
      congr 1; funext reply; exact ih reply

theorem mapHalt_mapHalt {S : Sig} {H₁ H₂ H₃ A : Type} (f : H₁ → H₂) (g : H₂ → H₃)
    (p : Process S H₁ A) :
    (p.mapHalt f).mapHalt g = p.mapHalt fun h => g (f h) := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      simp only [Process.mapHalt]
      congr 1; funext reply; exact ih reply

theorem markOwn_bind (frame : Frame) {H A B : Type}
    (p : Process (RSig M) H A) (k : A → Process (RSig M) H B) :
    Process.markOwn M frame (p.bind k) =
      (Process.markOwn M frame p).bind fun a => Process.markOwn M frame (k a) := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      cases op with
      | own kind hearers _ _ _ _ =>
          cases kind with
          | coin _ =>
              cases hearers <;> (simp only [Process.bind, Process.markOwn]; congr 1; funext reply; exact ih reply)
          | request _ =>
              simp only [Process.bind, Process.markOwn]
              congr 1; funext reply; exact ih reply
      | give _ _ _ _ _ | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [Process.bind, Process.markOwn]
          congr 1; funext reply; exact ih reply

theorem markOwn_map (frame : Frame) {H A B : Type} (f : A → B)
    (p : Process (RSig M) H A) :
    Process.markOwn M frame (p.map f) = (Process.markOwn M frame p).map f := by
  rw [Process.map_eq_bind, Process.map_eq_bind, markOwn_bind]
  rfl

theorem markOwn_mapHalt (frame : Frame) {H H' A : Type} (f : H → H')
    (p : Process (RSig M) H A) :
    Process.markOwn M frame (p.mapHalt f) = (Process.markOwn M frame p).mapHalt f := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      cases op with
      | own kind hearers _ _ _ _ =>
          cases kind with
          | coin _ =>
              cases hearers <;> (simp only [Process.mapHalt, Process.markOwn]; congr 1; funext reply; exact ih reply)
          | request _ =>
              simp only [Process.mapHalt, Process.markOwn]
              congr 1; funext reply; exact ih reply
      | give _ _ _ _ _ | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [Process.mapHalt, Process.markOwn]
          congr 1; funext reply; exact ih reply

theorem mapR_id {A : Type} (p : Program M A) : mapR M id p = p := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op k ih =>
      cases op with
      | give _ getters _ _ _ =>
          dsimp only [mapR]
          have hM : getters.map id = getters := List.map_id getters
          generalize getters.map id = gs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | own _ hearers _ _ _ _ =>
          dsimp only [mapR]
          have hM : hearers.map id = hearers := List.map_id hearers
          generalize hearers.map id = hs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [mapR, id_eq]
          congr 1; funext reply; exact ih reply

theorem mapR_comp (ρ₁ ρ₂ : Role → Role) {A : Type} (p : Program M A) :
    mapR M ρ₁ (mapR M ρ₂ p) = mapR M (fun q => ρ₁ (ρ₂ q)) p := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op k ih =>
      cases op with
      | give _ getters _ _ _ =>
          dsimp only [mapR]
          have hM : (getters.map ρ₂).map ρ₁ = getters.map (fun q => ρ₁ (ρ₂ q)) := List.map_map
          generalize (getters.map ρ₂).map ρ₁ = gs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | own _ hearers _ _ _ _ =>
          dsimp only [mapR]
          have hM : (hearers.map ρ₂).map ρ₁ = hearers.map (fun q => ρ₁ (ρ₂ q)) := List.map_map
          generalize (hearers.map ρ₂).map ρ₁ = hs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [mapR]
          congr 1; funext reply; exact ih reply

theorem mapR_congr {ρ₁ ρ₂ : Role → Role} (hEq : ∀ q, ρ₁ q = ρ₂ q) {A : Type} (p : Program M A) :
    mapR M ρ₁ p = mapR M ρ₂ p := by
  have hFun : ρ₁ = ρ₂ := funext hEq
  subst hFun; rfl

theorem mapR_bind (ρ : Role → Role) {A B : Type} (p : Program M A) (k : A → Program M B) :
    mapR M ρ (p.bind k) = (mapR M ρ p).bind fun a => mapR M ρ (k a) := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      cases op <;> (simp only [Process.bind, mapR]; congr 1; funext reply; exact ih reply)

theorem mapR_map (ρ : Role → Role) {A B : Type} (f : A → B) (p : Program M A) :
    mapR M ρ (p.map f) = (mapR M ρ p).map f := by
  rw [Process.map_eq_bind, Process.map_eq_bind, mapR_bind]
  rfl

theorem mapR_liftLocal (ρ : Role → Role) {A : Type} (lp : Local A) :
    mapR M ρ (liftLocal (S := RSig M) id lp) = liftLocal (S := RSig M) id lp := by
  cases lp with
  | done _ => rfl
  | halt _ => rfl
  | call op _ => nomatch op

theorem handler_run_liftLocal {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (retry : Retry (RSig M) (RSig M) Stop) {A B : Type}
    (lp : Local A) (k : A → Program M B) (s : HList M.Val σ) :
    h.run retry ((liftLocal (S := RSig M) id lp).bind k) s =
      (liftLocal (S := RSig M) (fun why => (why, s)) lp).bind fun a => h.run retry (k a) s := by
  cases lp with
  | done _ => rfl
  | halt _ => rfl
  | call op _ => nomatch op

theorem handler_run_noRetry_bind {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ)) {A B : Type}
    (p : Program M A) (k : A → Program M B) (s : HList M.Val σ) :
    h.run (retryOf M none) (p.bind k) s =
      (h.run (retryOf M none) p s).bind fun out => h.run (retryOf M none) (k out.1) out.2 := by
  induction p generalizing s with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      dsimp only [Process.bind, Handler.run, retryOf]
      rw [Process.bind_assoc]
      congr 1; funext out
      exact ih out.1 out.2

theorem handler_answer_mapHalt_const {σ : List V.Ty} {E A : Type}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (p : Program M A) (e : E) (s : HList M.Val σ) :
    h.answer (p.mapHalt fun why => (why, e)) e s =
      (h.run (retryOf M none) p s).mapHalt fun stop => (stop.1, e, stop.2) := by
  induction p generalizing s with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      dsimp only [Process.mapHalt, Handler.answer, Handler.run, retryOf]
      rw [mapHalt_bind]
      congr 1; funext out
      exact ih out.1 out.2

theorem recover_mapHalt_false {S : Sig} {H σ A : Type} (retriable : H → Bool)
    (onRetry : (Bool × H) × σ → Process S (H × σ) (A × σ))
    (p : Process S (H × σ) (A × σ)) :
    ((p.mapHalt fun s => ((false, s.1), s.2)).recover fun stop =>
      if stop.1.1 && retriable stop.1.2 then onRetry stop else .halt (stop.1.2, stop.2)) = p := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op k ih =>
      simp only [Process.mapHalt, Process.recover]
      congr 1; funext reply; exact ih reply

theorem handler_run_call_nonBegin {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (retry : Retry (RSig M) (RSig M) Stop) (op : ROp M)
    (hNotBeg : retry.begins op = none) {A : Type} (k : (RSig M).Reply op → Program M A)
    (s : HList M.Val σ) :
    h.run retry (.call op k) s = (h.clause op s).bind fun out => h.run retry (k out.1) out.2 := by
  rw [Handler.run, hNotBeg]

theorem localOp_lift_eq {fns₁ fns₂ : List (FnHeader V)}
    (t₁ : FnTable M fns₁) (t₂ : FnTable M fns₂)
    (fnLift : ∀ {hdr}, Member fns₁ hdr → Member fns₂ hdr)
    (hLift : ∀ hdr (f : Member fns₁ hdr), t₂ hdr (fnLift f) = t₁ hdr f)
    {ins res : List V.Ty} (lo : LocalOp V fns₁ ins res) (args : HList M.Val ins) :
    localOp M t₂ (lo.lift fnLift) args = localOp M t₁ lo args := by
  cases lo with
  | row _ _ _ | owned _ | literal _ _ _ => rfl
  | call callee => exact congrFun (hLift _ callee) args

def liftPick (r : Role) (ps : Holders) :
    {l : List V.Ty} → Pick M.Val l → Pick (RV M r) (l.map fun τ => ⟨τ, ps⟩)
  | _ :: _, .here u => .here (hide M r ⟨_, ps⟩ u)
  | _ :: _, .there p => .there (liftPick r ps p)

theorem pickAt_eq_liftPick (r : Role) (ps : Holders) :
    ∀ (altsT : Tys V.TypeKey) (u : altsT.Choice M.toCarriers),
      Tys.pickAt M ps (W := RV M r) (fun τ v => hide M r ⟨τ, ps⟩ v) altsT u =
        liftPick M r ps (Tys.pick M altsT u)
  | .nil, u => nomatch u
  | .cons _ _, .inl _ => rfl
  | .cons _ _, .inr v => congrArg Pick.there (pickAt_eq_liftPick r ps _ v)

/-! ## `NoBeginAt` and `handler_run_bind_noBegin` -/

/-- A role process emits no `.begin` matching `retry.begins`. -/
def NoBeginFor (retry : Retry (RSig M) (RSig M) Stop) {A : Type} : Program M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k => retry.begins op = none ∧ ∀ reply, NoBeginFor retry (k reply)

theorem noBeginFor_bind {retry : Retry (RSig M) (RSig M) Stop} {A B : Type}
    {p : Program M A} {k : A → Program M B}
    (hp : NoBeginFor M retry p) (hk : ∀ a, NoBeginFor M retry (k a)) :
    NoBeginFor M retry (p.bind k) := by
  induction p with
  | done a => exact hk a
  | halt _ => trivial
  | call op next ih => exact ⟨hp.1, fun reply => ih reply (hp.2 reply)⟩

theorem noBeginFor_map {retry : Retry (RSig M) (RSig M) Stop} {A B : Type}
    (f : A → B) {p : Program M A} (hp : NoBeginFor M retry p) :
    NoBeginFor M retry (p.map f) := by
  rw [Process.map_eq_bind]
  exact noBeginFor_bind M hp fun _ => trivial

theorem noBeginFor_mapR {retry : Retry (RSig M) (RSig M) Stop}
    (hPres : ∀ ρ op, retry.begins op = none →
      match op with
      | .give k gs at_ τ x => retry.begins (.give k (gs.map ρ) at_ τ x) = none
      | .get k g at_ τ => retry.begins (.get k (ρ g) at_ τ) = none
      | .own k hs at_ ins pl τ => retry.begins (.own k (hs.map ρ) at_ ins pl τ) = none
      | .hear k o at_ τ => retry.begins (.hear k (ρ o) at_ τ) = none
      | .begin at_ => retry.begins (.begin at_) = none
      | .settle at_ => retry.begins (.settle at_) = none)
    (ρ : Role → Role) {A : Type} {p : Program M A} (hp : NoBeginFor M retry p) :
    NoBeginFor M retry (mapR M ρ p) := by
  induction p with
  | done _ => trivial
  | halt _ => trivial
  | call op next ih =>
      cases op with
      | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          exact ⟨hPres ρ _ hp.1, fun reply => ih reply (hp.2 reply)⟩

theorem noBeginFor_liftLocal {retry : Retry (RSig M) (RSig M) Stop} {A : Type} (lp : Local A) :
    NoBeginFor M retry (liftLocal (S := RSig M) id lp) := by
  cases lp with
  | done _ => trivial
  | halt _ => trivial
  | call op _ => nomatch op

theorem noBeginFor_iterate {retry : Retry (RSig M) (RSig M) Stop} {A : Type}
    {step : Nat → A → Program M A} (hStep : ∀ i a, NoBeginFor M retry (step i a)) :
    ∀ n i a, NoBeginFor M retry (Process.iterate n step i a)
  | 0, _, _ => trivial
  | n + 1, i, a => noBeginFor_bind M (hStep i a) fun a' => noBeginFor_iterate hStep n (i + 1) a'

/-- When `p` never triggers `retry.begins`, running `p.bind cont` under `retry` factors through
running `p` without retry followed by `cont` under `retry`. -/
theorem handler_run_bind_noBegin {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (retry : Retry (RSig M) (RSig M) Stop) {A B : Type}
    (p : Program M A) (hp : NoBeginFor M retry p) (cont : A → Program M B) (s : HList M.Val σ) :
    h.run retry (p.bind cont) s =
      (h.run (retryOf M none) p s).bind fun out => h.run retry (cont out.1) out.2 := by
  induction p generalizing s with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      dsimp only [Process.bind]
      rw [handler_run_call_nonBegin M h retry op hp.1, Handler.run]
      dsimp only [retryOf]
      rw [Process.bind_assoc]
      congr 1; funext out
      exact ih out.1 (hp.2 out.1) out.2

/-- Every occurrence emitted by `Term.denote (roleSem ...)` under `path` extends `Frame.applications path`,
so if `through` is not a prefix of `retrySite.through`, no `.begin` at `retrySite` can occur. -/
theorem noBeginFor_retryOf_roleOp {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) (bound : Nat) (retrySite : Site) (r : Role)
    (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
        (path : List Frame) (ins : HList (RV M r') hdr.ins),
        ¬ ((Frame.applications path).isPrefixOf retrySite.through = true) →
        NoBeginFor M (retryOf M (some (bound, retrySite))) (rTable hdr m r' path ins))
    {Γ : Ctx (LTy V)} {outs ins res : List (LTy V)}
    (key : Key) (o : RoleOp V hs r ins res) (operands : HList (Var Γ) ins)
    (results : Names res) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hNotPref : ¬ ((Frame.applications path).isPrefixOf retrySite.through = true))
    (hRest : ∀ env', NoBeginFor M (retryOf M (some (bound, retrySite)))
      (rest.denote (roleSem M r fnTable rTable) path env')) :
    NoBeginFor M (retryOf M (some (bound, retrySite)))
      ((Term.op key o operands results rest).denote (roleSem M r fnTable rTable) path env) := by
  rw [Term.denote_op]
  cases o with
  | compute _ _ _ _ _ _ =>
      exact noBeginFor_bind M (noBeginFor_map M _ (noBeginFor_liftLocal M _)) fun _ => hRest _
  | absent _ _ => exact hRest _
  | give _ _ _ =>
      cases operands with | cons _ hNil => cases hNil; exact ⟨rfl, fun _ => hRest _⟩
  | get _ _ _ _ _ _ => exact ⟨rfl, fun _ => hRest _⟩
  | keep _ _ =>
      cases operands with | cons _ hNil => cases hNil; exact hRest _
  | own _ _ _ _ _ _ => exact ⟨rfl, fun _ => hRest _⟩
  | hear _ _ _ _ _ => exact ⟨rfl, fun _ => hRest _⟩
  | apply callee roles distinct _ _ _ =>
      refine noBeginFor_bind M (noBeginFor_map M _ (noBeginFor_mapR M (fun ρ op h => by
        cases op <;> exact h) _ ?_)) fun _ => hRest _
      refine hProt callee _ (path ++ [.application key]) _ ?_
      intro hPre
      rw [Frame.applications_append] at hPre
      exact hNotPref (list_isPrefixOf_append_left (Frame.applications path) [key] retrySite.through hPre)

mutual
  theorem noBeginFor_retryOf_roleTerm {hs : Headers V} (fnTable : FnTable M hs.fns)
      (rTable : RTable M hs.protocols) (bound : Nat) (retrySite : Site) (r : Role)
      (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
          (path : List Frame) (ins : HList (RV M r') hdr.ins),
          ¬ ((Frame.applications path).isPrefixOf retrySite.through = true) →
          NoBeginFor M (retryOf M (some (bound, retrySite))) (rTable hdr m r' path ins)) :
      ∀ {Γ : Ctx (LTy V)} {outs : List (LTy V)} (t : Term (roleDialect V hs r) Γ outs)
        (path : List Frame) (env : Env (RV M r) Γ),
        ¬ ((Frame.applications path).isPrefixOf retrySite.through = true) →
        NoBeginFor M (retryOf M (some (bound, retrySite))) (t.denote (roleSem M r fnTable rTable) path env)
    | _, _, .ret _, _, _, _ => trivial
    | _, _, .op key o operands results rest, path, env, hNotPref =>
        noBeginFor_retryOf_roleOp M fnTable rTable bound retrySite r hProt key o operands results rest
          path env hNotPref fun env' =>
            noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path env' hNotPref
    | _, _, .guard _ _ c _ _ rest, path, env, hNotPref => by
        rw [Term.denote_guard]
        cases (roleSem M r fnTable rTable).holds _ (env.get c) with
        | false => trivial
        | true => exact noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path env hNotPref
    | _, _, .choose _ _ c _ _ onTrue onFalse _ rest, path, env, hNotPref => by
        rw [Term.denote_choose]
        refine noBeginFor_bind M ?_ fun _ =>
          noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path _ hNotPref
        cases (roleSem M r fnTable rTable).holds _ (env.get c) with
        | false => exact noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt onFalse path env hNotPref
        | true => exact noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt onTrue path env hNotPref
    | _, _, .cases _ _ _ _ _ arms _ rest, path, env, hNotPref => by
        rw [Term.denote_cases]
        refine noBeginFor_bind M
          (noBeginFor_retryOf_roleArms fnTable rTable bound retrySite r hProt arms path env _ hNotPref)
          fun _ => noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path _ hNotPref
    | _, _, .loop key _ _ _ _ _ body _ rest, path, env, hNotPref => by
        rw [Term.denote_loop]
        refine noBeginFor_bind M (noBeginFor_iterate M (fun i st => ?_) _ _ _) fun _ =>
          noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path _ hNotPref
        refine noBeginFor_bind M ?_ fun _ => trivial
        refine noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt body
          (path ++ [.iteration key i]) _ ?_
        rw [Frame.applications_append]; simpa [Frame.applications] using hNotPref
    | _, _, .block key num body _ rest, path, env, hNotPref => by
        rw [Term.denote_block]
        refine noBeginFor_bind M ?_ fun _ =>
          noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path _ hNotPref
        refine noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt body
          (path ++ [.iteration key num]) env ?_
        rw [Frame.applications_append]; simpa [Frame.applications] using hNotPref
    | _, _, .attempt key w _ _ body _ rest, path, env, hNotPref => by
        rw [Term.denote_attempt]
        by_cases hw : r ∈ w
        · have hBeg : (roleSem M r fnTable rTable).begin w key path =
              .call (.begin ⟨path, key⟩) fun n => .done (hide M r (LTy.index w) n) := by
            dsimp only [roleSem]; exact ite_eq_left hw
          have hSet : (roleSem M r fnTable rTable).settle w key path =
              .call (.settle ⟨path, key⟩) fun _ => .done () := by
            dsimp only [roleSem]; exact ite_eq_left hw
          rw [hBeg, hSet]
          dsimp only [Process.bind]
          have hSiteNe : (⟨path, key⟩ : Occurrence).site ≠ retrySite := by
            intro hEq
            have hTh : Frame.applications path = retrySite.through := congrArg Site.through hEq
            exact hNotPref (by rw [hTh]; exact list_isPrefixOf_self retrySite.through)
          refine ⟨by dsimp only [retryOf]; exact ite_eq_right hSiteNe, fun _ => ?_⟩
          refine noBeginFor_bind M
            (noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt body path _ hNotPref)
            fun _ => ⟨rfl, fun _ =>
              noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path _ hNotPref⟩
        · have hBeg : (roleSem M r fnTable rTable).begin w key path =
              .done (hide M r (LTy.index w) 0) := by
            dsimp only [roleSem]; exact ite_eq_right hw
          have hSet : (roleSem M r fnTable rTable).settle w key path = .done () := by
            dsimp only [roleSem]; exact ite_eq_right hw
          rw [hBeg, hSet]
          dsimp only [Process.bind]
          exact noBeginFor_bind M
            (noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt body path _ hNotPref)
            fun _ => noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt rest path _ hNotPref

  theorem noBeginFor_retryOf_roleArms {hs : Headers V} (fnTable : FnTable M hs.fns)
      (rTable : RTable M hs.protocols) (bound : Nat) (retrySite : Site) (r : Role)
      (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
          (path : List Frame) (ins : HList (RV M r') hdr.ins),
          ¬ ((Frame.applications path).isPrefixOf retrySite.through = true) →
          NoBeginFor M (retryOf M (some (bound, retrySite))) (rTable hdr m r' path ins)) :
      ∀ {Γ : Ctx (LTy V)} {mid payloads : List (LTy V)}
        (arms : Arms (roleDialect V hs r) Γ mid payloads)
        (path : List Frame) (env : Env (RV M r) Γ) (pk : Pick (RV M r) payloads),
        ¬ ((Frame.applications path).isPrefixOf retrySite.through = true) →
        NoBeginFor M (retryOf M (some (bound, retrySite))) (arms.denote (roleSem M r fnTable rTable) path env pk)
    | _, _, _, .nil, _, _, pk, _ => nomatch pk
    | _, _, _, .cons _ arm _, path, _, .here _, hNotPref =>
        noBeginFor_retryOf_roleTerm fnTable rTable bound retrySite r hProt arm path _ hNotPref
    | _, _, _, .cons _ _ more, path, env, .there pk, hNotPref =>
        noBeginFor_retryOf_roleArms fnTable rTable bound retrySite r hProt more path env pk hNotPref
end

theorem noBeginFor_retryOf_defs {hs : Headers V} (defs : Defs V hs) (bound : Nat) (retrySite : Site) :
    ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r : Role)
      (path : List Frame) (ins : HList (RV M r) hdr.ins),
      ¬ ((Frame.applications path).isPrefixOf retrySite.through = true) →
      NoBeginFor M (retryOf M (some (bound, retrySite))) (Defs.rTable M defs hdr m r path ins) := by
  induction defs with
  | nil => intro _ m; exact nomatch m
  | fn _ _ _ _ _ _ ih => exact ih
  | protocol _ inputsP bodyP _ rest ih =>
      intro hdr m r path ins hNotPref
      cases m with
      | head =>
          exact noBeginFor_retryOf_roleTerm M (Defs.fnTable M rest) (Defs.rTable M rest)
            bound retrySite r ih (project r bodyP) path (Env.empty.extend inputsP ins) hNotPref
      | tail m' => exact ih m' r path ins hNotPref

/-! ## `NoSettleAt` from `Shape.attemptSites` -/

/-- A role process emits no `.settle` at `site`. -/
def NoSettleAt (site : Site) {A : Type} : Program M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k =>
      (match op with
       | .settle at_ => at_.site ≠ site
       | _ => True) ∧
      ∀ reply, NoSettleAt site (k reply)

theorem noSettleAt_bind {site : Site} {A B : Type} {p : Program M A}
    {k : A → Program M B} (hp : NoSettleAt M site p) (hk : ∀ a, NoSettleAt M site (k a)) :
    NoSettleAt M site (p.bind k) := by
  induction p with
  | done a => exact hk a
  | halt _ => trivial
  | call op next ih =>
      cases op with
      | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          exact ⟨hp.1, fun reply => ih reply (hp.2 reply)⟩

theorem noSettleAt_map {site : Site} {A B : Type} (f : A → B) {p : Program M A}
    (hp : NoSettleAt M site p) : NoSettleAt M site (p.map f) := by
  rw [Process.map_eq_bind]
  exact noSettleAt_bind M hp fun _ => trivial

theorem noSettleAt_mapR {site : Site} (ρ : Role → Role) {A : Type} {p : Program M A}
    (hp : NoSettleAt M site p) : NoSettleAt M site (mapR M ρ p) := by
  induction p with
  | done _ => trivial
  | halt _ => trivial
  | call op next ih =>
      cases op with
      | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          exact ⟨hp.1, fun reply => ih reply (hp.2 reply)⟩

theorem noSettleAt_liftLocal {site : Site} {A : Type} (lp : Local A) :
    NoSettleAt M site (liftLocal (S := RSig M) id lp) := by
  cases lp with
  | done _ => trivial
  | halt _ => trivial
  | call op _ => nomatch op

theorem noSettleAt_iterate {site : Site} {A : Type}
    {step : Nat → A → Program M A} (hStep : ∀ i a, NoSettleAt M site (step i a)) :
    ∀ n i a, NoSettleAt M site (Process.iterate n step i a)
  | 0, _, _ => trivial
  | n + 1, i, a => noSettleAt_bind M (hStep i a) fun a' => noSettleAt_iterate hStep n (i + 1) a'

private theorem not_mem_attemptSites_rest {hs : Headers V} (target : Site) (through : List Key)
    (key : Key) {ins res : List (LTy V)} (o : ProtocolOp V hs ins res) (sh : Shape V)
    (hNot : target ∉ (ProtocolOp.shape key o sh).attemptSites through) :
    target ∉ sh.attemptSites through := by
  cases o with
  | compute _ _ _ _ _ | narrow _ _ => exact hNot
  | flow _ _ _ _ _ | given _ _ _ _ _ _ _ _ => exact hNot
  | apply _ _ _ _ _ _ => exact fun h => hNot (List.mem_append_right _ h)

private theorem noSettleAt_project_op {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (target : Site) (r : Role)
    (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
        (through : List Key) (path : List Frame) (ins : HList (RV M r') hdr.ins),
        Frame.applications path = through →
        target ∉ hdr.shape.attemptSites through →
        NoSettleAt M target (rTable hdr m r' path ins))
    {Γ : Ctx (LTy V)} {outs ins res : List (LTy V)}
    (key : Key) (o : ProtocolOp V hs ins res) (operands : HList (Var Γ) ins)
    (results : Names res) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (sh : Shape V) (through : List Key) (path : List Frame) (env : Env (RV M r) Γ)
    (hP : Frame.applications path = through)
    (hNot : target ∉ (ProtocolOp.shape key o sh).attemptSites through)
    (hRest : ∀ env', NoSettleAt M target (rest.denote (roleSem M r fnTable rTable) path env')) :
    NoSettleAt M target
      ((ProtocolOp.project r key o operands results rest).denote
        (roleSem M r fnTable rTable) path env) := by
  cases o with
  | compute R lo opTys types held =>
      dsimp only [ProtocolOp.project]
      by_cases hIn : r ∈ R
      · rw [dite_eq_left hIn, Term.denote_op]
        exact noSettleAt_bind M (noSettleAt_map M _ (noSettleAt_liftLocal M _)) fun _ => hRest _
      · rw [dite_eq_right hIn, Term.denote_op]
        exact hRest _
  | flow kind giver getters holds apart =>
      cases operands with
      | cons x hNil =>
          cases hNil
          dsimp only [ProtocolOp.project]
          by_cases hG : r = giver
          · rw [dite_eq_left hG, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
            exact ⟨trivial, fun _ => hRest _⟩
          · rw [dite_eq_right hG]
            by_cases hM : r ∈ getters
            · rw [dite_eq_left hM, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
              exact ⟨trivial, fun _ => hRest _⟩
            · rw [dite_eq_right hM, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
              exact hRest _
  | given kind owner hearers opTys τ typed held apart =>
      dsimp only [ProtocolOp.project]
      by_cases hOwn : r = owner
      · rw [dite_eq_left hOwn]
        cases hOwn.symm
        rw [Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
        exact ⟨trivial, fun _ => hRest _⟩
      · rw [dite_eq_right hOwn]
        by_cases hH : r ∈ hearers
        · rw [dite_eq_left hH, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
          exact ⟨trivial, fun _ => hRest _⟩
        · rw [dite_eq_right hH, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
          exact hRest _
  | narrow R among =>
      cases operands with
      | cons x hNil =>
          cases hNil
          dsimp only [ProtocolOp.project]
          by_cases hIn : r ∈ R
          · rw [dite_eq_left hIn, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
            exact hRest _
          · rw [dite_eq_right hIn, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
            exact hRest _
  | apply callee roles distinct covers opTys fits =>
      dsimp only [ProtocolOp.project, ProtocolOp.shape, Shape.attemptSites] at hNot ⊢
      rw [Term.denote_op]
      refine noSettleAt_bind M (noSettleAt_map M _ (noSettleAt_mapR M _ ?_)) fun _ => hRest _
      exact hProt callee _ (through ++ [key]) (path ++ [Frame.application key]) _
        (by rw [Frame.applications_append, hP]; rfl) (fun h => hNot (List.mem_append_left _ h))

private theorem noSettleAt_projectLoop {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (target : Site) (r : Role) (key : Key) (ps : Holders) (hIn : r ∈ ps)
    {Γ : Ctx (LTy V)} {outs carried each : List (LTy V)}
    (times : Times (protocolDialect V hs) ps Γ) (init : HList (Var Γ) carried)
    (inputs : Names (LTy.index ps :: carried))
    (body : Term (roleDialect V hs r) (Γ.extend inputs) (carried ++ each))
    (results : Names (carried ++ each.map (LTy.collected times.size)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hBody : ∀ i env', NoSettleAt M target (body.denote (roleSem M r fnTable rTable) (path ++ [Frame.iteration key i]) env'))
    (hRest : ∀ env', NoSettleAt M target (rest.denote (roleSem M r fnTable rTable) path env')) :
    NoSettleAt M target
      ((projectLoop r key ps hIn times init inputs body results rest).denote
        (roleSem M r fnTable rTable) path env) := by
  cases inputs with
  | cons idxNm carriedInNames =>
      cases times with
      | fixed n =>
          dsimp only [projectLoop, Term.denote, Instr.denote, Semantics.loopStep]
          refine noSettleAt_bind M (noSettleAt_bind M (noSettleAt_iterate M ?_ _ _ _) fun _ => trivial) fun _ => hRest _
          intro i st
          exact noSettleAt_bind M (hBody i _) fun _ => trivial
      | value cnt ok =>
          dsimp only [projectLoop, Term.denote, Instr.denote, Semantics.loopStep]
          refine noSettleAt_bind M (noSettleAt_bind M (noSettleAt_iterate M ?_ _ _ _) fun _ => trivial) fun _ => hRest _
          intro i st
          exact noSettleAt_bind M (hBody i _) fun _ => trivial

mutual
  private theorem noSettleAt_project_term {hs : Headers V}
      (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (target : Site) (r : Role)
      (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
          (through : List Key) (path : List Frame) (ins : HList (RV M r') hdr.ins),
          Frame.applications path = through →
          target ∉ hdr.shape.attemptSites through →
          NoSettleAt M target (rTable hdr m r' path ins)) :
      ∀ {Γ : Ctx (LTy V)} {outs : List (LTy V)} (t : Term (protocolDialect V hs) Γ outs)
        (through : List Key) (path : List Frame) (env : Env (RV M r) Γ),
        Frame.applications path = through →
        target ∉ (shapeOf t).attemptSites through →
        NoSettleAt M target ((project r t).denote (roleSem M r fnTable rTable) path env)
    | _, _, .ret _, _, _, _, _, _ => trivial
    | _, _, .op key o operands results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf] at hNot ⊢
        have hNotRest := not_mem_attemptSites_rest target through key o (shapeOf rest) hNot
        exact noSettleAt_project_op M fnTable rTable target r hProt key o operands results
          (project r rest) (shapeOf rest) through path env hP hNot fun env' =>
            noSettleAt_project_term fnTable rTable target r hProt rest through path env' hP hNotRest
    | _, _, .guard key ps c ok why rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn, Term.denote_guard]
          cases (roleSem M r fnTable rTable).holds _ (env.get c) with
          | false => trivial
          | true => exact noSettleAt_project_term fnTable rTable target r hProt rest through path env hP hNot
        · rw [dite_eq_right hIn]
          exact noSettleAt_project_term fnTable rTable target r hProt rest through path env hP hNot
    | _, _, .choose key ps c ok gives onTrue onFalse results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites, Shapes.attemptSites] at hNot ⊢
        have h1 : target ∉ (shapeOf onTrue).attemptSites through := fun h => hNot (by simp [h])
        have h2 : target ∉ (shapeOf onFalse).attemptSites through := fun h => hNot (by simp [h])
        have h3 : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (by simp [h])
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn, Term.denote_choose]
          apply noSettleAt_bind M
          · cases (roleSem M r fnTable rTable).holds _ (env.get c) with
            | false => exact noSettleAt_project_term fnTable rTable target r hProt onFalse through path env hP h2
            | true => exact noSettleAt_project_term fnTable rTable target r hProt onTrue through path env hP h1
          · exact fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP h3
        · rw [dite_eq_right hIn, Term.denote_op]
          exact noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP h3
    | _, _, .cases key ps x ok gives arms results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hA : target ∉ (shapesOf arms).attemptSites through := fun h => hNot (List.mem_append_left _ h)
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_append_right _ h)
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn, Term.denote_cases]
          refine noSettleAt_bind M
            (noSettleAt_project_arms fnTable rTable target r hProt arms through path env _ hP hA)
            fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR
        · rw [dite_eq_right hIn, Term.denote_op]
          exact noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR
    | _, _, .loop key ps times gives init inputs body results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hB : target ∉ (shapeOf body).attemptSites through := fun h => hNot (List.mem_append_left _ h)
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_append_right _ h)
        have hBody : ∀ i env', NoSettleAt M target
            ((project r body).denote (roleSem M r fnTable rTable) (path ++ [Frame.iteration key i]) env') :=
          fun i env' => noSettleAt_project_term fnTable rTable target r hProt body through
            (path ++ [Frame.iteration key i]) env'
            (by rw [Frame.applications_append, hP]; exact List.append_nil _) hB
        have hRest : ∀ env', NoSettleAt M target
            ((project r rest).denote (roleSem M r fnTable rTable) path env') :=
          fun env' => noSettleAt_project_term fnTable rTable target r hProt rest through path env' hP hR
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          exact noSettleAt_projectLoop M fnTable rTable target r key ps hIn times init inputs
            (project r body) results (project r rest) path env hBody hRest
        · rw [dite_eq_right hIn, Term.denote_op]
          exact hRest _
    | _, _, .block key num body results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hB : target ∉ (shapeOf body).attemptSites through := fun h => hNot (List.mem_append_left _ h)
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_append_right _ h)
        rw [Term.denote_block]
        refine noSettleAt_bind M (noSettleAt_project_term fnTable rTable target r hProt body through
          (path ++ [Frame.iteration key num]) env
          (by rw [Frame.applications_append, hP]; exact List.append_nil _) hB)
          fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR
    | _, _, .attempt key w owns inputs body results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hNe : (⟨through, key⟩ : Site) ≠ target := fun h => hNot (by rw [h]; exact List.mem_cons_self)
        have hB : target ∉ (shapeOf body).attemptSites through := fun h => hNot (List.mem_cons_of_mem _ (List.mem_append_left _ h))
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_cons_of_mem _ (List.mem_append_right _ h))
        rw [Term.denote_attempt]
        by_cases hw : r ∈ w
        · have hBeg : (roleSem M r fnTable rTable).begin w key path =
              Process.call (ROp.begin ⟨path, key⟩) fun n => Process.done (hide M r (LTy.index w) n) := by
            dsimp only [roleSem]; exact ite_eq_left hw
          have hSet : (roleSem M r fnTable rTable).settle w key path =
              Process.call (ROp.settle ⟨path, key⟩) fun _ => Process.done () := by
            dsimp only [roleSem]; exact ite_eq_left hw
          rw [hBeg, hSet]
          dsimp only [Process.bind]
          refine ⟨trivial, fun n => noSettleAt_bind M
            (noSettleAt_project_term fnTable rTable target r hProt body through path _ hP hB) fun _ => ?_⟩
          exact ⟨by simp [Occurrence.site, hP, hNe],
            fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR⟩
        · have hBeg : (roleSem M r fnTable rTable).begin w key path =
              Process.done (hide M r (LTy.index w) 0) := by
            dsimp only [roleSem]; exact ite_eq_right hw
          have hSet : (roleSem M r fnTable rTable).settle w key path = Process.done () := by
            dsimp only [roleSem]; exact ite_eq_right hw
          rw [hBeg, hSet]
          dsimp only [Process.bind]
          exact noSettleAt_bind M
            (noSettleAt_project_term fnTable rTable target r hProt body through path _ hP hB)
            fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR

  private theorem noSettleAt_project_arms {hs : Headers V}
      (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (target : Site) (r : Role)
      (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
          (through : List Key) (path : List Frame) (ins : HList (RV M r') hdr.ins),
          Frame.applications path = through →
          target ∉ hdr.shape.attemptSites through →
          NoSettleAt M target (rTable hdr m r' path ins)) :
      ∀ {Γ : Ctx (LTy V)} {mid payloads : List (LTy V)}
        (as' : Arms (protocolDialect V hs) Γ mid payloads)
        (through : List Key) (path : List Frame) (env : Env (RV M r) Γ)
        (pk : Pick (RV M r) payloads),
        Frame.applications path = through →
        target ∉ (shapesOf as').attemptSites through →
        NoSettleAt M target ((projectArms r as').denote (roleSem M r fnTable rTable) path env pk)
    | _, _, _, .nil, _, _, _, pk, _, _ => nomatch pk
    | _, _, _, .cons _ arm _, through, path, _, .here _, hP, hNA =>
        noSettleAt_project_term fnTable rTable target r hProt arm through path _ hP
          (fun h => hNA (List.mem_append_left _ h))
    | _, _, _, .cons _ _ more, through, path, env, .there p, hP, hNA =>
        noSettleAt_project_arms fnTable rTable target r hProt more through path env p hP
          (fun h => hNA (List.mem_append_right _ h))
end

theorem noSettleAt_defs {hs : Headers V} (defs : Defs V hs) (target : Site) :
    ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r : Role)
      (through : List Key) (path : List Frame) (ins : HList (RV M r) hdr.ins),
      Frame.applications path = through →
      target ∉ hdr.shape.attemptSites through →
      NoSettleAt M target (Defs.rTable M defs hdr m r path ins) := by
  induction defs with
  | nil => intro _ m; exact nomatch m
  | fn _ _ _ _ _ _ ih => exact ih
  | protocol hdrP inputsP bodyP okP rest ih =>
      intro hdr m r through path ins hP hNot
      cases m with
      | head =>
          rw [okP.shaped] at hNot
          exact noSettleAt_project_term M (Defs.fnTable M rest) (Defs.rTable M rest) target r ih
            bodyP through path (Env.empty.extend inputsP ins) hP hNot
      | tail m' => exact ih m' r through path ins hP hNot

theorem noSettleAt_project_of_shape {hs : Headers V} (defs : Defs V hs) (target : Site)
    {Γ : Ctx (LTy V)} {outs : List (LTy V)} (body : Term (protocolDialect V hs) Γ outs)
    (r : Role) (through : List Key) (path : List Frame) (env : Env (RV M r) Γ)
    (hP : Frame.applications path = through)
    (hNot : target ∉ (shapeOf body).attemptSites through) :
    NoSettleAt M target ((project r body).denote (roleSem M r (Defs.fnTable M defs) (Defs.rTable M defs)) path env) :=
  noSettleAt_project_term M (Defs.fnTable M defs) (Defs.rTable M defs) target r
    (noSettleAt_defs M defs target) body through path env hP hNot

/-! ## Soundness contracts (`SpecOpSoundOn`, `RetryCfgOk`, `RoleTermWellNested`, `SpecTermHyp`) -/

/-- Soundness contract of an `EffectSpecializer` against a `Handler`, guarded by path relation `pathRel`. -/
def SpecOpSoundOn {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fnTable : FnTable M fns) (procTable : ClosedProcTable M procs) {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fns procs σ) (pathRel : List Key → List Frame → Prop) : Prop :=
  ∀ (through : List Key) (key : Key) {ins res : List V.Ty}
    (op : ResidualOp V ins res) {Δ : Ctx V.Ty} (args : HList (Var Δ) ins)
    (path : List Frame) (cenv : Env M.Val Δ) (s : HList M.Val σ),
    pathRel through path →
    (specOp through key op args).denote M fnTable procTable path cenv s =
      (h.clause (op.toROp M ⟨path, key⟩ (cenv.all args)) s).map fun out =>
        (op.replyOf M ⟨path, key⟩ (cenv.all args) out.1, out.2)

/-- Unconditional `SpecOpSound` (for `pathRel th path := Frame.applications path = th`). -/
abbrev SpecOpSound {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fnTable : FnTable M fns) (procTable : ClosedProcTable M procs) {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fns procs σ) : Prop :=
  SpecOpSoundOn M fnTable procTable h specOp (fun th path => Frame.applications path = th)

/-- Lifting an `EffectSpecializer` from `[]` to `procs` preserves `SpecOpSound`. -/
theorem specOpSound_liftProcs_nil {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fnTable : FnTable M fns) (procTable : ClosedProcTable M procs) {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fns [] σ)
    (hSound : SpecOpSound M fnTable (ClosedProcTable.empty M) h specOp) :
    SpecOpSound M fnTable procTable h (specOp.liftProcs emptyProcLift) := by
  intro through key ins res op Δ args path cenv s hPath
  dsimp only [EffectSpecializer.liftProcs]
  rw [closedTerm_denote_liftProcs M fnTable (ClosedProcTable.empty M) procTable
    emptyProcLift (fun _ m => nomatch m)]
  exact hSound through key op args path cenv s hPath

/-- On any call path where no clause of `layers` lies in the subtree (`subtreeFree (stackClauseSites layers)`),
`unhandledSpecOp` matches `Stack.handler ... layers` identically, regardless of static `through`! -/
private theorem clause_answer_miss_all {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r_top : Role} {state : V.Ty}
    (op : ROp M) (mine : M.Val state) :
    ∀ (cs : List (Clause V hs r_top state)),
      (∀ c ∈ cs, c.site.site.through ≠ (ROp.occurrence M op).site.through) →
      Clause.answer M fnTable rTable cs op mine = .call op fun reply => .done (reply, mine)
  | [], _ => rfl
  | c :: cs, hMiss => by
      dsimp only [Clause.answer]
      have hNe : c.site.site ≠ (ROp.occurrence M op).site := fun hEq =>
        hMiss c List.mem_cons_self (congrArg Site.through hEq)
      rw [dite_eq_right (fun h => hNe h.1)]
      exact clause_answer_miss_all fnTable rTable op mine cs fun c' hc' =>
        hMiss c' (List.mem_cons_of_mem _ hc')

theorem unhandledSpecOp_sound_on_free {hs : Headers V} (defs : Defs V hs)
    {procs : List (ClosedProcSig V)} (procTable : ClosedProcTable M procs)
    {r_top : Role} {ins_top : List (LTy V)} :
    ∀ (layers : List (Layer V hs r_top ins_top)),
      SpecOpSoundOn M (Defs.fnTable M defs) procTable
        (Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) layers)
        (unhandledSpecOp (Stack.States layers))
        (fun _ path => subtreeFree (stackClauseSites layers) (Frame.applications path) = true)
  | [] => by
      intro through key ins res op Δ args path cenv s _
      cases s; rfl
  | l :: rest => by
      intro through key ins res op Δ args path cenv s hFree
      cases s with
      | cons mine below =>
          have hFreeRest : subtreeFree (stackClauseSites rest) (Frame.applications path) = true := by
            unfold subtreeFree at hFree ⊢
            rw [stackClauseSites, List.all_append, Bool.and_eq_true] at hFree
            exact hFree.2
          have hMissL : ∀ c ∈ l.clauses, c.site.site.through ≠ (ROp.occurrence M (op.toROp M ⟨path, key⟩ (cenv.all args))).site.through := by
            intro c hc
            have hIn : c.site.site ∈ stackClauseSites (l :: rest) := by
              unfold stackClauseSites
              exact List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
            have hNe := subtreeFree_ne_through (stackClauseSites (l :: rest)) (Frame.applications path) hFree hIn
            rw [op.toROp_occurrence M ⟨path, key⟩ (cenv.all args)]
            exact hNe
          have hRec := unhandledSpecOp_sound_on_free defs procTable rest through key op args path cenv below hFreeRest
          change (((unhandledSpecOp (Stack.States rest) through key op args).denote
              M (Defs.fnTable M defs) procTable path cenv below).mapHalt
              fun stop => (stop.1, HList.cons mine stop.2)).map (fun out => (out.1, HList.cons mine out.2)) = _
          rw [hRec]
          change _ =
            Process.map (fun out => (op.replyOf M ⟨path, key⟩ (cenv.all args) out.1, out.2))
              (Process.map (fun out => (out.1, HList.cons out.2.1 out.2.2))
                (Process.mapHalt (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
                  ((Process.mapHalt (fun stop => (stop.1, stop.2.1, stop.2.2))
                    ((Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) rest).answer
                      (Clause.answer M (Defs.fnTable M defs) (Defs.rTable M defs) l.clauses
                        (op.toROp M ⟨path, key⟩ (cenv.all args)) mine) mine below)).bind
                    fun out => Process.done (out.1.1, out.1.2, out.2))))
          rw [clause_answer_miss_all M (Defs.fnTable M defs) (Defs.rTable M defs) _ mine l.clauses hMissL]
          dsimp only [Handler.answer]
          simp only [mapHalt_bind, mapHalt_mapHalt, Process.map_eq_bind,
            Process.bind_assoc, Process.bind, Process.mapHalt]

/-- Extract the `Retry` corresponding to an optional retry configuration. -/
def retryOfCfg {fns : List (FnHeader V)} {σ : List V.Ty} :
    Option (Nat × Site × StackAgain V fns σ) → Retry (RSig M) (RSig M) Stop
  | none => retryOf M none
  | some (bound, site, _) => retryOf M (some (bound, site))

/-- Consistency of `again` in `retryCfg` with `h.again`. -/
def RetryCfgOk {fns : List (FnHeader V)} (fnTable : FnTable M fns) {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ)) :
    Option (Nat × Site × StackAgain V fns σ) → Prop
  | none => True
  | some (_, _, ag) => StackAgain.eval M fnTable ag = h.again

theorem retryOfCfg_not_begin {fns : List (FnHeader V)} {σ : List V.Ty}
    (retryCfg : Option (Nat × Site × StackAgain V fns σ)) (op : ROp M)
    (h : match op with | .begin _ => False | _ => True) :
    (retryOfCfg M retryCfg).begins op = none := by
  cases retryCfg with
  | none => rfl
  | some cfg =>
      cases cfg with
      | mk b sr =>
          cases sr with
          | mk site ag =>
              cases op with
              | «begin» _ => exact nomatch h
              | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | settle _ => rfl

/-- Whether a single role operation respects the well-nested retry condition. -/
def RoleOpWellNested {hs : Headers V} {r : Role} (site : Site) (through : List Key) (key : Key) :
    {ins outs : List (LTy V)} → RoleOp V hs r ins outs → Prop
  | _, _, .apply (hdr := hdr) _ _ _ _ _ _ => Shape.noNestedAttempt site (through ++ [key]) hdr.shape = true
  | _, _, _ => True

mutual
  def RoleTermWellNested {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (r : Role) (site : Site) (through : List Key) :
      {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → Term (roleDialect V hs r) Γ outs → Prop
    | _, _, .ret _ => True
    | _, _, .op key o _ _ rest =>
        RoleOpWellNested site through key o ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .guard _ _ _ _ _ rest => RoleTermWellNested fnTable rTable r site through rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        RoleTermWellNested fnTable rTable r site through onTrue ∧
        RoleTermWellNested fnTable rTable r site through onFalse ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .cases _ _ _ _ _ arms _ rest =>
        RoleArmsWellNested fnTable rTable r site through arms ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .loop _ _ _ _ _ _ body _ rest =>
        RoleTermWellNested fnTable rTable r site through body ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .block _ _ body _ rest =>
        RoleTermWellNested fnTable rTable r site through body ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .attempt key w _ _ body _ rest =>
        (r ∈ w → ⟨through, key⟩ = site →
          ∀ (path : List Frame) (env : Env (RV M r) _),
            Frame.applications path = through →
            NoSettleAt M site (body.denote (roleSem M r fnTable rTable) path env)) ∧
        RoleTermWellNested fnTable rTable r site through body ∧
        RoleTermWellNested fnTable rTable r site through rest

  def RoleArmsWellNested {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (r : Role) (site : Site) (through : List Key) :
      {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
      Arms (roleDialect V hs r) Γ mid payloads → Prop
    | _, _, _, .nil => True
    | _, _, _, .cons _ arm rest =>
        RoleTermWellNested fnTable rTable r site through arm ∧
        RoleArmsWellNested fnTable rTable r site through rest
end

private theorem noNestedAttempt_rest {hs : Headers V} (site : Site) (through : List Key)
    (key : Key) {ins res : List (LTy V)} (o : ProtocolOp V hs ins res) (sh : Shape V)
    (hWN : Shape.noNestedAttempt site through (ProtocolOp.shape key o sh) = true) :
    Shape.noNestedAttempt site through sh = true := by
  cases o with
  | compute _ _ _ _ _ | narrow _ _ | flow _ _ _ _ _ | given _ _ _ _ _ _ _ _ => exact hWN
  | apply _ _ _ _ _ _ =>
      dsimp only [ProtocolOp.shape, Shape.noNestedAttempt] at hWN
      exact (Bool.and_eq_true _ _ |>.mp hWN).2

private theorem roleTermWellNested_project_op {hs : Headers V} (defs : Defs V hs) (site : Site)
    (r : Role) (through : List Key) {Γ : Ctx (LTy V)} {outs ins res : List (LTy V)}
    (key : Key) (o : ProtocolOp V hs ins res) (operands : HList (Var Γ) ins)
    (results : Names res) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (sh : Shape V)
    (hWN : Shape.noNestedAttempt site through (ProtocolOp.shape key o sh) = true)
    (hRest : RoleTermWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through rest) :
    RoleTermWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through
      (ProtocolOp.project r key o operands results rest) := by
  cases o with
  | compute R _ _ _ _ =>
      dsimp only [ProtocolOp.project]
      by_cases hIn : r ∈ R
      · rw [dite_eq_left hIn]; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hIn]; exact ⟨trivial, hRest⟩
  | narrow R _ =>
      dsimp only [ProtocolOp.project]
      by_cases hIn : r ∈ R
      · rw [dite_eq_left hIn]; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hIn]; exact ⟨trivial, hRest⟩
  | flow _ giver getters _ _ =>
      dsimp only [ProtocolOp.project]
      by_cases hG : r = giver
      · rw [dite_eq_left hG]; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hG]
        by_cases hM : r ∈ getters
        · rw [dite_eq_left hM]; exact ⟨trivial, hRest⟩
        · rw [dite_eq_right hM]; exact ⟨trivial, hRest⟩
  | given _ owner hearers _ _ _ _ _ =>
      dsimp only [ProtocolOp.project]
      by_cases hOwn : r = owner
      · rw [dite_eq_left hOwn]; cases hOwn.symm; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hOwn]
        by_cases hH : r ∈ hearers
        · rw [dite_eq_left hH]; exact ⟨trivial, hRest⟩
        · rw [dite_eq_right hH]; exact ⟨trivial, hRest⟩
  | apply _ _ _ _ _ _ =>
      dsimp only [ProtocolOp.project, ProtocolOp.shape, Shape.noNestedAttempt] at hWN ⊢
      exact ⟨(Bool.and_eq_true _ _ |>.mp hWN).1, hRest⟩

mutual
  theorem roleTermWellNested_of_shape {hs : Headers V} (defs : Defs V hs) (site : Site)
      (r : Role) (through : List Key) :
      ∀ {Γ : Ctx (LTy V)} {outs : List (LTy V)} (body : Term (protocolDialect V hs) Γ outs),
        Shape.noNestedAttempt site through (shapeOf body) = true →
        RoleTermWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through (project r body)
    | _, _, .ret _, _ => trivial
    | _, _, .op key o operands results rest, hWN => by
        dsimp only [project, shapeOf] at hWN ⊢
        have hRest := roleTermWellNested_of_shape defs site r through rest
          (noNestedAttempt_rest site through key o (shapeOf rest) hWN)
        exact roleTermWellNested_project_op M defs site r through key o operands results
          (project r rest) (shapeOf rest) hWN hRest
    | _, _, .guard _ ps _ _ _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]; exact roleTermWellNested_of_shape defs site r through rest hWN
        · rw [dite_eq_right hIn]; exact roleTermWellNested_of_shape defs site r through rest hWN
    | _, _, .choose _ ps _ _ _ onTrue onFalse _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt, Shapes.noNestedAttempt] at hWN ⊢
        simp only [Bool.and_eq_true, Bool.and_true] at hWN
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          exact ⟨roleTermWellNested_of_shape defs site r through onTrue hWN.1.1,
            roleTermWellNested_of_shape defs site r through onFalse hWN.1.2,
            roleTermWellNested_of_shape defs site r through rest hWN.2⟩
        · rw [dite_eq_right hIn]
          exact ⟨trivial, roleTermWellNested_of_shape defs site r through rest hWN.2⟩
    | _, _, .cases _ ps _ _ _ arms _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        rw [Bool.and_eq_true] at hWN
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          exact ⟨roleArmsWellNested_of_shape defs site r through arms hWN.1,
            roleTermWellNested_of_shape defs site r through rest hWN.2⟩
        · rw [dite_eq_right hIn]
          exact ⟨trivial, roleTermWellNested_of_shape defs site r through rest hWN.2⟩
    | _, _, .loop _ ps times _ _ _ bodyL _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        rw [Bool.and_eq_true] at hWN
        have hBody := roleTermWellNested_of_shape defs site r through bodyL hWN.1
        have hRest := roleTermWellNested_of_shape defs site r through rest hWN.2
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          cases times <;> exact ⟨hBody, hRest⟩
        · rw [dite_eq_right hIn]
          exact ⟨trivial, hRest⟩
    | _, _, .block _ _ bodyB _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        rw [Bool.and_eq_true] at hWN
        exact ⟨roleTermWellNested_of_shape defs site r through bodyB hWN.1,
          roleTermWellNested_of_shape defs site r through rest hWN.2⟩
    | _, _, .attempt key w _ _ bodyA _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        simp only [Bool.and_eq_true] at hWN
        refine ⟨fun _ hEq path env hP => ?_,
          roleTermWellNested_of_shape defs site r through bodyA hWN.1.2,
          roleTermWellNested_of_shape defs site r through rest hWN.2⟩
        have hNotMem : site ∉ (shapeOf bodyA).attemptSites through := by
          have h1 := hWN.1.1
          rw [ite_eq_left hEq, Bool.not_eq_true', decide_eq_false_iff_not] at h1
          exact h1
        exact noSettleAt_project_of_shape M defs site bodyA r through path env hP hNotMem

  theorem roleArmsWellNested_of_shape {hs : Headers V} (defs : Defs V hs) (site : Site)
      (r : Role) (through : List Key) :
      ∀ {Γ : Ctx (LTy V)} {mid payloads : List (LTy V)}
        (as' : Arms (protocolDialect V hs) Γ mid payloads),
        Shapes.noNestedAttempt site through (shapesOf as') = true →
        RoleArmsWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through (projectArms r as')
    | _, _, _, .nil, _ => trivial
    | _, _, _, .cons _ arm more, hA => by
        dsimp only [shapesOf, Shapes.noNestedAttempt] at hA
        rw [Bool.and_eq_true] at hA
        exact ⟨roleTermWellNested_of_shape defs site r through arm hA.1,
          roleArmsWellNested_of_shape defs site r through more hA.2⟩
end

/-- Closure properties of a path relation `pathRel : List Key → List Frame → Prop` under frame extensions. -/
structure PathRelClosed (pathRel : List Key → List Frame → Prop) : Prop where
  app : ∀ th key path, pathRel th path → pathRel (th ++ [key]) (path ++ [.application key])
  iter : ∀ th key num path, pathRel th path → pathRel th (path ++ [.iteration key num])

theorem pathRelClosed_exact : PathRelClosed (fun th path => Frame.applications path = th) where
  app := fun _ key path h => by rw [Frame.applications_append, h]; rfl
  iter := fun _ key num path h => by rw [Frame.applications_append, h]; exact List.append_nil _

theorem pathRelClosed_free (sites : List Site) :
    PathRelClosed (fun _ path => subtreeFree sites (Frame.applications path) = true) where
  app := fun _ key path h => by
    rw [Frame.applications_append]
    exact subtreeFree_append sites (Frame.applications path) [key] h
  iter := fun _ key num path h => by
    rw [Frame.applications_append]
    simpa [Frame.applications] using h

/-- CPS soundness hypothesis for `specializeTerm` parameterized over `procs`, `procTable`, and `pathRel`. -/
def SpecTermHyp {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
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
    {outs : List (LTy V)} (t : Term (roleDialect V hs r) Γ outs) : Prop :=
  ∀ (path : List Frame) (env : Env (RV M r) Γ) (cenv : Env M.Val Δ) (s : HList M.Val σ)
    {B : Type} (cont : HList (RV M r) outs → Program M B),
    EnvRel M r hCtx env cenv →
    pathRel through path →
    (∀ b site ag, retryCfg = some (b, site, ag) →
      Frame.applications path = through ∧ RoleTermWellNested M fnTable rTable r site through t) →
    h.run (retryOfCfg M retryCfg)
      ((mapR M perm.apply (t.denote (roleSem M r fnTable rTable) path env)).bind cont) s =
      ((specializeTerm specOp fnLift specApply retryCfg through perm r hCtx t).denote
        M fullTable procTable path cenv s).bind
        fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2

/-- Soundness contract for `specApply` (handling both `.shared` and `.inlined` targets). -/
def SpecApplySound {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fullTable : FnTable M fullFns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (pathRel : List Key → List Frame → Prop)
    (retryAllowed : Option (Nat × Site × StackAgain V fullFns σ) → Prop)
    {hs : Headers V} (rTable : RTable M hs.protocols)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → FinPerm → (r : Role) →
      ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs)) : Prop :=
  ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
    RetryCfgOk M fullTable h retryCfg →
    retryAllowed retryCfg →
    ∀ {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr)
      (through : List Key) (perm : FinPerm) (r : Role)
      (path : List Frame) (ins : HList (RV M r) hdr.ins)
      (s : HList M.Val σ) {B : Type} (cont : HList (RV M r) hdr.outs → Program M B),
      pathRel through path →
      (∀ b site ag, retryCfg = some (b, site, ag) →
        Frame.applications path = through ∧ Shape.noNestedAttempt site through hdr.shape = true) →
      h.run (retryOfCfg M retryCfg) ((mapR M perm.apply (rTable hdr callee r path ins)).bind cont) s =
        (match specApply retryCfg callee through perm r with
         | .shared mem => procTable _ mem path (heldValues M r ins) s
         | .inlined calleeIns calleeBody =>
             calleeBody.denote M fullTable procTable path
               (Env.empty.extend calleeIns (heldValues M r ins)) s).bind
          fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2

end CoreSpecLemmas

end Zkc.Core
