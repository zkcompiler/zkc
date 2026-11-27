module

public import Zkc.Core.Scheme.Proof.RoleProcess

@[expose] public section

/-!
Outgoing payload validity (`roleMeaning_validPayload`) and shape-event matching
(`roleMeaning_matchesShape`, `protocolMeaning_matchesShape`) for admitted programs.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-! ## `roleMeaning_validPayload`: outgoing effect payloads are valid -/

section ValidPayload

private theorem safeWith_mapR_validPayload {B : Type} (ρ : Role → Role)
    {P : B → Prop} {R : Stop → Prop} :
    ∀ (p : Program M B),
      p.SafeWith M (ValidReply M) (ROp.ValidPayload M) P R →
      (mapR M ρ p).SafeWith M (ValidReply M) (ROp.ValidPayload M) P R
  | .done _, h => h
  | .halt _, h => h
  | .call (.give ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.get ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.own ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.hear ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.begin ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.settle ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩

private theorem ofLocated_revealAll_valid {r : Role} :
    ∀ {items : List (LTy V)} (here : ∀ a ∈ items, r ∈ a.holders) (vs : HList (RV M r) items),
      vs.All (RV.Valid M r) → (HList.ofLocated M (revealAll M here vs)).All M.Valid
  | [], _, .nil, _ => trivial
  | a :: _, here, .cons _ vs, hv =>
      ⟨hv.1 (here a List.mem_cons_self),
       ofLocated_revealAll_valid (fun b hb => here b (List.mem_cons_of_mem _ hb)) vs hv.2⟩

private theorem computeArgs_revealAll_valid {r : Role} {operands : List (LTy V)}
    {ins : List V.Ty} (types : operands.map (·.ty) = ins) (here : ∀ a ∈ operands, r ∈ a.holders)
    (vs : HList (RV M r) operands) (hv : vs.All (RV.Valid M r)) :
    (computeArgs M types (revealAll M here vs)).All M.Valid := by
  subst types
  exact ofLocated_revealAll_valid M here vs hv

private theorem hideAll_located_valid {r : Role} (R : Holders) :
    ∀ {outs : List V.Ty} (vs : HList M.Val outs),
      vs.All M.Valid → (hideAll M r (HList.located M R vs)).All (RV.Valid M r)
  | [], .nil, _ => trivial
  | τ :: _, .cons v vs, hv => by
      refine ⟨?_, hideAll_located_valid R vs hv.2⟩
      intro hIn
      exact (BodyAnalysis.RoleContracts.valid_hide M r (a := ⟨τ, R⟩) hIn v).mpr hv.1 hIn

private theorem roleOp_validPayload {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (keeps : FnTable.KeepsValidity fns)
    (roles : RTable M hs.protocols)
    (rcallees : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
      (args : HList (RV M j) hdr.ins), args.All (RV.Valid M j) →
      (roles hdr callee j path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
        (fun ys => ys.All (RV.Valid M j)) (fun _ => True))
    {ins res : List (LTy V)} (key : Key) (o : RoleOp V hs r ins res) (path : List Frame)
    (args : HList (RV M r) ins) (hv : args.All (RV.Valid M r)) :
    (roleOp M r fns roles key o path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
      (fun ys => ys.All (RV.Valid M r)) (fun _ => True) := by
  cases o with
  | compute R op operands types mine here =>
      show ((liftLocal id (localOp M fns op (computeArgs M types (revealAll M here args)))).map
        (fun outs => hideAll M r (HList.located M R outs))).SafeWith M _ _ _ _
      rw [Process.safeWith_map]
      cases hrun : localOp M fns op (computeArgs M types (revealAll M here args)) with
      | done outs =>
          have houts := localOp_valid fns keeps op _ outs
            (computeArgs_revealAll_valid M types here args hv) hrun
          exact hideAll_located_valid M R outs houts
      | halt _ => trivial
      | call op' _ => cases op'
  | absent items out => exact BodyAnalysis.RoleContracts.nothings_valid M r out
  | give kind getters here =>
      obtain ⟨v, rfl⟩ := HList.one args
      exact ⟨hv.1 here, fun _ _ => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr (hv.1 here) hIn, trivial⟩⟩
  | get τ H kind giver getters mine =>
      exact ⟨trivial, fun x hx => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr hx hIn, trivial⟩⟩
  | keep H same =>
      obtain ⟨v, rfl⟩ := HList.one args
      exact ⟨(BodyAnalysis.RoleContracts.valid_carry M same v).mpr hv.1, trivial⟩
  | own kind hearers operands τ typed here =>
      exact ⟨ofLocated_revealAll_valid M here args hv, fun x hx => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr hx hIn, trivial⟩⟩
  | hear kind owner hearers τ mine =>
      exact ⟨trivial, fun x hx => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr hx hIn, trivial⟩⟩
  | apply callee peers distinct covers operands fits =>
      let ρ := RoleMap.ofList peers distinct
      show ((mapR M ρ.to (roles _ callee (ρ.back r) (path ++ [.application key])
        (enterAll M ρ r (fitAllRV M fits args)))).map (leaveAll M ρ r)).SafeWith M _ _ _ _
      rw [Process.safeWith_map]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun ys hy => BodyAnalysis.RoleContracts.leaveAll_valid M ρ r ys hy) (fun _ _ => trivial)
        (safeWith_mapR_validPayload M ρ.to _
          (rcallees _ callee _ _ _
            (BodyAnalysis.RoleContracts.enterAll_valid M ρ r _
              (BodyAnalysis.RoleContracts.fitAllRV_valid M fits args hv))))

private theorem env_extend_rv_valid {r : Role} {Γ : Ctx (LTy V)} {env : Env (RV M r) Γ}
    (hv : ∀ a (x : Var Γ a), RV.Valid M r a (env.get x)) :
    ∀ {items : List (LTy V)} (bound : Names items) (vals : HList (RV M r) items),
      vals.All (RV.Valid M r) → ∀ a (x : Var (Γ.extend bound) a),
      RV.Valid M r a ((env.extend bound vals).get x)
  | [], .nil, .nil, _, _, x => hv _ x
  | σ :: _, .cons n rest, .cons v vs, hvs, a, x =>
      env_extend_rv_valid (fun b y => by
        by_cases hEq : y.name = n
        · have hTy : σ = b := by
            have ht := y.typed; rw [Ctx.find?_insert, ite_eq_left hEq] at ht
            exact Option.some.inj ht
          subst hTy
          show RV.Valid M r σ ((env.insert n v) y.name σ y.typed)
          rw [eq_of_heq (Env.insert_at_bound env n v hEq y.typed)]
          exact hvs.1
        · show RV.Valid M r b ((env.insert n v) y.name b y.typed)
          rw [Env.insert_at_other env n v hEq y.typed]
          exact hv b ⟨y.name, by
            have ht := y.typed; rw [Ctx.find?_insert, ite_eq_right hEq] at ht; exact ht⟩)
        rest vs hvs.2 a x

private theorem pushAll_rv_valid {r : Role} :
    ∀ {each : List (LTy V)} {acc : HList (fun a => List (RV M r a)) each}
      {step : HList (RV M r) each} {k : Nat},
      HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = k) acc →
      step.All (RV.Valid M r) →
      HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = k + 1)
        (HList.push acc step)
  | [], .nil, .nil, _, _, _ => trivial
  | _ :: _, .cons xs rest, .cons v vs, _, hacc, hstep => by
      refine ⟨⟨fun w hw => ?_, by simp [hacc.1.2]⟩, pushAll_rv_valid hacc.2 hstep.2⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hstep.1
      · exact hacc.1.1 w hw

private theorem collected_rv_valid {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (size : Option Nat) (count : Nat) (hsize : ∀ n, size = some n → count = n) :
    ∀ {each : List (LTy V)} (acc : HList (fun a => List (RV M r a)) each),
      HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = count) acc →
      ((roleSem M r fns roles).collected size acc).All (RV.Valid M r)
  | [], .nil, _ => trivial
  | a :: _, .cons xs rest, hacc =>
      ⟨BodyAnalysis.RoleContracts.role_collect M r fns roles size a xs.reverse
          (fun n hn => by rw [List.length_reverse]; exact hacc.1.2.trans (hsize n hn))
          (fun v hv => hacc.1.1 v (List.mem_reverse.mp hv)),
       collected_rv_valid r fns roles size count hsize rest hacc.2⟩

private theorem hlist_all_append {α : Type} {F : α → Type} {P : ∀ a, F a → Prop} :
    ∀ {as bs : List α} {xs : HList F as} {ys : HList F bs},
      xs.All P → ys.All P → (xs.append ys).All P
  | [], _, .nil, _, _, hy => hy
  | _ :: _, _, .cons _ _, _, hx, hy => ⟨hx.1, hlist_all_append hx.2 hy⟩

private theorem hlist_split_all {α : Type} {F : α → Type} {P : ∀ a, F a → Prop} :
    ∀ (as : List α) {bs : List α} (xs : HList F (as ++ bs)),
      xs.All P → (HList.split as xs).1.All P ∧ (HList.split as xs).2.All P
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: as, _, .cons _ rest, h =>
      let ih := hlist_split_all as rest h.2
      ⟨⟨h.1, ih.1⟩, ih.2⟩

private theorem iterate_safeWith {σ : Type} {Inv : σ → Prop}
    {step : Nat → σ → Process (RSig M) Stop σ}
    (hstep : ∀ i s, Inv s → (step i s).SafeWith M (ValidReply M) (ROp.ValidPayload M) Inv (fun _ => True)) :
    ∀ (n i : Nat) (s : σ), Inv s →
      (Process.iterate n step i s).SafeWith M (ValidReply M) (ROp.ValidPayload M) Inv (fun _ => True)
  | 0, _, _, hs => hs
  | n + 1, i, s, hs => by
      simp only [Process.iterate]
      rw [Process.safeWith_bind]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun s' hs' => iterate_safeWith hstep n (i + 1) s' hs') (fun _ _ => trivial)
        (hstep i s hs)

mutual
  private theorem term_role_validPayload {hs : Headers V} (r : Role)
      (fns : FnTable M hs.fns) (keeps : FnTable.KeepsValidity fns)
      (roles : RTable M hs.protocols)
      (rcallees : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins), args.All (RV.Valid M j) →
        (roles hdr callee j path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M j)) (fun _ => True)) :
      ∀ {Γ outs} (t : Term (roleDialect V hs r) Γ outs) (path : List Frame) (env : Env (RV M r) Γ),
        (∀ a (x : Var Γ a), RV.Valid M r a (env.get x)) →
        (t.denote (roleSem M r fns roles) path env).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M r)) (fun _ => True)
    | _, _, .ret exit, _, env, hv => env_all_rv_valid M hv exit
    | _, _, .op key o operands results rest, path, env, hv => by
        rw [Term.denote_op, Process.safeWith_bind]
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial)
          (roleOp_validPayload M r fns keeps roles rcallees key o path (env.all operands)
            (env_all_rv_valid M hv operands))
    | _, _, .guard key w c ok why rest, path, env, hv => by
        rw [Term.denote_guard]
        cases (roleSem M r fns roles).holds ok (env.get c)
        · trivial
        · exact term_role_validPayload r fns keeps roles rcallees rest path env hv
    | _, _, .choose key w c ok gives onTrue onFalse results rest, path, env, hv => by
        rw [Term.denote_choose, Process.safeWith_bind]
        have hArm : (bif (roleSem M r fns roles).holds ok (env.get c)
            then onTrue.denote (roleSem M r fns roles) path env
            else onFalse.denote (roleSem M r fns roles) path env).SafeWith M
            (ValidReply M) (ROp.ValidPayload M) (fun ys => ys.All (RV.Valid M r)) (fun _ => True) := by
          cases (roleSem M r fns roles).holds ok (env.get c)
          · exact term_role_validPayload r fns keeps roles rcallees onFalse path env hv
          · exact term_role_validPayload r fns keeps roles rcallees onTrue path env hv
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial) hArm
    | _, _, .cases key w x ok gives arms results rest, path, env, hv => by
        rw [Term.denote_cases, Process.safeWith_bind]
        have hPick := BodyAnalysis.RoleContracts.role_pick M r fns roles ok (env.get x) (hv _ x)
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial)
          (arms_role_validPayload r fns keeps roles rcallees arms path env hv _ hPick)
    | _, _, .loop (carried := carried) (each := each) key w times gives initial inputs body results rest,
        path, env, hv => by
        rw [Term.denote_loop, Process.safeWith_bind]
        let count := (roleSem M r fns roles).times times env
        have hEmpty : ∀ (es : List (LTy V)),
            HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = 0)
              (HList.empties (V := RV M r) es) := by
          intro es
          induction es with
          | nil => trivial
          | cons _ _ ih => exact ⟨⟨(fun _ h => nomatch h), rfl⟩, ih⟩
        have hIter : ∀ (n i : Nat) (s : (roleSem M r fns roles).LoopState carried each),
            s.1.All (RV.Valid M r) ∧
              HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = i) s.2 →
            (Process.iterate n ((roleSem M r fns roles).loopStep w inputs
              (fun at_ inside => body.denote (roleSem M r fns roles) at_ inside) key path env) i s).SafeWith
              M (ValidReply M) (ROp.ValidPayload M)
              (fun st => st.1.All (RV.Valid M r) ∧
                HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = i + n) st.2)
              (fun _ => True) := by
          intro n
          induction n with
          | zero => intro i s hs; exact hs
          | succ m ih =>
              intro i s hs
              simp only [Process.iterate, Semantics.loopStep]
              rw [Process.safeWith_bind, Process.safeWith_bind]
              have hIdx : RV.Valid M r (LTy.index w) ((roleSem M r fns roles).index w i) := by
                intro hIn
                exact (BodyAnalysis.RoleContracts.valid_hide M r (a := LTy.index w) hIn i).mpr trivial hIn
              have hBody := term_role_validPayload r fns keeps roles rcallees body
                (path ++ [.iteration key i]) _
                (env_extend_rv_valid M hv inputs (.cons ((roleSem M r fns roles).index w i) s.1)
                  ⟨hIdx, hs.1⟩)
              exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                (fun ys hys => by
                  have hsp := hlist_split_all carried ys hys
                  have hst' := ih (i + 1) ((HList.split carried ys).1, s.2.push (HList.split carried ys).2)
                    ⟨hsp.1, pushAll_rv_valid M hs.2 hsp.2⟩
                  simpa [Process.SafeWith, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hst')
                (fun _ _ => trivial) hBody
        have hRun := hIter count 0 (env.all initial, HList.empties each)
          ⟨env_all_rv_valid M hv initial, hEmpty each⟩
        refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun st hst => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results _
              (hlist_all_append hst.1
                (collected_rv_valid M r fns roles times.size count
                  (by
                    intro n hn
                    cases times with
                    | fixed m => cases hn; rfl
                    | value _ _ => cases hn)
                  st.2 (by simpa using hst.2)))))
          (fun _ _ => trivial) hRun
    | _, _, .block key number body results rest, path, env, hv => by
        rw [Term.denote_block, Process.safeWith_bind]
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial)
          (term_role_validPayload r fns keeps roles rcallees body (path ++ [.iteration key number]) env hv)
    | _, _, .attempt key w owns inputs body results rest, path, env, hv => by
        rw [Term.denote_attempt, Process.safeWith_bind]
        have hBeg : ((roleSem M r fns roles).begin w key path).SafeWith M (ValidReply M)
            (ROp.ValidPayload M) (fun n => RV.Valid M r (LTy.index w) n) (fun _ => True) := by
          show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
          split
          · next hIn =>
              refine ⟨trivial, fun n _ => ?_⟩
              exact (BodyAnalysis.RoleContracts.valid_hide M r (a := LTy.index w) hIn n).mpr trivial
          · next hOut => exact BodyAnalysis.RoleContracts.valid_out M r (a := LTy.index w) hOut _
        have hSet : ((roleSem M r fns roles).settle w key path).SafeWith M (ValidReply M)
            (ROp.ValidPayload M) (fun _ => True) (fun _ => True) := by
          show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
          split
          · exact ⟨trivial, fun _ _ => trivial⟩
          · trivial
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun n hn => by
            rw [Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun ys hys => by
                rw [Process.safeWith_bind]
                exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                  (fun _ _ => term_role_validPayload r fns keeps roles rcallees rest path _
                    (env_extend_rv_valid M hv results ys hys))
                  (fun _ _ => trivial) hSet)
              (fun _ _ => trivial)
              (term_role_validPayload r fns keeps roles rcallees body path _
                (env_extend_rv_valid M hv inputs (.cons n .nil) ⟨hn, trivial⟩)))
          (fun _ _ => trivial) hBeg
  private theorem arms_role_validPayload {hs : Headers V} (r : Role)
      (fns : FnTable M hs.fns) (keeps : FnTable.KeepsValidity fns)
      (roles : RTable M hs.protocols)
      (rcallees : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins), args.All (RV.Valid M j) →
        (roles hdr callee j path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M j)) (fun _ => True)) :
      ∀ {Γ mid payloads} (arms : Arms (roleDialect V hs r) Γ mid payloads)
        (path : List Frame) (env : Env (RV M r) Γ),
        (∀ a (x : Var Γ a), RV.Valid M r a (env.get x)) →
        (p : Pick (RV M r) payloads) → p.All (RV.Valid M r) →
        (arms.denote (roleSem M r fns roles) path env p).SafeWith M (ValidReply M)
          (ROp.ValidPayload M) (fun ys => ys.All (RV.Valid M r)) (fun _ => True)
    | _, _, _, .nil, _, _, _, p, _ => nomatch p
    | _, _, _, .cons inputs arm _, path, env, hv, .here v, hp =>
        term_role_validPayload r fns keeps roles rcallees arm path (env.extend inputs (.cons v .nil))
          (env_extend_rv_valid M hv inputs (.cons v .nil) ⟨hp, trivial⟩)
    | _, _, _, .cons _ _ rest, path, env, hv, .there p, hp =>
        arms_role_validPayload r fns keeps roles rcallees rest path env hv p hp
end

private theorem defs_rTable_validPayload :
    ∀ {hs : Headers V} (defs : Defs V hs),
      FnTable.KeepsValidity (Defs.fnTable M defs) →
      ∀ hdr (callee : Member hs.protocols hdr) (r : Role) (path : List Frame)
        (args : HList (RV M r) hdr.ins), args.All (RV.Valid M r) →
        (Defs.rTable M defs hdr callee r path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M r)) (fun _ => True)
  | _, .nil, _, _, p, _, _, _, _ => nomatch p
  | _, .fn _ _ _ _ rest _, keeps, hdr, callee, r, path, args, hv =>
      defs_rTable_validPayload rest (fun h f => keeps h (.tail f)) hdr callee r path args hv
  | _, .protocol hdr inputs body _ rest, keeps, _, callee, r, path, args, hv => by
      cases callee with
      | head =>
          exact term_role_validPayload M r (Defs.fnTable M rest) keeps (Defs.rTable M rest)
            (defs_rTable_validPayload rest keeps) (project r body) path _
            (env_extend_rv_valid M (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed)
              inputs args hv)
      | tail callee => exact defs_rTable_validPayload rest keeps _ callee r path args hv

unseal fnMeaning roleMeaning protocolMeaning in
/-- Every outgoing `.give` and `.own` payload emitted by an admitted role program on valid inputs
and valid replies is valid in `M`. -/
theorem roleMeaning_validPayload (a : Admitted V) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (r : Role) (path : List Frame)
    (args : HList (RV M r) hdr.ins) (valid : args.All (RV.Valid M r)) :
    (roleMeaning M a.program callee r path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
      (fun ys => ys.All (RV.Valid M r)) (fun _ => True) :=
  defs_rTable_validPayload M a.program.defs (a.assured M).2.1 hdr callee r path args valid

/-- Combined role safety and payload validity under `ValidReply M`. -/
theorem roleMeaning_safeWith_valid {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (accepted : admit named assoc = .ok a) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (r : Role) (path : List Frame)
    (args : HList (RV M r) hdr.ins) (valid : args.All (RV.Valid M r)) :
    (roleMeaning M a.program callee r path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
      (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) :=
  Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h.2) (fun _ h => h.1) (fun _ h => h.1)
    (Process.safeWith_and M
      (Process.safeWith_of_every M (rolesSafe_validReply M accepted callee r path args valid))
      (roleMeaning_validPayload M a callee r path args valid))

/-! ## `roleMeaning_matchesShape`: every emitted effect matches `hdr.shape.events` -/

end ValidPayload

section ShapeMatch

/-- A single role effect matches a `ShapeEvent` at role `r`. -/
def ROp.MatchesShapeEvent (r : Role) (e : ShapeEvent V) : ROp M → Prop
  | .give kind getters at_ τ _ => e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind r getters
  | .get kind giver at_ τ =>
      giver ≠ r ∧ e.site = at_.site ∧ e.τ = τ ∧ ∃ getters, r ∈ getters ∧ e.cls = .flow kind giver getters
  | .own kind hearers at_ ins _ τ =>
      e.site = at_.site ∧ e.τ = τ ∧ e.cls = .given kind r hearers ∧ kind.Typed ins τ
  | .hear kind owner at_ τ =>
      owner ≠ r ∧ e.site = at_.site ∧ e.τ = τ ∧ ∃ hearers, r ∈ hearers ∧ e.cls = .given kind owner hearers
  | .begin _ => True
  | .settle _ => True

/-- Every non-attempt effect matches some event in `events` for role `r`. -/
def ROp.MatchesShape (r : Role) (events : List (ShapeEvent V)) : ROp M → Prop
  | .begin _ => True
  | .settle _ => True
  | op => ∃ e ∈ events, ROp.MatchesShapeEvent M r e op

private theorem list_getD_of_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem frame_applications_append :
    ∀ (p q : List Frame), Frame.applications (p ++ q) = Frame.applications p ++ Frame.applications q
  | [], _ => rfl
  | .application k :: rest, q => congrArg (k :: ·) (frame_applications_append rest q)
  | .iteration _ _ :: rest, q => frame_applications_append rest q
  | .attempt _ _ :: rest, q => frame_applications_append rest q

private theorem eventClass_rename_comp (f g : Role → Role) (c : EventClass V) :
    (c.rename g).rename f = c.rename (fun j => f (g j)) := by
  cases c with
  | flow kind giver getters => simp [EventClass.rename, List.map_map, Function.comp_def]
  | given kind owner hearers => simp [EventClass.rename, List.map_map, Function.comp_def]

private theorem eventClass_rename_id (c : EventClass V) : c.rename id = c := by
  cases c <;> simp [EventClass.rename]

mutual
  private theorem shape_events_map (through : List Key) (rename : Role → Role) :
      ∀ (s : Shape V),
        s.events through rename =
          (s.events [] id).map fun e =>
            ⟨⟨through ++ e.site.through, e.site.key⟩, e.cls.rename rename, e.τ⟩
    | .nil => rfl
    | .event key cls τ rest => by
        simp only [Shape.events, List.map_cons, List.append_nil, eventClass_rename_id,
          shape_events_map through rename rest]
    | .choice _ _ arms rest => by
        simp only [Shape.events, List.map_append, shapes_events_map through rename arms,
          shape_events_map through rename rest]
    | .loop _ _ body rest => by
        simp only [Shape.events, List.map_append, shape_events_map through rename body,
          shape_events_map through rename rest]
    | .apply key _ roles inner rest => by
        simp only [Shape.events, List.map_append, List.nil_append, id_eq,
          shape_events_map (through ++ [key]) _ inner, shape_events_map [key] _ inner,
          shape_events_map through rename rest, List.map_map]
        congr 1
        apply List.map_congr_left
        intro e _
        simp only [Function.comp_def, List.append_assoc, eventClass_rename_comp]
    | .block _ _ body rest => by
        simp only [Shape.events, List.map_append, shape_events_map through rename body,
          shape_events_map through rename rest]
    | .guard _ _ _ rest => shape_events_map through rename rest
    | .attempt _ _ body rest => by
        simp only [Shape.events, List.map_append, shape_events_map through rename body,
          shape_events_map through rename rest]
  private theorem shapes_events_map (through : List Key) (rename : Role → Role) :
      ∀ (ss : Shapes V),
        ss.events through rename =
          (ss.events [] id).map fun e =>
            ⟨⟨through ++ e.site.through, e.site.key⟩, e.cls.rename rename, e.τ⟩
    | .nil => rfl
    | .cons arm rest => by
        simp only [Shapes.events, List.map_append, shape_events_map through rename arm,
          shapes_events_map through rename rest]
end

private def EventClass.AllIn (parts : List Role) : EventClass V → Prop
  | .flow _ giver getters => giver ∈ parts ∧ ∀ g ∈ getters, g ∈ parts
  | .given _ owner hearers => owner ∈ parts ∧ ∀ h ∈ hearers, h ∈ parts

private theorem eventClass_rename_congr {parts : List Role} {f g : Role → Role}
    (h : ∀ j ∈ parts, f j = g j) : ∀ {c : EventClass V}, c.AllIn parts → c.rename f = c.rename g
  | .flow kind giver getters, ⟨hg, hgs⟩ => by
      simp only [EventClass.rename, h giver hg]
      congr 1
      exact List.map_congr_left fun x hx => h x (hgs x hx)
  | .given kind owner hearers, ⟨ho, hhs⟩ => by
      simp only [EventClass.rename, h owner ho]
      congr 1
      exact List.map_congr_left fun x hx => h x (hhs x hx)

private theorem shape_events_within {hs : Headers V}
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles)) :
    ∀ {parts : List Role} {Γ outs} (t : Term (protocolDialect V hs) Γ outs),
      Within parts t → ∀ e ∈ (shapeOf t).events [] id, e.cls.AllIn parts
  | _, _, _, .ret _, _, e, he => nomatch he
  | parts, _, _, .op key o _ _ rest, w, e, he => by
      have hRest := shape_events_within hProt rest w.2
      cases o with
      | compute | narrow => exact hRest e he
      | flow kind giver getters =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨w.1.1, by simpa [EventClass.rename] using w.1.2⟩
          · exact hRest e he
      | given kind owner hearers =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨w.1.1, by simpa [EventClass.rename] using w.1.2⟩
          · exact hRest e he
      | @apply hdr callee roles distinct covers _ _ =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append] at he
          rcases he with he | he
          · rw [shape_events_map] at he
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            have hall0 := hProt hdr (Member.mem callee) e0 he0
            have hMap : ∀ j ∈ List.range hdr.roles, roles.getD j j ∈ parts := by
              intro j hj
              have hlt : j < roles.length := covers.symm ▸ List.mem_range.mp hj
              rw [list_getD_of_lt roles j j hlt]
              exact w.1 _ (List.getElem_mem hlt)
            cases hcls : e0.cls with
            | flow kind giver getters =>
                rw [hcls] at hall0
                refine ⟨hMap giver hall0.1, fun x hx => ?_⟩
                obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
                exact hMap g (hall0.2 g hg)
            | given kind owner hearers =>
                rw [hcls] at hall0
                refine ⟨hMap owner hall0.1, fun x hx => ?_⟩
                obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
                exact hMap h (hall0.2 h hh)
          · exact hRest e he
  | parts, _, _, .guard _ _ _ _ _ rest, w, e, he =>
      shape_events_within hProt rest w.2 e he
  | parts, _, _, .choose _ _ _ _ _ onTrue onFalse _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, Shapes.events, List.append_nil, List.mem_append] at he
      rcases he with (he | he) | he
      · exact shape_events_within hProt onTrue w.2.1 e he
      · exact shape_events_within hProt onFalse w.2.2.1 e he
      · exact shape_events_within hProt rest w.2.2.2 e he
  | parts, _, _, .cases _ _ _ _ _ arms _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact arms_shape_events_within hProt arms w.2.1 e he
      · exact shape_events_within hProt rest w.2.2 e he
  | parts, _, _, .loop _ _ _ _ _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within hProt body w.2.1 e he
      · exact shape_events_within hProt rest w.2.2 e he
  | parts, _, _, .block _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within hProt body w.1 e he
      · exact shape_events_within hProt rest w.2 e he
  | parts, _, _, .attempt _ _ _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within hProt body w.2.1 e he
      · exact shape_events_within hProt rest w.2.2 e he
where
  arms_shape_events_within {hs : Headers V}
      (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles)) :
      ∀ {parts : List Role} {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads),
        WithinArms parts arms → ∀ e ∈ (shapesOf arms).events [] id, e.cls.AllIn parts
    | _, _, _, _, .nil, _, e, he => nomatch he
    | parts, _, _, _, .cons _ arm rest, w, e, he => by
        simp only [shapesOf, Shapes.events, List.mem_append] at he
        rcases he with he | he
        · exact shape_events_within hProt arm w.1 e he
        · exact arms_shape_events_within hProt rest w.2 e he

private theorem safeWith_mapR_shape {B : Type} (ρ : RoleMap) (r : Role)
    (events : List (ShapeEvent V)) (events' : List (ShapeEvent V))
    (hMap : ∀ e ∈ events, ⟨e.site, e.cls.rename ρ.to, e.τ⟩ ∈ events') :
    ∀ (p : Program M B),
      p.SafeWith M (fun _ _ => True) (ROp.MatchesShape M (ρ.back r) events) (fun _ => True) (fun _ => True) →
      (mapR M ρ.to p).SafeWith M (fun _ _ => True) (ROp.MatchesShape M r events') (fun _ => True) (fun _ => True)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.give kind getters at_ τ x) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hSite, hTy, hCls⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he, hSite, hTy, by
          simp only [hCls, EventClass.rename, ρ.right r]⟩,
        fun u _ => safeWith_mapR_shape ρ r events events' hMap (k u) (hk u trivial)⟩
  | .call (.get kind giver at_ τ) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hNe, hSite, hTy, getters, hrIn, hCls⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he,
          fun heq => hNe (by have := congrArg ρ.back heq; rwa [ρ.left giver] at this),
          hSite, hTy, getters.map ρ.to,
          List.mem_map.mpr ⟨ρ.back r, hrIn, ρ.right r⟩, by simp only [hCls, EventClass.rename]⟩,
        fun y _ => safeWith_mapR_shape ρ r events events' hMap (k y) (hk y trivial)⟩
  | .call (.own kind hearers at_ ins payload τ) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hSite, hTy, hCls, hTyped⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he, hSite, hTy, by
          simp only [hCls, EventClass.rename, ρ.right r], hTyped⟩,
        fun y _ => safeWith_mapR_shape ρ r events events' hMap (k y) (hk y trivial)⟩
  | .call (.hear kind owner at_ τ) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hNe, hSite, hTy, hearers, hrIn, hCls⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he,
          fun heq => hNe (by have := congrArg ρ.back heq; rwa [ρ.left owner] at this),
          hSite, hTy, hearers.map ρ.to,
          List.mem_map.mpr ⟨ρ.back r, hrIn, ρ.right r⟩, by simp only [hCls, EventClass.rename]⟩,
        fun y _ => safeWith_mapR_shape ρ r events events' hMap (k y) (hk y trivial)⟩
  | .call (.begin _) k, ⟨_, hk⟩ =>
      ⟨trivial, fun n _ => safeWith_mapR_shape ρ r events events' hMap (k n) (hk n trivial)⟩
  | .call (.settle _) k, ⟨_, hk⟩ =>
      ⟨trivial, fun u _ => safeWith_mapR_shape ρ r events events' hMap (k u) (hk u trivial)⟩

private theorem matchesShape_mono (r : Role) {ev₁ ev₂ : List (ShapeEvent V)}
    (hSub : ∀ e ∈ ev₁, e ∈ ev₂) {op : ROp M}
    (h : ROp.MatchesShape M r ev₁ op) : ROp.MatchesShape M r ev₂ op := by
  cases op with
  | «begin» | settle => trivial
  | give | get | own | hear =>
      obtain ⟨e, he, hm⟩ := h
      exact ⟨e, hSub e he, hm⟩

private theorem iterate_safeWith_true {σ : Type} {opOk : ROp M → Prop}
    {step : Nat → σ → Process (RSig M) Stop σ}
    (hstep : ∀ i s, (step i s).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)) :
    ∀ (n i : Nat) (s : σ),
      (Process.iterate n step i s).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
  | 0, _, _ => trivial
  | n + 1, i, s => by
      simp only [Process.iterate]
      rw [Process.safeWith_bind]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun s' _ => iterate_safeWith_true hstep n (i + 1) s') (fun _ _ => trivial)
        (hstep i s)

private theorem liftLocal_safeWith_true {A : Type} {opOk : ROp M → Prop} (p : Local A) :
    (liftLocal (S := RSig M) id p).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True) := by
  cases p with
  | done _ => trivial
  | halt _ => trivial
  | call op _ => cases op

private theorem project_matchesShape {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
    (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
      (args : HList (RV M j) hdr.ins),
      (roles hdr callee j path args).SafeWith M (fun _ _ => True)
        (ROp.MatchesShape M j (hdr.shape.events (Frame.applications path) id))
        (fun _ => True) (fun _ => True)) :
    ∀ {Γ outs} (t : Term (protocolDialect V hs) Γ outs) (path : List Frame) (env : Env (RV M r) Γ),
      ((project r t).denote (roleSem M r fns roles) path env).SafeWith M (fun _ _ => True)
        (ROp.MatchesShape M r ((shapeOf t).events (Frame.applications path) id))
        (fun _ => True) (fun _ => True)
  | _, _, .ret _, _, _ => trivial
  | _, _, .op key o args results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys)
      cases o with
      | compute R op operands types held =>
          by_cases hIn : r ∈ R
          · simp only [project, ProtocolOp.project, dite_eq_left hIn, Term.denote_op, Process.safeWith_bind]
            show Process.SafeWith M _ _ _ _ ((liftLocal id _).map _)
            rw [Process.safeWith_map]
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun ys _ => hRest _) (fun _ _ => trivial) (liftLocal_safeWith_true M _)
          · simp only [project, ProtocolOp.project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
            exact hRest _
      | narrow R among =>
          by_cases hIn : r ∈ R
          · simp only [project, ProtocolOp.project, dite_eq_left hIn, Term.denote_op, Process.safeWith_bind]
            obtain ⟨x, rfl⟩ := HList.one args
            exact hRest _
          · simp only [project, ProtocolOp.project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
            exact hRest _
      | flow kind giver getters holds unique =>
          by_cases hg : r = giver
          · subst hg
            simp only [project, ProtocolOp.project, dite_true, Term.denote_op, Process.safeWith_bind]
            obtain ⟨x, rfl⟩ := HList.one args
            refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.flow kind r getters).rename id, _⟩,
              List.mem_cons_self, rfl, rfl, eventClass_rename_id (.flow kind r getters)⟩, fun _ _ => ?_⟩
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
              (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
          · by_cases hm : r ∈ getters
            · simp only [project, ProtocolOp.project, dite_eq_right hg, dite_eq_left hm,
                Term.denote_op, Process.safeWith_bind]
              refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.flow kind giver getters).rename id, _⟩,
                List.mem_cons_self, Ne.symm hg, rfl, rfl, getters, hm, eventClass_rename_id (.flow kind giver getters)⟩, fun _ _ => ?_⟩
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
            · simp only [project, ProtocolOp.project, dite_eq_right hg, dite_eq_right hm,
                Term.denote_op, Process.safeWith_bind]
              obtain ⟨x, rfl⟩ := HList.one args
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
      | given kind owner hearers operands τ typed held unique =>
          by_cases ho : r = owner
          · subst ho
            simp only [project, ProtocolOp.project, dite_true, Term.denote_op, Process.safeWith_bind]
            refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.given kind r hearers).rename id, τ⟩,
              List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given kind r hearers), typed⟩, fun _ _ => ?_⟩
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
              (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
          · by_cases hh : r ∈ hearers
            · simp only [project, ProtocolOp.project, dite_eq_right ho, dite_eq_left hh,
                Term.denote_op, Process.safeWith_bind]
              refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.given kind owner hearers).rename id, τ⟩,
                List.mem_cons_self, Ne.symm ho, rfl, rfl, hearers, hh, eventClass_rename_id (.given kind owner hearers)⟩, fun _ _ => ?_⟩
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
            · simp only [project, ProtocolOp.project, dite_eq_right ho, dite_eq_right hh,
                Term.denote_op, Process.safeWith_bind]
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
      | @apply hdr callee peers distinct covers operands fits =>
          simp only [project, ProtocolOp.project, Term.denote_op, Process.safeWith_bind]
          let ρ := RoleMap.ofList peers distinct
          have hApp : Frame.applications (path ++ [.application key]) = Frame.applications path ++ [key] := by
            rw [frame_applications_append]; rfl
          have hCall := hCallee hdr callee (ρ.back r) (path ++ [.application key])
            (enterAll M ρ r (fitAllRV M fits (env.all args)))
          rw [hApp] at hCall
          have hMap : ∀ e ∈ hdr.shape.events (Frame.applications path ++ [key]) id,
              ⟨e.site, e.cls.rename ρ.to, e.τ⟩ ∈
                ((shapeOf (.op key (.apply callee peers distinct covers _ fits) args results rest)).events
                  (Frame.applications path) id) := by
            intro e he
            simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]
            left
            rw [shape_events_map] at he ⊢
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            refine List.mem_map.mpr ⟨e0, he0, ?_⟩
            have hall := hProt hdr (Member.mem callee) e0 he0
            have hCong := eventClass_rename_congr (parts := List.range hdr.roles)
              (f := fun j => peers.getD j j) (g := ρ.to) (fun j hj => by
                have hlt : j < peers.length := covers.symm ▸ List.mem_range.mp hj
                rw [list_getD_of_lt peers j j hlt, RoleMap.ofList_to peers distinct j hlt]) hall
            simp only [eventClass_rename_id]
            exact congrArg (fun c => ShapeEvent.mk _ c e0.τ) hCong
          have hMapped := safeWith_mapR_shape M ρ r _ _ hMap _ hCall
          show Process.SafeWith M _ _ _ _ (Process.map (leaveAll M ρ r) _)
          rw [Process.safeWith_map]
          exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
            (fun ys _ => Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => by
                simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]
                exact .inr he) h)
              (fun _ _ => trivial) (fun _ _ => trivial) (hRest _))
            (fun _ _ => trivial) hMapped
  | _, _, .guard key ps c ok why rest, path, env => by
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn, Term.denote_guard]
        cases asBool M ok.1 (reveal M (ok.2.1 r hIn) (env.get c))
        · trivial
        · exact project_matchesShape r fns roles hProt hCallee rest path env
      · simp only [project, dite_eq_right hIn]
        exact project_matchesShape r fns roles hProt hCallee rest path env
  | _, _, .choose key ps c ok gives onTrue onFalse results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r
            (ev₂ := (shapeOf (.choose key ps c ok gives onTrue onFalse results rest)).events
              (Frame.applications path) id)
            (fun e he => by simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys))
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn, Term.denote_choose, Process.safeWith_bind]
        cases asBool M ok.1 (reveal M (ok.2.1 r hIn) (env.get c))
        · exact Process.safeWith_mono M (fun _ _ h => h)
            (fun _ h => matchesShape_mono M r (fun e he => by
              simp only [shapeOf, Shape.events, Shapes.events, List.append_nil, List.mem_append]
              exact .inl (.inr he)) h)
            (fun ys _ => hRest ys) (fun _ _ => trivial)
            (project_matchesShape r fns roles hProt hCallee onFalse path env)
        · exact Process.safeWith_mono M (fun _ _ h => h)
            (fun _ h => matchesShape_mono M r (fun e he => by
              simp only [shapeOf, Shape.events, Shapes.events, List.append_nil, List.mem_append]
              exact .inl (.inl he)) h)
            (fun ys _ => hRest ys) (fun _ _ => trivial)
            (project_matchesShape r fns roles hProt hCallee onTrue path env)
      · simp only [project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
        exact hRest _
  | _, _, .cases key ps x ok gives arms results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r
            (ev₂ := (shapeOf (.cases key ps x ok gives arms results rest)).events
              (Frame.applications path) id)
            (fun e he => by simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys))
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn, Term.denote_cases, Process.safeWith_bind]
        exact Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
          (fun ys _ => hRest ys) (fun _ _ => trivial)
          (projectArms_matchesShape r fns roles hProt hCallee arms path env _)
      · simp only [project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
        exact hRest _
  | _, _, .loop key ps times gives init inputs body results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r
            (ev₂ := (shapeOf (.loop key ps times gives init inputs body results rest)).events
              (Frame.applications path) id)
            (fun e he => by simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys))
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn]
        have hLoopStep : ∀ i st,
            ((roleSem M r fns roles).loopStep ps inputs
              (fun at_ inside => (project r body).denote (roleSem M r fns roles) at_ inside)
              key path env i st).SafeWith M (fun _ _ => True)
              (ROp.MatchesShape M r ((shapeOf body).events (Frame.applications path) id))
              (fun _ => True) (fun _ => True) := by
          intro i st
          simp only [Semantics.loopStep]
          rw [Process.safeWith_bind]
          have hApp : Frame.applications (path ++ [.iteration key i]) = Frame.applications path := by
            rw [frame_applications_append]; simp [Frame.applications]
          have hb := project_matchesShape r fns roles hProt hCallee body (path ++ [.iteration key i])
            (env.extend inputs (.cons ((roleSem M r fns roles).index ps i) st.1))
          rwa [hApp] at hb
        cases times with
        | fixed n =>
            simp only [projectLoop]
            erw [Term.denote_loop, Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => by
                simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
              (fun st _ => hRest _) (fun _ _ => trivial)
              (iterate_safeWith_true M hLoopStep _ 0 _)
        | value c ok =>
            simp only [projectLoop]
            erw [Term.denote_loop, Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => by
                simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
              (fun st _ => hRest _) (fun _ _ => trivial)
              (iterate_safeWith_true M hLoopStep _ 0 _)
      · simp only [project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
        exact hRest _
  | _, _, .block key number body results rest, path, env => by
      simp only [project, Term.denote_block, Process.safeWith_bind]
      have hApp : Frame.applications (path ++ [.iteration key number]) = Frame.applications path := by
        rw [frame_applications_append]; simp [Frame.applications]
      have hb := project_matchesShape r fns roles hProt hCallee body (path ++ [.iteration key number]) env
      rw [hApp] at hb
      exact Process.safeWith_mono M (fun _ _ h => h)
        (fun _ h => matchesShape_mono M r (fun e he => by
          simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
        (fun ys _ => Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys)))
        (fun _ _ => trivial) hb
  | _, _, .attempt key w owns inputs body results rest, path, env => by
      simp only [project, Term.denote_attempt, Process.safeWith_bind]
      have hBeg : ((roleSem M r fns roles).begin w key path).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r ((shapeOf (.attempt key w owns inputs body results rest)).events
            (Frame.applications path) id)) (fun _ => True) (fun _ => True) := by
        show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
        split
        · exact ⟨trivial, fun _ _ => trivial⟩
        · trivial
      have hSet : ((roleSem M r fns roles).settle w key path).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r ((shapeOf (.attempt key w owns inputs body results rest)).events
            (Frame.applications path) id)) (fun _ => True) (fun _ => True) := by
        show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
        split
        · exact ⟨trivial, fun _ _ => trivial⟩
        · trivial
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun n _ =>
          Process.safeWith_mono M (fun _ _ h => h)
            (fun _ h => matchesShape_mono M r (fun e he => by
              simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
            (fun ys _ =>
              Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                (fun _ _ => Process.safeWith_mono M (fun _ _ h => h)
                  (fun _ h => matchesShape_mono M r (fun e he => by
                    simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
                  (fun _ _ => trivial) (fun _ _ => trivial)
                  (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys)))
                (fun _ _ => trivial) hSet)
            (fun _ _ => trivial)
            (project_matchesShape r fns roles hProt hCallee body path (env.extend inputs (.cons n .nil))))
        (fun _ _ => trivial) hBeg
where
  projectArms_matchesShape {hs : Headers V} (r : Role)
      (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
      (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
      (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins),
        (roles hdr callee j path args).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M j (hdr.shape.events (Frame.applications path) id))
          (fun _ => True) (fun _ => True)) :
      ∀ {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (RV M r) Γ) (p : Pick (RV M r) payloads),
        ((projectArms r arms).denote (roleSem M r fns roles) path env p).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r ((shapesOf arms).events (Frame.applications path) id))
          (fun _ => True) (fun _ => True)
    | _, _, _, .nil, _, _, p => nomatch p
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inl he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee arm path (env.extend inputs (.cons v .nil)))
    | _, _, _, .cons _ _ rest, path, env, .there p =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (projectArms_matchesShape r fns roles hProt hCallee rest path env p)

private theorem defs_rTable_matchesShape :
    ∀ {hs : Headers V} (defs : Defs V hs),
      (∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles)) ∧
      (∀ hdr (callee : Member hs.protocols hdr) (r : Role) (path : List Frame)
        (args : HList (RV M r) hdr.ins),
        (Defs.rTable M defs hdr callee r path args).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r (hdr.shape.events (Frame.applications path) id))
          (fun _ => True) (fun _ => True))
  | _, .nil => ⟨(fun _ h => nomatch h), (fun _ p => nomatch p)⟩
  | _, .fn _ _ _ _ rest _ => defs_rTable_matchesShape rest
  | _, .protocol hdr inputs body ok rest => by
      have ⟨hProt, hCallee⟩ := defs_rTable_matchesShape rest
      have hHeadProt : ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles) := by
        rw [ok.shaped]
        exact shape_events_within hProt body ok.within
      refine ⟨fun h hm => ?_, fun _ callee r path args => ?_⟩
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hHeadProt
        · exact hProt h hm
      · cases callee with
        | head =>
            rw [ok.shaped]
            exact project_matchesShape M r (Defs.fnTable M rest) (Defs.rTable M rest)
              hProt hCallee body path (Env.empty.extend inputs args)
        | tail callee => exact hCallee _ callee r path args

unseal roleMeaning in
/-- Every non-attempt effect emitted by a role program (even against arbitrary replies!) matches
an event of `hdr.shape.events (Frame.applications path) id`. -/
theorem roleMeaning_matchesShape (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (r : Role) (path : List Frame)
    (args : HList (RV M r) hdr.ins) :
    (roleMeaning M p callee r path args).SafeWith M (fun _ _ => True)
      (ROp.MatchesShape M r (hdr.shape.events (Frame.applications path) id))
      (fun _ => True) (fun _ => True) :=
  (defs_rTable_matchesShape M p.defs).2 hdr callee r path args

/-- A single protocol-level effect matches a `ShapeEvent`. -/
def GOp.MatchesShape (events : List (ShapeEvent V)) : GOp M → Prop
  | .flow kind giver getters at_ τ _ =>
      ∃ e ∈ events, e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind giver getters
  | .given kind owner hearers at_ _ _ τ =>
      ∃ e ∈ events, e.site = at_.site ∧ e.τ = τ ∧ e.cls = .given kind owner hearers

/-- Every effect emitted along a protocol process matches an event in `events`. -/
def Protocol.MatchesShape {A : Type} (events : List (ShapeEvent V)) : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k => GOp.MatchesShape M events op ∧ ∀ v, Protocol.MatchesShape events (k v)

private theorem protocol_matchesShape_mono {A : Type} {ev₁ ev₂ : List (ShapeEvent V)}
    (hSub : ∀ e ∈ ev₁, e ∈ ev₂) : ∀ {p : Protocol M A},
    Protocol.MatchesShape M ev₁ p → Protocol.MatchesShape M ev₂ p
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) _, ⟨⟨e, he, hm⟩, hk⟩ =>
      ⟨⟨e, hSub e he, hm⟩, fun v => protocol_matchesShape_mono hSub (hk v)⟩
  | .call (.given ..) _, ⟨⟨e, he, hm⟩, hk⟩ =>
      ⟨⟨e, hSub e he, hm⟩, fun v => protocol_matchesShape_mono hSub (hk v)⟩

private theorem protocol_matchesShape_bind {A B : Type} {events : List (ShapeEvent V)} :
    ∀ (p : Protocol M A) (f : A → Protocol M B),
      Protocol.MatchesShape M events p → (∀ a, Protocol.MatchesShape M events (f a)) →
      Protocol.MatchesShape M events (p.bind f)
  | .done a, _, _, hf => hf a
  | .halt _, _, _, _ => trivial
  | .call _ k, f, ⟨ho, hk⟩, hf => ⟨ho, fun v => protocol_matchesShape_bind (k v) f (hk v) hf⟩

private theorem protocol_matchesShape_map {A B : Type} {events : List (ShapeEvent V)} (g : A → B) :
    ∀ (p : Protocol M A), Protocol.MatchesShape M events p → Protocol.MatchesShape M events (p.map g)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call _ k, ⟨ho, hk⟩ => ⟨ho, fun v => protocol_matchesShape_map g (k v) (hk v)⟩

private theorem protocol_matchesShape_liftLocal {A : Type} {events : List (ShapeEvent V)}
    (who : List Role) : ∀ (p : Local A), Protocol.MatchesShape M events (liftLocal (fun w => (who, w)) p)
  | .done _ => trivial
  | .halt _ => trivial
  | .call op _ => nomatch op

private theorem protocol_matchesShape_mapG {A : Type} (ρ : Role → Role)
    {ev₁ ev₂ : List (ShapeEvent V)}
    (hMap : ∀ e ∈ ev₁, ⟨e.site, e.cls.rename ρ, e.τ⟩ ∈ ev₂) :
    ∀ (p : Protocol M A), Protocol.MatchesShape M ev₁ p → Protocol.MatchesShape M ev₂ (mapG M ρ p)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) k, ⟨⟨e, he, hSite, hTy, hCls⟩, hk⟩ =>
      ⟨⟨⟨e.site, e.cls.rename ρ, e.τ⟩, hMap e he, hSite, hTy, by simp [hCls, EventClass.rename]⟩,
        fun v => protocol_matchesShape_mapG ρ hMap (k v) (hk v)⟩
  | .call (.given ..) k, ⟨⟨e, he, hSite, hTy, hCls⟩, hk⟩ =>
      ⟨⟨⟨e.site, e.cls.rename ρ, e.τ⟩, hMap e he, hSite, hTy, by simp [hCls, EventClass.rename]⟩,
        fun v => protocol_matchesShape_mapG ρ hMap (k v) (hk v)⟩

private theorem protocol_matchesShape_iterate {σ : Type} {events : List (ShapeEvent V)}
    {step : Nat → σ → Protocol M σ}
    (hstep : ∀ i s, Protocol.MatchesShape M events (step i s)) :
    ∀ (n i : Nat) (s : σ), Protocol.MatchesShape M events (Process.iterate n step i s)
  | 0, _, _ => trivial
  | n + 1, i, s =>
      protocol_matchesShape_bind M (step i s) _ (hstep i s) fun s' =>
        protocol_matchesShape_iterate hstep n (i + 1) s'

private theorem term_observe_matchesShape {hs : Headers V}
    (fns : FnTable M hs.fns) (gTable : GTable M hs.protocols)
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
    (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (path : List Frame)
      (args : HList (LVal M) hdr.ins),
      Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
        (gTable hdr callee path args)) :
    ∀ {Γ outs} (t : Term (protocolDialect V hs) Γ outs) (path : List Frame) (env : Env (LVal M) Γ),
      Protocol.MatchesShape M ((shapeOf t).events (Frame.applications path) id)
        (Term.observe M fns gTable t path env)
  | _, _, .ret _, _, _ => trivial
  | _, _, .op key o args results rest, path, env => by
      have hRest := fun ys => term_observe_matchesShape fns gTable hProt hCallee rest path
        (env.extend results ys)
      cases o with
      | compute R op operands types held =>
          simp only [Term.observe, observeOp, protocolOp]
          exact protocol_matchesShape_bind M _ _
            (protocol_matchesShape_map M _ _ (protocol_matchesShape_liftLocal M R _)) (fun _ => hRest _)
      | narrow R among =>
          obtain ⟨x, rfl⟩ := HList.one args
          simp only [Term.observe, observeOp, protocolOp]
          exact hRest _
      | flow kind giver getters holds unique =>
          obtain ⟨x, rfl⟩ := HList.one args
          simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
          refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.flow kind giver getters).rename id, _⟩,
            List.mem_cons_self, rfl, rfl, eventClass_rename_id (.flow kind giver getters)⟩, fun _ => ?_⟩
          exact protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _))
      | given kind owner hearers operands τ typed held unique =>
          cases kind with
          | coin law =>
              cases hearers with
              | nil =>
                  simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
                  refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.given (.coin law) owner []).rename id, τ⟩,
                    List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given (.coin law) owner [])⟩, fun _ => ?_⟩
                  exact protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _)
              | cons h0 hs0 =>
                  simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
                  refine ⟨⟨⟨⟨Frame.applications path, key⟩,
                      (EventClass.given (.coin law) owner (h0 :: hs0)).rename id, τ⟩,
                    List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given (.coin law) owner (h0 :: hs0))⟩, fun _ => ?_⟩
                  exact protocol_matchesShape_map M _ _
                    (protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _))
          | request service =>
              simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
              refine ⟨⟨⟨⟨Frame.applications path, key⟩,
                  (EventClass.given (.request service) owner hearers).rename id, τ⟩,
                List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given (.request service) owner hearers)⟩, fun _ => ?_⟩
              exact protocol_matchesShape_map M _ _
                (protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _))
      | @apply hdr callee peers distinct covers operands fits =>
          simp only [Term.observe, observeOp]
          let ρ := RoleMap.ofList peers distinct
          have hApp : Frame.applications (path ++ [.application key]) = Frame.applications path ++ [key] := by
            rw [frame_applications_append]; rfl
          have hCall := hCallee hdr callee (path ++ [.application key])
            (unmapAll M ρ.to (fitAll M fits (env.all args)))
          rw [hApp] at hCall
          have hMap : ∀ e ∈ hdr.shape.events (Frame.applications path ++ [key]) id,
              ⟨e.site, e.cls.rename ρ.to, e.τ⟩ ∈
                ((shapeOf (.op key (.apply callee peers distinct covers _ fits) args results rest)).events
                  (Frame.applications path) id) := by
            intro e he
            simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]
            left
            rw [shape_events_map] at he ⊢
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            refine List.mem_map.mpr ⟨e0, he0, ?_⟩
            have hall := hProt hdr (Member.mem callee) e0 he0
            have hCong := eventClass_rename_congr (parts := List.range hdr.roles)
              (f := fun j => peers.getD j j) (g := ρ.to) (fun j hj => by
                have hlt : j < peers.length := covers.symm ▸ List.mem_range.mp hj
                rw [list_getD_of_lt peers j j hlt, RoleMap.ofList_to peers distinct j hlt]) hall
            simp only [eventClass_rename_id]
            exact congrArg (fun c => ShapeEvent.mk _ c e0.τ) hCong
          exact protocol_matchesShape_bind M _ _
            (protocol_matchesShape_mapG M ρ.to hMap _ hCall)
            (fun ys => protocol_matchesShape_map M _ _
              (protocol_matchesShape_mono M (fun e he => by
                simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]; exact .inr he) (hRest _)))
  | _, _, .guard key ps c ok why rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      cases asBool M ok.1 (env.get c)
      · trivial
      · exact term_observe_matchesShape fns gTable hProt hCallee rest path env
  | _, _, .choose key ps c ok gives onTrue onFalse results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      cases asBool M ok.1 (env.get c)
      · exact protocol_matchesShape_bind M _ _
          (protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => by
              simp only [Shapes.events, List.mem_append]; exact .inl (.inr (.inl he)))
              (term_observe_matchesShape fns gTable hProt hCallee onFalse path env)))
          (fun out => protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
              (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
      · exact protocol_matchesShape_bind M _ _
          (protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => by
              simp only [Shapes.events, List.mem_append]; exact .inl (.inl he))
              (term_observe_matchesShape fns gTable hProt hCallee onTrue path env)))
          (fun out => protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
              (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
  | _, _, .cases key ps s ok gives arms results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      exact protocol_matchesShape_bind M _ _
        (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he))
          (observeArms_matchesShape fns gTable hProt hCallee arms path env
            ((protocolSem M fns gTable).pick ok (env.get s))))
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
  | _, _, .loop key ps times ok carried inputs body results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      refine protocol_matchesShape_bind M _ _
        (protocol_matchesShape_iterate M (fun i st =>
          protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he))
              (by
                have hBody := term_observe_matchesShape fns gTable hProt hCallee body
                  (path ++ [.iteration key i]) (env.extend inputs (.cons i st.1.1))
                have hApp : Frame.applications (path ++ [.iteration key i]) = Frame.applications path := by
                  rw [frame_applications_append]; simp [Frame.applications]
                rwa [hApp] at hBody))) _ 0 _)
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path _)))
  | _, _, .block key number body results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      have hApp : Frame.applications (path ++ [.iteration key number]) = Frame.applications path := by
        rw [frame_applications_append]; simp [Frame.applications]
      have hBody := term_observe_matchesShape fns gTable hProt hCallee body
        (path ++ [.iteration key number]) env
      rw [hApp] at hBody
      exact protocol_matchesShape_bind M _ _
        (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he)) hBody)
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
  | _, _, .attempt key ps ok inputs body results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      exact protocol_matchesShape_bind M _ _
        (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he))
          (term_observe_matchesShape fns gTable hProt hCallee body path (env.extend inputs (.cons 0 .nil))))
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
where
  observeArms_matchesShape {hs : Headers V}
      (fns : FnTable M hs.fns) (gTable : GTable M hs.protocols)
      (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
      (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (path : List Frame)
        (args : HList (LVal M) hdr.ins),
        Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
          (gTable hdr callee path args)) :
      ∀ {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (LVal M) Γ) (p : Pick (LVal M) payloads),
        Protocol.MatchesShape M ((shapesOf arms).events (Frame.applications path) id)
          (Arms.observe M fns gTable arms path env p)
    | _, _, _, .nil, _, _, p => nomatch p
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inl he)
            (term_observe_matchesShape fns gTable hProt hCallee arm path (env.extend inputs (.cons v .nil))))
    | _, _, _, .cons _ _ rest, path, env, .there p =>
        protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inr he)
            (observeArms_matchesShape fns gTable hProt hCallee rest path env p))

private theorem defs_gTable_matchesShape :
    ∀ {hs : Headers V} (defs : Defs V hs) (hdr : ProtocolHeader V)
      (callee : Member hs.protocols hdr) (path : List Frame) (args : HList (LVal M) hdr.ins),
      Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
        (Defs.gTable M defs hdr callee path args)
  | _, .nil, _, p, _, _ => nomatch p
  | _, .fn _ _ _ _ rest _, hdr, callee, path, args => defs_gTable_matchesShape rest hdr callee path args
  | _, .protocol hdr inputs body ok rest, _, callee, path, args => by
      cases callee with
      | head =>
          have hObs := term_observe_matchesShape M (Defs.fnTable M rest) (Defs.gTable M rest)
            (defs_rTable_matchesShape M rest).1 (defs_gTable_matchesShape rest) body path
            (Env.empty.extend inputs args)
          rw [ok.shaped]
          exact protocol_matchesShape_map M _ _ hObs
      | tail callee => exact defs_gTable_matchesShape rest _ callee path args

unseal protocolMeaning in
/-- Every effect emitted along a protocol process matches an event of
`hdr.shape.events (Frame.applications path) id`. -/
theorem protocolMeaning_matchesShape (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (path : List Frame)
    (args : HList (LVal M) hdr.ins) :
    Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
      (protocolMeaning M p callee path args) :=
  defs_gTable_matchesShape M p.defs hdr callee path args

end ShapeMatch


end

end Zkc.Core
