module

public import Zkc.Core.Scheme.Layer.Builders
public import Zkc.Core.Scheme.Layer.CombinatorLemmas
public import Zkc.Core.Scheme.Deploy.Lookup

@[expose] public section

/-!
Denotation, validity, safety, and prover/verifier agreement lemmas for `start`, `again`, `finish`,
`constructionStart`, `idealStart`, and compact `layout` start builders.
-/

namespace Zkc.Core

namespace LayerBuild

section
variable {V : Vocabulary} (M : Model V)

/-! ## Denotation lemmas for `start`, `again`, `finish` builders -/

theorem restoreAgain_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) (state : V.Ty)
    (i : Nat) (entry stop : M.Val state) :
    (restoreAgain (V := V) (fns := fns) state).denote (localSem M fns fnTable) []
      (Env.positional (.cons i (.cons entry (.cons stop .nil)))) = .done (.cons entry .nil) := by
  unfold restoreAgain
  rw [Term.denote_ret]
  show Process.done (HList.cons ((Env.positional _).get (posVar _ 1 rfl)) .nil) = _
  rw [env_get_positional_1]

theorem env_all_positionalVars {T : Type} {F : T → Type} (start : Nat) {Γ : Ctx T}
    (env : Env F Γ) :
    ∀ (types : List T) (vals : HList F types)
      (hΓ : ∀ k a, types[k]? = some a → Γ.find? (start + k) = some a)
      (_hEnv : ∀ k a (ha : types[k]? = some a), env.get ⟨start + k, hΓ k a ha⟩ = HList.getAt vals k ha),
      env.all (positionalVars types start hΓ) = vals
  | [], .nil, _, _ => rfl
  | a :: as, .cons v vs, hΓ, hEnv => by
      show HList.cons (env.get ⟨start, hΓ 0 a rfl⟩)
          (env.all (positionalVars as (start + 1) _)) = HList.cons v vs
      congr 1
      · exact hEnv 0 a rfl
      · exact env_all_positionalVars (start + 1) env as vs _ fun k b hb => by
          have hk := hEnv (k + 1) b hb
          simpa [HList.getAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk

theorem env_all_cast {T : Type} {F : T → Type} {Γ : Ctx T} {as bs : List T} (h : as = bs)
    (env : Env F Γ) (xs : HList (Var Γ) as) :
    env.all (cast (congrArg (HList (Var Γ)) h) xs) =
      cast (congrArg (HList F) h) (env.all xs) := by
  subst h; rfl

theorem env_all_append {T : Type} {F : T → Type} {Γ : Ctx T} (env : Env F Γ) :
    ∀ {as bs : List T} (xs : HList (Var Γ) as) (ys : HList (Var Γ) bs),
      env.all (HList.append xs ys) = HList.append (env.all xs) (env.all ys)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ xs, ys => congrArg (HList.cons _) (env_all_append env xs ys)

theorem aloneIn_append (r : Role) :
    ∀ {as bs : List V.Ty} (xs : HList M.Val as) (ys : HList M.Val bs),
      aloneIn M r (HList.append xs ys) =
        cast (congrArg (HList (RV M r)) (by simp [alone, List.map_append]))
          (HList.append (aloneIn M r xs) (aloneIn M r ys))
  | [], _, .nil, _ => rfl
  | a :: as, bs, .cons x xs, ys => by
      have ih := aloneIn_append r xs ys
      change HList.cons (hide M r ⟨a, [r]⟩ x) (aloneIn M r (HList.append xs ys)) = _
      rw [ih]
      have hApp : alone r (as ++ bs) = alone r as ++ alone r bs := by simp [alone, List.map_append]
      exact (cast_hlist_cons hApp.symm (hide M r ⟨a, [r]⟩ x) (HList.append (aloneIn M r xs) (aloneIn M r ys))).symm

theorem aloneIn_cast (r : Role) {as bs : List V.Ty} (h : as = bs) (xs : HList M.Val as) :
    aloneIn M r (cast (congrArg (HList M.Val) h) xs) =
      cast (congrArg (fun ts => HList (RV M r) (alone r ts)) h) (aloneIn M r xs) := by
  subst h; rfl

private theorem tysOfList_ofHList_valid :
    ∀ (ts : List V.Ty) (vals : HList M.Val ts),
      vals.All M.Valid →
      Tys.Valid M.toCarriers (tysOfList ts)
        (Tys.ofHList M (tysOfList ts) (cast (congrArg (HList M.Val) (tysOfList_toList ts).symm) vals))
  | [], .nil, _ => trivial
  | t :: ts, .cons v vs, ⟨hv, hvs⟩ => by
      have hcast :
          cast (congrArg (HList M.Val) (tysOfList_toList (t :: ts)).symm) (HList.cons v vs) =
            HList.cons v (cast (congrArg (HList M.Val) (tysOfList_toList ts).symm) vs) :=
        cast_hlist_cons (tysOfList_toList ts).symm v vs
      rw [hcast]
      exact ⟨hv, tysOfList_ofHList_valid ts vs hvs⟩

theorem samplesAgain_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    (heldP : List V.Ty) (htfree : Tys.anyLinear V (samplesStateTys heldP) = false)
    (i : Nat) (entry stop : M.Val (samplesStateTy heldP)) :
    (samplesAgain (V := V) (fns := fns) heldP htfree).denote (localSem M fns fnTable) []
      (Env.positional (.cons i (.cons entry (.cons stop .nil)))) =
      .done (.cons (a := samplesStateTy heldP) (i, (stop.2.1, (stop.2.2.1, ()))) .nil) := by
  rcases stop with ⟨sAtt, sSeq, sHeld, ⟨⟩⟩
  let env0 := Env.positional (V := M.Val)
    (.cons (a := Ty.nat) i (.cons (a := samplesStateTy heldP) entry
      (.cons (a := samplesStateTy heldP) (sAtt, (sSeq, (sHeld, ()))) .nil)))
  unfold samplesAgain
  rw [letOp1_local_owned_denote]
  simp only [Env.all]
  change (ownedOp M (.getTuple (samplesStateTys heldP) (.tail .head) htfree)
    (.cons (env0.get (posVar [.nat, samplesStateTy heldP, samplesStateTy heldP] 2 rfl)) .nil)).bind _ = _
  rw [env_get_positional_2]
  refine (congrFun (congrArg Process.bind
    (ownedOp_getTuple M (samplesStateTys heldP) (.tail .head) htfree (sAtt, (sSeq, (sHeld, ()))))) _).trans ?_
  dsimp only [Tys.getAt, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all]
  change (ownedOp M (.getTuple (samplesStateTys heldP) (.tail (.tail .head)) htfree)
    (.cons ((env0.insert 3 sSeq).get
      ((posVar [.nat, samplesStateTy heldP, samplesStateTy heldP] 2 rfl).reindex _)) .nil)).bind _ = _
  have hGet2 : ∀ (w), (env0.insert 3 sSeq).get
      ((posVar [.nat, samplesStateTy heldP, samplesStateTy heldP] 2 rfl).reindex w) =
      (sAtt, (sSeq, (sHeld, ()))) := fun w => by
    rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, posVar])]
    exact env_get_positional_2 (τ₀ := Ty.nat) (τ₁ := samplesStateTy heldP) (τ₂ := samplesStateTy heldP)
      i entry (sAtt, (sSeq, (sHeld, ()))) .nil
  rw [hGet2]
  refine (congrFun (congrArg Process.bind
    (ownedOp_getTuple M (samplesStateTys heldP) (.tail (.tail .head)) htfree (sAtt, (sSeq, (sHeld, ()))))) _).trans ?_
  dsimp only [Tys.getAt, Process.bind, HList.single]
  rw [letOp1_local_makeTuple3_denote,
      env_get_insert_ne _ _ _ (by simp [Var.reindex, posVar]),
      env_get_insert_ne _ _ _ (by simp [Var.reindex, posVar]),
      env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
      env_get_insert_eq _ _ _ rfl,
      env_get_insert_self]
  simp only [Term.denote_ret, Env.all, env_get_insert_self]
  exact congrArg (fun x => Process.done (HList.cons (V := M.Val) (a := samplesStateTy heldP)
      (x, (sSeq, (sHeld, ()))) HList.nil))
    (env_get_positional_0 (τ := Ty.nat) i
      (.cons entry (.cons (a := samplesStateTy heldP) (sAtt, (sSeq, (sHeld, ()))) .nil)))

theorem emptyFinish_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) (state : V.Ty)
    (s : M.Val state) :
    (emptyFinish (V := V) (fns := fns) state).denote (localSem M fns fnTable) []
      (Env.positional (.cons s .nil)) = .done .nil :=
  rfl

theorem identityFinish_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) (state : V.Ty)
    (s : M.Val state) :
    (identityFinish (V := V) (fns := fns) state).denote (localSem M fns fnTable) []
      (Env.positional (.cons s .nil)) = .done (.cons s .nil) := by
  unfold identityFinish
  rw [Term.denote_ret]
  show Process.done (HList.cons ((Env.positional _).get (posVar _ 0 rfl)) .nil) = _
  rw [env_get_positional_0]

theorem samplesStart_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins : List (LTy V)} (vals : HList M.Val (held r ins)) :
    (samplesStart (V := V) (fns := fns) (r := r) (ins := ins)).denote (localSem M fns fnTable) []
      (Env.positional vals) =
      .done (.cons (a := samplesStateTy (held r ins))
        ((0 : Nat), ((0 : Nat),
          (Tys.ofHList M (tysOfList (held r ins))
            (cast (congrArg (HList M.Val) (tysOfList_toList (held r ins)).symm) vals), ()))) .nil) := by
  unfold samplesStart
  rw [letOp1_local_natLiteral_denote]
  rw [letOp1_local_natLiteral_denote]
  rw [letOp1_local_owned_denote]
  have hInVars :
      (((Env.positional vals).insert (held r ins).length (0 : Nat)).insert
        ((held r ins).length + 1) (0 : Nat)).all
        (cast (congrArg (HList (Var _)) (tysOfList_toList (held r ins)).symm)
          ((positionalVars (held r ins) 0 fun k a ha => by
              rw [Ctx.find?_positional]; simpa using ha).reindex
            (((positional_freshFrom (held r ins)).within .nat).trans
              (((positional_freshFrom (held r ins)).insert .nat).within .nat)))) =
      cast (congrArg (HList M.Val) (tysOfList_toList (held r ins)).symm) vals := by
    rw [env_all_cast (tysOfList_toList (held r ins)).symm]
    congr 1
    have hRe : ∀ {ts : List V.Ty} (xs : HList (Var (Ctx.positional (held r ins))) ts),
        (((Env.positional vals).insert (held r ins).length (0 : Nat)).insert
          ((held r ins).length + 1) (0 : Nat)).all
          (xs.reindex (((positional_freshFrom (held r ins)).within .nat).trans
            (((positional_freshFrom (held r ins)).insert .nat).within .nat))) =
        (Env.positional vals).all xs := by
      intro ts xs
      induction xs with
      | nil => rfl
      | cons x rest ih =>
          show HList.cons _ _ = HList.cons _ _
          rw [env_get_insert2_reindex _ (positional_freshFrom (held r ins)), ih]
    rw [hRe]
    exact env_all_positionalVars 0 (Env.positional vals) (held r ins) vals _ fun k a ha => by
      simpa [posVar, Nat.zero_add] using env_get_positional vals k ha
  erw [hInVars, ownedOp_makeTuple]
  simp only [Process.bind, HList.single]
  rw [letOp1_local_makeTuple3_denote]
  rw [env_get_insert_ne _ _ _ (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))),
      env_get_insert_ne _ _ _ (Nat.ne_of_lt (Nat.lt_succ_self _)),
      env_get_insert_eq _ _ _ rfl,
      env_get_insert_ne _ _ _ (Nat.ne_of_lt (Nat.lt_succ_self _)),
      env_get_insert_eq _ _ _ rfl,
      env_get_insert_self]
  simp only [Term.denote_ret, Env.all, env_get_insert_self]

theorem samplesStart_valid {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins : List (LTy V)} (vals : HList M.Val (held r ins)) (hvals : vals.All M.Valid) :
    ((samplesStart (V := V) (fns := fns) (r := r) (ins := ins)).denote (localSem M fns fnTable) []
      (Env.positional vals)).Every (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined) := by
  rw [samplesStart_denote]
  exact ⟨⟨trivial, trivial, tysOfList_ofHList_valid M (held r ins) vals hvals, trivial⟩, trivial⟩

theorem layoutPStart_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins : List (LTy V)} (unitTy : V.Ty) (vals : HList M.Val (held r ins)) :
    (layoutPStart (V := V) (fns := fns) (r := r) (ins := ins) unitTy).denote
      (localSem M fns fnTable) [] (Env.positional vals) =
      .done (.cons ([] : List (M.Val unitTy)) .nil) := by
  unfold layoutPStart
  rw [letOp1_local_owned_denote]
  simp only [ownedOp, HList.toItems, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [ownedOp, Env.all, env_get_insert_self, Process.bind, HList.single, Term.denote_ret]

theorem layoutVStart_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins : List (LTy V)} (unitTy : V.Ty)
    (proof : List (M.Val unitTy)) (vals : HList M.Val (held r ins)) :
    (layoutVStart (V := V) (fns := fns) (r := r) (ins := ins) unitTy).denote
      (localSem M fns fnTable) [] (Env.positional (.cons proof vals)) =
      .done (.cons (proof, ((0 : Nat), ())) .nil) := by
  unfold layoutVStart
  rw [letOp1_local_natLiteral_denote, letOp1_local_makeTuple2_denote]
  rw [env_get_insert_reindex _ (positional_freshFrom _), env_get_insert_self, env_get_positional_0]
  simp only [Term.denote_ret, Env.all, env_get_insert_self]

theorem layoutVFinish_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) (unitTy : V.Ty)
    (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (buf : List (M.Val unitTy)) (off : Nat) :
    (layoutVFinish (V := V) (fns := fns) unitTy hfree guardKey).denote
      (localSem M fns fnTable) [] (Env.positional (.cons (buf, (off, ())) .nil)) =
      bif Nat.beq off buf.length then .done .nil else .halt (.declared .reject ⟨[], guardKey⟩) := by
  unfold layoutVFinish
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_positional_0]
  erw [ownedOp_getTuple]
  dsimp only [Tys.getAt, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all]
  erw [ownedOp_getTuple]
  dsimp only [Tys.getAt, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all]
  erw [ownedOp_seqLength]
  dsimp only [Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert_self]
  erw [ownedOp_natEqual]
  dsimp only [Process.bind, HList.single]
  erw [Term.denote_guard, env_get_insert_self]
  rfl

/-! ## `buildAbsorbChain` and `constructionStart` denotation, safety, and prover/verifier agreement -/

/-- Pure fold matching `buildAbsorbChain` on a list of `(ty, val, label, encodeRef)` items. -/
def absorbChainFold {fns : List (FnHeader V)} {stateTy unitTy : V.Ty}
    (fnTable : FnTable M fns)
    (absorbRef : TypedFnRef V fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (st : M.Val stateTy) {Γ : Ctx V.Ty} (env : Env M.Val Γ) :
    List (StmtAbsorbItem V fns unitTy Γ) → Local (M.Val stateTy)
  | [] => .done st
  | item :: rest =>
      (item.encode.eval M fnTable (.cons (env.get item.input) .nil)).bind fun enc =>
        (absorbRef.eval M fnTable (.cons st (.cons item.label (.cons enc.single .nil)))).bind
          fun nextSt => absorbChainFold fnTable absorbRef nextSt.single env rest

theorem absorbChainFold_reindex {fns : List (FnHeader V)} {stateTy unitTy : V.Ty}
    (fnTable : FnTable M fns)
    (absorbRef : TypedFnRef V fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    {Γ Δ : Ctx V.Ty} (env : Env M.Val Γ) (env' : Env M.Val Δ) (w : Γ.Within Δ)
    (hagree : ∀ {τ} (x : Var Γ τ), env'.get (x.reindex w) = env.get x) :
    ∀ (st : M.Val stateTy) (items : List (StmtAbsorbItem V fns unitTy Γ)),
      absorbChainFold M fnTable absorbRef st env'
          (items.map fun it => ⟨it.ty, it.input.reindex w, it.label, it.labelBytes, it.encode⟩) =
        absorbChainFold M fnTable absorbRef st env items
  | _, [] => rfl
  | st, item :: rest => by
      simp only [List.map_cons, absorbChainFold, hagree]
      congr 1; funext enc; congr 1; funext nextSt
      exact absorbChainFold_reindex fnTable absorbRef env env' w hagree nextSt.single rest

theorem buildAbsorbChain_denote {fns : List (FnHeader V)} {stateTy unitTy : V.Ty}
    (fnTable : FnTable M fns)
    (absorbRef : TypedFnRef V fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (n : Nat) :
    ∀ {Γ : Ctx V.Ty} (fresh : Nat) (hfresh : FreshFrom Γ fresh) (env : Env M.Val Γ)
      (stVar : Var Γ stateTy) (items : List (StmtAbsorbItem V fns unitTy Γ)),
      items.length = n →
      (buildAbsorbChain absorbRef fresh hfresh stVar items).denote (localSem M fns fnTable) [] env =
        (absorbChainFold M fnTable absorbRef (env.get stVar) env items).map fun st => .cons st .nil := by
  induction n with
  | zero =>
      intro Γ fresh hfresh env stVar items hlen
      cases items with
      | nil => unfold buildAbsorbChain; rfl
      | cons _ _ => cases hlen
  | succ k ih =>
      intro Γ fresh hfresh env stVar items hlen
      cases items with
      | nil => cases hlen
      | cons item rest =>
          unfold buildAbsorbChain
          erw [letOp1_denote, localSem_op_literal, bytesLiteral_val M item.label item.labelBytes]
          simp only [Process.bind, HList.single]
          rw [letOp1_local_denote]
          simp only [Env.all]
          rw [env_get_insert_reindex env hfresh]
          change (item.encode.eval M fnTable (.cons (env.get item.input) .nil)).bind _ = _
          simp only [absorbChainFold, Process.map_bind]
          congr 1; funext enc
          rw [letOp1_local_denote]
          simp only [Env.all]
          rw [env_get_insert2_reindex env hfresh,
              env_get_insert_reindex _ (hfresh.insert bytesTy),
              env_get_insert_self, env_get_insert_self]
          change (absorbRef.eval M fnTable
              (.cons (env.get stVar) (.cons item.label (.cons enc.single .nil)))).bind _ = _
          congr 1; funext nextSt
          rw [ih _ _ _ _ _ (by rw [List.length_map]; exact Nat.succ.inj hlen)]
          rw [env_get_insert_self]
          congr 1
          apply absorbChainFold_reindex M fnTable absorbRef env _ _
          intro τ x
          exact env_get_insert3_reindex env hfresh _ _ _ _ x

theorem absorbChainFold_done (a : Admitted V) {stateTy unitTy : V.Ty}
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    ∀ {Γ : Ctx V.Ty} (env : Env M.Val Γ) (st : M.Val stateTy) (_hst : M.Valid stateTy st)
      (items : List (StmtAbsorbItem V a.program.headers.fns unitTy Γ))
      (_hitems : ∀ it ∈ items, M.Valid it.ty (env.get it.input)),
      ∃ stEnd,
        absorbChainFold M (Defs.fnTable M a.program.defs) absorbRef st env items = .done stEnd ∧
        M.Valid stateTy stEnd
  | _, _, st, hst, [], _ => ⟨st, rfl, hst⟩
  | _, env, st, hst, item :: rest, hitems => by
      have hit : M.Valid item.ty (env.get item.input) := hitems item List.mem_cons_self
      obtain ⟨enc, henc, hencV⟩ := item.encode.eval_done M a (.cons (env.get item.input) .nil)
        (valid_single _ hit)
      have hlblV : M.Valid bytesTy item.label :=
        ⟨fun b hb => item.labelBytes b hb, fun _ h => nomatch h⟩
      have hencS : M.Valid (.seq unitTy none) enc.single := by
        cases enc with | cons e encNil => cases encNil; exact hencV.1
      obtain ⟨nextSt, hnext, hnextV⟩ := absorbRef.eval_done M a
        (.cons st (.cons item.label (.cons enc.single .nil)))
        ⟨hst, hlblV, hencS, trivial⟩
      have hnextS : M.Valid stateTy nextSt.single := by
        cases nextSt with | cons s stNil => cases stNil; exact hnextV.1
      obtain ⟨stEnd, hend, hendV⟩ := absorbChainFold_done a absorbRef env nextSt.single hnextS rest
        (fun it h => hitems it (List.mem_cons_of_mem _ h))
      refine ⟨stEnd, ?_, hendV⟩
      simp only [absorbChainFold, henc, hnext, Process.bind, hend]

theorem constructionStart_done (a : Admitted V) {stateTy unitTy : V.Ty}
    {r : Role} {ins : List (LTy V)}
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (startRef : TypedFnRef V a.program.headers.fns [bytesTy] [stateTy])
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (items : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held r ins))))
    (vals : HList M.Val (held r ins)) (hvals : vals.All M.Valid) :
    ∃ stEnd,
      (constructionStart sessionBytes hsess startRef absorbRef items).denote
        (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) [] (Env.positional vals) =
        .done (.cons stEnd .nil) ∧
      M.Valid stateTy stEnd := by
  have hsessV : M.Valid bytesTy sessionBytes := ⟨hsess, fun _ h => nomatch h⟩
  obtain ⟨st0, hst0, hst0V⟩ := startRef.eval_done M a (.cons sessionBytes .nil)
    (valid_single _ hsessV)
  have hitems : ∀ it ∈ items, M.Valid it.ty ((Env.positional vals).get it.input) := by
    intro it _
    have htyped := it.input.typed
    rw [Ctx.find?_positional] at htyped
    have hget : (Env.positional vals).get it.input = HList.getAt vals it.input.name htyped := by
      have := env_get_positional vals it.input.name htyped
      simpa [posVar] using this
    rw [hget]
    exact HList.getAt_valid vals it.input.name htyped hvals
  have hst0S : M.Valid stateTy st0.single := by
    cases st0 with | cons s stNil => cases stNil; exact hst0V.1
  obtain ⟨stEnd, hend, hendV⟩ := absorbChainFold_done M a absorbRef (Env.positional vals)
    st0.single hst0S items hitems
  refine ⟨stEnd, ?_, hendV⟩
  unfold constructionStart
  erw [letOp1_denote, localSem_op_literal, bytesLiteral_val M sessionBytes hsess]
  simp only [Process.bind, HList.single]
  rw [letOp1_local_denote]
  simp only [Env.all, env_get_insert_self]
  change (startRef.eval M (Defs.fnTable M a.program.defs) (.cons sessionBytes .nil)).bind _ = _
  rw [hst0]
  simp only [Process.bind]
  rw [buildAbsorbChain_denote M _ absorbRef _ _ _ _ _ _ rfl, env_get_insert_self]
  rw [absorbChainFold_reindex M (Defs.fnTable M a.program.defs) absorbRef (Env.positional vals) _ _
    (fun x => env_get_insert2_reindex _ (positional_freshFrom (held r ins)) _ _ _ x)]
  rw [hend]
  rfl

theorem heldValues_cons_in (r : Role) {a : LTy V} {rest : List (LTy V)}
    (h : r ∈ a.holders) (v : RV M r a) (vs : HList (RV M r) rest) :
    heldValues M r (.cons v vs) =
      cast (by simp [held, h]) (HList.cons (reveal M h v) (heldValues M r vs)) := by
  change (if h' : r ∈ a.holders then _ else _) = _
  exact dite_eq_left h

theorem heldValues_cons_out (r : Role) {a : LTy V} {rest : List (LTy V)}
    (h : r ∉ a.holders) (v : RV M r a) (vs : HList (RV M r) rest) :
    heldValues M r (.cons v vs) =
      cast (by simp [held, h]) (heldValues M r vs) := by
  change (if h' : r ∈ a.holders then _ else _) = _
  exact dite_eq_right h

/-- `heldValues M r (hideAll M r ins)` preserves validity of all held values. -/
theorem heldValues_valid (r : Role) :
    ∀ {ins : List (LTy V)} (vals : HList (RV M r) ins),
      vals.All (RV.Valid M r) → (heldValues M r vals).All M.Valid
  | [], .nil, _ => trivial
  | a :: rest, .cons v vs, hv => by
      have hcast : ∀ {as bs : List V.Ty} (h : as = bs) (xs : HList M.Val as),
          xs.All M.Valid → (cast (congrArg (HList M.Val) h) xs).All M.Valid := by
        intro as bs h xs hxs; subst h; exact hxs
      have ih := heldValues_valid r vs hv.2
      by_cases hIn : r ∈ a.holders
      · rw [heldValues_cons_in M r hIn v vs]
        exact hcast (by simp [held, hIn]) (.cons (reveal M hIn v) (heldValues M r vs)) ⟨hv.1 hIn, ih⟩
      · rw [heldValues_cons_out M r hIn v vs]
        exact hcast (by simp [held, hIn]) (heldValues M r vs) ih

private theorem getAt_cast {T : Type} {V : T → Type} {as bs : List T} (h : as = bs)
    (xs : HList V as) (i : Nat) {τ : T} (hi : bs[i]? = some τ) :
    HList.getAt (cast (congrArg (HList V) h) xs) i hi = HList.getAt xs i (h ▸ hi) := by
  subst h; rfl

/-- Extract `(stmtIndex, ⟨ty, val⟩)` from a `StmtPos` and held values. -/
def stmtPosEntry (r : Role) {ins : List (LTy V)} (vals : HList (LVal M) ins)
    (sp : StmtPos V r ins) : Nat × ((τ : V.Ty) × M.Val τ) :=
  (sp.stmtIndex, ⟨sp.ty, HList.getAt (heldValues M r (hideAll M r vals)) sp.heldIndex sp.atHeld⟩)

private theorem stmtPosEntry_cons_in (r : Role) {a : LTy V} {rest : List (LTy V)}
    (hr : r ∈ a.holders) (v : LVal M a) (vs : HList (LVal M) rest)
    (p : StmtPos V r rest) :
    stmtPosEntry M r (.cons v vs)
      ⟨p.stmtIndex, p.heldIndex + 1, p.ty, by simp [held, hr, p.atHeld]⟩ =
    stmtPosEntry M r vs p := by
  unfold stmtPosEntry
  change (p.stmtIndex, (⟨p.ty, HList.getAt (heldValues M r (.cons (hide M r a v) (hideAll M r vs)))
      (p.heldIndex + 1) _⟩ : (τ : V.Ty) × M.Val τ)) = _
  rw [heldValues_cons_in M r hr, getAt_cast (by simp [held, hr])]
  rfl

private theorem stmtPosEntry_cons_out (r : Role) {a : LTy V} {rest : List (LTy V)}
    (hr : r ∉ a.holders) (v : LVal M a) (vs : HList (LVal M) rest)
    (p : StmtPos V r rest) :
    stmtPosEntry M r (.cons v vs)
      ⟨p.stmtIndex, p.heldIndex, p.ty, by simp [held, hr, p.atHeld]⟩ =
    stmtPosEntry M r vs p := by
  unfold stmtPosEntry
  change (p.stmtIndex, (⟨p.ty, HList.getAt (heldValues M r (.cons (hide M r a v) (hideAll M r vs)))
      p.heldIndex _⟩ : (τ : V.Ty) × M.Val τ)) = _
  rw [heldValues_cons_out M r hr, getAt_cast (by simp [held, hr])]

theorem statementPositions_go_agree (prover verifier : Role) :
    ∀ (sIdx : Nat) (ins : List (LTy V)) (vals : HList (LVal M) ins),
      (statementPositions.go prover prover verifier (.inl rfl) sIdx ins).map
        (stmtPosEntry M prover vals) =
      (statementPositions.go verifier prover verifier (.inr rfl) sIdx ins).map
        (stmtPosEntry M verifier vals)
  | _, [], .nil => rfl
  | sIdx, a :: rest, .cons v vs => by
      unfold statementPositions.go
      by_cases hBoth : prover ∈ a.holders ∧ verifier ∈ a.holders
      · rw [dite_eq_left hBoth, dite_eq_left hBoth]
        simp only [List.map_cons, List.map_map]
        have hP : prover ∈ a.holders := hBoth.1
        have hV : verifier ∈ a.holders := hBoth.2
        have hHead :
            HList.getAt (heldValues M prover (hideAll M prover (.cons v vs))) 0
              (show (held prover (a :: rest))[0]? = some a.ty by simp [held, hP]) =
            HList.getAt (heldValues M verifier (hideAll M verifier (.cons v vs))) 0
              (show (held verifier (a :: rest))[0]? = some a.ty by simp [held, hV]) := by
          change HList.getAt (heldValues M prover (.cons (hide M prover a v) (hideAll M prover vs))) 0 _ =
            HList.getAt (heldValues M verifier (.cons (hide M verifier a v) (hideAll M verifier vs))) 0 _
          rw [heldValues_cons_in M prover hP, heldValues_cons_in M verifier hV,
              getAt_cast (by simp [held, hP]), getAt_cast (by simp [held, hV])]
          simp only [HList.getAt, reveal_hide]
        have hTail := statementPositions_go_agree prover verifier (sIdx + 1) rest vs
        have hLP :
            List.map (stmtPosEntry M prover (.cons v vs) ∘ fun p =>
              ⟨p.stmtIndex, p.heldIndex + 1, p.ty, by simp [held, hP, p.atHeld]⟩)
              (statementPositions.go prover prover verifier (.inl rfl) (sIdx + 1) rest) =
            List.map (stmtPosEntry M prover vs)
              (statementPositions.go prover prover verifier (.inl rfl) (sIdx + 1) rest) := by
          apply List.map_congr_left
          intro p _; exact stmtPosEntry_cons_in M prover hP v vs p
        have hLV :
            List.map (stmtPosEntry M verifier (.cons v vs) ∘ fun p =>
              ⟨p.stmtIndex, p.heldIndex + 1, p.ty, by simp [held, hV, p.atHeld]⟩)
              (statementPositions.go verifier prover verifier (.inr rfl) (sIdx + 1) rest) =
            List.map (stmtPosEntry M verifier vs)
              (statementPositions.go verifier prover verifier (.inr rfl) (sIdx + 1) rest) := by
          apply List.map_congr_left
          intro p _; exact stmtPosEntry_cons_in M verifier hV v vs p
        rw [hLP, hLV, hTail]
        congr 1
        simp only [stmtPosEntry, hHead]
      · rw [dite_eq_right hBoth, dite_eq_right hBoth]
        have hTail := statementPositions_go_agree prover verifier sIdx rest vs
        by_cases hP : prover ∈ a.holders <;> by_cases hV : verifier ∈ a.holders
        · exact absurd ⟨hP, hV⟩ hBoth
        · rw [dite_eq_left hP, dite_eq_right hV]
          simp only [List.map_map]
          have hLP : List.map (stmtPosEntry M prover (.cons v vs) ∘ _)
              (statementPositions.go prover prover verifier (.inl rfl) sIdx rest) =
            List.map (stmtPosEntry M prover vs)
              (statementPositions.go prover prover verifier (.inl rfl) sIdx rest) :=
            List.map_congr_left fun p _ => stmtPosEntry_cons_in M prover hP v vs p
          have hLV : List.map (stmtPosEntry M verifier (.cons v vs) ∘ _)
              (statementPositions.go verifier prover verifier (.inr rfl) sIdx rest) =
            List.map (stmtPosEntry M verifier vs)
              (statementPositions.go verifier prover verifier (.inr rfl) sIdx rest) :=
            List.map_congr_left fun p _ => stmtPosEntry_cons_out M verifier hV v vs p
          rw [hLP, hLV, hTail]
        · rw [dite_eq_right hP, dite_eq_left hV]
          simp only [List.map_map]
          have hLP : List.map (stmtPosEntry M prover (.cons v vs) ∘ _)
              (statementPositions.go prover prover verifier (.inl rfl) sIdx rest) =
            List.map (stmtPosEntry M prover vs)
              (statementPositions.go prover prover verifier (.inl rfl) sIdx rest) :=
            List.map_congr_left fun p _ => stmtPosEntry_cons_out M prover hP v vs p
          have hLV : List.map (stmtPosEntry M verifier (.cons v vs) ∘ _)
              (statementPositions.go verifier prover verifier (.inr rfl) sIdx rest) =
            List.map (stmtPosEntry M verifier vs)
              (statementPositions.go verifier prover verifier (.inr rfl) sIdx rest) :=
            List.map_congr_left fun p _ => stmtPosEntry_cons_in M verifier hV v vs p
          rw [hLP, hLV, hTail]
        · rw [dite_eq_right hP, dite_eq_right hV]
          simp only [List.map_map]
          have hLP : List.map (stmtPosEntry M prover (.cons v vs) ∘ _)
              (statementPositions.go prover prover verifier (.inl rfl) sIdx rest) =
            List.map (stmtPosEntry M prover vs)
              (statementPositions.go prover prover verifier (.inl rfl) sIdx rest) :=
            List.map_congr_left fun p _ => stmtPosEntry_cons_out M prover hP v vs p
          have hLV : List.map (stmtPosEntry M verifier (.cons v vs) ∘ _)
              (statementPositions.go verifier prover verifier (.inr rfl) sIdx rest) =
            List.map (stmtPosEntry M verifier vs)
              (statementPositions.go verifier prover verifier (.inr rfl) sIdx rest) :=
            List.map_congr_left fun p _ => stmtPosEntry_cons_out M verifier hV v vs p
          rw [hLP, hLV, hTail]

/-- Prover and verifier evaluate `constructionStart` to the exact same transcript state on parts
of one input `ins`. -/
theorem constructionStart_agree (a : Admitted V) (suite : ModuleRef) {stateTy unitTy : V.Ty}
    (prover verifier : Role) (ins : List (LTy V)) (declKey : Key)
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (startRef : TypedFnRef V a.program.headers.fns [bytesTy] [stateTy])
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (stmtP : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held prover ins))))
    (stmtV : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held verifier ins))))
    (hP : buildStmtAbsorbItems a suite unitTy prover prover verifier (.inl rfl) ins declKey = .ok stmtP)
    (hV : buildStmtAbsorbItems a suite unitTy verifier prover verifier (.inr rfl) ins declKey = .ok stmtV)
    (vals : HList (LVal M) ins) :
    (constructionStart sessionBytes hsess startRef absorbRef stmtP).denote
      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
      (Env.positional (heldValues M prover (hideAll M prover vals))) =
    (constructionStart sessionBytes hsess startRef absorbRef stmtV).denote
      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
      (Env.positional (heldValues M verifier (hideAll M verifier vals))) := by
  let fnTable := Defs.fnTable M a.program.defs
  unfold constructionStart
  erw [letOp1_denote, letOp1_denote, localSem_op_literal, bytesLiteral_val M sessionBytes hsess]
  simp only [Process.bind, HList.single]
  erw [letOp1_denote, letOp1_denote, localSem_op]
  simp only [Env.all, env_get_insert_self]
  congr 1; funext st0
  rw [buildAbsorbChain_denote M fnTable absorbRef _ _ _ _ _ _ rfl,
      buildAbsorbChain_denote M fnTable absorbRef _ _ _ _ _ _ rfl,
      env_get_insert_self, env_get_insert_self]
  rw [absorbChainFold_reindex M fnTable absorbRef
    (Env.positional (heldValues M prover (hideAll M prover vals))) _ _
    (fun x => env_get_insert2_reindex _ (positional_freshFrom (held prover ins)) _ _ _ x)]
  rw [absorbChainFold_reindex M fnTable absorbRef
    (Env.positional (heldValues M verifier (hideAll M verifier vals))) _ _
    (fun x => env_get_insert2_reindex _ (positional_freshFrom (held verifier ins)) _ _ _ x)]
  congr 1
  have hAgree := statementPositions_go_agree M prover verifier 0 ins vals
  have hFoldEq : ∀ (spsP : List (StmtPos V prover ins)) (spsV : List (StmtPos V verifier ins))
      (itsP : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held prover ins))))
      (itsV : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held verifier ins))))
      (st : M.Val stateTy),
      spsP.map (stmtPosEntry M prover vals) = spsV.map (stmtPosEntry M verifier vals) →
      spsP.mapM (fun sp => match findSuiteEncode a suite unitTy sp.ty with
        | some encRef => Except.ok ⟨sp.ty, posVar (held prover ins) sp.heldIndex sp.atHeld,
            stmtLabel sp.stmtIndex, stmtLabel_bytes sp.stmtIndex, encRef⟩
        | none => Except.error (deployErr (V := V) declKey .callee)) = Except.ok itsP →
      spsV.mapM (fun sp => match findSuiteEncode a suite unitTy sp.ty with
        | some encRef => Except.ok ⟨sp.ty, posVar (held verifier ins) sp.heldIndex sp.atHeld,
            stmtLabel sp.stmtIndex, stmtLabel_bytes sp.stmtIndex, encRef⟩
        | none => Except.error (deployErr (V := V) declKey .callee)) = Except.ok itsV →
      absorbChainFold M fnTable absorbRef st (Env.positional (heldValues M prover (hideAll M prover vals))) itsP =
      absorbChainFold M fnTable absorbRef st (Env.positional (heldValues M verifier (hideAll M verifier vals))) itsV := by
    intro spsP
    induction spsP with
    | nil =>
        intro spsV itsP itsV st hEq hmP hmV
        cases spsV with
        | nil =>
            simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmP hmV
            subst hmP; subst hmV; rfl
        | cons _ _ => simp at hEq
    | cons spP restP ih =>
        intro spsV itsP itsV st hEq hmP hmV
        cases spsV with
        | nil => simp at hEq
        | cons spV restV =>
            simp only [List.map_cons, stmtPosEntry, List.cons.injEq, Prod.mk.injEq,
              Sigma.mk.injEq] at hEq
            obtain ⟨⟨hIdx, hTy, hVal⟩, hRest⟩ := hEq
            cases spP with | mk sIdxP hIdxP tyP atP =>
            cases spV with | mk sIdxV hIdxV tyV atV =>
            dsimp only at hIdx hTy hVal
            subst hIdx; subst hTy
            have hVal' := eq_of_heq hVal
            simp only [List.mapM_cons] at hmP hmV
            cases hEnc : findSuiteEncode a suite unitTy tyP with
            | none => simp [hEnc, bind, Except.bind] at hmP
            | some encRef =>
                simp only [hEnc, bind, Except.bind] at hmP hmV
                split at hmP
                · cases hmP
                · rename_i rP hRP
                  split at hmV
                  · cases hmV
                  · rename_i rV hRV
                    simp only [pure, Except.pure, Except.ok.injEq] at hmP hmV
                    subst hmP; subst hmV
                    simp only [absorbChainFold, env_get_positional, hVal']
                    congr 1; funext enc; congr 1; funext nextSt
                    exact ih restV rP rV nextSt.single hRest hRP hRV
  exact hFoldEq _ _ stmtP stmtV st0.single hAgree hP hV

/-! ## Pure collision-free ideal transcript path lemmas (`idealStart`, `idealAbsorbClause`, `idealDeriveClause`) -/

private theorem append_singleton_inj {α : Type} :
    ∀ {xs ys : List α} {a b : α}, xs ++ [a] = ys ++ [b] → xs = ys ∧ a = b
  | [], [], _, _, h => ⟨rfl, (List.cons.inj h).1⟩
  | [], _ :: ys, _, _, h => by
      have hnil := (List.cons.inj h).2
      cases ys <;> cases hnil
  | _ :: xs, [], _, _, h => by
      have hnil := (List.cons.inj h).2
      cases xs <;> cases hnil
  | x :: xs, y :: ys, a, b, h => by
      have ⟨hxy, hrest⟩ := List.cons.inj h
      have ⟨hxs, hab⟩ := append_singleton_inj hrest
      exact ⟨by rw [hxy, hxs], hab⟩

/-- Appending onto a pure ideal transcript path is unconditionally injective (zero hash collision
assumption). -/
theorem idealPathPush_injective {unitTy : V.Ty} {st₁ st₂ : M.Val (idealPathTy unitTy)}
    {lbl₁ lbl₂ : List Nat} {enc₁ enc₂ : List (M.Val unitTy)}
    (h : idealPathPush M st₁ lbl₁ enc₁ = idealPathPush M st₂ lbl₂ enc₂) :
    st₁ = st₂ ∧ lbl₁ = lbl₂ ∧ enc₁ = enc₂ := by
  cases st₁ with | mk m₁ d₁ =>
  cases d₁ with | mk dl₁ u₁ =>
  cases u₁
  cases st₂ with | mk m₂ d₂ =>
  cases d₂ with | mk dl₂ u₂ =>
  cases u₂
  have ⟨hm, hd⟩ := Prod.mk.inj h
  have hd1 := (Prod.mk.inj hd).1
  have ⟨hmEq, hlbl⟩ := append_singleton_inj hm
  have ⟨hdEq, henc⟩ := append_singleton_inj hd1
  subst hmEq; subst hdEq; subst hlbl; subst henc
  exact ⟨rfl, rfl, rfl⟩

theorem idealPathInit_valid (unitTy : V.Ty) (sessionBytes : List Nat)
    (hsess : ∀ b, b ∈ sessionBytes → b < 256) :
    M.Valid (idealPathTy unitTy) (idealPathInit M unitTy sessionBytes) := by
  refine ⟨⟨?_, (fun _ h => nomatch h)⟩, ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩, trivial⟩
  intro bs hbs
  rcases List.mem_singleton.mp hbs with rfl
  refine ⟨fun b hb => ?_, (fun _ h => nomatch h)⟩
  rcases List.mem_cons.mp hb with rfl | hmem
  · exact Nat.zero_lt_succ 255
  · exact hsess b hmem

theorem idealPathPush_valid {unitTy : V.Ty} (st : M.Val (idealPathTy unitTy))
    (tagLbl : List Nat) (encVal : List (M.Val unitTy))
    (hst : M.Valid (idealPathTy unitTy) st)
    (hlbl : ∀ b, b ∈ tagLbl → b < 256)
    (henc : M.Valid (.seq unitTy none) encVal) :
    M.Valid (idealPathTy unitTy) (idealPathPush M st tagLbl encVal) := by
  refine ⟨⟨?_, (fun _ h => nomatch h)⟩, ⟨?_, (fun _ h => nomatch h)⟩, trivial⟩
  · intro bs hbs
    rcases List.mem_append.mp hbs with hm | hs
    · exact hst.1.1 bs hm
    · rcases List.mem_singleton.mp hs with rfl
      exact ⟨hlbl, (fun _ h => nomatch h)⟩
  · intro ds hds
    rcases List.mem_append.mp hds with hm | hs
    · exact hst.2.1.1 ds hm
    · rcases List.mem_singleton.mp hs with rfl
      exact henc

private theorem var_name_lt_of_fresh {T : Type} {Γ : Ctx T} {n : Nat} {τ : T}
    (h : FreshFrom Γ n) (x : Var Γ τ) : (x.name : Nat) < n := by
  by_cases hlt : (x.name : Nat) < n
  · exact hlt
  · have hnone := h x.name (Nat.le_of_not_lt hlt)
    have hx := x.typed
    rw [hnone] at hx
    cases hx

private theorem name_ne_of_lt_add {a b : Name} (k : Nat) (h : (a : Nat) < b) : a ≠ b + k :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right b k))

private theorem getAt_idealPath_head {unitTy : V.Ty} (st : M.Val (idealPathTy unitTy)) :
    Tys.getAt M (idealPathTys unitTy) .head st = st.1 := by
  cases st; rfl

private theorem getAt_idealPath_tail_head {unitTy : V.Ty} (st : M.Val (idealPathTy unitTy)) :
    Tys.getAt M (idealPathTys unitTy) (.tail .head) st = st.2.1 := by
  cases st with | mk _ d => cases d; rfl

private theorem env_all_idealPath {T : Type} {F : T → Type} {Γ : Ctx T} (env : Env F Γ)
    {a b : T} (x : Var Γ a) (y : Var Γ b) :
    env.all (HList.cons x (HList.cons y HList.nil)) =
      HList.cons (env.get x) (HList.cons (env.get y) HList.nil) :=
  rfl

theorem appendIdealPathLocal_denote_eq {fns : List (FnHeader V)} {unitTy : V.Ty}
    (fnTable : FnTable M fns) (hfree : Ty.isLinear V unitTy = false)
    {Γ : Ctx V.Ty} {outs : List V.Ty} (fresh : Nat) (hfresh : FreshFrom Γ fresh)
    (stVar : Var Γ (idealPathTy unitTy)) (tagLblVar : Var Γ bytesTy)
    (encVar : Var Γ (.seq unitTy none))
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (fresh + 9) → Γ.Within Γ' →
      Var Γ' (idealPathTy unitTy) → Term (localDialect V fns) Γ' outs)
    (path : List Frame) (env : Env M.Val Γ)
    (target : Local (HList M.Val outs))
    (hrest : ∀ (Γ' : Ctx V.Ty) (h' : FreshFrom Γ' (fresh + 9)) (w : Γ.Within Γ')
      (nextSt : Var Γ' (idealPathTy unitTy)) (env' : Env M.Val Γ'),
      env'.get nextSt = idealPathPush M (env.get stVar) (env.get tagLblVar) (env.get encVar) →
      (∀ {τ} (x : Var Γ' τ) (hΓ : Γ.find? x.name = some τ), env'.get x = env.get ⟨x.name, hΓ⟩) →
      (rest Γ' h' w nextSt).denote (localSem M fns fnTable) path env' = target) :
    (appendIdealPathLocal hfree fresh hfresh stVar tagLblVar encVar rest).denote
      (localSem M fns fnTable) path env = target := by
  have hEncLt : (encVar.name : Nat) < fresh := var_name_lt_of_fresh hfresh encVar
  unfold appendIdealPathLocal
  rw [letOp1_local_owned_denote]
  simp only [Env.all]
  erw [ownedOp_getTuple, getAt_idealPath_head]
  dsimp only [Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert_reindex env hfresh]
  erw [ownedOp_getTuple, getAt_idealPath_tail_head]
  dsimp only [Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert2_reindex env hfresh, ownedOp, HList.toItems,
    Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert_self]
  rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
  · erw [ownedOp_seqConcat]
    dsimp only [Process.bind, HList.single]
    rw [letOp1_local_owned_denote]
    simp only [Env.all]
    rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne]
    rotate_left 1
    · dsimp only [Var.reindex]; exact Nat.ne_of_lt hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 1 hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 2 hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 3 hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 4 hEncLt
    simp only [ownedOp, HList.toItems, Process.bind, HList.single]
    rw [letOp1_local_owned_denote]
    simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
    rw [letOp1_local_owned_denote]
    simp only [Env.all, env_get_insert_self]
    rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
        env_get_insert_ne, env_get_insert_eq]
    · erw [ownedOp_seqConcat]
      dsimp only [Process.bind, HList.single]
      erw [letOp1_local_makeTuple2_denote]
      dsimp only [concatSize]
      rw [env_get_insert_self, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
          env_get_insert_eq]
      · apply hrest _ _ _ _ _
        · rw [env_get_insert_self]
          simp only [idealPathPush, Var.reindex]
        · intro τ x hΓ
          have hxLt : (x.name : Nat) < fresh := var_name_lt_of_fresh hfresh ⟨x.name, hΓ⟩
          rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
              env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
              env_get_insert_ne]
          all_goals (try dsimp only [Var.reindex, freshVar]) <;>
            first | rfl | exact Nat.ne_of_lt hxLt | exact name_ne_of_lt_add _ hxLt
      all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)
    all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)
  all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)

/-- Pure fold matching `buildIdealPathChain` on statement items. -/
def idealPathChainFold {fns : List (FnHeader V)} {unitTy : V.Ty}
    (fnTable : FnTable M fns)
    (st : M.Val (idealPathTy unitTy)) {Γ : Ctx V.Ty} (env : Env M.Val Γ) :
    List (StmtAbsorbItem V fns unitTy Γ) → Local (M.Val (idealPathTy unitTy))
  | [] => .done st
  | item :: rest =>
      (item.encode.eval M fnTable (.cons (env.get item.input) .nil)).bind fun enc =>
        idealPathChainFold fnTable (idealPathPush M st (1 :: item.label) enc.single) env rest

theorem idealPathChainFold_reindex {fns : List (FnHeader V)} {unitTy : V.Ty}
    (fnTable : FnTable M fns)
    {Γ Δ : Ctx V.Ty} (env : Env M.Val Γ) (env' : Env M.Val Δ) (w : Γ.Within Δ)
    (hagree : ∀ {τ} (x : Var Γ τ), env'.get (x.reindex w) = env.get x) :
    ∀ (st : M.Val (idealPathTy unitTy)) (items : List (StmtAbsorbItem V fns unitTy Γ)),
      idealPathChainFold M fnTable st env'
          (items.map fun it => ⟨it.ty, it.input.reindex w, it.label, it.labelBytes, it.encode⟩) =
        idealPathChainFold M fnTable st env items
  | _, [] => rfl
  | st, item :: rest => by
      simp only [List.map_cons, idealPathChainFold, hagree]
      congr 1; funext enc
      exact idealPathChainFold_reindex fnTable env env' w hagree
        (idealPathPush M st (1 :: item.label) enc.single) rest

theorem buildIdealPathChain_denote {fns : List (FnHeader V)} {unitTy : V.Ty}
    (fnTable : FnTable M fns) (hfree : Ty.isLinear V unitTy = false) (n : Nat) :
    ∀ {Γ : Ctx V.Ty} (fresh : Nat) (hfresh : FreshFrom Γ fresh) (env : Env M.Val Γ)
      (stVar : Var Γ (idealPathTy unitTy)) (items : List (StmtAbsorbItem V fns unitTy Γ)),
      items.length = n →
      (buildIdealPathChain hfree fresh hfresh stVar items).denote (localSem M fns fnTable) [] env =
        (idealPathChainFold M fnTable (env.get stVar) env items).map fun st => .cons st .nil := by
  induction n with
  | zero =>
      intro Γ fresh hfresh env stVar items hlen
      cases items with
      | nil => unfold buildIdealPathChain; rfl
      | cons _ _ => cases hlen
  | succ k ih =>
      intro Γ fresh hfresh env stVar items hlen
      cases items with
      | nil => cases hlen
      | cons item rest =>
          have hTagLbl : ∀ b, b ∈ (1 :: item.label) → b < 256 := fun b hb => by
            rcases List.mem_cons.mp hb with rfl | hm
            · exact Nat.succ_lt_succ (Nat.zero_lt_succ 254)
            · exact item.labelBytes b hm
          unfold buildIdealPathChain
          erw [letOp1_denote, localSem_op_literal, bytesLiteral_val M (1 :: item.label) hTagLbl]
          simp only [Process.bind, HList.single]
          rw [letOp1_local_denote]
          simp only [Env.all]
          rw [env_get_insert_reindex env hfresh]
          change (item.encode.eval M fnTable (.cons (env.get item.input) .nil)).bind _ = _
          simp only [idealPathChainFold, Process.map_bind]
          congr 1; funext enc
          apply appendIdealPathLocal_denote_eq M fnTable hfree
          intro Γ' h' w nextSt env' hNext hAgree
          rw [ih _ _ env' nextSt _ (by rw [List.length_map]; exact Nat.succ.inj hlen)]
          rw [hNext, env_get_insert2_reindex env hfresh,
              env_get_insert_reindex _ (hfresh.insert bytesTy),
              env_get_insert_self, env_get_insert_self]
          congr 1
          apply idealPathChainFold_reindex M fnTable env env' _
          intro τ x
          have hxLt : (x.name : Nat) < fresh := var_name_lt_of_fresh hfresh x
          have hIn2 : ((Γ.insert fresh bytesTy).insert (fresh + 1) (.seq unitTy none)).find?
              (x.reindex ((hfresh.within bytesTy).trans ((hfresh.insert bytesTy).within (.seq unitTy none)) |>.trans w)).name = some τ := by
            change ((Γ.insert fresh bytesTy).insert (fresh + 1) (.seq unitTy none)).find? x.name = some τ
            rw [Ctx.find?_insert, ite_eq_right, Ctx.find?_insert, ite_eq_right]
            · exact x.typed
            · exact Nat.ne_of_lt hxLt
            · exact name_ne_of_lt_add 1 hxLt
          rw [hAgree _ hIn2, env_get_insert_ne, env_get_insert_ne]
          · rfl
          · dsimp only [Var.reindex]; exact Nat.ne_of_lt hxLt
          · dsimp only [Var.reindex]; exact name_ne_of_lt_add 1 hxLt

theorem idealPathChainFold_done (a : Admitted V) {unitTy : V.Ty} :
    ∀ {Γ : Ctx V.Ty} (env : Env M.Val Γ) (st : M.Val (idealPathTy unitTy))
      (_hst : M.Valid (idealPathTy unitTy) st)
      (items : List (StmtAbsorbItem V a.program.headers.fns unitTy Γ))
      (_hitems : ∀ it ∈ items, M.Valid it.ty (env.get it.input)),
      ∃ stEnd,
        idealPathChainFold M (Defs.fnTable M a.program.defs) st env items = .done stEnd ∧
        M.Valid (idealPathTy unitTy) stEnd
  | _, _, st, hst, [], _ => ⟨st, rfl, hst⟩
  | _, env, st, hst, item :: rest, hitems => by
      have hit : M.Valid item.ty (env.get item.input) := hitems item List.mem_cons_self
      obtain ⟨enc, henc, hencV⟩ := item.encode.eval_done M a (.cons (env.get item.input) .nil)
        (valid_single _ hit)
      have hencS : M.Valid (.seq unitTy none) enc.single := by
        cases enc with | cons e encNil => cases encNil; exact hencV.1
      have hlbl : ∀ b, b ∈ (1 :: item.label) → b < 256 := fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hm
        · exact Nat.succ_lt_succ (Nat.zero_lt_succ 254)
        · exact item.labelBytes b hm
      have hnextV := idealPathPush_valid M st (1 :: item.label) enc.single hst hlbl hencS
      obtain ⟨stEnd, hend, hendV⟩ := idealPathChainFold_done a env
        (idealPathPush M st (1 :: item.label) enc.single) hnextV rest
        (fun it h => hitems it (List.mem_cons_of_mem _ h))
      refine ⟨stEnd, ?_, hendV⟩
      simp only [idealPathChainFold, henc, Process.bind, hend]

theorem idealStart_denote {fns : List (FnHeader V)} {unitTy : V.Ty}
    (fnTable : FnTable M fns) (hfree : Ty.isLinear V unitTy = false)
    {r : Role} {ins : List (LTy V)}
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (items : List (StmtAbsorbItem V fns unitTy (Ctx.positional (held r ins))))
    (vals : HList M.Val (held r ins)) :
    (idealStart hfree sessionBytes hsess items).denote (localSem M fns fnTable) []
      (Env.positional vals) =
      (idealPathChainFold M fnTable (idealPathInit M unitTy sessionBytes)
        (Env.positional vals) items).map fun st => .cons st .nil := by
  have hTagSess : ∀ b, b ∈ (0 :: sessionBytes) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hm
    · exact Nat.zero_lt_succ 255
    · exact hsess b hm
  unfold idealStart
  erw [letOp1_denote, localSem_op_literal, bytesLiteral_val M (0 :: sessionBytes) hTagSess]
  simp only [Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert_self, ownedOp, HList.toItems, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [ownedOp, HList.toItems, Process.bind, HList.single]
  rw [letOp1_local_owned_denote]
  simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
  rw [letOp1_local_makeTuple2_denote]
  rw [env_get_insert_self, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
  · rw [buildIdealPathChain_denote M fnTable hfree _ _ _ _ _ _ rfl, env_get_insert_self]
    congr 1
    apply idealPathChainFold_reindex M fnTable (Env.positional vals) _ _
    intro τ x
    have hxLt : (x.name : Nat) < (held r ins).length :=
      var_name_lt_of_fresh (positional_freshFrom (held r ins)) x
    rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
        env_get_insert_ne, env_get_insert_ne, env_get_insert_ne]
    all_goals (try dsimp only [Var.reindex]) <;>
      first | rfl | exact Nat.ne_of_lt hxLt | exact name_ne_of_lt_add _ hxLt
  all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)

theorem idealStart_done (a : Admitted V) {unitTy : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    {r : Role} {ins : List (LTy V)}
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (items : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held r ins))))
    (vals : HList M.Val (held r ins)) (hvals : vals.All M.Valid) :
    ∃ stEnd,
      (idealStart hfree sessionBytes hsess items).denote
        (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) [] (Env.positional vals) =
        .done (.cons stEnd .nil) ∧
      M.Valid (idealPathTy unitTy) stEnd := by
  have hitems : ∀ it ∈ items, M.Valid it.ty ((Env.positional vals).get it.input) := by
    intro it _
    have htyped := it.input.typed
    rw [Ctx.find?_positional] at htyped
    have hget : (Env.positional vals).get it.input = HList.getAt vals it.input.name htyped := by
      have := env_get_positional vals it.input.name htyped
      simpa [posVar] using this
    rw [hget]
    exact HList.getAt_valid vals it.input.name htyped hvals
  obtain ⟨stEnd, hend, hendV⟩ := idealPathChainFold_done M a (Env.positional vals)
    (idealPathInit M unitTy sessionBytes) (idealPathInit_valid M unitTy sessionBytes hsess)
    items hitems
  refine ⟨stEnd, ?_, hendV⟩
  rw [idealStart_denote, hend]
  rfl

/-- `idealInitialPath` agrees identically with `idealStart` on any valid verifier input. -/
theorem idealInitialPath_eq_idealStart (a : Admitted V) (suite : ModuleRef) {unitTy : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (prover verifier : Role) {ins : List (LTy V)} (declKey : Key)
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (stmtV : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held verifier ins))))
    (hSV : buildStmtAbsorbItems a suite unitTy verifier prover verifier (.inr rfl) ins declKey = .ok stmtV)
    (vals : HList (RV M verifier) ins) (hvals : vals.All (RV.Valid M verifier)) :
    ∃ st0,
      (idealStart hfree sessionBytes hsess stmtV).denote
        (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
        (Env.positional (heldValues M verifier vals)) = .done (.cons st0 .nil) ∧
      idealInitialPath M a suite unitTy prover verifier sessionBytes vals = some st0 ∧
      M.Valid (idealPathTy unitTy) st0 := by
  have hHeldV := heldValues_valid M verifier vals hvals
  have hGo : ∀ (sps : List (StmtPos V verifier ins))
      (items : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held verifier ins))))
      (st : M.Val (idealPathTy unitTy)),
      M.Valid (idealPathTy unitTy) st →
      sps.mapM (fun sp => match findSuiteEncode a suite unitTy sp.ty with
        | some encRef => Except.ok ⟨sp.ty, posVar (held verifier ins) sp.heldIndex sp.atHeld,
            stmtLabel sp.stmtIndex, stmtLabel_bytes sp.stmtIndex, encRef⟩
        | none => Except.error (deployErr (V := V) declKey .callee)) = Except.ok items →
      ∃ stEnd,
        idealPathChainFold M (Defs.fnTable M a.program.defs) st
          (Env.positional (heldValues M verifier vals)) items = .done stEnd ∧
        idealInitialPath.go M a suite unitTy verifier vals st sps = some stEnd ∧
        M.Valid (idealPathTy unitTy) stEnd := by
    intro sps
    induction sps with
    | nil =>
        intro items st hst hm
        simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm
        subst hm
        exact ⟨st, rfl, rfl, hst⟩
    | cons sp rest ih =>
        intro items st hst hm
        simp only [List.mapM_cons] at hm
        cases hEnc : findSuiteEncode a suite unitTy sp.ty with
        | none => simp [hEnc, bind, Except.bind] at hm
        | some encRef =>
            simp only [hEnc, bind, Except.bind] at hm
            split at hm
            · cases hm
            · rename_i restItems hRestM
              simp only [pure, Except.pure, Except.ok.injEq] at hm
              subst hm
              have hv : M.Valid sp.ty
                  ((Env.positional (heldValues M verifier vals)).get
                    (posVar (held verifier ins) sp.heldIndex sp.atHeld)) := by
                rw [env_get_positional]
                exact HList.getAt_valid (heldValues M verifier vals) sp.heldIndex sp.atHeld hHeldV
              obtain ⟨enc, henc, hencV⟩ := encRef.eval_done M a
                (.cons ((Env.positional (heldValues M verifier vals)).get
                  (posVar (held verifier ins) sp.heldIndex sp.atHeld)) .nil) ⟨hv, trivial⟩
              cases enc with
              | cons encV encNil =>
                  cases encNil
                  have hTagLbl : ∀ b, b ∈ (1 :: stmtLabel sp.stmtIndex) → b < 256 := fun b hb => by
                    rcases List.mem_cons.mp hb with rfl | hm'
                    · decide
                    · exact stmtLabel_bytes sp.stmtIndex b hm'
                  have hNextV := idealPathPush_valid M st (1 :: stmtLabel sp.stmtIndex) encV
                    hst hTagLbl hencV.1
                  obtain ⟨stEnd, hFold, hInit, hEndV⟩ := ih restItems _ hNextV hRestM
                  refine ⟨stEnd, ?_, ?_, hEndV⟩
                  · simp only [idealPathChainFold, henc, Process.bind, HList.single, hFold]
                  · unfold idealInitialPath.go
                    simp only [hEnc, henc, HList.single, hInit]
  obtain ⟨st0, hFold, hInit, hStV⟩ := hGo _ stmtV (idealPathInit M unitTy sessionBytes)
    (idealPathInit_valid M unitTy sessionBytes hsess) hSV
  refine ⟨st0, ?_, hInit, hStV⟩
  rw [idealStart_denote, hFold]
  rfl

theorem appendIdealPathRole_denote_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy : V.Ty} (hfree : Ty.isLinear V unitTy = false)
    {Γ : Ctx (LTy V)} {outs : List (LTy V)} (fresh : Nat) (hfresh : FreshFrom Γ fresh)
    (stVar : Var Γ ⟨idealPathTy unitTy, [r]⟩) (tagLblVar : Var Γ ⟨bytesTy, [r]⟩)
    (encVar : Var Γ ⟨.seq unitTy none, [r]⟩)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (fresh + 9) → Γ.Within Γ' →
      Var Γ' ⟨idealPathTy unitTy, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (st : M.Val (idealPathTy unitTy)) (tagLbl : List Nat) (enc : List (M.Val unitTy))
    (hst : env.get stVar = hide M r ⟨idealPathTy unitTy, [r]⟩ st)
    (hlbl : env.get tagLblVar = hide M r ⟨bytesTy, [r]⟩ tagLbl)
    (henc : env.get encVar = hide M r ⟨.seq unitTy none, [r]⟩ enc)
    (target : Process (RSig M) Stop (HList (RV M r) outs))
    (hrest : ∀ (Γ' : Ctx (LTy V)) (h' : FreshFrom Γ' (fresh + 9)) (w : Γ.Within Γ')
      (nextSt : Var Γ' ⟨idealPathTy unitTy, [r]⟩) (env' : Env (RV M r) Γ'),
      env'.get nextSt = hide M r ⟨idealPathTy unitTy, [r]⟩ (idealPathPush M st tagLbl enc) →
      (∀ {a} (x : Var Γ' a) (hΓ : Γ.find? x.name = some a), env'.get x = env.get ⟨x.name, hΓ⟩) →
      (rest Γ' h' w nextSt).denote (roleSem M r fnTable rTable) path env' = target) :
    (appendIdealPathRole hfree r fresh hfresh stVar tagLblVar encVar rest).denote
      (roleSem M r fnTable rTable) path env = target := by
  have htfree : Tys.anyLinear V (idealPathTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  have hEncLt : (encVar.name : Nat) < fresh := var_name_lt_of_fresh hfresh encVar
  unfold appendIdealPathRole
  refine (letOp1_computeAlone1_eq M r fnTable rTable _ _ _ st _ _ _ _ _ hst).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (idealPathTys unitTy) .head htfree st))) _).trans ?_
  rw [getAt_idealPath_head]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M r fnTable rTable _ _ _ st _ _ _ _ _
    ((env_get_insert_reindex env hfresh _ stVar).trans hst)).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (idealPathTys unitTy) (.tail .head) htfree st))) _).trans ?_
  rw [getAt_idealPath_tail_head]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M r fnTable rTable _ _ _ tagLbl _ _ _ _ _
    ((env_get_insert2_reindex env hfresh _ _ _ tagLblVar).trans hlbl)).trans ?_
  dsimp only [localOp, ownedOp, HList.toItems, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M r fnTable rTable (τ₁ := .seq bytesTy (some 1)) _ _ _
    [tagLbl] _ _ _ _ _ (env_get_insert_self _ (fresh + 2) _)).trans ?_
  dsimp only [localOp, ownedOp, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M r fnTable rTable (τ₂ := metaLogTy) _ _ _ _ st.1 [tagLbl] _ _ _ _ _
    ?_ (env_get_insert_self _ (fresh + 3) _)).trans ?_
  · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
    all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_seqConcat M bytesTy none none st.1 [tagLbl]))) _).trans ?_
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M r fnTable rTable _ _ _ enc _ _ _ _ _ ?_).trans ?_
  · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
        env_get_insert_ne]
    · cases encVar; exact henc
    all_goals (try dsimp only [Var.reindex]) <;>
      first | exact Nat.ne_of_lt hEncLt | exact name_ne_of_lt_add _ hEncLt
  dsimp only [localOp, ownedOp, HList.toItems, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M r fnTable rTable (τ₁ := .seq (.seq unitTy none) (some 1)) _ _ _
    [enc] _ _ _ _ _ (env_get_insert_self _ (fresh + 5) _)).trans ?_
  dsimp only [localOp, ownedOp, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M r fnTable rTable (τ₂ := dataLogTy unitTy) _ _ _ _ st.2.1 [enc] _ _ _ _ _
    ?_ (env_get_insert_self _ (fresh + 6) _)).trans ?_
  · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
        env_get_insert_ne, env_get_insert_eq]
    all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_seqConcat M (.seq unitTy none) none none st.2.1 [enc]))) _).trans ?_
  dsimp only [concatSize, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M r fnTable rTable (τ₁ := metaLogTy) (τ₂ := dataLogTy unitTy) _ _ _ _
    (st.1 ++ [tagLbl]) (st.2.1 ++ [enc]) _ _ _ _ _ ?_ (env_get_insert_self _ (fresh + 7) _)).trans ?_
  · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
    all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_makeTuple M (idealPathTys unitTy) (.cons (st.1 ++ [tagLbl]) (.cons (st.2.1 ++ [enc]) .nil))))) _).trans ?_
  dsimp only [idealPathTys, Tys.ofHList, liftLocal_done, Process.bind, HList.single]
  apply hrest _ _ _ _ _
  · rw [env_get_insert_self]; rfl
  · intro a x hΓ
    have hxLt : (x.name : Nat) < fresh := var_name_lt_of_fresh hfresh ⟨x.name, hΓ⟩
    rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
        env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
        env_get_insert_ne]
    all_goals (try dsimp only [Var.reindex, freshVar]) <;>
      first | rfl | exact Nat.ne_of_lt hxLt | exact name_ne_of_lt_add _ hxLt

/-! ## Compact layout `start` safety -/

private theorem hlist_all_cast {T : Type} {V : T → Type} {P : ∀ t, V t → Prop}
    {as bs : List T} (h : as = bs) (vs : HList V as) (hv : vs.All P) :
    (cast (congrArg (HList V) h) vs).All P := by
  subst h; exact hv

theorem buildCompactParse_safe (a : Admitted V) (unitTy : V.Ty)
    (hfree : Ty.isLinear V unitTy = false) (guardKey : Key) (wireTys : List V.Ty) :
    ∀ {Γ : Ctx V.Ty} (fresh : Nat) (hfresh : FreshFrom Γ fresh) (env : Env M.Val Γ)
      (bufVar : Var Γ (.seq unitTy none)) (offVar : Var Γ .nat)
      (parsedAcc : List V.Ty) (accVars : HList (Var Γ) parsedAcc)
      (readers : List ((τ : V.Ty) × SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]))
      (hMatch : parsedAcc ++ readers.map Sigma.fst = wireTys),
      M.Valid (.seq unitTy none) (env.get bufVar) →
      (env.all accVars).All M.Valid →
      ((buildCompactParse unitTy hfree guardKey wireTys fresh hfresh bufVar offVar
          parsedAcc accVars readers hMatch).denote
        (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) [] env).Every
        (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined)
  | Γ, fresh, hfresh, env, bufVar, offVar, parsedAcc, accVars, [], hMatch, _, hacc => by
      unfold buildCompactParse
      rw [letOp1_local_owned_denote]
      simp only [Env.all]
      rw [ownedOp_seqLength]
      simp only [Process.bind, HList.single]
      rw [letOp1_local_owned_denote]
      simp only [Env.all]
      rw [env_get_insert_reindex env hfresh, env_get_insert_self, ownedOp_natEqual]
      simp only [Process.bind, HList.single]
      erw [Term.denote_guard, env_get_insert_self, localSem_holds, localSem_stop]
      cases Nat.beq (env.get offVar) (env.get bufVar).length with
      | false =>
          change Stop.declared Reason.reject ⟨[], guardKey⟩ ≠ Stop.undefined
          intro h; cases h
      | true =>
          simp only [Bool.cond_true]
          rw [letOp1_local_owned_denote]
          rw [ownedOp_makeTuple]
          simp only [Process.bind, HList.single, Term.denote_ret,
            Env.all, env_get_insert_self, Process.Every]
          have hacc' : (((env.insert fresh (env.get bufVar).length).insert (fresh + 1) true).all
              (accVars.reindex ((hfresh.within .nat).trans ((hfresh.insert .nat).within .bool)))).All
              M.Valid := by
            have hstep : ∀ {items : List V.Ty} (xs : HList (Var Γ) items),
                ((env.insert fresh (env.get bufVar).length).insert (fresh + 1) true).all
                  (xs.reindex ((hfresh.within .nat).trans ((hfresh.insert .nat).within .bool))) =
                  env.all xs := by
              intro items xs
              induction xs with
              | nil => rfl
              | cons x rest ih =>
                  show HList.cons _ _ = HList.cons _ _
                  rw [env_get_insert2_reindex env hfresh, ih]
            rw [hstep accVars]
            exact hacc
          refine ⟨Tys.ofHList_valid (tysOfList wireTys) _ ?_, trivial⟩
          have hCastEq : parsedAcc = (tysOfList wireTys).toList := by
            rw [tysOfList_toList]; simpa using hMatch
          rw [env_all_cast hCastEq]
          exact hlist_all_cast hCastEq _ hacc'
  | Γ, fresh, hfresh, env, bufVar, offVar, parsedAcc, accVars, ⟨τ, readRef⟩ :: rest, hMatch,
      hbuf, hacc => by
      unfold buildCompactParse
      erw [letOp2_denote, localSem_op]
      simp only [Env.all]
      have hreadSafe := readRef.eval_safe M a (.cons (env.get bufVar) (.cons (env.get offVar) .nil))
        ⟨hbuf, trivial, trivial⟩
      change ((readRef.eval M (Defs.fnTable M a.program.defs)
          (.cons (env.get bufVar) (.cons (env.get offVar) .nil))).bind _).Every _ _ _
      rw [Process.every_bind]
      refine Process.every_mono _ _ ?_ (fun _ h => h) hreadSafe
      intro res hres
      cases res with
      | cons v res1 =>
          cases res1 with
          | cons nextOff res2 =>
              cases res2
              apply buildCompactParse_safe a unitTy hfree guardKey wireTys (fresh + 2)
                ((hfresh.insert τ).insert .nat) ((env.insert fresh v).insert (fresh + 1) nextOff)
                (bufVar.reindex ((hfresh.within τ).trans ((hfresh.insert τ).within .nat)))
                (freshVar (Γ.insert fresh τ) (fresh + 1) .nat)
                (parsedAcc ++ [τ])
                (HList.append (accVars.reindex ((hfresh.within τ).trans ((hfresh.insert τ).within .nat)))
                  (.cons ((freshVar Γ fresh τ).reindex ((hfresh.insert τ).within .nat)) .nil))
                rest (by simpa [List.append_assoc] using hMatch)
              · rw [env_get_insert2_reindex env hfresh]
                exact hbuf
              · have hacc2 : ((env.insert fresh v).insert (fresh + 1) nextOff).all
                    (HList.append (accVars.reindex ((hfresh.within τ).trans ((hfresh.insert τ).within .nat)))
                      (.cons ((freshVar Γ fresh τ).reindex ((hfresh.insert τ).within .nat)) .nil)) =
                    HList.append (env.all accVars) (.cons v .nil) := by
                  have hApp : ∀ {as bs : List V.Ty} {Δ : Ctx V.Ty} (e : Env M.Val Δ)
                      (xs : HList (Var Δ) as) (ys : HList (Var Δ) bs),
                      e.all (HList.append xs ys) = HList.append (e.all xs) (e.all ys) := by
                    intro as bs Δ e xs ys
                    induction xs with
                    | nil => rfl
                    | cons _ _ ih => show HList.cons _ _ = HList.cons _ _; rw [ih]
                  have hReindex : ∀ {items : List V.Ty} (xs : HList (Var Γ) items),
                      ((env.insert fresh v).insert (fresh + 1) nextOff).all
                        (xs.reindex ((hfresh.within τ).trans ((hfresh.insert τ).within .nat))) =
                        env.all xs := by
                    intro items xs
                    induction xs with
                    | nil => rfl
                    | cons _ _ ih =>
                        show HList.cons _ _ = HList.cons _ _
                        rw [env_get_insert2_reindex env hfresh, ih]
                  rw [hApp]
                  congr 1
                  · exact hReindex accVars
                  · show HList.cons _ .nil = HList.cons _ .nil
                    rw [env_get_insert_reindex _ (hfresh.insert τ), env_get_insert_self]
                rw [hacc2]
                have hAllApp : ∀ {as bs : List V.Ty} (xs : HList M.Val as) (ys : HList M.Val bs),
                    xs.All M.Valid → ys.All M.Valid → (HList.append xs ys).All M.Valid := by
                  intro as bs xs ys hx hy
                  induction xs with
                  | nil => exact hy
                  | cons _ _ ih => exact ⟨hx.1, ih hx.2⟩
                exact hAllApp _ _ hacc ⟨hres.1, trivial⟩

theorem compactLayoutVStart_safe (a : Admitted V) {r : Role} {ins : List (LTy V)}
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (stmtItems : List ((τ : V.Ty) × Var (Ctx.positional (.seq unitTy none :: held r ins)) τ))
    (readers : List ((τ : V.Ty) × SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]))
    (proof : List (M.Val unitTy)) (hproof : M.Valid (.seq unitTy none) proof)
    (vals : HList M.Val (held r ins)) (hvals : vals.All M.Valid) :
    ((compactLayoutVStart unitTy hfree guardKey stmtItems readers).denote
      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
      (Env.positional (.cons proof vals))).Every
      (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined) := by
  unfold compactLayoutVStart
  rw [letOp1_local_natLiteral_denote]
  apply buildCompactParse_safe
  · rw [env_get_insert_reindex _ (positional_freshFrom _), env_get_positional_0]
    exact hproof
  · induction stmtItems with
    | nil =>
        simp only [compactLayoutVStart.packStmts]
        trivial
    | cons it rest ih =>
        cases it with
        | mk itTy itVar =>
            simp only [compactLayoutVStart.packStmts, Env.all, HList.all_cons]
            refine ⟨?_, ih⟩
            rw [env_get_insert_reindex _ (positional_freshFrom _)]
            have htyped := itVar.typed
            rw [Ctx.find?_positional] at htyped
            have hget : (Env.positional (.cons proof vals)).get itVar =
                HList.getAt (.cons proof vals) itVar.name htyped := by
              have := env_get_positional (.cons proof vals) itVar.name htyped
              simpa [posVar] using this
            rw [hget]
            exact HList.getAt_valid (.cons proof vals) itVar.name htyped (HList.all_cons.mpr ⟨hproof, hvals⟩)


end

end LayerBuild

end Zkc.Core
