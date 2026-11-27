module

public import Zkc.Core.Scheme.Deploy
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Meaning.Stops

@[expose] public section

/-!
Denotation, event-key, safety, validity, and statement-agreement lemmas for every `Core.Layer`
term builder in `LayerBuild`.
-/

namespace Zkc.Core

namespace LayerBuild

/-! ## Combinator denotation and event-key lemmas -/

theorem letOp1_denote {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty} {ins outs : List D.Ty}
    {τ : D.Ty} (key : Key) (o : D.Op ins [τ]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx D.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' → Var Γ' τ → Term D Γ' outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (letOp1 key o operands n hfresh rest).denote sem path env =
      (sem.op key o path (env.all operands)).bind fun vs =>
        (rest (Γ.insert n τ) (hfresh.insert τ) (hfresh.within τ) (freshVar Γ n τ)).denote sem path
          (env.insert n vs.single) := by
  change (sem.op key o path (env.all operands)).bind (fun vs =>
      (rest (Γ.insert n τ) (hfresh.insert τ) (hfresh.within τ) (freshVar Γ n τ)).denote sem path
        (env.extend (.cons n .nil) vs)) = _
  congr 1
  funext vs
  cases vs with
  | cons v restVs =>
      cases restVs
      rfl

theorem letOp2_denote {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty} {ins outs : List D.Ty}
    {τ₁ τ₂ : D.Ty} (key : Key) (o : D.Op ins [τ₁, τ₂]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx D.Ty) → FreshFrom Γ' (n + 2) → Γ.Within Γ' →
      Var Γ' τ₁ → Var Γ' τ₂ → Term D Γ' outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (letOp2 key o operands n hfresh rest).denote sem path env =
      (sem.op key o path (env.all operands)).bind fun vs =>
        match vs with
        | .cons v₁ (.cons v₂ .nil) =>
            (rest ((Γ.insert n τ₁).insert (n + 1) τ₂) ((hfresh.insert τ₁).insert τ₂)
              ((hfresh.within τ₁).trans ((hfresh.insert τ₁).within τ₂))
              ((freshVar Γ n τ₁).reindex ((hfresh.insert τ₁).within τ₂))
              (freshVar (Γ.insert n τ₁) (n + 1) τ₂)).denote sem path
              ((env.insert n v₁).insert (n + 1) v₂) := by
  unfold letOp2
  change (sem.op key o path (env.all operands)).bind (fun vs =>
      Term.denote sem _ path (env.extend (HList.cons n (HList.cons (n + 1) HList.nil)) vs)) = _
  congr 1
  funext vs
  cases vs with
  | cons v₁ restVs =>
      cases restVs with
      | cons v₂ nilVs =>
          cases nilVs
          rfl

theorem letOp1_eventKeys {D : Dialect} (isEvent : ∀ {ins res : List D.Ty}, D.Op ins res → Bool)
    {Γ : Ctx D.Ty} {ins outs : List D.Ty} {τ : D.Ty}
    (key : Key) (o : D.Op ins [τ]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx D.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' → Var Γ' τ → Term D Γ' outs) :
    Term.eventKeys isEvent (letOp1 key o operands n hfresh rest) =
      (if isEvent o then [key] else []) ++
        Term.eventKeys isEvent
          (rest (Γ.insert n τ) (hfresh.insert τ) (hfresh.within τ) (freshVar Γ n τ)) :=
  rfl

theorem letOp2_eventKeys {D : Dialect} (isEvent : ∀ {ins res : List D.Ty}, D.Op ins res → Bool)
    {Γ : Ctx D.Ty} {ins outs : List D.Ty} {τ₁ τ₂ : D.Ty}
    (key : Key) (o : D.Op ins [τ₁, τ₂]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx D.Ty) → FreshFrom Γ' (n + 2) → Γ.Within Γ' →
      Var Γ' τ₁ → Var Γ' τ₂ → Term D Γ' outs) :
    Term.eventKeys isEvent (letOp2 key o operands n hfresh rest) =
      (if isEvent o then [key] else []) ++
        Term.eventKeys isEvent
          (rest ((Γ.insert n τ₁).insert (n + 1) τ₂) ((hfresh.insert τ₁).insert τ₂)
            ((hfresh.within τ₁).trans ((hfresh.insert τ₁).within τ₂))
            ((freshVar Γ n τ₁).reindex ((hfresh.insert τ₁).within τ₂))
            (freshVar (Γ.insert n τ₁) (n + 1) τ₂)) :=
  rfl

/-! ## Environment lookup and `alone` helpers -/

theorem env_get_insert_ne {T : Type} {V : T → Type} {Γ : Ctx T}
    (env : Env V Γ) {n : Name} {σ τ : T} (v : V σ)
    (x : Var (Γ.insert n σ) τ) (hne : x.name ≠ n) :
    (env.insert n v).get x = env.get ⟨x.name, by
      have ht := x.typed; rw [Ctx.find?_insert, ite_eq_right hne] at ht; exact ht⟩ :=
  Env.insert_at_other env n v hne x.typed

theorem env_get_insert_eq {T : Type} {V : T → Type} {Γ : Ctx T}
    (env : Env V Γ) {n : Name} {τ : T} (v : V τ)
    (x : Var (Γ.insert n τ) τ) (heq : x.name = n) :
    (env.insert n v).get x = v :=
  eq_of_heq (Env.insert_at_bound env n v heq x.typed)

theorem env_get_insert2_reindex {T : Type} {V : T → Type} {Γ : Ctx T}
    (env : Env V Γ) {n : Name} (h : FreshFrom Γ n) {σ₁ σ₂ τ : T} (v₁ : V σ₁) (v₂ : V σ₂)
    (w : Γ.Within ((Γ.insert n σ₁).insert (n + 1) σ₂)) (x : Var Γ τ) :
    ((env.insert n v₁).insert (n + 1) v₂).get (x.reindex w) = env.get x :=
  (env_get_insert_reindex (env.insert n v₁) (h.insert σ₁) v₂ (x.reindex (h.within σ₁))).trans
    (env_get_insert_reindex env h v₁ x)

theorem env_get_insert3_reindex {T : Type} {V : T → Type} {Γ : Ctx T}
    (env : Env V Γ) {n : Name} (h : FreshFrom Γ n) {σ₁ σ₂ σ₃ τ : T}
    (v₁ : V σ₁) (v₂ : V σ₂) (v₃ : V σ₃)
    (w : Γ.Within (((Γ.insert n σ₁).insert (n + 1) σ₂).insert (n + 2) σ₃)) (x : Var Γ τ) :
    (((env.insert n v₁).insert (n + 1) v₂).insert (n + 2) v₃).get (x.reindex w) = env.get x :=
  (env_get_insert_reindex ((env.insert n v₁).insert (n + 1) v₂) ((h.insert σ₁).insert σ₂) v₃
    (x.reindex ((h.within σ₁).trans ((h.insert σ₁).within σ₂)))).trans
    (env_get_insert2_reindex env h v₁ v₂ _ x)

theorem env_all_reindex_insert {T : Type} {V : T → Type} {Γ : Ctx T}
    (env : Env V Γ) {n : Nat} (h : FreshFrom Γ n) {τ : T} (v : V τ) :
    ∀ {items : List T} (xs : HList (Var Γ) items),
      (env.insert n v).all (xs.reindex (h.within τ)) = env.all xs
  | [], .nil => rfl
  | _ :: _, .cons x rest => by
      show HList.cons ((env.insert n v).get (x.reindex (h.within τ)))
          ((env.insert n v).all (rest.reindex (h.within τ))) =
        HList.cons (env.get x) (env.all rest)
      rw [env_get_insert_reindex env h v x, env_all_reindex_insert env h v rest]

theorem env_extend_counting_outside {T : Type} {V : T → Type} :
    ∀ {types : List T} {Γ : Ctx T} (env : Env V Γ) (start : Nat) (vals : HList V types)
      (k : Nat) (hk : k < start ∨ start + types.length ≤ k)
      {σ : T} (hfound : (Γ.extend (Names.counting start types)).find? k = some σ),
      (env.extend (Names.counting start types) vals) k σ hfound =
        env k σ (by
          rw [Ctx.find?_extend_counting] at hfound
          have hout : ¬ (start ≤ k ∧ k < start + types.length) := by omega
          rwa [ite_eq_right hout] at hfound)
  | [], _, _, _, .nil, _, _, _, _ => rfl
  | _ :: rest, _, env, start, .cons v vs, k, hk, σ, hfound => by
      have hne : k ≠ start := by simp only [List.length_cons] at hk; omega
      have hk' : k < start + 1 ∨ (start + 1) + rest.length ≤ k := by
        simp only [List.length_cons] at hk; omega
      show ((env.insert start v).extend (Names.counting (start + 1) rest) vs) k σ hfound = _
      rw [env_extend_counting_outside (env.insert start v) (start + 1) vs k hk' hfound]
      rw [Env.insert_at_other env start v hne]

/-- Lookup element `i` from an `HList` given `types[i]? = some τ`. -/
def HList.getAt {T : Type} {V : T → Type} :
    {types : List T} → HList V types → (i : Nat) → {τ : T} → types[i]? = some τ → V τ
  | [], .nil, _, _, h => by simp at h
  | _ :: _, .cons v _, 0, _, h => (Option.some.inj h) ▸ v
  | _ :: _, .cons _ rest, i + 1, _, h => HList.getAt rest i h

theorem HList.getAt_valid {T : Type} {V : T → Type} {P : ∀ t, V t → Prop} :
    ∀ {types : List T} (vals : HList V types) (i : Nat) {τ : T} (hi : types[i]? = some τ),
      vals.All P → P τ (HList.getAt vals i hi)
  | [], .nil, _, _, hi, _ => by simp at hi
  | _ :: _, .cons v _, 0, _, hi, hv => by
      cases Option.some.inj hi
      exact hv.1
  | _ :: _, .cons _ rest, i + 1, _, hi, hv => HList.getAt_valid rest i hi hv.2

theorem env_get_extend_counting_getAt {T : Type} {V : T → Type} :
    ∀ {types : List T} {Γ : Ctx T} (env : Env V Γ) (start : Nat) (vals : HList V types)
      (i : Nat) {τ : T} (hi : types[i]? = some τ)
      (hfound : (Γ.extend (Names.counting start types)).find? (start + i) = some τ),
      (env.extend (Names.counting start types) vals).get ⟨start + i, hfound⟩ =
        HList.getAt vals i hi
  | [], _, _, _, .nil, _, _, hi, _ => by simp at hi
  | σ :: rest, Γ, env, start, .cons v vs, 0, τ, hi, hfound => by
      have hEq : σ = τ := Option.some.inj hi
      subst hEq
      have hk : start < start + 1 ∨ (start + 1) + rest.length ≤ start := .inl (by omega)
      have hfound0 : ((Γ.insert start σ).extend (Names.counting (start + 1) rest)).find? start = some σ :=
        by simpa [Ctx.extend, Names.counting] using hfound
      show ((env.insert start v).extend (Names.counting (start + 1) rest) vs) (start + 0) σ hfound = _
      have hstep := env_extend_counting_outside (env.insert start v) (start + 1) vs start hk hfound0
      simpa [HList.getAt] using hstep.trans (eq_of_heq (Env.insert_at_bound env start v rfl _))
  | σ :: rest, Γ, env, start, .cons v vs, i + 1, τ, hi, hfound => by
      have hEq : start + (i + 1) = (start + 1) + i := by omega
      have hfound' : ((Γ.insert start σ).extend (Names.counting (start + 1) rest)).find?
          ((start + 1) + i) = some τ := hEq ▸ hfound
      have ih := env_get_extend_counting_getAt (env.insert start v) (start + 1) vs i hi hfound'
      change ((env.insert start v).extend (Names.counting (start + 1) rest) vs)
          (start + (i + 1)) τ hfound = HList.getAt vs i hi
      simpa [Env.get, hEq] using ih

theorem env_get_positional {T : Type} {V : T → Type} {types : List T} (vals : HList V types)
    (i : Nat) {τ : T} (hi : types[i]? = some τ) :
    (Env.positional vals).get (posVar types i hi) = HList.getAt vals i hi := by
  have hfound : (Ctx.empty.extend (Names.counting 0 types)).find? (0 + i) = some τ := by
    rw [Nat.zero_add]
    change (Ctx.positional types).find? i = some τ
    rw [Ctx.find?_positional]
    exact hi
  have h := env_get_extend_counting_getAt (Env.empty : Env V Ctx.empty) 0 vals i hi hfound
  simpa [Env.positional, posVar, Env.get, Nat.zero_add] using h

theorem env_get_positional_0 {T : Type} {V : T → Type} {τ : T} {rest : List T}
    (v : V τ) (vs : HList V rest) :
    (Env.positional (.cons v vs)).get (posVar (τ :: rest) 0 rfl) = v := by
  simpa [HList.getAt] using env_get_positional (.cons v vs) 0 rfl

theorem env_get_positional_1 {T : Type} {V : T → Type} {τ₀ τ₁ : T} {rest : List T}
    (v₀ : V τ₀) (v₁ : V τ₁) (vs : HList V rest) :
    (Env.positional (.cons v₀ (.cons v₁ vs))).get (posVar (τ₀ :: τ₁ :: rest) 1 rfl) = v₁ := by
  simpa [HList.getAt] using env_get_positional (.cons v₀ (.cons v₁ vs)) 1 rfl

theorem env_get_positional_2 {T : Type} {V : T → Type} {τ₀ τ₁ τ₂ : T} {rest : List T}
    (v₀ : V τ₀) (v₁ : V τ₁) (v₂ : V τ₂) (vs : HList V rest) :
    (Env.positional (.cons v₀ (.cons v₁ (.cons v₂ vs)))).get
      (posVar (τ₀ :: τ₁ :: τ₂ :: rest) 2 rfl) = v₂ := by
  simpa [HList.getAt] using env_get_positional (.cons v₀ (.cons v₁ (.cons v₂ vs))) 2 rfl

theorem env_get_positional_eq {T : Type} {V : T → Type} {types : List T} (vals : HList V types)
    (i : Nat) {τ : T} (x : Var (Ctx.positional types) τ) (hx : x.name = i)
    (hi : types[i]? = some τ) :
    (Env.positional vals).get x = HList.getAt vals i hi := by
  cases x with
  | mk name typed =>
      dsimp only at hx
      subst hx
      exact env_get_positional vals name hi

theorem env_get_positional_alone_0 {V : Vocabulary} (M : Model V) (r : Role)
    {τ : V.Ty} {rest : List V.Ty} (v : M.Val τ) (vs : HList M.Val rest)
    (x : Var (Ctx.positional (alone r (τ :: rest))) ⟨τ, [r]⟩) (hx : x.name = 0) :
    (Env.positional (aloneIn M r (.cons v vs))).get x = hide M r ⟨τ, [r]⟩ v :=
  env_get_positional_eq (aloneIn M r (.cons v vs)) 0 x hx rfl

theorem env_get_positional_alone_1 {V : Vocabulary} (M : Model V) (r : Role)
    {τ₀ τ₁ : V.Ty} {rest : List V.Ty} (v₀ : M.Val τ₀) (v₁ : M.Val τ₁) (vs : HList M.Val rest)
    (x : Var (Ctx.positional (alone r (τ₀ :: τ₁ :: rest))) ⟨τ₁, [r]⟩) (hx : x.name = 1) :
    (Env.positional (aloneIn M r (.cons v₀ (.cons v₁ vs)))).get x = hide M r ⟨τ₁, [r]⟩ v₁ :=
  env_get_positional_eq (aloneIn M r (.cons v₀ (.cons v₁ vs))) 1 x hx rfl

section
variable {V : Vocabulary} (M : Model V)

theorem aloneOut_aloneIn (r : Role) :
    ∀ {tys : List V.Ty} (vals : HList M.Val tys), aloneOut M r (aloneIn M r vals) = vals
  | [], .nil => rfl
  | τ :: _, .cons v rest => by
      show HList.cons (reveal M (a := ⟨τ, [r]⟩) (List.mem_singleton_self r) (hide M r ⟨τ, [r]⟩ v))
          (aloneOut M r (aloneIn M r rest)) = HList.cons v rest
      rw [reveal_hide, aloneOut_aloneIn r rest]

theorem hideAll_located_alone (r : Role) :
    ∀ {tys : List V.Ty} (vals : HList M.Val tys),
      hideAll M r (HList.located M [r] vals) = aloneIn M r vals
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (HList.cons _) (hideAll_located_alone r rest)

private theorem cast_hlist_cons {α : Type} {F : α → Type} {as bs : List α} (h : as = bs)
    {t : α} (x : F t) (xs : HList F as) :
    cast (congrArg (HList F) (congrArg (List.cons t) h)) (HList.cons x xs) =
      HList.cons x (cast (congrArg (HList F) h) xs) := by
  subst h; rfl

theorem computeArgs_alone (r : Role) :
    ∀ {tys : List V.Ty} (vals : HList M.Val tys),
      computeArgs M (alone_map_ty r tys)
        (revealAll M (alone_mem_holders r tys) (aloneIn M r vals)) = vals
  | [], .nil => rfl
  | τ :: ts, .cons v rest => by
      have ih := computeArgs_alone r rest
      unfold computeArgs at ih ⊢
      change cast (congrArg (HList M.Val) (congrArg (List.cons τ) (alone_map_ty r ts)))
        (HList.cons (reveal M (List.mem_singleton_self r) (hide M r ⟨τ, [r]⟩ v))
          (HList.ofLocated M (revealAll M (alone_mem_holders r ts) (aloneIn M r rest)))) =
        HList.cons v rest
      rw [reveal_hide, cast_hlist_cons (alone_map_ty r ts), ih]

theorem aloneIn_aloneOut (r : Role) :
    ∀ {tys : List V.Ty} (vals : HList (RV M r) (alone r tys)),
      aloneIn M r (aloneOut M r vals) = vals
  | [], .nil => rfl
  | τ :: _, .cons v rest => by
      show HList.cons (hide M r ⟨τ, [r]⟩ (reveal M (a := ⟨τ, [r]⟩) (List.mem_singleton_self r) v))
          (aloneIn M r (aloneOut M r rest)) = HList.cons v rest
      have hhr : hide M r ⟨τ, [r]⟩ (reveal M (a := ⟨τ, [r]⟩) (List.mem_singleton_self r) v) = v := by
        simp [hide, reveal]
      rw [hhr, aloneIn_aloneOut r rest]
      rfl

theorem aloneOut_all_nil (r : Role) {Γ : Ctx (LTy V)} (env : Env (RV M r) Γ) :
    aloneOut M r (types := []) (env.all .nil) = HList.nil :=
  rfl

theorem aloneOut_all_cons (r : Role) {Γ : Ctx (LTy V)} (env : Env (RV M r) Γ)
    {τ : V.Ty} {rest : List V.Ty} (x : Var Γ ⟨τ, [r]⟩) (xs : HList (Var Γ) (alone r rest)) :
    aloneOut M r (types := τ :: rest) (env.all (.cons x xs)) =
      HList.cons (reveal M (a := ⟨τ, [r]⟩) (List.mem_singleton_self r) (env.get x))
        (aloneOut M r (env.all xs)) :=
  rfl

theorem computeAlone_denote {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {ins outs : List V.Ty} (key : Key)
    (o : LocalOp V hs.fns ins outs) (path : List Frame) (vals : HList M.Val ins) :
    (roleSem M r fnTable rTable).op key (computeAlone r o) path (aloneIn M r vals) =
      (liftLocal id (localOp M fnTable o vals)).map (aloneIn M r) := by
  show (liftLocal id (localOp M fnTable o
      (computeArgs M (alone_map_ty r ins)
        (revealAll M (alone_mem_holders r ins) (aloneIn M r vals))))).map
      (fun os => hideAll M r (HList.located M [r] os)) = _
  rw [computeArgs_alone M r vals]
  congr 1
  funext os
  exact hideAll_located_alone M r os

theorem letOp1_computeAlone_denote {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {ins : List V.Ty} {τ : V.Ty}
    {outs : List (LTy V)} (key : Key) (o : LocalOp V hs.fns ins [τ])
    (operands : HList (Var Γ) (alone r ins)) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ) :
    (letOp1 key (computeAlone r o) operands n hfresh rest).denote (roleSem M r fnTable rTable)
        path env =
      (liftLocal id (localOp M fnTable o (aloneOut M r (env.all operands)))).bind fun vs =>
        (rest (Γ.insert n ⟨τ, [r]⟩) (hfresh.insert ⟨τ, [r]⟩) (hfresh.within ⟨τ, [r]⟩)
          (freshVar Γ n ⟨τ, [r]⟩)).denote (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, [r]⟩ vs.single)) := by
  have hstep : (letOp1 key (computeAlone r o) operands n hfresh rest).denote
      (roleSem M r fnTable rTable) path env =
      ((roleSem M r fnTable rTable).op key (computeAlone r o) path
        (aloneIn M r (aloneOut M r (env.all operands)))).bind fun vs =>
        (rest (Γ.insert n ⟨τ, [r]⟩) (hfresh.insert ⟨τ, [r]⟩) (hfresh.within ⟨τ, [r]⟩)
          (freshVar Γ n ⟨τ, [r]⟩)).denote (roleSem M r fnTable rTable) path
          (env.insert n vs.single) := by
    rw [aloneIn_aloneOut M r (env.all operands)]
    exact letOp1_denote (roleSem M r fnTable rTable) key (computeAlone r o) operands n hfresh rest
      path env
  rw [hstep, computeAlone_denote, Process.bind_map]
  congr 1; funext vs
  cases vs with
  | cons v vNil =>
      cases vNil
      rfl

theorem letOp2_computeAlone_denote {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {ins : List V.Ty} {τ₁ τ₂ : V.Ty}
    {outs : List (LTy V)} (key : Key) (o : LocalOp V hs.fns ins [τ₁, τ₂])
    (operands : HList (Var Γ) (alone r ins)) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 2) → Γ.Within Γ' →
      Var Γ' ⟨τ₁, [r]⟩ → Var Γ' ⟨τ₂, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ) :
    (letOp2 key (computeAlone r o) operands n hfresh rest).denote (roleSem M r fnTable rTable)
        path env =
      (liftLocal id (localOp M fnTable o (aloneOut M r (env.all operands)))).bind fun vs =>
        match vs with
        | .cons v₁ (.cons v₂ .nil) =>
            (rest ((Γ.insert n ⟨τ₁, [r]⟩).insert (n + 1) ⟨τ₂, [r]⟩)
              ((hfresh.insert ⟨τ₁, [r]⟩).insert ⟨τ₂, [r]⟩)
              ((hfresh.within ⟨τ₁, [r]⟩).trans ((hfresh.insert ⟨τ₁, [r]⟩).within ⟨τ₂, [r]⟩))
              ((freshVar Γ n ⟨τ₁, [r]⟩).reindex ((hfresh.insert ⟨τ₁, [r]⟩).within ⟨τ₂, [r]⟩))
              (freshVar (Γ.insert n ⟨τ₁, [r]⟩) (n + 1) ⟨τ₂, [r]⟩)).denote
              (roleSem M r fnTable rTable) path
              ((env.insert n (hide M r ⟨τ₁, [r]⟩ v₁)).insert (n + 1) (hide M r ⟨τ₂, [r]⟩ v₂)) := by
  unfold letOp2
  change ((roleSem M r fnTable rTable).op key (computeAlone r o) path (env.all operands)).bind
      (fun vs => Term.denote (roleSem M r fnTable rTable) _ path
        (env.extend (.cons n (.cons (n + 1) .nil)) vs)) = _
  rw [← aloneIn_aloneOut M r (env.all operands), computeAlone_denote, Process.bind_map,
    aloneOut_aloneIn]
  apply congrArg (Process.bind _)
  funext vs
  cases vs with
  | cons v₁ vs1 =>
      cases vs1 with
      | cons v₂ vs2 =>
          cases vs2
          rfl

theorem letOp1_computeAlone_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {ins : List V.Ty} {τ : V.Ty}
    {outs : List (LTy V)} (key : Key) (o : LocalOp V hs.fns ins [τ])
    (operands : HList (Var Γ) (alone r ins)) (vals : HList M.Val ins)
    (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hvals : env.all operands = aloneIn M r vals) :
    (letOp1 key (computeAlone r o) operands n hfresh rest).denote (roleSem M r fnTable rTable)
        path env =
      (liftLocal id (localOp M fnTable o vals)).bind fun vs =>
        (rest (Γ.insert n ⟨τ, [r]⟩) (hfresh.insert ⟨τ, [r]⟩) (hfresh.within ⟨τ, [r]⟩)
          (freshVar Γ n ⟨τ, [r]⟩)).denote (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, [r]⟩ vs.single)) := by
  rw [letOp1_computeAlone_denote, hvals, aloneOut_aloneIn]

theorem letOp2_computeAlone_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {ins : List V.Ty} {τ₁ τ₂ : V.Ty}
    {outs : List (LTy V)} (key : Key) (o : LocalOp V hs.fns ins [τ₁, τ₂])
    (operands : HList (Var Γ) (alone r ins)) (vals : HList M.Val ins)
    (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 2) → Γ.Within Γ' →
      Var Γ' ⟨τ₁, [r]⟩ → Var Γ' ⟨τ₂, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hvals : env.all operands = aloneIn M r vals) :
    (letOp2 key (computeAlone r o) operands n hfresh rest).denote (roleSem M r fnTable rTable)
        path env =
      (liftLocal id (localOp M fnTable o vals)).bind fun vs =>
        match vs with
        | .cons w₁ (.cons w₂ .nil) =>
            (rest ((Γ.insert n ⟨τ₁, [r]⟩).insert (n + 1) ⟨τ₂, [r]⟩)
              ((hfresh.insert ⟨τ₁, [r]⟩).insert ⟨τ₂, [r]⟩)
              ((hfresh.within ⟨τ₁, [r]⟩).trans ((hfresh.insert ⟨τ₁, [r]⟩).within ⟨τ₂, [r]⟩))
              ((freshVar Γ n ⟨τ₁, [r]⟩).reindex ((hfresh.insert ⟨τ₁, [r]⟩).within ⟨τ₂, [r]⟩))
              (freshVar (Γ.insert n ⟨τ₁, [r]⟩) (n + 1) ⟨τ₂, [r]⟩)).denote
              (roleSem M r fnTable rTable) path
              ((env.insert n (hide M r ⟨τ₁, [r]⟩ w₁)).insert (n + 1) (hide M r ⟨τ₂, [r]⟩ w₂)) := by
  rw [letOp2_computeAlone_denote, hvals, aloneOut_aloneIn]

theorem letOp1_computeAlone0_denote {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {τ : V.Ty} {outs : List (LTy V)}
    (key : Key) (o : LocalOp V hs.fns [] [τ]) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ) :
    (letOp1 key (computeAlone r o) .nil n hfresh rest).denote (roleSem M r fnTable rTable)
        path env =
      (liftLocal id (localOp M fnTable o .nil)).bind fun vs =>
        (rest (Γ.insert n ⟨τ, [r]⟩) (hfresh.insert ⟨τ, [r]⟩) (hfresh.within ⟨τ, [r]⟩)
          (freshVar Γ n ⟨τ, [r]⟩)).denote (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, [r]⟩ vs.single)) :=
  letOp1_computeAlone_eq M r fnTable rTable key o .nil .nil n hfresh rest path env rfl

theorem letOp1_computeAlone1_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {τ₁ τ : V.Ty} {outs : List (LTy V)}
    (key : Key) (o : LocalOp V hs.fns [τ₁] [τ]) (x₁ : Var Γ ⟨τ₁, [r]⟩) (v₁ : M.Val τ₁)
    (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hv₁ : env.get x₁ = hide M r ⟨τ₁, [r]⟩ v₁) :
    (letOp1 key (computeAlone r o) (.cons x₁ .nil) n hfresh rest).denote
        (roleSem M r fnTable rTable) path env =
      (liftLocal id (localOp M fnTable o (.cons v₁ .nil))).bind fun vs =>
        (rest (Γ.insert n ⟨τ, [r]⟩) (hfresh.insert ⟨τ, [r]⟩) (hfresh.within ⟨τ, [r]⟩)
          (freshVar Γ n ⟨τ, [r]⟩)).denote (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, [r]⟩ vs.single)) := by
  apply letOp1_computeAlone_eq M r fnTable rTable key o (.cons x₁ .nil) (.cons v₁ .nil)
    n hfresh rest path env
  show HList.cons (env.get x₁) .nil = HList.cons (hide M r ⟨τ₁, [r]⟩ v₁) .nil
  rw [hv₁]

theorem letOp1_computeAlone2_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {τ₁ τ₂ τ : V.Ty} {outs : List (LTy V)}
    (key : Key) (o : LocalOp V hs.fns [τ₁, τ₂] [τ])
    (x₁ : Var Γ ⟨τ₁, [r]⟩) (x₂ : Var Γ ⟨τ₂, [r]⟩) (v₁ : M.Val τ₁) (v₂ : M.Val τ₂)
    (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hv₁ : env.get x₁ = hide M r ⟨τ₁, [r]⟩ v₁) (hv₂ : env.get x₂ = hide M r ⟨τ₂, [r]⟩ v₂) :
    (letOp1 key (computeAlone r o) (.cons x₁ (.cons x₂ .nil)) n hfresh rest).denote
        (roleSem M r fnTable rTable) path env =
      (liftLocal id (localOp M fnTable o (.cons v₁ (.cons v₂ .nil)))).bind fun vs =>
        (rest (Γ.insert n ⟨τ, [r]⟩) (hfresh.insert ⟨τ, [r]⟩) (hfresh.within ⟨τ, [r]⟩)
          (freshVar Γ n ⟨τ, [r]⟩)).denote (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, [r]⟩ vs.single)) := by
  apply letOp1_computeAlone_eq M r fnTable rTable key o (.cons x₁ (.cons x₂ .nil))
    (.cons v₁ (.cons v₂ .nil)) n hfresh rest path env
  show HList.cons (env.get x₁) (.cons (env.get x₂) .nil) =
    HList.cons (hide M r ⟨τ₁, [r]⟩ v₁) (.cons (hide M r ⟨τ₂, [r]⟩ v₂) .nil)
  rw [hv₁, hv₂]

theorem letOp1_computeAlone3_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {τ₁ τ₂ τ₃ τ : V.Ty} {outs : List (LTy V)}
    (key : Key) (o : LocalOp V hs.fns [τ₁, τ₂, τ₃] [τ])
    (x₁ : Var Γ ⟨τ₁, [r]⟩) (x₂ : Var Γ ⟨τ₂, [r]⟩) (x₃ : Var Γ ⟨τ₃, [r]⟩)
    (v₁ : M.Val τ₁) (v₂ : M.Val τ₂) (v₃ : M.Val τ₃)
    (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hv₁ : env.get x₁ = hide M r ⟨τ₁, [r]⟩ v₁)
    (hv₂ : env.get x₂ = hide M r ⟨τ₂, [r]⟩ v₂)
    (hv₃ : env.get x₃ = hide M r ⟨τ₃, [r]⟩ v₃) :
    (letOp1 key (computeAlone r o) (.cons x₁ (.cons x₂ (.cons x₃ .nil))) n hfresh rest).denote
        (roleSem M r fnTable rTable) path env =
      (liftLocal id (localOp M fnTable o (.cons v₁ (.cons v₂ (.cons v₃ .nil))))).bind fun vs =>
        (rest (Γ.insert n ⟨τ, [r]⟩) (hfresh.insert ⟨τ, [r]⟩) (hfresh.within ⟨τ, [r]⟩)
          (freshVar Γ n ⟨τ, [r]⟩)).denote (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, [r]⟩ vs.single)) := by
  apply letOp1_computeAlone_eq M r fnTable rTable key o
    (.cons x₁ (.cons x₂ (.cons x₃ .nil))) (.cons v₁ (.cons v₂ (.cons v₃ .nil)))
    n hfresh rest path env
  show HList.cons (env.get x₁) (.cons (env.get x₂) (.cons (env.get x₃) .nil)) =
    HList.cons (hide M r ⟨τ₁, [r]⟩ v₁) (.cons (hide M r ⟨τ₂, [r]⟩ v₂) (.cons (hide M r ⟨τ₃, [r]⟩ v₃) .nil))
  rw [hv₁, hv₂, hv₃]

theorem letOp2_computeAlone2_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {ι₁ ι₂ τ₁ τ₂ : V.Ty} {outs : List (LTy V)}
    (key : Key) (o : LocalOp V hs.fns [ι₁, ι₂] [τ₁, τ₂])
    (x₁ : Var Γ ⟨ι₁, [r]⟩) (x₂ : Var Γ ⟨ι₂, [r]⟩) (v₁ : M.Val ι₁) (v₂ : M.Val ι₂)
    (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 2) → Γ.Within Γ' →
      Var Γ' ⟨τ₁, [r]⟩ → Var Γ' ⟨τ₂, [r]⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hv₁ : env.get x₁ = hide M r ⟨ι₁, [r]⟩ v₁) (hv₂ : env.get x₂ = hide M r ⟨ι₂, [r]⟩ v₂) :
    (letOp2 key (computeAlone r o) (.cons x₁ (.cons x₂ .nil)) n hfresh rest).denote
        (roleSem M r fnTable rTable) path env =
      (liftLocal id (localOp M fnTable o (.cons v₁ (.cons v₂ .nil)))).bind fun vs =>
        match vs with
        | .cons w₁ (.cons w₂ .nil) =>
            (rest ((Γ.insert n ⟨τ₁, [r]⟩).insert (n + 1) ⟨τ₂, [r]⟩)
              ((hfresh.insert ⟨τ₁, [r]⟩).insert ⟨τ₂, [r]⟩)
              ((hfresh.within ⟨τ₁, [r]⟩).trans ((hfresh.insert ⟨τ₁, [r]⟩).within ⟨τ₂, [r]⟩))
              ((freshVar Γ n ⟨τ₁, [r]⟩).reindex ((hfresh.insert ⟨τ₁, [r]⟩).within ⟨τ₂, [r]⟩))
              (freshVar (Γ.insert n ⟨τ₁, [r]⟩) (n + 1) ⟨τ₂, [r]⟩)).denote
              (roleSem M r fnTable rTable) path
              ((env.insert n (hide M r ⟨τ₁, [r]⟩ w₁)).insert (n + 1) (hide M r ⟨τ₂, [r]⟩ w₂)) := by
  apply letOp2_computeAlone_eq M r fnTable rTable key o (.cons x₁ (.cons x₂ .nil))
    (.cons v₁ (.cons v₂ .nil)) n hfresh rest path env
  show HList.cons (env.get x₁) (.cons (env.get x₂) .nil) =
    HList.cons (hide M r ⟨ι₁, [r]⟩ v₁) (.cons (hide M r ⟨ι₂, [r]⟩ v₂) .nil)
  rw [hv₁, hv₂]

theorem letOp1_give_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {τ : V.Ty} {H : Holders}
    {outs : List (LTy V)} (key : Key) (kind : FlowKind) (getters : List Role) (hIn : r ∈ H)
    (x : Var Γ ⟨τ, H⟩) (v : M.Val τ) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, Holders.ofList (getters ++ H)⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ) (hx : env.get x = hide M r ⟨τ, H⟩ v) :
    (letOp1 (D := roleDialect V hs r) key (RoleOp.give kind getters hIn)
        (.cons x .nil) n hfresh rest).denote (roleSem M r fnTable rTable) path env =
      .call (ROp.give kind getters ⟨path, key⟩ τ v) fun _ =>
        (rest (Γ.insert n ⟨τ, Holders.ofList (getters ++ H)⟩)
          (hfresh.insert ⟨τ, Holders.ofList (getters ++ H)⟩)
          (hfresh.within ⟨τ, Holders.ofList (getters ++ H)⟩)
          (freshVar Γ n ⟨τ, Holders.ofList (getters ++ H)⟩)).denote
          (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ v)) := by
  rw [letOp1_denote]
  change (Process.call (S := RSig M) (ROp.give kind getters ⟨path, key⟩ τ
      (reveal M (a := ⟨τ, H⟩) hIn (env.get x))) fun _ =>
      Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩
        (reveal M (a := ⟨τ, H⟩) hIn (env.get x))) HList.nil)).bind _ = _
  rw [hx, reveal_hide]
  rfl

theorem letOp1_keep_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {τ : V.Ty} {H R : Holders}
    {outs : List (LTy V)} (key : Key) (same : r ∈ H ↔ r ∈ R)
    (x : Var Γ ⟨τ, H⟩) (v : M.Val τ) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, R⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ) (hx : env.get x = hide M r ⟨τ, H⟩ v) :
    (letOp1 (D := roleDialect V hs r) key (RoleOp.keep R same)
        (.cons x .nil) n hfresh rest).denote (roleSem M r fnTable rTable) path env =
      (rest (Γ.insert n ⟨τ, R⟩) (hfresh.insert ⟨τ, R⟩) (hfresh.within ⟨τ, R⟩)
        (freshVar Γ n ⟨τ, R⟩)).denote (roleSem M r fnTable rTable) path
        (env.insert n (hide M r ⟨τ, R⟩ v)) := by
  rw [letOp1_denote]
  change (Process.done (HList.cons (carry M same (env.get x)) HList.nil)).bind _ = _
  rw [hx, carry_hide]
  rfl

theorem letOp1_request1_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {ι τ : V.Ty} {outs : List (LTy V)}
    (key serviceKey : Key) (hheld : ∀ a ∈ [LTy.mk ι [r]], r ∈ a.holders)
    (x : Var Γ ⟨ι, [r]⟩) (v : M.Val ι) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' ⟨τ, Holders.ofList (r :: [])⟩ → Term (roleDialect V hs r) Γ' outs)
    (path : List Frame) (env : Env (RV M r) Γ) (hx : env.get x = hide M r ⟨ι, [r]⟩ v) :
    (letOp1 (D := roleDialect V hs r) key
        (RoleOp.own (.request serviceKey) [] [LTy.mk ι [r]] τ rfl hheld) (.cons x .nil)
        n hfresh rest).denote (roleSem M r fnTable rTable) path env =
      .call (ROp.own (.request serviceKey) [] ⟨path, key⟩ [ι] (.cons v .nil) τ) fun coin =>
        (rest (Γ.insert n ⟨τ, Holders.ofList (r :: [])⟩)
          (hfresh.insert ⟨τ, Holders.ofList (r :: [])⟩)
          (hfresh.within ⟨τ, Holders.ofList (r :: [])⟩)
          (freshVar Γ n ⟨τ, Holders.ofList (r :: [])⟩)).denote
          (roleSem M r fnTable rTable) path
          (env.insert n (hide M r ⟨τ, Holders.ofList (r :: [])⟩ coin)) := by
  rw [letOp1_denote]
  change (Process.call (S := RSig M) (ROp.own (.request serviceKey) [] ⟨path, key⟩ [ι]
      (HList.cons (reveal M (hheld (LTy.mk ι [r]) List.mem_cons_self) (env.get x)) HList.nil) τ) fun coin =>
      Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (r :: [])⟩ coin) HList.nil)).bind _ = _
  rw [hx, reveal_hide]
  rfl

theorem term_denote_guard_eq {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {outs : List (LTy V)}
    (key : Key) (c : Var Γ ⟨.bool, [r]⟩)
    (ok : (roleDialect V hs r).Condition [r] ⟨.bool, [r]⟩) (why : Reason)
    (rest : Term (roleDialect V hs r) Γ outs) (path : List Frame) (env : Env (RV M r) Γ)
    (b : Bool) (hc : env.get c = hide M r ⟨.bool, [r]⟩ b) :
    (Term.guard key [r] c ok why rest).denote (roleSem M r fnTable rTable) path env =
      bif b then rest.denote (roleSem M r fnTable rTable) path env
      else .halt (.declared why ⟨path, key⟩) := by
  rw [Term.denote_guard]
  have hholds : (roleSem M r fnTable rTable).holds ok (env.get c) = b := by
    rw [hc]
    simp only [asBool, reveal_hide, cast_eq]
  rw [hholds]

theorem term_denote_ret1 {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {a : LTy V}
    (x : Var Γ a) (path : List Frame) (env : Env (RV M r) Γ) (v : RV M r a)
    (hx : env.get x = v) :
    (Term.ret (D := roleDialect V hs r) (.cons x .nil)).denote
        (roleSem M r fnTable rTable) path env =
      .done (HList.cons v HList.nil) := by
  rw [Term.denote_ret]
  show Process.done (HList.cons (env.get x) HList.nil) = .done (HList.cons v HList.nil)
  rw [hx]

theorem term_denote_ret2 {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {a₁ a₂ : LTy V}
    (x₁ : Var Γ a₁) (x₂ : Var Γ a₂) (path : List Frame) (env : Env (RV M r) Γ)
    (v₁ : RV M r a₁) (v₂ : RV M r a₂)
    (hx₁ : env.get x₁ = v₁) (hx₂ : env.get x₂ = v₂) :
    (Term.ret (D := roleDialect V hs r) (.cons x₁ (.cons x₂ .nil))).denote
        (roleSem M r fnTable rTable) path env =
      .done (HList.cons v₁ (HList.cons v₂ HList.nil)) := by
  rw [Term.denote_ret]
  show Process.done (HList.cons (env.get x₁) (HList.cons (env.get x₂) HList.nil)) =
    .done (HList.cons v₁ (HList.cons v₂ HList.nil))
  rw [hx₁, hx₂]

theorem liftLocal_bind (S : Sig) {H A B : Type} (f : Stop → H) (p : Local A) (k : A → Local B) :
    liftLocal (S := S) f (p.bind k) =
      (liftLocal (S := S) f p).bind fun a => liftLocal (S := S) f (k a) := by
  cases p with
  | done a => rfl
  | halt why => rfl
  | call op _ => cases op

theorem liftLocal_map (S : Sig) {H A B : Type} (f : Stop → H) (g : A → B) (p : Local A) :
    liftLocal (S := S) f (p.map g) = (liftLocal (S := S) f p).map g := by
  cases p with
  | done a => rfl
  | halt why => rfl
  | call op _ => cases op

theorem liftLocal_done {S : Sig} {H A : Type} (f : Stop → H) (a : A) :
    liftLocal (S := S) f (.done a) = .done a :=
  rfl

theorem liftLocal_halt {S : Sig} {H A : Type} (f : Stop → H) (why : Stop) :
    liftLocal (S := S) (A := A) f (.halt why) = .halt (f why) :=
  rfl

theorem localSem_op {fns : List (FnHeader V)} (fnTable : FnTable M fns) {ins res : List V.Ty}
    (key : Key) (o : LocalOp V fns ins res) (path : List Frame) (args : HList M.Val ins) :
    (localSem M fns fnTable).op key o path args = localOp M fnTable o args :=
  rfl

theorem localSem_op_literal {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    (key : Key) (τ : V.Ty) (data : List Nat) (reads : V.Reads τ data)
    (path : List Frame) (args : HList M.Val []) :
    (localSem M fns fnTable).op key (.literal τ data reads) path args =
      .done (.cons (Ty.readLiteral M τ data reads) .nil) :=
  rfl

theorem localSem_op_natLiteral {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    (key : Key) (n : Nat) (path : List Frame) (args : HList M.Val []) :
    (localSem M fns fnTable).op key (.literal .nat [n] rfl) path args =
      .done (.cons (a := Ty.nat) n .nil) :=
  rfl

theorem localSem_op_owned {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {ins res : List V.Ty} (key : Key) (o : OwnedOp V ins res)
    (path : List Frame) (args : HList M.Val ins) :
    (localSem M fns fnTable).op key (.owned o) path args = ownedOp M o args :=
  rfl

theorem localSem_holds {fns : List (FnHeader V)} (fnTable : FnTable M fns) (b : Bool) :
    (localSem M fns fnTable).holds (w := ()) (t := .bool) rfl b = b :=
  rfl

theorem localSem_stop {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    (why : Reason) (at_ : Occurrence) :
    (localSem M fns fnTable).stop () why at_ = .declared why at_ :=
  rfl

theorem ownedOp_getTuple (items : Tys V.TypeKey) {τ : V.Ty} (pos : Member items.toList τ)
    (free : Tys.anyLinear V items = false) (v : items.Val M.toCarriers) :
    ownedOp M (.getTuple items pos free) (.cons v .nil) =
      .done (.cons (Tys.getAt M items pos v) .nil) :=
  rfl

theorem ownedOp_makeTuple (items : Tys V.TypeKey) (vs : HList M.Val items.toList) :
    ownedOp M (.makeTuple items) vs = .done (.cons (Tys.ofHList M items vs) .nil) :=
  rfl

theorem ownedOp_seqLength (item : V.Ty) (size : Option Nat) (free : Ty.isLinear V item = false)
    (xs : List (M.Val item)) :
    ownedOp M (.seqLength item size free) (.cons xs .nil) = .done (.cons xs.length .nil) :=
  rfl

theorem ownedOp_natEqual (a b : Nat) :
    ownedOp M .natEqual (.cons a (.cons b .nil)) = .done (.cons (Nat.beq a b) .nil) :=
  rfl

theorem ownedOp_seqConcat (item : V.Ty) (s₁ s₂ : Option Nat) (xs ys : List (M.Val item)) :
    ownedOp M (.seqConcat item s₁ s₂) (.cons xs (.cons ys .nil)) =
      .done (.cons (xs ++ ys) .nil) :=
  rfl

theorem ownedOp_takeTuple (items : Tys V.TypeKey) (v : items.Val M.toCarriers) :
    ownedOp M (.takeTuple items) (.cons v .nil) = .done (Tys.toHList M items v) :=
  rfl

/-! ## `TypedFnRef` and `SafeFnRef` evaluation and safety -/

/-- Evaluate a `TypedFnRef` directly in a function table. -/
def TypedFnRef.eval {fns : List (FnHeader V)} (fnTable : FnTable M fns) {ins outs : List V.Ty}
    (ref : TypedFnRef V fns ins outs) (args : HList M.Val ins) : Local (HList M.Val outs) :=
  localOp M fnTable (callLocal ref) args

/-- Evaluate a `SafeFnRef` directly in a function table. -/
def SafeFnRef.eval {fns : List (FnHeader V)} (fnTable : FnTable M fns) {ins outs : List V.Ty}
    (ref : SafeFnRef V fns ins outs) (args : HList M.Val ins) : Local (HList M.Val outs) :=
  localOp M fnTable (callLocalSafe ref) args

theorem TypedFnRef.eval_eq_fnTable {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {ins outs : List V.Ty} (ref : TypedFnRef V fns ins outs) (args : HList M.Val ins) :
    ref.eval M fnTable args =
      cast (congrArg (fun os => Local (HList M.Val os)) ref.outsEq)
        (fnTable ref.hdr ref.member (cast (congrArg (HList M.Val) ref.insEq.symm) args)) := by
  rcases ref with ⟨hdr, member, hIn, hOut, uncond, canStopFalse⟩
  cases hIn
  cases hOut
  rfl

theorem SafeFnRef.eval_eq_fnTable {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {ins outs : List V.Ty} (ref : SafeFnRef V fns ins outs) (args : HList M.Val ins) :
    ref.eval M fnTable args =
      cast (congrArg (fun os => Local (HList M.Val os)) ref.outsEq)
        (fnTable ref.hdr ref.member (cast (congrArg (HList M.Val) ref.insEq.symm) args)) := by
  rcases ref with ⟨hdr, member, hIn, hOut, uncond⟩
  cases hIn
  cases hOut
  rfl

unseal fnMeaning in
theorem TypedFnRef.eval_done (a : Admitted V) {ins outs : List V.Ty}
    (ref : TypedFnRef V a.program.headers.fns ins outs) (args : HList M.Val ins)
    (hvalid : args.All M.Valid) :
    ∃ outsVal, ref.eval M (Defs.fnTable M a.program.defs) args = .done outsVal ∧
      outsVal.All M.Valid := by
  rcases ref with ⟨hdr, member, hIn, hOut, uncond, canStopFalse⟩
  cases hIn
  cases hOut
  have hreq : FnHeader.Required M (Defs.fnTable M a.program.defs) hdr args := by
    intro r hr; rw [uncond] at hr; cases hr
  have hnoStop : (fnMeaning M a.program member args).Stops (fun _ => False) :=
    headersSayWhoStops a M hdr member args hvalid hreq canStopFalse
  cases hrun : Defs.fnTable M a.program.defs hdr member args with
  | done outsVal =>
      have hv : outsVal.All M.Valid :=
        functionsKeepValidity a M hdr member args outsVal hvalid hrun
      exact ⟨outsVal, hrun, hv⟩
  | halt why =>
      change (Defs.fnTable M a.program.defs hdr member args).Stops (fun _ => False) at hnoStop
      rw [hrun] at hnoStop
      exact False.elim hnoStop
  | call op _ => cases op

unseal fnMeaning in
theorem SafeFnRef.eval_safe (a : Admitted V) {ins outs : List V.Ty}
    (ref : SafeFnRef V a.program.headers.fns ins outs) (args : HList M.Val ins)
    (hvalid : args.All M.Valid) :
    (ref.eval M (Defs.fnTable M a.program.defs) args).Every (fun _ _ => True)
      (fun outsVal => outsVal.All M.Valid) (· ≠ .undefined) := by
  rcases ref with ⟨hdr, member, hIn, hOut, uncond⟩
  cases hIn
  cases hOut
  have hreq : FnHeader.Required M (Defs.fnTable M a.program.defs) hdr args := by
    intro r hr; rw [uncond] at hr; cases hr
  have hsafe := functionsSafe a M hdr member args hvalid hreq
  change (Defs.fnTable M a.program.defs hdr member args).Every _ _ _
  cases hrun : Defs.fnTable M a.program.defs hdr member args with
  | done outsVal =>
      exact functionsKeepValidity a M hdr member args outsVal hvalid hrun
  | halt why =>
      change (Defs.fnTable M a.program.defs hdr member args).Stops (· ≠ .undefined) at hsafe
      rw [hrun] at hsafe
      exact hsafe
  | call op _ => cases op

/-! ## Denotation lemmas for `start`, `again`, `finish` builders -/

theorem restoreAgain_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) (state : V.Ty)
    (i : Nat) (entry stop : M.Val state) :
    (restoreAgain (V := V) (fns := fns) state).denote (localSem M fns fnTable) []
      (Env.positional (.cons i (.cons entry (.cons stop .nil)))) = .done (.cons entry .nil) := by
  unfold restoreAgain
  rw [Term.denote_ret]
  show Process.done (HList.cons ((Env.positional _).get (posVar _ 1 rfl)) .nil) = _
  rw [env_get_positional_1]

theorem attemptNumAgain_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    (i entry stop : Nat) :
    (attemptNumAgain (V := V) (fns := fns)).denote (localSem M fns fnTable) []
      (Env.positional (.cons i (.cons entry (.cons stop .nil)))) = .done (.cons i .nil) := by
  unfold attemptNumAgain
  rw [Term.denote_ret]
  show Process.done (HList.cons ((Env.positional _).get (posVar _ 0 rfl)) .nil) = _
  rw [env_get_positional_0]

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
      (Env.positional vals) = .done (.cons (0 : Nat) .nil) := by
  unfold samplesStart
  erw [letOp1_denote, localSem_op_literal]
  simp only [Process.bind, HList.single, Term.denote_ret, Env.all, env_get_insert_self]
  rfl

theorem layoutPStart_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins : List (LTy V)} (unitTy : V.Ty) (vals : HList M.Val (held r ins)) :
    (layoutPStart (V := V) (fns := fns) (r := r) (ins := ins) unitTy).denote
      (localSem M fns fnTable) [] (Env.positional vals) =
      .done (.cons ([] : List (M.Val unitTy)) .nil) := by
  unfold layoutPStart
  erw [letOp1_denote, localSem_op_owned]
  simp only [ownedOp, HList.toItems, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [ownedOp, Env.all, env_get_insert_self, Process.bind, HList.single, Term.denote_ret]

theorem layoutVStart_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins : List (LTy V)} (unitTy : V.Ty)
    (proof : List (M.Val unitTy)) (vals : HList M.Val (held r ins)) :
    (layoutVStart (V := V) (fns := fns) (r := r) (ins := ins) unitTy).denote
      (localSem M fns fnTable) [] (Env.positional (.cons proof vals)) =
      .done (.cons (proof, ((0 : Nat), ())) .nil) := by
  unfold layoutVStart
  erw [letOp1_denote, localSem_op_natLiteral]
  simp only [Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  have hAll :
      ((Env.positional (.cons proof vals)).insert (Ty.seq unitTy none :: held r ins).length
          (0 : Nat)).all
        (HList.cons ((posVar (Ty.seq unitTy none :: held r ins) 0 rfl).reindex
            ((positional_freshFrom _).within .nat))
          (HList.cons (freshVar (Ctx.positional (Ty.seq unitTy none :: held r ins))
            (Ty.seq unitTy none :: held r ins).length .nat) HList.nil)) =
      HList.cons proof (HList.cons (0 : Nat) HList.nil) := by
    show HList.cons _ (HList.cons _ HList.nil) = _
    rw [env_get_insert_reindex _ (positional_freshFrom _), env_get_insert_self, env_get_positional_0]
  erw [hAll, ownedOp_makeTuple]
  simp only [Process.bind, HList.single, Term.denote_ret, Env.all, env_get_insert_self]
  rfl

theorem layoutVFinish_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) (unitTy : V.Ty)
    (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (buf : List (M.Val unitTy)) (off : Nat) :
    (layoutVFinish (V := V) (fns := fns) unitTy hfree guardKey).denote
      (localSem M fns fnTable) [] (Env.positional (.cons (buf, (off, ())) .nil)) =
      bif Nat.beq off buf.length then .done .nil else .halt (.declared .reject ⟨[], guardKey⟩) := by
  unfold layoutVFinish
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_positional_0]
  erw [ownedOp_getTuple]
  dsimp only [Tys.getAt, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all]
  erw [ownedOp_getTuple]
  dsimp only [Tys.getAt, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all]
  erw [ownedOp_seqLength]
  dsimp only [Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
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
          erw [letOp1_denote, localSem_op]
          simp only [Env.all]
          rw [env_get_insert_reindex env hfresh]
          change (item.encode.eval M fnTable (.cons (env.get item.input) .nil)).bind _ = _
          simp only [absorbChainFold, Process.map_bind]
          congr 1; funext enc
          erw [letOp1_denote, localSem_op]
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
  erw [letOp1_denote, localSem_op]
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

/-- Initial pure ideal transcript path `([0 :: sessionBytes], [])`. -/
def idealPathInit (unitTy : V.Ty) (sessionBytes : List Nat) : M.Val (idealPathTy unitTy) :=
  ([0 :: sessionBytes], ([], ()))

/-- Pure ideal transcript path extension appending `(tagLbl, encVal)` to `(metaLog, dataLog)`. -/
def idealPathPush {unitTy : V.Ty} (st : M.Val (idealPathTy unitTy))
    (tagLbl : List Nat) (encVal : List (M.Val unitTy)) : M.Val (idealPathTy unitTy) :=
  (st.1 ++ [tagLbl], (st.2.1 ++ [encVal], ()))

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
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all]
  erw [ownedOp_getTuple, getAt_idealPath_head]
  dsimp only [Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_insert_reindex env hfresh]
  erw [ownedOp_getTuple, getAt_idealPath_tail_head]
  dsimp only [Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_insert2_reindex env hfresh, ownedOp, HList.toItems,
    Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_insert_self]
  rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
  · erw [ownedOp_seqConcat]
    dsimp only [Process.bind, HList.single]
    erw [letOp1_denote, localSem_op_owned]
    simp only [Env.all]
    rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne]
    rotate_left 1
    · dsimp only [Var.reindex]; exact Nat.ne_of_lt hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 1 hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 2 hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 3 hEncLt
    · dsimp only [Var.reindex]; exact name_ne_of_lt_add 4 hEncLt
    simp only [ownedOp, HList.toItems, Process.bind, HList.single]
    erw [letOp1_denote, localSem_op_owned]
    simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
    erw [letOp1_denote, localSem_op_owned]
    simp only [Env.all, env_get_insert_self]
    rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
        env_get_insert_ne, env_get_insert_eq]
    · erw [ownedOp_seqConcat]
      dsimp only [Process.bind, HList.single]
      erw [letOp1_denote, localSem_op_owned]
      erw [env_all_idealPath]
      dsimp only [concatSize]
      rw [env_get_insert_self, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
          env_get_insert_eq]
      · erw [ownedOp_makeTuple]
        dsimp only [idealPathTys, Tys.ofHList, Process.bind, HList.single]
        apply hrest _ _ _ _ _
        · rw [env_get_insert_self]
          simp only [idealPathPush, Var.reindex]
          cases encVar; rfl
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
          erw [letOp1_denote, localSem_op]
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
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_insert_self, ownedOp, HList.toItems, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [ownedOp, HList.toItems, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  simp only [Env.all, env_get_insert_self, ownedOp, Process.bind, HList.single]
  erw [letOp1_denote, localSem_op_owned]
  erw [env_all_idealPath]
  rw [env_get_insert_self, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
  · erw [ownedOp_makeTuple]
    dsimp only [idealPathTys, Tys.ofHList, Process.bind, HList.single]
    rw [buildIdealPathChain_denote M fnTable hfree _ _ _ _ _ _ rfl, env_get_insert_self]
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

private theorem env_all_cast {T : Type} {V : T → Type} {Γ : Ctx T} {as bs : List T} (h : as = bs)
    (e : Env V Γ) (xs : HList (Var Γ) as) :
    e.all (cast (congrArg (HList (Var Γ)) h) xs) = cast (congrArg (HList V) h) (e.all xs) := by
  subst h; rfl

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
      erw [letOp1_denote, localSem_op_owned]
      simp only [Env.all]
      rw [ownedOp_seqLength]
      simp only [Process.bind, HList.single]
      erw [letOp1_denote, localSem_op_owned]
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
          erw [letOp1_denote, localSem_op_owned]
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
  erw [letOp1_denote, localSem_op_natLiteral]
  simp only [Process.bind, HList.single]
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

/-! ## Exact denotation lemmas for every generated `Clause` -/

theorem layoutDropClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (path : List Frame) (x : M.Val τ) (s : M.Val stateTy) :
    (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters).code.denote
      (roleSem M r fnTable rTable) path (Env.positional (aloneIn M r (.cons x (.cons s .nil)))) =
      .done (aloneIn M r (.cons s .nil)) := by
  unfold layoutDropClause
  dsimp only
  erw [Term.denote_ret]
  show Process.done (HList.cons ((Env.positional _).get _) HList.nil) = _
  erw [env_get_positional_alone_1 M r x s .nil _ rfl]
  rfl

theorem layoutPWriteClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (writeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (path : List Frame) (msg : M.Val τ) (buf : List (M.Val unitTy)) :
    (layoutPWriteClause prover site kind getters writeRef).code.denote
      (roleSem M prover fnTable rTable) path
      (Env.positional (aloneIn M prover (.cons msg (.cons buf .nil)))) =
      (liftLocal id (writeRef.eval M fnTable (.cons msg .nil))).map fun chunk =>
        aloneIn M prover (.cons (buf ++ (chunk.single : List (M.Val unitTy))) .nil) := by
  unfold layoutPWriteClause
  dsimp only
  refine (letOp1_computeAlone1_eq M prover fnTable rTable _ _ _ msg _ _ _ _ _
    (by exact env_get_positional_alone_0 M prover msg (HList.cons (a := Ty.seq unitTy none) buf .nil) _ rfl)).trans ?_
  change (liftLocal id (writeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext chunk
  cases chunk with
  | cons ch chNil =>
      cases chNil
      refine (letOp1_computeAlone2_eq M prover fnTable rTable _ _ _ _ buf ch _ _ _ _ _
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
          exact env_get_positional_alone_1 M prover (τ₁ := Ty.seq unitTy none) msg buf .nil _ rfl)
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      change (liftLocal id (ownedOp M (.seqConcat unitTy none none) (.cons buf (.cons ch .nil)))).bind _ = _
      rw [ownedOp_seqConcat]
      dsimp only [liftLocal_done, Process.bind, HList.single]
      exact term_denote_ret1 M prover fnTable rTable _ _ _ _ (env_get_insert_eq _ _ _ rfl)

theorem layoutVReadClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (path : List Frame) (buf : List (M.Val unitTy)) (off : Nat) :
    (layoutVReadClause hfree verifier prover site kind readRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons (buf, (off, ())) .nil))) =
      (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).map fun res =>
        match res with
        | .cons v (.cons nextOff .nil) =>
            aloneIn M verifier (.cons v (.cons (buf, (nextOff, ())) .nil)) := by
  unfold layoutVReadClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by exact env_get_positional_alone_0 M verifier (τ := streamStateTy unitTy) (buf, (off, ())) .nil _ (by rfl))).trans ?_
  have htfree : Tys.anyLinear V (streamStateTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) .head htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M verifier (τ := streamStateTy unitTy) (buf, (off, ())) .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) (.tail .head) htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp2_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf off _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext res
  cases res with
  | cons v res1 =>
      cases res1 with
      | cons nextOff res2 =>
          cases res2
          refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf nextOff _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)
            (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
          dsimp only [localOp]
          refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
            (ownedOp_makeTuple M (streamStateTys unitTy) (.cons buf (.cons nextOff .nil))))) _).trans ?_
          dsimp only [Tys.ofHList, liftLocal_done, Process.bind, HList.single]
          exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)
            (env_get_insert_eq _ _ _ rfl)

theorem layoutVCarryClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (path : List Frame) (derived : M.Val τ) (buf : List (M.Val unitTy)) (off : Nat) :
    (layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons derived (.cons (buf, (off, ())) .nil)))) =
      (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).bind fun res =>
        match res with
        | .cons carried (.cons nextOff .nil) =>
            (liftLocal id (eqRef.eval M fnTable (.cons derived (.cons carried .nil)))).bind
              fun eqRes =>
                bif eqRes.single then
                  .done (aloneIn M verifier (.cons (buf, (nextOff, ())) .nil))
                else .halt (.declared .reject ⟨path, guardKey⟩) := by
  unfold layoutVCarryClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by exact env_get_positional_alone_1 M verifier (τ₁ := streamStateTy unitTy) derived (buf, (off, ())) .nil _ (by rfl))).trans ?_
  have htfree : Tys.anyLinear V (streamStateTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) .head htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_1 M verifier (τ₁ := streamStateTy unitTy) derived (buf, (off, ())) .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) (.tail .head) htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp2_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf off _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).bind _ = _
  congr 1; funext res
  cases res with
  | cons carried res1 =>
      cases res1 with
      | cons nextOff res2 =>
          cases res2
          refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ derived carried _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
              exact env_get_positional_alone_0 M verifier derived
                (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil) _ (by rfl))
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)).trans ?_
          change (liftLocal id (eqRef.eval M fnTable (.cons derived (.cons carried .nil)))).bind _ = _
          congr 1; funext eqRes
          cases eqRes with
          | cons eqb eqNil =>
              cases eqNil
              refine (term_denote_guard_eq M verifier fnTable rTable _ _ _ _ _ _ _ eqb
                (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
              dsimp only [HList.single]
              cases eqb with
              | false => rfl
              | true =>
                  simp only [Bool.cond_true]
                  refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf nextOff _ _ _ _ _
                    (by
                      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                        env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                        env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                        env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
                      exact env_get_insert_eq _ _ _ rfl)
                    (by
                      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
                      exact env_get_insert_eq _ _ _ rfl)).trans ?_
                  dsimp only [localOp]
                  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
                    (ownedOp_makeTuple M (streamStateTys unitTy) (.cons buf (.cons nextOff .nil))))) _).trans ?_
                  dsimp only [Tys.ofHList, liftLocal_done, Process.bind, HList.single]
                  exact term_denote_ret1 M verifier fnTable rTable _ _ _ _ (env_get_insert_eq _ _ _ rfl)

theorem proverAbsorbClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (path : List Frame) (msg : M.Val τ) (st : M.Val stateTy) :
    (proverAbsorbClause prover site kind getters label hlabel encodeRef absorbRef).code.denote
      (roleSem M prover fnTable rTable) path
      (Env.positional (aloneIn M prover (.cons msg (.cons st .nil)))) =
      (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
        (liftLocal id (absorbRef.eval M fnTable
            (.cons st (.cons label (.cons enc.single .nil))))).bind fun nextSt =>
          .call (ROp.give kind getters ⟨path, site.key⟩ τ msg) fun _ =>
            .done (aloneIn M prover nextSt) := by
  unfold proverAbsorbClause
  dsimp only
  refine (letOp1_computeAlone0_denote M prover fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M prover fnTable rTable _ _ _ msg _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M prover msg (.cons st .nil) _ rfl)).trans ?_
  change (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      refine (letOp1_computeAlone3_eq M prover fnTable rTable _ _ _ _ _ st label encVal _ _ _ _ _
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
          exact env_get_positional_alone_1 M prover msg st .nil _ rfl)
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
          exact env_get_insert_eq _ _ _ rfl)
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      change (liftLocal id (absorbRef.eval M fnTable (.cons st (.cons label (.cons encVal .nil))))).bind _ = _
      congr 1; funext nextSt
      cases nextSt with
      | cons st' stNil =>
          cases stNil
          refine (letOp1_give_eq M prover fnTable rTable _ _ _ _ _ msg _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
              exact env_get_positional_alone_0 M prover msg (.cons st .nil) _ rfl)).trans ?_
          congr 1

theorem verifierAbsorbClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (path : List Frame) (st : M.Val stateTy) :
    (verifierAbsorbClause verifier prover site kind label hlabel encodeRef absorbRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons st .nil))) =
      .call (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg =>
        (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
          (liftLocal id (absorbRef.eval M fnTable
              (.cons st (.cons label (.cons enc.single .nil))))).map fun nextSt =>
            aloneIn M verifier (.cons msg nextSt) := by
  unfold verifierAbsorbClause
  dsimp only
  refine (letOp1_denote (roleSem M verifier fnTable rTable) _ _ _ _ _ _ _ _).trans ?_
  change (Process.call (S := RSig M) (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg => _).bind _ = _
  simp only [Process.bind]
  congr 1; funext msg
  refine (letOp1_keep_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      refine (letOp1_computeAlone3_eq M verifier fnTable rTable _ _ _ _ _ st label encVal _ _ _ _ _
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
          exact env_get_positional_alone_0 M verifier st .nil _ rfl)
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
          exact env_get_insert_eq _ _ _ rfl)
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      change (liftLocal id (absorbRef.eval M fnTable (.cons st (.cons label (.cons encVal .nil))))).bind _ = _
      rw [Process.map_eq_bind]
      congr 1; funext nextSt
      cases nextSt with
      | cons st' stNil =>
          cases stNil
          exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)
            (env_get_insert_eq _ _ _ rfl)

theorem deriveClause_denote_nil {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (r peer : Role) (site : Site) (part : Part V)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (deriveRef : TypedFnRef V hs.fns [stateTy, bytesTy] [τ, stateTy])
    (path : List Frame) (st : M.Val stateTy) :
    (deriveClause r peer site part [] toldKey label hlabel deriveRef).code.denote
      (roleSem M r fnTable rTable) path
      (Env.positional (aloneIn M r (.cons st .nil))) =
      (liftLocal id (deriveRef.eval M fnTable (.cons st (.cons label .nil)))).bind fun res =>
        match res with
        | .cons coin (.cons nextSt .nil) =>
            .call (ROp.give .message [peer] ⟨path, toldKey⟩ τ coin) fun _ =>
              .done (aloneIn M r (.cons coin (.cons nextSt .nil))) := by
  unfold deriveClause
  dsimp only
  refine (letOp1_computeAlone0_denote M r fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single, List.nil_append, List.length_nil,
    takeVars, id, HList.reindex]
  refine (letOp2_computeAlone2_eq M r fnTable rTable _ _ _ _ st label _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, posVar])]
      exact env_get_positional_alone_0 M r st .nil _ rfl)
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (deriveRef.eval M fnTable (.cons st (.cons label .nil)))).bind _ = _
  congr 1; funext res
  cases res with
  | cons coin res1 =>
      cases res1 with
      | cons nextSt res2 =>
          cases res2
          refine (letOp1_give_eq M r fnTable rTable _ _ _ _ _ coin _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)).trans ?_
          congr 1

theorem idealAbsorbClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (path : List Frame) (st : M.Val (idealPathTy unitTy)) :
    (idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons st .nil))) =
      .call (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg =>
        (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).map fun enc =>
          aloneIn M verifier (.cons msg (.cons (idealPathPush M st (2 :: label) enc.single) .nil)) := by
  have hTagLbl : ∀ b, b ∈ (2 :: label) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hm
    · exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 253))
    · exact hlabel b hm
  unfold idealAbsorbClause
  dsimp only
  refine (letOp1_denote (roleSem M verifier fnTable rTable) _ _ _ _ _ _ _ _).trans ?_
  change (Process.call (S := RSig M) (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg => _).bind _ = _
  simp only [Process.bind]
  congr 1; funext msg
  refine (letOp1_keep_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M (2 :: label) hTagLbl]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      apply appendIdealPathRole_denote_eq M verifier fnTable rTable hfree _ _ _ _ _ _ path _
        st (2 :: label) encVal
      · rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
          env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
          env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
          env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
        exact env_get_positional_alone_0 M verifier st .nil _ rfl
      · rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
        exact env_get_insert_eq _ _ _ rfl
      · exact env_get_insert_eq _ _ _ rfl
      · intro Γ' h' w nextSt env' hNext hAgree
        apply term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _ _ hNext
        rw [hAgree _ (by
          change (((((Ctx.positional (alone verifier [idealPathTy unitTy])).insert 1 _).insert 2 _).insert 3 _).insert 4 _).find? 2 = some ⟨τ, [verifier]⟩
          rw [Ctx.find?_insert, ite_eq_right, Ctx.find?_insert, ite_eq_right,
              Ctx.find?_insert, ite_eq_left rfl]
          · decide
          · decide),
          env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
        · rfl
        · dsimp only [Var.reindex, freshVar]; decide
        · dsimp only [Var.reindex, freshVar]; decide

theorem idealDeriveClause_denote_nil {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (part : Part V)
    (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (path : List Frame) (st : M.Val (idealPathTy unitTy)) :
    (idealDeriveClause hfree verifier prover site part [] serviceKey reqKey toldKey
        label hlabel encodeRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons st .nil))) =
      .call (ROp.own (.request serviceKey) [] ⟨path, reqKey⟩ [idealQueryTy unitTy]
          (.cons (st, (label, ())) .nil) τ) fun coin =>
        .call (ROp.give .message [prover] ⟨path, toldKey⟩ τ coin) fun _ =>
          (liftLocal id (encodeRef.eval M fnTable (.cons coin .nil))).map fun enc =>
            aloneIn M verifier (.cons coin (.cons (idealPathPush M st (3 :: label) enc.single) .nil)) := by
  have hTagLbl : ∀ b, b ∈ (3 :: label) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hm
    · exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 252)))
    · exact hlabel b hm
  unfold idealDeriveClause
  dsimp only [List.nil_append, List.length_singleton, List.length_nil]
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ st label _ _ _ _ _
    ?_ ?_).trans ?_
  · rw [env_get_insert_ne]
    · exact env_get_positional_alone_0 M verifier st .nil _ rfl
    · dsimp only [Var.reindex, posVar]; decide
  · exact env_get_insert_eq _ _ _ rfl
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_makeTuple M (idealQueryTys unitTy) (.cons st (.cons label .nil))))) _).trans ?_
  dsimp only [Tys.ofHList, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_request1_eq M verifier fnTable rTable _ _ _ _ (st, (label, ())) _ _ _ _ _ ?_).trans ?_
  · exact env_get_insert_eq _ _ _ rfl
  congr 1; funext coin
  refine (letOp1_keep_eq M verifier fnTable rTable _ _ _ coin _ _ _ _ _ ?_).trans ?_
  · exact env_get_insert_eq _ _ _ rfl
  refine (letOp1_give_eq M verifier fnTable rTable _ _ _ _ _ coin _ _ _ _ _ ?_).trans ?_
  · exact env_get_insert_eq _ _ _ rfl
  congr 1; funext _
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M (3 :: label) hTagLbl]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ coin _ _ _ _ _ ?_).trans ?_
  · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
    · rfl
    · dsimp only [Var.reindex, freshVar]; decide
    · dsimp only [Var.reindex, freshVar]; decide
  change (liftLocal id (encodeRef.eval M fnTable (.cons coin .nil))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      apply appendIdealPathRole_denote_eq M verifier fnTable rTable hfree _ _ _ _ _ _ path _
        st (3 :: label) encVal
      · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
            env_get_insert_ne, env_get_insert_ne, env_get_insert_ne]
        · exact env_get_positional_alone_0 M verifier st .nil _ rfl
        all_goals (dsimp only [Var.reindex, posVar]; decide)
      · rw [env_get_insert_ne, env_get_insert_eq]
        all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)
      · exact env_get_insert_eq _ _ _ rfl
      · intro Γ' h' w nextSt env' hNext hAgree
        apply term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _ _ hNext
        rw [hAgree _ (by
          change ((((((((Ctx.positional (alone verifier [idealPathTy unitTy])).insert 1 _).insert 2 _).insert 3 _).insert 4 _).insert 5 _).insert 6 _).insert 7 _).find? 4 = some ⟨τ, [verifier]⟩
          rw [Ctx.find?_insert, ite_eq_right, Ctx.find?_insert, ite_eq_right,
              Ctx.find?_insert, ite_eq_right, Ctx.find?_insert, ite_eq_left rfl]
          · decide
          · decide
          · decide),
          env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
        · rfl
        · dsimp only [Var.reindex, freshVar]; decide
        · dsimp only [Var.reindex, freshVar]; decide
        · dsimp only [Var.reindex, freshVar]; decide

theorem proverSampleClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {τ : V.Ty}
    (prover : Role) (site : Site) (law : V.LawKey)
    (sampleRef : TypedFnRef V hs.fns [.nat, .nat] [τ])
    (path : List Frame) (att : Nat) :
    (proverSampleClause prover site law sampleRef).code.denote
      (roleSem M prover fnTable rTable) path
      (Env.positional (aloneIn M prover (.cons att .nil))) =
      (liftLocal id (sampleRef.eval M fnTable (.cons att (.cons site.key.number .nil)))).map
        fun coin => aloneIn M prover (.cons coin.single (.cons att .nil)) := by
  unfold proverSampleClause
  dsimp only
  refine (letOp1_computeAlone0_denote M prover fnTable rTable _ _ _ _ _ _ _).trans ?_
  have hlit : localOp M fnTable (.literal .nat [site.key.number] rfl) .nil =
      .done (.cons (a := Ty.nat) site.key.number .nil) := rfl
  rw [hlit]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M prover fnTable rTable _ _ _ _ att site.key.number _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M prover (τ := Ty.nat) att .nil _ (by rfl))
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (sampleRef.eval M fnTable (.cons att (.cons site.key.number .nil)))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1

theorem compactReadSlotClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ)
    (path : List Frame) (st : stateTys.Val M.toCarriers) :
    (compactReadSlotClause (hs := hs) htfree verifier prover site kind pos).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))) =
      .done (aloneIn M verifier (.cons (Tys.getAt M stateTys pos st) (.cons (a := Ty.tuple stateTys) st .nil))) := by
  unfold compactReadSlotClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (v₁ := (st : M.Val (.tuple stateTys))) _ _ _ _ _
    (by exact env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M stateTys pos htfree st))) _).trans ?_
  dsimp only [liftLocal_done, Process.bind, HList.single]
  exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
    (env_get_insert_eq _ _ _ rfl)
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil _ (by rfl))

theorem compactCompareClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ)
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (path : List Frame) (derived : M.Val τ) (st : stateTys.Val M.toCarriers) :
    (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons derived (.cons (a := Ty.tuple stateTys) st .nil)))) =
      (liftLocal id (eqRef.eval M fnTable
          (.cons derived (.cons (Tys.getAt M stateTys pos st) .nil)))).bind fun eqRes =>
        bif eqRes.single then .done (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))
        else .halt (.declared .reject ⟨path, guardKey⟩) := by
  unfold compactCompareClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (v₁ := (st : M.Val (.tuple stateTys))) _ _ _ _ _
    (by exact env_get_positional_alone_1 M verifier (τ₁ := Ty.tuple stateTys) derived st .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M stateTys pos htfree st))) _).trans ?_
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ derived (Tys.getAt M stateTys pos st) _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M verifier derived (.cons (a := Ty.tuple stateTys) st .nil) _ (by rfl))
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (eqRef.eval M fnTable (.cons derived (.cons (Tys.getAt M stateTys pos st) .nil)))).bind _ = _
  congr 1; funext eqRes
  cases eqRes with
  | cons eqb eqNil =>
      cases eqNil
      refine (term_denote_guard_eq M verifier fnTable rTable _ _ _ _ _ _ _ eqb
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      dsimp only [HList.single]
      cases eqb with
      | false => rfl
      | true =>
          simp only [Bool.cond_true]
          exact term_denote_ret1 M verifier fnTable rTable _ _ _ _ (by
            rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
              env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
            exact env_get_positional_alone_1 M verifier (τ₁ := Ty.tuple stateTys) derived st .nil _ (by rfl))

theorem compactRecoverClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recoverRef : SafeFnRef V hs.fns stateTys.toList [τ])
    (path : List Frame) (st : stateTys.Val M.toCarriers) :
    (compactRecoverClause verifier prover site kind recoverRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))) =
      (liftLocal id (recoverRef.eval M fnTable (Tys.toHList M stateTys st))).map fun res =>
        aloneIn M verifier (.cons res.single (.cons (a := Ty.tuple stateTys) st .nil)) := by
  unfold compactRecoverClause
  dsimp only
  refine (Term.denote_op (roleSem M verifier fnTable rTable) _ _ _ _ _ _ _).trans ?_
  have hOp0 :
      (roleSem M verifier fnTable rTable).op ⟨0⟩ (computeAlone verifier (.owned (.takeTuple stateTys))) path
        ((Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))).all
          (.cons (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) .nil)) =
      .done (aloneIn M verifier (Tys.toHList M stateTys st)) := by
    have hAll :
        (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))).all
          (.cons (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) .nil) =
        aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil) := by
      show HList.cons _ HList.nil = HList.cons _ HList.nil
      exact congrArg (fun v => HList.cons v HList.nil)
        (env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) rfl)
    erw [hAll, computeAlone_denote]
    dsimp only [localOp]
    rw [ownedOp_takeTuple]
    rfl
  refine (congrFun (congrArg Process.bind hOp0) _).trans ?_
  dsimp only [Process.bind]
  have hBuild : ∀ (start : Nat) {Γ : Ctx (LTy V)} (env : Env (RV M verifier) Γ)
      (tys : List (LTy V)) (vals : HList (RV M verifier) tys)
      (hΓ : ∀ k a, tys[k]? = some a → Γ.find? (start + k) = some a)
      (hEnv : ∀ k a (ha : tys[k]? = some a),
        env.get ⟨start + k, hΓ k a ha⟩ = HList.getAt vals k ha),
      env.all (compactRecoverClause.buildFieldVars start tys hΓ) = vals := by
    intro start Γ env tys
    induction tys generalizing start with
    | nil =>
        intro vals _ _
        cases vals
        rfl
    | cons a ts ih =>
        intro vals hΓ hEnv
        cases vals with
        | cons v vs =>
            show HList.cons (env.get ⟨start, hΓ 0 a rfl⟩) _ = HList.cons v vs
            congr 1
            · exact hEnv 0 a rfl
            · exact ih (start + 1) vs _ fun k b hb => by
                have hk := hEnv (k + 1) b hb
                simpa [HList.getAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
  refine (letOp1_computeAlone_eq M verifier fnTable rTable _ _ _ (Tys.toHList M stateTys st) _ _ _ _ _
    (hBuild 1 _ (alone verifier stateTys.toList)
      (aloneIn M verifier (Tys.toHList M stateTys st)) _ fun k a ha =>
      env_get_extend_counting_getAt _ 1 _ k ha _)).trans ?_
  change (liftLocal id (recoverRef.eval M fnTable (Tys.toHList M stateTys st))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext res
  cases res with
  | cons v vNil =>
      cases vNil
      exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
        (env_get_insert_eq _ _ _ rfl)
        (by
          rw [env_get_insert_ne _ _ _ (by
            intro h
            change (0 : Nat) = 1 + (alone verifier stateTys.toList).length at h
            exact Nat.zero_ne_add_one _ (Nat.add_comm 1 _ ▸ h))]
          dsimp only [Var.reindex]
          refine (env_extend_counting_outside
            (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))) 1
            (aloneIn M verifier (Tys.toHList M stateTys st)) 0 (.inl (by omega)) _).trans ?_
          exact env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil
            (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) rfl)

end

/-! ## Event-key lemmas for every generated clause -/

theorem computeAlone_isEvent {V : Vocabulary} {hs : Headers V} (r : Role) {ins outs : List V.Ty}
    (o : LocalOp V hs.fns ins outs) :
    RoleOp.isEvent (computeAlone (hs := hs) r o) = false :=
  rfl

theorem proverAbsorbClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (proverAbsorbClause prover site kind getters label hlabel encodeRef absorbRef).code =
      [site.key] :=
  rfl

theorem verifierAbsorbClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (verifierAbsorbClause verifier prover site kind label hlabel encodeRef absorbRef).code =
      [site.key] :=
  rfl

theorem deriveClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy τ : V.Ty}
    (r peer : Role) (site : Site) (part : Part V) (drawIns : List V.Ty)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (deriveRef : TypedFnRef V hs.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (deriveClause r peer site part drawIns toldKey label hlabel deriveRef).code =
      [toldKey] :=
  rfl

theorem idealAbsorbClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef).code =
      [site.key] :=
  rfl

theorem idealDeriveClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (part : Part V) (drawIns : List V.Ty)
    (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (idealDeriveClause hfree verifier prover site part drawIns serviceKey reqKey toldKey
        label hlabel encodeRef).code =
      [reqKey, toldKey] :=
  rfl

theorem layoutPWriteClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (writeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutPWriteClause prover site kind getters writeRef).code = [] :=
  rfl

theorem layoutDropClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters).code = [] :=
  rfl

theorem layoutVReadClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutVReadClause hfree verifier prover site kind readRef).code = [] :=
  rfl

theorem layoutVCarryClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef).code = [] :=
  rfl

theorem proverSampleClause_eventKeys {V : Vocabulary} {hs : Headers V} {τ : V.Ty}
    (prover : Role) (site : Site) (law : V.LawKey)
    (sampleRef : TypedFnRef V hs.fns [.nat, .nat] [τ]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (proverSampleClause prover site law sampleRef).code = [] :=
  rfl

theorem compactReadSlotClause_eventKeys {V : Vocabulary} {hs : Headers V}
    {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (compactReadSlotClause (hs := hs) htfree verifier prover site kind pos).code = [] :=
  rfl

theorem compactCompareClause_eventKeys {V : Vocabulary} {hs : Headers V}
    {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ)
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef).code = [] :=
  rfl

theorem compactRecoverClause_eventKeys {V : Vocabulary} {hs : Headers V}
    {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recoverRef : SafeFnRef V hs.fns stateTys.toList [τ]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (compactRecoverClause verifier prover site kind recoverRef).code = [] :=
  rfl

end LayerBuild

end Zkc.Core
