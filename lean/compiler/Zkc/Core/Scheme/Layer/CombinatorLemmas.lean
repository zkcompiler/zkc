module

public import Zkc.Core.Scheme.Layer.Combinators
public import Zkc.Core.Admission.Theorems
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Meaning.Stops

@[expose] public section

/-!
Denotation, event-key, environment-lookup, and function-reference lemmas for `Layer.Combinators`.
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

theorem cast_hlist_cons {α : Type} {F : α → Type} {as bs : List α} (h : as = bs)
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

theorem ownedOp_natAdd (a b : Nat) :
    ownedOp M .natAdd (.cons a (.cons b .nil)) = .done (.cons (a + b) .nil) :=
  rfl

theorem ownedOp_takeTuple (items : Tys V.TypeKey) (v : items.Val M.toCarriers) :
    ownedOp M (.takeTuple items) (.cons v .nil) = .done (Tys.toHList M items v) :=
  rfl

/-! ## `TypedFnRef` and `SafeFnRef` evaluation and safety -/

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


section LocalDenote
variable {V : Vocabulary} (M : Model V)

/-! ## Specialized `localDialect` `letOp1` denotation lemmas (eliminating `erw`) -/

theorem letOp1_local_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {Γ : Ctx V.Ty} {ins outs : List V.Ty} {τ : V.Ty}
    (key : Key) (o : LocalOp V fns ins [τ]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' → Var Γ' τ → Term (localDialect V fns) Γ' outs)
    (path : List Frame) (env : Env M.Val Γ) :
    (letOp1 (D := localDialect V fns) key o operands n hfresh rest).denote (localSem M fns fnTable) path env =
      (localOp M fnTable o (env.all operands)).bind fun vs =>
        (rest (Γ.insert n τ) (hfresh.insert τ) (hfresh.within τ) (freshVar Γ n τ)).denote
          (localSem M fns fnTable) path (env.insert n vs.single) :=
  letOp1_denote (localSem M fns fnTable) key o operands n hfresh rest path env

theorem letOp1_local_owned_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {Γ : Ctx V.Ty} {ins outs : List V.Ty} {τ : V.Ty}
    (key : Key) (o : OwnedOp V ins [τ]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' → Var Γ' τ → Term (localDialect V fns) Γ' outs)
    (path : List Frame) (env : Env M.Val Γ) :
    (letOp1 (D := localDialect V fns) key (.owned o) operands n hfresh rest).denote (localSem M fns fnTable) path env =
      (ownedOp M o (env.all operands)).bind fun vs =>
        (rest (Γ.insert n τ) (hfresh.insert τ) (hfresh.within τ) (freshVar Γ n τ)).denote
          (localSem M fns fnTable) path (env.insert n vs.single) :=
  letOp1_local_denote M fnTable key (.owned o) operands n hfresh rest path env

theorem letOp1_local_natLiteral_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {Γ : Ctx V.Ty} {outs : List V.Ty}
    (key : Key) (k : Nat) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' → Var Γ' .nat → Term (localDialect V fns) Γ' outs)
    (path : List Frame) (env : Env M.Val Γ) :
    (letOp1 (D := localDialect V fns) key (.literal .nat [k] rfl) .nil n hfresh rest).denote
        (localSem M fns fnTable) path env =
      (rest (Γ.insert n .nat) (hfresh.insert .nat) (hfresh.within .nat) (freshVar Γ n .nat)).denote
        (localSem M fns fnTable) path (env.insert n k) :=
  letOp1_local_denote M fnTable key (.literal .nat [k] rfl) .nil n hfresh rest path env

theorem letOp1_local_bytesLiteral_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {Γ : Ctx V.Ty} {outs : List V.Ty}
    (key : Key) (bs : List Nat) (hbs : ∀ b, b ∈ bs → b < 256) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' → Var Γ' bytesTy → Term (localDialect V fns) Γ' outs)
    (path : List Frame) (env : Env M.Val Γ) :
    (letOp1 (D := localDialect V fns) key (.literal bytesTy (bs.length :: bs) (bytesLiteral_reads bs hbs))
        .nil n hfresh rest).denote (localSem M fns fnTable) path env =
      (rest (Γ.insert n bytesTy) (hfresh.insert bytesTy) (hfresh.within bytesTy) (freshVar Γ n bytesTy)).denote
        (localSem M fns fnTable) path (env.insert n bs) := by
  rw [letOp1_local_denote, localOp, bytesLiteral_val M bs hbs]
  rfl

theorem letOp1_local_makeTuple2_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {Γ : Ctx V.Ty} {τ₁ τ₂ : V.Ty} {outs : List V.Ty}
    (key : Key) (x₁ : Var Γ τ₁) (x₂ : Var Γ τ₂) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' (.tuple (.cons τ₁ (.cons τ₂ .nil))) → Term (localDialect V fns) Γ' outs)
    (path : List Frame) (env : Env M.Val Γ) :
    (letOp1 (D := localDialect V fns) key (.owned (.makeTuple (.cons τ₁ (.cons τ₂ .nil))))
        (.cons x₁ (.cons x₂ .nil)) n hfresh rest).denote (localSem M fns fnTable) path env =
      (rest (Γ.insert n (.tuple (.cons τ₁ (.cons τ₂ .nil))))
        (hfresh.insert (.tuple (.cons τ₁ (.cons τ₂ .nil))))
        (hfresh.within (.tuple (.cons τ₁ (.cons τ₂ .nil))))
        (freshVar Γ n (.tuple (.cons τ₁ (.cons τ₂ .nil))))).denote
        (localSem M fns fnTable) path (env.insert n (env.get x₁, (env.get x₂, ()))) :=
  letOp1_local_owned_denote M fnTable key (.makeTuple (.cons τ₁ (.cons τ₂ .nil)))
    (.cons x₁ (.cons x₂ .nil)) n hfresh rest path env

theorem letOp1_local_makeTuple3_denote {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {Γ : Ctx V.Ty} {τ₁ τ₂ τ₃ : V.Ty} {outs : List V.Ty}
    (key : Key) (x₁ : Var Γ τ₁) (x₂ : Var Γ τ₂) (x₃ : Var Γ τ₃) (n : Name) (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' →
      Var Γ' (.tuple (.cons τ₁ (.cons τ₂ (.cons τ₃ .nil)))) → Term (localDialect V fns) Γ' outs)
    (path : List Frame) (env : Env M.Val Γ) :
    (letOp1 (D := localDialect V fns) key (.owned (.makeTuple (.cons τ₁ (.cons τ₂ (.cons τ₃ .nil)))))
        (.cons x₁ (.cons x₂ (.cons x₃ .nil))) n hfresh rest).denote (localSem M fns fnTable) path env =
      (rest (Γ.insert n (.tuple (.cons τ₁ (.cons τ₂ (.cons τ₃ .nil)))))
        (hfresh.insert (.tuple (.cons τ₁ (.cons τ₂ (.cons τ₃ .nil)))))
        (hfresh.within (.tuple (.cons τ₁ (.cons τ₂ (.cons τ₃ .nil)))))
        (freshVar Γ n (.tuple (.cons τ₁ (.cons τ₂ (.cons τ₃ .nil)))))).denote
        (localSem M fns fnTable) path (env.insert n (env.get x₁, (env.get x₂, (env.get x₃, ())))) :=
  letOp1_local_owned_denote M fnTable key (.makeTuple (.cons τ₁ (.cons τ₂ (.cons τ₃ .nil))))
    (.cons x₁ (.cons x₂ (.cons x₃ .nil))) n hfresh rest path env

end LocalDenote

end

end LayerBuild

end Zkc.Core
