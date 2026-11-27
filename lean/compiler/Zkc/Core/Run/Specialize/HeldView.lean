module

public import Zkc.Core.Scheme.Deployed
public import Zkc.Core.Meaning.Program

@[expose] public section

/-!
Inductive held-value view (`HeldRel`) and context/environment erasure (`CtxRel`, `EnvRel`).

`HeldRel r items ts` witnesses that `ts = held r items` element-by-element (`nil`, `keep`, `drop`).
Operating directly on `HeldRel` eliminates dependent `cast`s across `Names`, `Var`, `RV`, `Val`,
and loop accumulators, while bridging seamlessly to the existing `held` / `heldValues` API.
-/

namespace Zkc.Core

/-! ## Basic `held` structural equalities -/

section HeldBasics
variable {V : Vocabulary}

theorem held_cons_pos (r : Role) (a : LTy V) (rest : List (LTy V)) (h : r ∈ a.holders) :
    held r (a :: rest) = a.ty :: held r rest := by
  simp [held, h]

theorem held_cons_neg (r : Role) (a : LTy V) (rest : List (LTy V)) (h : r ∉ a.holders) :
    held r (a :: rest) = held r rest := by
  simp [held, h]

theorem held_append (r : Role) : ∀ (as bs : List (LTy V)),
    held r (as ++ bs) = held r as ++ held r bs
  | [], _ => rfl
  | a :: as, bs => by
      simp only [List.cons_append, held]
      split
      · simp only [List.cons_append, held_append r as bs]
      · exact held_append r as bs

theorem held_alone (r : Role) : ∀ (types : List V.Ty),
    held r (alone r types) = types
  | [] => rfl
  | τ :: rest => by
      change held r (⟨τ, [r]⟩ :: alone r rest) = τ :: rest
      simp only [held, List.mem_singleton, ↓reduceIte]
      exact congrArg (τ :: ·) (held_alone r rest)

theorem held_map_collected (r : Role) (size : Option Nat) : ∀ (each : List (LTy V)),
    held r (each.map (LTy.collected size)) = (held r each).map (fun τ => .seq τ size)
  | [] => rfl
  | a :: rest => by
      simp only [List.map_cons, held, LTy.collected]
      split
      · simp only [List.map_cons, held_map_collected r size rest]
      · exact held_map_collected r size rest

theorem held_map_roleMap (ρ : RoleMap) (r : Role) : ∀ (items : List (LTy V)),
    held r (items.map (LTy.map ρ.to)) = held (ρ.back r) items
  | [] => rfl
  | a :: rest => by
      simp only [List.map_cons, held, LTy.map, ρ.mem_map]
      split
      · simp only [held_map_roleMap ρ r rest]
      · exact held_map_roleMap ρ r rest

theorem held_map_holders (r : Role) (R : Holders) (h : r ∈ R) : ∀ (outs : List V.Ty),
    held r (outs.map fun τ => ⟨τ, R⟩) = outs
  | [] => rfl
  | _ :: rest => by
      simp only [List.map_cons, held, h, ↓reduceIte, held_map_holders r R h rest]

theorem held_all_out (r : Role) : ∀ (items : List (LTy V)),
    (∀ a, a ∈ items → r ∉ a.holders) → held r items = []
  | [], _ => rfl
  | a :: rest, out => by
      have ha : r ∉ a.holders := out a List.mem_cons_self
      simp only [held, ha, ↓reduceIte]
      exact held_all_out r rest fun b hb => out b (List.mem_cons_of_mem _ hb)

theorem ctx_extend_cast {T : Type} (Δ : Ctx T) {as bs : List T} (h : as = bs) (ns : Names as) :
    Δ.extend (cast (congrArg Names h) ns) = Δ.extend ns := by
  subst h; rfl

theorem hlist_cons_cast {α : Type} {F : α → Type} {a : α} {as bs : List α}
    (e : as = bs) (x : F a) (xs : HList F as) :
    HList.cons x (cast (congrArg (HList F) e) xs) =
      cast (congrArg (HList F) (congrArg (a :: ·) e)) (HList.cons x xs) := by
  subst e; rfl

theorem hlist_append_cast {α : Type} {F : α → Type} {as bs cs : List α}
    (e : as = bs) (xs : HList F as) (ys : HList F cs) :
    (cast (congrArg (HList F) e) xs).append ys =
      cast (congrArg (HList F) (congrArg (· ++ cs) e)) (xs.append ys) := by
  subst e; rfl

end HeldBasics

/-! ## Inductive `HeldRel` view -/

section HeldViewDef
variable {V : Vocabulary}

/-- Inductive witness that `ts` is the subsequence of plain types held by role `r` in `items`. -/
inductive HeldRel (r : Role) : List (LTy V) → List V.Ty → Type where
  | nil : HeldRel r [] []
  | keep {a : LTy V} {rest : List (LTy V)} {ts : List V.Ty}
      (h : r ∈ a.holders) (tail : HeldRel r rest ts) :
      HeldRel r (a :: rest) (a.ty :: ts)
  | drop {a : LTy V} {rest : List (LTy V)} {ts : List V.Ty}
      (h : r ∉ a.holders) (tail : HeldRel r rest ts) :
      HeldRel r (a :: rest) ts

/-- Every `HeldRel r items ts` witnesses `ts = held r items`. -/
theorem HeldRel.eq_held {r : Role} :
    ∀ {items : List (LTy V)} {ts : List V.Ty}, HeldRel r items ts → ts = held r items
  | _, _, .nil => rfl
  | _, _, .keep h tail => by rw [held_cons_pos _ _ _ h, tail.eq_held]
  | _, _, .drop h tail => by rw [held_cons_neg _ _ _ h, tail.eq_held]

/-- Canonical `HeldRel` at the computed type list `held r items`. -/
def HeldRel.ofList (r : Role) : (items : List (LTy V)) → HeldRel r items (held r items)
  | [] => .nil
  | a :: rest =>
      if h : r ∈ a.holders then
        (held_cons_pos r a rest h).symm ▸ .keep h (HeldRel.ofList r rest)
      else
        (held_cons_neg r a rest h).symm ▸ .drop h (HeldRel.ofList r rest)

/-- Functional uniqueness of `HeldRel`: any two views of `(r, items)` have equal target lists
and are heterogeneously equal. -/
theorem HeldRel.unique_heq {r : Role} :
    ∀ {items : List (LTy V)} {ts₁ ts₂ : List V.Ty}
      (v₁ : HeldRel r items ts₁) (v₂ : HeldRel r items ts₂),
      HEq v₁ v₂
  | _, _, _, .nil, .nil => HEq.rfl
  | _, _, _, .keep _ t₁, .keep _ t₂ => by
      have hT : _ = _ := (t₁.eq_held).trans t₂.eq_held.symm
      cases hT
      cases eq_of_heq (HeldRel.unique_heq t₁ t₂)
      exact HEq.rfl
  | _, _, _, .keep h₁ _, .drop h₂ _ => absurd h₁ h₂
  | _, _, _, .drop h₁ _, .keep h₂ _ => absurd h₂ h₁
  | _, _, _, .drop _ t₁, .drop _ t₂ => by
      have hT : _ = _ := (t₁.eq_held).trans t₂.eq_held.symm
      cases hT
      cases eq_of_heq (HeldRel.unique_heq t₁ t₂)
      exact HEq.rfl

theorem HeldRel.unique {r : Role} {items : List (LTy V)} {ts : List V.Ty}
    (v₁ v₂ : HeldRel r items ts) : v₁ = v₂ :=
  eq_of_heq (HeldRel.unique_heq v₁ v₂)

/-- Zero-cast append of `HeldRel` views. -/
def HeldRel.append {r : Role} {as bs : List (LTy V)} {ts₁ ts₂ : List V.Ty} :
    HeldRel r as ts₁ → HeldRel r bs ts₂ → HeldRel r (as ++ bs) (ts₁ ++ ts₂)
  | .nil, vb => vb
  | .keep h va, vb => .keep h (va.append vb)
  | .drop h va, vb => .drop h (va.append vb)

/-- Zero-cast `HeldRel` for `alone r types`. -/
def HeldRel.alone (r : Role) : (types : List V.Ty) → HeldRel r (Core.alone r types) types
  | [] => .nil
  | _ :: rest => .keep (List.mem_singleton_self r) (HeldRel.alone r rest)

/-- Zero-cast `HeldRel` for types all held by `R` with `r ∈ R`. -/
def HeldRel.mapHolders (r : Role) (R : Holders) (h : r ∈ R) :
    (outs : List V.Ty) → HeldRel r (outs.map fun τ => ⟨τ, R⟩) outs
  | [] => .nil
  | _ :: rest => .keep h (HeldRel.mapHolders r R h rest)

/-- Zero-cast `HeldRel` when `r` holds none of `items`. -/
def HeldRel.allOut (r : Role) :
    (items : List (LTy V)) → (∀ a ∈ items, r ∉ a.holders) → HeldRel r items []
  | [], _ => .nil
  | a :: rest, hOut =>
      .drop (hOut a List.mem_cons_self)
        (HeldRel.allOut r rest fun b hb => hOut b (List.mem_cons_of_mem _ hb))

/-- Zero-cast `HeldRel` across `LTy.collected`. -/
def HeldRel.mapCollected {r : Role} (size : Option Nat) {each : List (LTy V)} {ts : List V.Ty} :
    HeldRel r each ts → HeldRel r (each.map (LTy.collected size)) (ts.map fun τ => .seq τ size)
  | .nil => .nil
  | .keep h tail => .keep h (tail.mapCollected size)
  | .drop h tail => .drop h (tail.mapCollected size)

/-- Zero-cast `HeldRel` across `LTy.map ρ.to`. -/
def HeldRel.mapRoleMap (ρ : RoleMap) (r : Role) {items : List (LTy V)} {ts : List V.Ty} :
    HeldRel (ρ.back r) items ts → HeldRel r (items.map (LTy.map ρ.to)) ts
  | .nil => .nil
  | .keep h tail => .keep (ρ.mem_map.mpr h) (tail.mapRoleMap ρ r)
  | .drop h tail => .drop (fun m => h (ρ.mem_map.mp m)) (tail.mapRoleMap ρ r)

/-- Zero-cast name projection along `HeldRel`. -/
def HeldRel.names {r : Role} {items : List (LTy V)} {ts : List V.Ty} :
    HeldRel r items ts → Names items → Names ts
  | .nil, .nil => .nil
  | .keep _ tail, .cons nm more => .cons nm (tail.names more)
  | .drop _ tail, .cons _ more => tail.names more

theorem HeldRel.names_cast {r : Role} {items : List (LTy V)} {ts₁ ts₂ : List V.Ty}
    (v₁ : HeldRel r items ts₁) (v₂ : HeldRel r items ts₂) (ns : Names items) :
    v₁.names ns = cast (congrArg Names (v₂.eq_held.trans v₁.eq_held.symm)) (v₂.names ns) := by
  have hT : ts₂ = ts₁ := v₂.eq_held.trans v₁.eq_held.symm
  cases hT
  rw [HeldRel.unique v₁ v₂]
  rfl

/-- Keep the names of bindings whose located type is held by `r`. -/
def heldNames (r : Role) {items : List (LTy V)} (ns : Names items) : Names (held r items) :=
  (HeldRel.ofList r items).names ns

theorem heldNames_eq_cast {r : Role} {items : List (LTy V)} {ts : List V.Ty}
    (v : HeldRel r items ts) (ns : Names items) :
    v.names ns = cast (congrArg Names v.eq_held.symm) (heldNames r ns) :=
  HeldRel.names_cast v (HeldRel.ofList r items) ns

theorem heldNames_cons_pos {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∈ a.holders) (name : Name) (more : Names rest) :
    heldNames r (HList.cons name more) =
      cast (congrArg Names (held_cons_pos r a rest h).symm)
        (HList.cons name (heldNames r more)) :=
  (HeldRel.names_cast (.keep h (HeldRel.ofList r rest)) (HeldRel.ofList r (a :: rest)) (.cons name more)).symm |>
    fun hEq => by
      have h1 := HeldRel.names_cast (HeldRel.ofList r (a :: rest)) (.keep h (HeldRel.ofList r rest)) (.cons name more)
      simpa [heldNames, HeldRel.names] using h1

theorem heldNames_cons_neg {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∉ a.holders) (name : Name) (more : Names rest) :
    heldNames r (HList.cons name more) =
      cast (congrArg Names (held_cons_neg r a rest h).symm)
        (heldNames r more) := by
  have h1 := HeldRel.names_cast (HeldRel.ofList r (a :: rest)) (.drop h (HeldRel.ofList r rest)) (.cons name more)
  simpa [heldNames, HeldRel.names] using h1

end HeldViewDef

/-! ## Context erasure (`CtxRel`), variable projection, and `LocalOp.lift` -/

section ContextErasure
variable {V : Vocabulary}

/-- Context erasure invariant: every name held by `r` in `Γ` is present in `Δ` at its plain type. -/
def CtxRel (r : Role) (Γ : Ctx (LTy V)) (Δ : Ctx V.Ty) : Prop :=
  ∀ name a, Γ.find? name = some a → r ∈ a.holders → Δ.find? name = some a.ty

theorem CtxRel.empty (r : Role) : CtxRel r (Ctx.empty : Ctx (LTy V)) (Ctx.empty : Ctx V.Ty) :=
  fun name _ h _ => nomatch (Ctx.find?_empty name).symm.trans h

theorem CtxRel.insert_held {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    (name : Name) {a : LTy V} :
    CtxRel r (Γ.insert name a) (Δ.insert name a.ty) := by
  intro name' b hΓ hr
  rw [Ctx.find?_insert] at hΓ ⊢
  by_cases same : name' = name
  · rw [ite_eq_left same] at hΓ ⊢
    cases Option.some.inj hΓ
    rfl
  · rw [ite_eq_right same] at hΓ ⊢
    exact hCtx name' b hΓ hr

theorem CtxRel.insert_unheld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    (name : Name) {a : LTy V} (hOut : r ∉ a.holders) :
    CtxRel r (Γ.insert name a) Δ := by
  intro name' b hΓ hr
  rw [Ctx.find?_insert] at hΓ
  by_cases same : name' = name
  · rw [ite_eq_left same] at hΓ
    cases Option.some.inj hΓ
    exact absurd hr hOut
  · rw [ite_eq_right same] at hΓ
    exact hCtx name' b hΓ hr

/-- Zero-cast context extension along `HeldRel`. -/
theorem CtxRel.extend_rel {r : Role} :
    ∀ {items : List (LTy V)} {ts : List V.Ty} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty},
      CtxRel r Γ Δ → (v : HeldRel r items ts) → (bound : Names items) →
      CtxRel r (Γ.extend bound) (Δ.extend (v.names bound))
  | _, _, _, _, hCtx, .nil, .nil => hCtx
  | _, _, _, _, hCtx, .keep _ tail, .cons name more =>
      CtxRel.extend_rel (hCtx.insert_held name) tail more
  | _, _, _, _, hCtx, .drop hOut tail, .cons name more =>
      CtxRel.extend_rel (hCtx.insert_unheld name hOut) tail more

theorem CtxRel.extend {r : Role} {items : List (LTy V)} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) (bound : Names items) :
    CtxRel r (Γ.extend bound) (Δ.extend (heldNames r bound)) :=
  hCtx.extend_rel (HeldRel.ofList r items) bound

theorem CtxRel.positional_alone (r : Role) (types : List V.Ty) :
    CtxRel r (Ctx.positional (alone r types)) (Ctx.positional types) := by
  intro name a hΓ _
  rw [Ctx.find?_positional] at hΓ ⊢
  rw [alone, List.getElem?_map] at hΓ
  cases hT : types[name]? with
  | none => rw [hT] at hΓ; cases hΓ
  | some τ =>
      rw [hT] at hΓ
      cases Option.some.inj hΓ
      rfl

/-- Lift a held located variable along `CtxRel` to a plain `V.Ty` variable. -/
def varHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {a : LTy V} (x : Var Γ a) (h : r ∈ a.holders) : Var Δ a.ty :=
  ⟨x.name, hCtx x.name a x.typed h⟩

/-- Zero-cast variable list projection along `HeldRel`. -/
def HeldRel.vars {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {items : List (LTy V)} {ts : List V.Ty} :
    HeldRel r items ts → HList (Var Γ) items → HList (Var Δ) ts
  | .nil, .nil => .nil
  | .keep h tail, .cons x more => .cons (varHeld hCtx x h) (tail.vars hCtx more)
  | .drop _ tail, .cons _ more => tail.vars hCtx more

/-- Lift a list of located variables to the plain variables held by `r`. -/
def varsHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {items : List (LTy V)} (xs : HList (Var Γ) items) : HList (Var Δ) (held r items) :=
  (HeldRel.ofList r items).vars hCtx xs

/-- Lift a list of variables all held by `r` to plain variables of their underlying types. -/
def varsAllHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ) :
    {items : List (LTy V)} → (∀ a, a ∈ items → r ∈ a.holders) →
    HList (Var Γ) items → HList (Var Δ) (items.map LTy.ty)
  | [], _, .nil => .nil
  | a :: _, here, .cons x rest =>
      .cons (varHeld hCtx x (here a List.mem_cons_self))
        (varsAllHeld hCtx (fun b hb => here b (List.mem_cons_of_mem _ hb)) rest)

/-- Zero-cast caller operand selection matching a callee's `HeldRel` across a `RoleMap`. -/
def HeldRel.fitVars {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    (ρ : RoleMap) {as bs : List (LTy V)} {ts : List V.Ty} :
    HeldRel (ρ.back r) bs ts → Fits as (bs.map (LTy.map ρ.to)) →
    HList (Var Γ) as → HList (Var Δ) ts
  | .nil, _, .nil => .nil
  | .keep h tail, fits, .cons x rest =>
      let hr : r ∈ _ := fits.1.2 r (ρ.mem_map.mpr h)
      let v : Var Δ _ := cast (congrArg (Var Δ) fits.1.1) (varHeld hCtx x hr)
      .cons v (tail.fitVars hCtx ρ fits.2 rest)
  | .drop _ tail, fits, .cons _ rest =>
      tail.fitVars hCtx ρ fits.2 rest
  | .keep _ _, fits, .nil => nomatch fits
  | .drop _ _, fits, .nil => nomatch fits
  | .nil, fits, .cons _ _ => nomatch fits

/-- Select and cast caller operand variables matching the callee's held ports across a `RoleMap`. -/
def fitVars {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ) (ρ : RoleMap)
    {as bs : List (LTy V)} (fits : Fits as (bs.map (LTy.map ρ.to)))
    (xs : HList (Var Γ) as) : HList (Var Δ) (held (ρ.back r) bs) :=
  (HeldRel.ofList (ρ.back r) bs).fitVars hCtx ρ fits xs

/-- Weaken a `LocalOp` from earlier function headers `fns₁` to the full program headers `fns₂`. -/
def LocalOp.lift {fns₁ fns₂ : List (FnHeader V)}
    (fnLift : ∀ {hdr}, Member fns₁ hdr → Member fns₂ hdr) :
    {ins res : List V.Ty} → LocalOp V fns₁ ins res → LocalOp V fns₂ ins res
  | _, _, .row key sig known => .row key sig known
  | _, _, .owned o => .owned o
  | _, _, .literal τ data reads => .literal τ data reads
  | _, _, .call callee => .call (fnLift callee)

end ContextErasure

/-! ## Value and environment erasure (`HeldRel.values`, `EnvRel`) -/

section ValueErasure
variable {V : Vocabulary} (M : Model V)

theorem hide_reveal {r : Role} {a : LTy V} (h : r ∈ a.holders) (v : RV M r a) :
    hide M r a (reveal M h v) = v := by
  simp [hide, reveal, h]

theorem nothing_eq {r : Role} {a : LTy V} (h : r ∉ a.holders) (v : RV M r a) :
    nothing M h = v := by
  unfold nothing
  have hRV : RV M r a = Unit := by simp [RV, h]
  have h1 : cast hRV.symm (cast hRV v) = v := by rw [cast_cast, cast_eq]
  exact (congrArg (cast hRV.symm) (rfl : () = cast hRV v)).trans h1

/-- Zero-cast value projection along `HeldRel`. -/
def HeldRel.values {r : Role} {items : List (LTy V)} {ts : List V.Ty} :
    HeldRel r items ts → HList (RV M r) items → HList M.Val ts
  | .nil, .nil => .nil
  | .keep h tail, .cons v vs => .cons (reveal M h v) (tail.values vs)
  | .drop _ tail, .cons _ vs => tail.values vs

/-- Zero-cast value reconstruction along `HeldRel`. -/
def HeldRel.unvalues {r : Role} {items : List (LTy V)} {ts : List V.Ty} :
    HeldRel r items ts → HList M.Val ts → HList (RV M r) items
  | .nil, .nil => .nil
  | .keep _ tail, .cons v vs => .cons (hide M r _ v) (tail.unvalues vs)
  | .drop h tail, vs => .cons (nothing M h) (tail.unvalues vs)

/-- Zero-cast loop-accumulator projection along `HeldRel`. -/
def HeldRel.acc {r : Role} {items : List (LTy V)} {ts : List V.Ty} :
    HeldRel r items ts → HList (fun a => List (RV M r a)) items →
    HList (fun τ => List (M.Val τ)) ts
  | .nil, .nil => .nil
  | .keep h tail, .cons xs rest => .cons (xs.map (reveal M h)) (tail.acc rest)
  | .drop _ tail, .cons _ rest => tail.acc rest

/-- Reverse each collected list into its sequence value, matching `Semantics.collected`. -/
def closedCollected (size : Option Nat) :
    {each : List V.Ty} → HList (fun τ => List (M.Val τ)) each →
    HList M.Val (each.map fun τ => .seq τ size)
  | [], .nil => .nil
  | _ :: _, .cons vs rest => .cons vs.reverse (closedCollected size rest)

/-- Reconstruct a role's located values `HList (RV M r) items` from its held plain values. -/
def unheldValues (r : Role) {items : List (LTy V)} (vs : HList M.Val (held r items)) :
    HList (RV M r) items :=
  (HeldRel.ofList r items).unvalues M vs

/-- Project a list-of-located-values loop accumulator to its held plain lists. -/
def heldAcc (r : Role) {each : List (LTy V)} (xs : HList (fun a => List (RV M r a)) each) :
    HList (fun τ => List (M.Val τ)) (held r each) :=
  (HeldRel.ofList r each).acc M xs

theorem HeldRel.values_cast {r : Role} {items : List (LTy V)} {ts₁ ts₂ : List V.Ty}
    (v₁ : HeldRel r items ts₁) (v₂ : HeldRel r items ts₂) (xs : HList (RV M r) items) :
    v₁.values M xs = cast (congrArg (HList M.Val) (v₂.eq_held.trans v₁.eq_held.symm)) (v₂.values M xs) := by
  have hT : ts₂ = ts₁ := v₂.eq_held.trans v₁.eq_held.symm
  cases hT
  rw [HeldRel.unique v₁ v₂]
  rfl

theorem HeldRel.unvalues_values {r : Role} :
    ∀ {items : List (LTy V)} {ts : List V.Ty} (v : HeldRel r items ts) (xs : HList (RV M r) items),
      v.unvalues M (v.values M xs) = xs
  | _, _, .nil, .nil => rfl
  | _, _, .keep h tail, .cons x xs => by
      change HList.cons (hide M r _ (reveal M h x)) (tail.unvalues M (tail.values M xs)) = _
      rw [hide_reveal M h x, tail.unvalues_values xs]
  | _, _, .drop h tail, .cons x xs => by
      change HList.cons (nothing M h) (tail.unvalues M (tail.values M xs)) = _
      rw [nothing_eq M h x, tail.unvalues_values xs]

theorem HeldRel.values_unvalues {r : Role} :
    ∀ {items : List (LTy V)} {ts : List V.Ty} (v : HeldRel r items ts) (xs : HList M.Val ts),
      v.values M (v.unvalues M xs) = xs
  | _, _, .nil, .nil => rfl
  | _, _, .keep h tail, .cons x xs => by
      change HList.cons (reveal M h (hide M r _ x)) (tail.values M (tail.unvalues M xs)) = _
      rw [reveal_hide, tail.values_unvalues xs]
  | _, _, .drop _ tail, xs => tail.values_unvalues xs

theorem HeldRel.values_eq_heldValues {r : Role} :
    ∀ {items : List (LTy V)} {ts : List V.Ty} (v : HeldRel r items ts) (xs : HList (RV M r) items),
      v.values M xs = cast (congrArg (HList M.Val) v.eq_held.symm) (heldValues M r xs)
  | _, _, .nil, .nil => rfl
  | a :: rest, _, .keep h tail, .cons x xs => by
      have hPos : heldValues M r (.cons x xs) =
          cast (congrArg (HList M.Val) (held_cons_pos r a rest h).symm)
            (.cons (reveal M h x) (heldValues M r xs)) := by
        change (if h' : r ∈ a.holders then _ else _) = _
        exact dite_eq_left h
      rw [hPos, HeldRel.values, tail.values_eq_heldValues xs,
        hlist_cons_cast tail.eq_held.symm, cast_cast]
  | a :: rest, _, .drop h tail, .cons x xs => by
      have hNeg : heldValues M r (.cons x xs) =
          cast (congrArg (HList M.Val) (held_cons_neg r a rest h).symm)
            (heldValues M r xs) := by
        change (if h' : r ∈ a.holders then _ else _) = _
        exact dite_eq_right h
      rw [hNeg, HeldRel.values, tail.values_eq_heldValues xs, cast_cast]

theorem HeldRel.values_ofList (r : Role) {items : List (LTy V)} (xs : HList (RV M r) items) :
    (HeldRel.ofList r items).values M xs = heldValues M r xs := by
  simpa using HeldRel.values_eq_heldValues M (HeldRel.ofList r items) xs

theorem unheldValues_heldValues (r : Role) {items : List (LTy V)} (vs : HList (RV M r) items) :
    unheldValues M r (heldValues M r vs) = vs := by
  unfold unheldValues
  rw [← HeldRel.values_ofList M r vs]
  exact (HeldRel.ofList r items).unvalues_values M vs

theorem heldValues_unheldValues (r : Role) {items : List (LTy V)} (vs : HList M.Val (held r items)) :
    heldValues M r (unheldValues M r vs) = vs := by
  unfold unheldValues
  rw [← HeldRel.values_ofList M r]
  exact (HeldRel.ofList r items).values_unvalues M vs

theorem heldValues_cons_pos {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∈ a.holders) (v : RV M r a) (vs : HList (RV M r) rest) :
    heldValues M r (HList.cons v vs) =
      cast (congrArg (HList M.Val) (held_cons_pos r a rest h).symm)
        (HList.cons (reveal M h v) (heldValues M r vs)) := by
  change (if h' : r ∈ a.holders then _ else _) = _
  exact dite_eq_left h

theorem heldValues_cons_neg {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∉ a.holders) (v : RV M r a) (vs : HList (RV M r) rest) :
    heldValues M r (HList.cons v vs) =
      cast (congrArg (HList M.Val) (held_cons_neg r a rest h).symm)
        (heldValues M r vs) := by
  change (if h' : r ∈ a.holders then _ else _) = _
  exact dite_eq_right h

theorem HeldRel.values_append {r : Role} :
    ∀ {as bs : List (LTy V)} {ts₁ ts₂ : List V.Ty}
      (va : HeldRel r as ts₁) (vb : HeldRel r bs ts₂)
      (xs : HList (RV M r) as) (ys : HList (RV M r) bs),
      (va.append vb).values M (xs.append ys) = (va.values M xs).append (vb.values M ys)
  | _, _, _, _, .nil, _, .nil, _ => rfl
  | _, _, _, _, .keep _ va, vb, .cons _ xs, ys =>
      congrArg (HList.cons _) (va.values_append vb xs ys)
  | _, _, _, _, .drop _ va, vb, .cons _ xs, ys =>
      va.values_append vb xs ys

theorem heldValues_append (r : Role) {as bs : List (LTy V)}
    (xs : HList (RV M r) as) (ys : HList (RV M r) bs) :
    heldValues M r (xs.append ys) =
      cast (congrArg (HList M.Val) (held_append r as bs).symm)
        ((heldValues M r xs).append (heldValues M r ys)) := by
  have h1 := ((HeldRel.ofList r as).append (HeldRel.ofList r bs)).values_eq_heldValues M (xs.append ys)
  rw [HeldRel.values_append, HeldRel.values_ofList, HeldRel.values_ofList] at h1
  have h2 := congrArg (cast (congrArg (HList M.Val) (held_append r as bs).symm)) h1
  simpa [cast_cast] using h2.symm

theorem HeldRel.values_aloneIn (r : Role) :
    ∀ {types : List V.Ty} (vs : HList M.Val types),
      (HeldRel.alone r types).values M (aloneIn M r vs) = vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      have ih := HeldRel.values_aloneIn r vs
      change HList.cons (reveal M (List.mem_singleton_self r) (hide M r ⟨_, [r]⟩ v))
        ((HeldRel.alone r _).values M (aloneIn M r vs)) = HList.cons v vs
      rw [reveal_hide]
      exact congrArg (HList.cons v) ih

theorem heldValues_aloneIn (r : Role) {types : List V.Ty} (vs : HList M.Val types) :
    heldValues M r (aloneIn M r vs) =
      cast (congrArg (HList M.Val) (held_alone r types).symm) vs := by
  have h := (HeldRel.alone r types).values_eq_heldValues M (aloneIn M r vs)
  rw [HeldRel.values_aloneIn] at h
  have h2 := congrArg (cast (congrArg (HList M.Val) (held_alone r types).symm)) h
  simpa [cast_cast] using h2.symm

theorem HeldRel.aloneOut_eq_values (r : Role) :
    ∀ {types : List V.Ty} (vs : HList (RV M r) (Core.alone r types)),
      aloneOut M r vs = (HeldRel.alone r types).values M vs
  | [], .nil => rfl
  | _ :: _, .cons _ vs => congrArg (HList.cons _) (HeldRel.aloneOut_eq_values r vs)

theorem aloneOut_eq_heldValues (r : Role) {types : List V.Ty} (vs : HList (RV M r) (alone r types)) :
    aloneOut M r vs = cast (congrArg (HList M.Val) (held_alone r types)) (heldValues M r vs) := by
  rw [HeldRel.aloneOut_eq_values, HeldRel.values_eq_heldValues]

theorem HeldRel.values_hideAll_located (r : Role) (R : Holders) (h : r ∈ R) :
    ∀ {outs : List V.Ty} (vs : HList M.Val outs),
      (HeldRel.mapHolders r R h outs).values M (hideAll M r (HList.located M R vs)) = vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      have ih := HeldRel.values_hideAll_located r R h vs
      change HList.cons (reveal M h (hide M r ⟨_, R⟩ v))
        ((HeldRel.mapHolders r R h _).values M (hideAll M r (HList.located M R vs))) = HList.cons v vs
      rw [reveal_hide]
      exact congrArg (HList.cons v) ih

theorem heldValues_hideAll_located (r : Role) (R : Holders) (h : r ∈ R)
    {outs : List V.Ty} (vs : HList M.Val outs) :
    heldValues M r (hideAll M r (HList.located M R vs)) =
      cast (congrArg (HList M.Val) (held_map_holders r R h outs).symm) vs := by
  have h1 := (HeldRel.mapHolders r R h outs).values_eq_heldValues M (hideAll M r (HList.located M R vs))
  rw [HeldRel.values_hideAll_located] at h1
  have h2 := congrArg (cast (congrArg (HList M.Val) (held_map_holders r R h outs).symm)) h1
  simpa [cast_cast] using h2.symm

theorem HeldRel.values_nothings (r : Role) :
    ∀ {items : List (LTy V)} (out : ∀ a, a ∈ items → r ∉ a.holders),
      (HeldRel.allOut r items out).values M (nothings M out) = .nil
  | [], _ => rfl
  | _ :: _, out => HeldRel.values_nothings r fun b hb => out b (List.mem_cons_of_mem _ hb)

theorem heldValues_nothings (r : Role) {items : List (LTy V)}
    (out : ∀ a, a ∈ items → r ∉ a.holders) :
    heldValues M r (nothings M out) =
      cast (congrArg (HList M.Val) (held_all_out r items out).symm) .nil := by
  have h1 := (HeldRel.allOut r items out).values_eq_heldValues M (nothings M out)
  rw [HeldRel.values_nothings] at h1
  have h2 := congrArg (cast (congrArg (HList M.Val) (held_all_out r items out).symm)) h1
  simpa [cast_cast] using h2.symm

theorem HeldRel.values_leaveAll (ρ : RoleMap) (r : Role) :
    ∀ {items : List (LTy V)} {ts : List V.Ty} (v : HeldRel (ρ.back r) items ts)
      (vs : HList (RV M (ρ.back r)) items),
      (v.mapRoleMap ρ r).values M (leaveAll M ρ r vs) = v.values M vs
  | _, _, .nil, .nil => rfl
  | _, _, .keep h tail, .cons x xs => by
      change HList.cons (reveal M (ρ.mem_map.mpr h) (leave M ρ r _ x))
        ((tail.mapRoleMap ρ r).values M (leaveAll M ρ r xs)) = HList.cons (reveal M h x) (tail.values M xs)
      rw [leave, dite_eq_left h, reveal_hide, tail.values_leaveAll ρ r xs]
  | _, _, .drop _ tail, .cons _ xs => tail.values_leaveAll ρ r xs

theorem heldValues_leaveAll (ρ : RoleMap) (r : Role) {items : List (LTy V)}
    (vs : HList (RV M (ρ.back r)) items) :
    heldValues M r (leaveAll M ρ r vs) =
      cast (congrArg (HList M.Val) (held_map_roleMap ρ r items).symm) (heldValues M (ρ.back r) vs) := by
  have h1 := ((HeldRel.ofList (ρ.back r) items).mapRoleMap ρ r).values_eq_heldValues M (leaveAll M ρ r vs)
  rw [HeldRel.values_leaveAll, HeldRel.values_ofList] at h1
  have h2 := congrArg (cast (congrArg (HList M.Val) (held_map_roleMap ρ r items).symm)) h1
  simpa [cast_cast] using h2.symm

theorem HeldRel.acc_empties {r : Role} :
    ∀ {each : List (LTy V)} {ts : List V.Ty} (v : HeldRel r each ts),
      v.acc M (HList.empties each) = HList.empties ts
  | _, _, .nil => rfl
  | _, _, .keep _ tail => by
      simp only [HList.empties, HeldRel.acc, List.map_nil, tail.acc_empties]
  | _, _, .drop _ tail => tail.acc_empties

theorem heldAcc_empties (r : Role) (each : List (LTy V)) :
    heldAcc M r (HList.empties each) = HList.empties (held r each) :=
  (HeldRel.ofList r each).acc_empties M

theorem HeldRel.acc_push {r : Role} :
    ∀ {each : List (LTy V)} {ts : List V.Ty} (v : HeldRel r each ts)
      (acc : HList (fun a => List (RV M r a)) each) (vs : HList (RV M r) each),
      v.acc M (acc.push vs) = (v.acc M acc).push (v.values M vs)
  | _, _, .nil, .nil, .nil => rfl
  | _, _, .keep _ tail, .cons xs acc, .cons x vs => by
      simp only [HList.push, HeldRel.acc, HeldRel.values, List.map_cons, tail.acc_push acc vs]
  | _, _, .drop _ tail, .cons _ acc, .cons _ vs => tail.acc_push acc vs

theorem heldAcc_push (r : Role) {each : List (LTy V)}
    (acc : HList (fun a => List (RV M r a)) each) (vs : HList (RV M r) each) :
    heldAcc M r (acc.push vs) = (heldAcc M r acc).push (heldValues M r vs) := by
  unfold heldAcc
  rw [(HeldRel.ofList r each).acc_push M acc vs, HeldRel.values_ofList]

theorem HeldRel.values_collected {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) (r : Role) (size : Option Nat) :
    ∀ {each : List (LTy V)} {ts : List V.Ty} (v : HeldRel r each ts)
      (acc : HList (fun a => List (RV M r a)) each),
      (v.mapCollected size).values M (Semantics.collected (roleSem M r fnTable rTable) size acc) =
        closedCollected M size (v.acc M acc)
  | _, _, .nil, .nil => rfl
  | a :: _, _, .keep h tail, .cons vs acc => by
      rw [Semantics.collected]
      change HList.cons (reveal M (a := LTy.collected size a) h (collectRV M r size a vs.reverse))
          ((tail.mapCollected size).values M (Semantics.collected (roleSem M r fnTable rTable) size acc)) = _
      rw [collectRV, dite_eq_left h, reveal_hide, List.map_reverse,
        tail.values_collected fnTable rTable r size acc]
      rfl
  | _, _, .drop _ tail, .cons _ acc => by
      rw [Semantics.collected]
      exact tail.values_collected fnTable rTable r size acc

theorem heldValues_collected {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) (r : Role) (size : Option Nat)
    {each : List (LTy V)} (acc : HList (fun a => List (RV M r a)) each) :
    heldValues M r (Semantics.collected (roleSem M r fnTable rTable) size acc) =
      cast (congrArg (HList M.Val) (held_map_collected r size each).symm)
        (closedCollected M size (heldAcc M r acc)) := by
  have h1 := ((HeldRel.ofList r each).mapCollected size).values_eq_heldValues M
    (Semantics.collected (roleSem M r fnTable rTable) size acc)
  rw [HeldRel.values_collected] at h1
  have h2 := congrArg (cast (congrArg (HList M.Val) (held_map_collected r size each).symm)) h1
  simpa [heldAcc, cast_cast] using h2.symm

theorem heldValues_split (r : Role) {as bs : List (LTy V)} (vs : HList (RV M r) (as ++ bs)) :
    (HList.split (held r as) (cast (congrArg (HList M.Val) (held_append r as bs)) (heldValues M r vs))).1 =
      heldValues M r (HList.split as vs).1 ∧
    (HList.split (held r as) (cast (congrArg (HList M.Val) (held_append r as bs)) (heldValues M r vs))).2 =
      heldValues M r (HList.split as vs).2 := by
  have hApp := heldValues_append M r (HList.split as vs).1 (HList.split as vs).2
  rw [split_append as vs] at hApp
  rw [hApp, cast_cast, cast_eq]
  have hSp : ∀ {ts₁ ts₂ : List V.Ty} (x : HList M.Val ts₁) (y : HList M.Val ts₂),
      HList.split ts₁ (x.append y) = (x, y) := by
    intro ts₁ ts₂ x y
    induction x with
    | nil => rfl
    | cons _ _ ih => simp only [HList.append, HList.split, ih]
  rw [hSp]
  exact ⟨rfl, rfl⟩

/-- Environment erasure invariant corresponding to `CtxRel`. -/
def EnvRel (r : Role) {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    (env : Env (RV M r) Γ) (cenv : Env M.Val Δ) : Prop :=
  ∀ name a (hΓ : Γ.find? name = some a) (hr : r ∈ a.holders),
    cenv name a.ty (hCtx name a hΓ hr) = reveal M hr (env name a hΓ)

theorem EnvRel.empty (r : Role) :
    EnvRel M r (CtxRel.empty r) Env.empty Env.empty :=
  fun name _ hΓ _ => nomatch (Ctx.find?_empty name).symm.trans hΓ

theorem EnvRel.insert_held {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (name : Name) {a : LTy V} (hr : r ∈ a.holders)
    (v : RV M r a) :
    EnvRel M r (hCtx.insert_held name) (env.insert name v) (cenv.insert name (reveal M hr v)) := by
  intro name' b hΓ hrb
  by_cases same : name' = name
  · have hEq : a = b := by
      rw [Ctx.find?_insert, ite_eq_left same] at hΓ
      exact Option.some.inj hΓ
    subst hEq
    have h1 := Env.insert_at_bound cenv name (reveal M hr v) same (hCtx.insert_held name name' a hΓ hrb)
    have h2 := Env.insert_at_bound env name v same hΓ
    rw [eq_of_heq h1, eq_of_heq h2]
  · rw [Env.insert_at_other cenv name (reveal M hr v) same, Env.insert_at_other env name v same]
    exact hEnv name' b _ hrb

theorem EnvRel.insert_unheld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (name : Name) {a : LTy V} (hOut : r ∉ a.holders)
    (v : RV M r a) :
    EnvRel M r (hCtx.insert_unheld name hOut) (env.insert name v) cenv := by
  intro name' b hΓ hrb
  by_cases same : name' = name
  · have hEq : a = b := by
      rw [Ctx.find?_insert, ite_eq_left same] at hΓ
      exact Option.some.inj hΓ
    subst hEq
    exact absurd hrb hOut
  · rw [Env.insert_at_other env name v same]
    exact hEnv name' b _ hrb

theorem env_extend_cast {T : Type} {Val : T → Type} {Δ : Ctx T} (env : Env Val Δ)
    {as bs : List T} (h : as = bs) (ns : Names as) (vs : HList Val as) :
    HEq (env.extend (cast (congrArg Names h) ns) (cast (congrArg (HList Val) h) vs))
      (env.extend ns vs) := by
  subst h; exact HEq.rfl

/-- Zero-cast environment extension along `HeldRel`. -/
theorem EnvRel.extend_rel {r : Role} :
    ∀ {items : List (LTy V)} {ts : List V.Ty} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
      {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ},
      EnvRel M r hCtx env cenv → (v : HeldRel r items ts) →
      (bound : Names items) → (vs : HList (RV M r) items) →
      EnvRel M r (hCtx.extend_rel v bound) (env.extend bound vs)
        (cenv.extend (v.names bound) (v.values M vs))
  | _, _, _, _, _, _, _, hEnv, .nil, .nil, .nil => hEnv
  | _, _, _, _, _, _, _, hEnv, .keep h tail, .cons name more, .cons x moreV =>
      EnvRel.extend_rel (hEnv.insert_held M name h x) tail more moreV
  | _, _, _, _, _, _, _, hEnv, .drop hOut tail, .cons name more, .cons x moreV =>
      EnvRel.extend_rel (hEnv.insert_unheld M name hOut x) tail more moreV

theorem EnvRel.extend {r : Role} {items : List (LTy V)} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (bound : Names items) (vs : HList (RV M r) items) :
    EnvRel M r (hCtx.extend bound) (env.extend bound vs)
      (cenv.extend (heldNames r bound) (heldValues M r vs)) := by
  have h := hEnv.extend_rel M (HeldRel.ofList r items) bound vs
  rwa [HeldRel.values_ofList] at h

theorem EnvRel.positional_alone (r : Role) {types : List V.Ty} (vs : HList M.Val types) :
    EnvRel M r (CtxRel.positional_alone r types) (Env.positional (aloneIn M r vs)) (Env.positional vs) := by
  have hExt : ∀ (start : Nat) {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
      (env : Env (RV M r) Γ) (cenv : Env M.Val Δ),
      EnvRel M r hCtx env cenv →
      ∀ {ts : List V.Ty} (ws : HList M.Val ts)
        (hCtx' : CtxRel r (Γ.extend (Names.counting start (alone r ts))) (Δ.extend (Names.counting start ts))),
        EnvRel M r hCtx'
          (env.extend (Names.counting start (alone r ts)) (aloneIn M r ws))
          (cenv.extend (Names.counting start ts) ws) := by
    intro start Γ Δ hCtx env cenv hEnv ts ws
    induction ws generalizing start Γ Δ with
    | nil => intro _; exact hEnv
    | cons v rest ih =>
        intro hCtx'
        have hIns : EnvRel M r (hCtx.insert_held start)
            (env.insert start (hide M r ⟨_, [r]⟩ v))
            (cenv.insert start v) := by
          have h := hEnv.insert_held M start (a := ⟨_, [r]⟩) List.mem_cons_self (hide M r ⟨_, [r]⟩ v)
          rwa [reveal_hide] at h
        exact ih (start + 1) (hCtx.insert_held start) _ _ hIns hCtx'
  exact hExt 0 (CtxRel.empty r) Env.empty Env.empty (EnvRel.empty M r) vs (CtxRel.positional_alone r types)

theorem env_get_varHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) {a : LTy V} (x : Var Γ a) (h : r ∈ a.holders) :
    cenv.get (varHeld hCtx x h) = reveal M h (env.get x) :=
  hEnv x.name a x.typed h

/-- Zero-cast evaluation of `HeldRel.vars` under `EnvRel`. -/
theorem env_all_vars_rel {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) :
    ∀ {items : List (LTy V)} {ts : List V.Ty} (v : HeldRel r items ts) (xs : HList (Var Γ) items),
      cenv.all (v.vars hCtx xs) = v.values M (env.all xs)
  | _, _, .nil, .nil => rfl
  | _, _, .keep h tail, .cons x xs => by
      simp only [HeldRel.vars, Env.all, HeldRel.values, env_get_varHeld M hEnv x h,
        env_all_vars_rel hEnv tail xs]
  | _, _, .drop _ tail, .cons _ xs => env_all_vars_rel hEnv tail xs

theorem env_all_varsHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) {items : List (LTy V)} (xs : HList (Var Γ) items) :
    cenv.all (varsHeld hCtx xs) = heldValues M r (env.all xs) := by
  unfold varsHeld
  rw [env_all_vars_rel M hEnv (HeldRel.ofList r items) xs, HeldRel.values_ofList]

theorem env_all_varsAllHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) :
    ∀ {items : List (LTy V)} (here : ∀ a, a ∈ items → r ∈ a.holders) (xs : HList (Var Γ) items),
      cenv.all (varsAllHeld hCtx here xs) = HList.ofLocated M (revealAll M here (env.all xs))
  | [], _, .nil => rfl
  | a :: rest, here, .cons x xs => by
      simp only [varsAllHeld, Env.all, revealAll, HList.ofLocated,
        env_get_varHeld M hEnv x (here a List.mem_cons_self),
        env_all_varsAllHeld hEnv (fun b hb => here b (List.mem_cons_of_mem _ hb)) xs]

theorem env_all_fitVars_rel {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (ρ : RoleMap) :
    ∀ {as bs : List (LTy V)} {ts : List V.Ty} (v : HeldRel (ρ.back r) bs ts)
      (fits : Fits as (bs.map (LTy.map ρ.to))) (xs : HList (Var Γ) as),
      cenv.all (v.fitVars hCtx ρ fits xs) =
        v.values M (enterAll M ρ r (fitAllRV M fits (env.all xs)))
  | _, _, _, .nil, _, .nil => rfl
  | _ :: _, b :: _, _, .keep h tail, fits, .cons x xs => by
      have h' : r ∈ (b.map ρ.to).holders := ρ.mem_map.mpr h
      change HList.cons (cenv.get _) (cenv.all (tail.fitVars hCtx ρ fits.2 xs)) =
        HList.cons (reveal M h (enter M ρ r b (coverRV M fits.1 (env.get x))))
          (tail.values M (enterAll M ρ r (fitAllRV M fits.2 (env.all xs))))
      rw [enter, coverRV, dite_eq_left h, dite_eq_left h', reveal_hide, reveal_hide,
        env_all_fitVars_rel hEnv ρ tail fits.2 xs]
      congr 1
      unfold cover
      have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (w : Var Δ τ₁),
          cenv.get (cast (congrArg (Var Δ) e) w) = cast (congrArg M.Val e) (cenv.get w) := by
        intro _ _ e _; subst e; rfl
      rw [hc fits.1.1, env_get_varHeld M hEnv x]
  | _, _, _, .drop _ tail, fits, .cons _ xs =>
      env_all_fitVars_rel hEnv ρ tail fits.2 xs
  | _, _, _, .keep _ _, fits, .nil => nomatch fits
  | _, _, _, .drop _ _, fits, .nil => nomatch fits
  | _, _, _, .nil, fits, .cons _ _ => nomatch fits

theorem env_all_fitVars {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (ρ : RoleMap)
    {as bs : List (LTy V)} (fits : Fits as (bs.map (LTy.map ρ.to)))
    (xs : HList (Var Γ) as) :
    cenv.all (fitVars hCtx ρ fits xs) =
      heldValues M (ρ.back r) (enterAll M ρ r (fitAllRV M fits (env.all xs))) := by
  unfold fitVars
  rw [env_all_fitVars_rel M hEnv ρ (HeldRel.ofList (ρ.back r) bs) fits xs, HeldRel.values_ofList]

end ValueErasure

end Zkc.Core
