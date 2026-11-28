module

public import Zkc.Core.World.Stack
public import Zkc.Core.Scheme.Identity

@[expose] public section

/-!
Core IR term-building combinators for handler layers: byte-sequence literals, positional contexts,
`FreshFrom` name allocation, `letOp1`/`letOp2`, statement input positioning, and typed/safe
function references (`TypedFnRef`, `SafeFnRef`).
-/

namespace Zkc.Core

namespace LayerBuild

/-! ## Byte-sequence literals in every vocabulary -/

/-- A byte type (`fin 256`), available in every vocabulary. -/
abbrev byteTy {V : Vocabulary} : V.Ty := .fin 256

/-- An unsized sequence of bytes (`[byte]`), available in every vocabulary. -/
abbrev bytesTy {V : Vocabulary} : V.Ty := .seq (.fin 256) none

private theorem scanMany_byte {V : Vocabulary} :
    ∀ (bs : List Nat), (∀ b, b ∈ bs → b < 256) →
      scanMany (Ty.scan V byteTy) bs.length bs = some []
  | [], _ => rfl
  | b :: bs, h => by
      have hb : b < 256 := h b List.mem_cons_self
      have hbs : ∀ x, x ∈ bs → x < 256 := fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [List.length_cons, scanMany, Ty.scan, byteTy, hb, ↓reduceIte, Option.bind_some]
      exact scanMany_byte bs hbs

/-- Any list of bytes (`< 256`), length-prefixed, reads as a literal of `bytesTy`. -/
theorem bytesLiteral_reads {V : Vocabulary} (bs : List Nat) (h : ∀ b, b ∈ bs → b < 256) :
    V.Reads bytesTy (bs.length :: bs) :=
  scanMany_byte bs h

private theorem readMany_byte {V : Vocabulary} (M : Model V) :
    ∀ (bs : List Nat), (∀ b, b ∈ bs → b < 256) →
      readMany (Ty.read M byteTy) bs.length bs = some (bs, [])
  | [], _ => rfl
  | b :: bs, h => by
      have hb : b < 256 := h b List.mem_cons_self
      have hbs : ∀ x, x ∈ bs → x < 256 := fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [List.length_cons, readMany, Ty.read, byteTy, hb, ↓reduceIte, Option.bind_some,
        readMany_byte M bs hbs, Option.map_some]

/-- Evaluating a byte-sequence literal recovers the exact byte list `bs`. -/
theorem bytesLiteral_val {V : Vocabulary} (M : Model V) (bs : List Nat)
    (h : ∀ b, b ∈ bs → b < 256) :
    Ty.readLiteral M bytesTy (bs.length :: bs) (bytesLiteral_reads bs h) = bs := by
  have hr := Ty.read_readLiteral M bytesTy (bs.length :: bs) (bytesLiteral_reads bs h)
  have heq : Ty.read M bytesTy (bs.length :: bs) = some (bs, []) := readMany_byte M bs h
  rw [heq] at hr
  exact (Prod.mk.inj (Option.some.inj hr)).1.symm

/-! ## Positional context, fresh-name, and term-building combinators -/

/-- A context has no binding at or above `n`. -/
def FreshFrom {T : Type} (Γ : Ctx T) (n : Nat) : Prop :=
  ∀ k, n ≤ k → Γ.find? k = none

theorem positional_freshFrom {T : Type} (types : List T) :
    FreshFrom (Ctx.positional types) types.length := by
  intro k hk
  rw [Ctx.find?_positional]
  exact List.getElem?_eq_none hk

theorem FreshFrom.insert {T : Type} {Γ : Ctx T} {n : Nat} (h : FreshFrom Γ n) (τ : T) :
    FreshFrom (Γ.insert n τ) (n + 1) := by
  intro k hk
  rw [Ctx.find?_insert]
  have hne : k ≠ n := by omega
  rw [ite_eq_right hne]
  exact h k (by omega)

theorem FreshFrom.within {T : Type} {Γ : Ctx T} {n : Nat} (h : FreshFrom Γ n) (τ : T) :
    Γ.Within (Γ.insert n τ) :=
  Ctx.Within.fresh (h n (Nat.le_refl n)) τ

/-- The variable just bound at name `n` in `Γ.insert n τ`. -/
def freshVar {T : Type} (Γ : Ctx T) (n : Nat) (τ : T) : Var (Γ.insert n τ) τ :=
  ⟨n, by rw [Ctx.find?_insert, ite_eq_left rfl]⟩

/-- Look up positional variable `i` from a proof that `types[i]? = some τ`. -/
def posVar {T : Type} (types : List T) (i : Nat) {τ : T} (h : types[i]? = some τ) :
    Var (Ctx.positional types) τ :=
  ⟨i, by rw [Ctx.find?_positional]; exact h⟩

/-- Look up positional variable `i` in `Ctx.positional (alone r types)`, keeping the equality proof
explicitly typed at `(alone r types)[i]? = some ⟨τ, [r]⟩` so downstream rewrites stay well-typed
under `implicit` transparency. -/
def alonePosVar {V : Vocabulary} (r : Role) (types : List V.Ty) (i : Nat) {τ : V.Ty}
    (h : types[i]? = some τ) : Var (Ctx.positional (alone r types)) ⟨τ, [r]⟩ :=
  posVar (alone r types) i (by simp [alone, h])

/-- `FreshFrom` for `Ctx.positional (alone r types)` stated at `types.length` rather than
`(alone r types).length`, keeping clause terms well-typed under `implicit` transparency. -/
theorem alone_positional_freshFrom {V : Vocabulary} (r : Role) (types : List V.Ty) :
    FreshFrom (Ctx.positional (alone r types)) types.length := by
  simpa [alone] using positional_freshFrom (alone r types)

theorem env_get_insert_self {T : Type} {V : T → Type} {Γ : Ctx T}
    (env : Env V Γ) (n : Nat) {τ : T} (v : V τ) :
    (env.insert n v).get (freshVar Γ n τ) = v :=
  eq_of_heq (Env.insert_at_bound env n v rfl (freshVar Γ n τ).typed)

theorem env_get_insert_reindex {T : Type} {V : T → Type} {Γ : Ctx T}
    (env : Env V Γ) {n : Nat} (h : FreshFrom Γ n) {τ σ : T} (v : V τ) (x : Var Γ σ) :
    (env.insert n v).get (x.reindex (h.within τ)) = env.get x := by
  have hne : x.name ≠ n := by
    intro heq
    have hnone : Γ.find? x.name = none := h x.name (Nat.le_of_eq heq.symm)
    have hx := x.typed
    rw [hnone] at hx
    cases hx
  show env.insert n v x.name σ (h.within τ x.name σ x.typed) = env x.name σ x.typed
  rw [Env.insert_at_other env n v hne]

/-- Emit a single-result `.op` binding fresh name `n` and pass the extended context, freshness
proof, weakening proof, and bound variable to the continuation. -/
def letOp1 {D : Dialect} {Γ : Ctx D.Ty} {ins outs : List D.Ty} {τ : D.Ty}
    (key : Key) (o : D.Op ins [τ]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx D.Ty) → FreshFrom Γ' (n + 1) → Γ.Within Γ' → Var Γ' τ → Term D Γ' outs) :
    Term D Γ outs :=
  .op key o operands (.cons n .nil)
    (rest (Γ.insert n τ) (hfresh.insert τ) (hfresh.within τ) (freshVar Γ n τ))

/-- Emit a two-result `.op` binding fresh names `n` and `n + 1`. -/
def letOp2 {D : Dialect} {Γ : Ctx D.Ty} {ins outs : List D.Ty} {τ₁ τ₂ : D.Ty}
    (key : Key) (o : D.Op ins [τ₁, τ₂]) (operands : HList (Var Γ) ins) (n : Name)
    (hfresh : FreshFrom Γ n)
    (rest : (Γ' : Ctx D.Ty) → FreshFrom Γ' (n + 2) → Γ.Within Γ' →
      Var Γ' τ₁ → Var Γ' τ₂ → Term D Γ' outs) :
    Term D Γ outs :=
  let Γ1 := Γ.insert n τ₁
  let h1 := hfresh.insert τ₁
  let w01 := hfresh.within τ₁
  let w12 := h1.within τ₂
  .op key o operands (.cons n (.cons (n + 1) .nil))
    (rest (Γ1.insert (n + 1) τ₂) (h1.insert τ₂) (w01.trans w12)
      ((freshVar Γ n τ₁).reindex w12) (freshVar Γ1 (n + 1) τ₂))

/-! ## Statement input positions inside `held r ins` -/

/-- A statement input of `hdr.ins` (held by both `prover` and `verifier`), together with its
position in `held r ins` and its index among statement inputs. -/
structure StmtPos (V : Vocabulary) (r : Role) (ins : List (LTy V)) where
  stmtIndex : Nat
  heldIndex : Nat
  ty : V.Ty
  atHeld : (held r ins)[heldIndex]? = some ty

/-- Positions of all statement inputs inside `held r ins`, with proofs of their types. -/
def statementPositions {V : Vocabulary} (r prover verifier : Role) (hr : r = prover ∨ r = verifier)
    (ins : List (LTy V)) : List (StmtPos V r ins) :=
  go 0 ins
where
  go (sIdx : Nat) : (xs : List (LTy V)) → List (StmtPos V r xs)
    | [] => []
    | a :: rest =>
        if hBoth : prover ∈ a.holders ∧ verifier ∈ a.holders then
          have hrIn : r ∈ a.holders := by rcases hr with rfl | rfl; exact hBoth.1; exact hBoth.2
          let here : StmtPos V r (a :: rest) :=
            ⟨sIdx, 0, a.ty, by simp [held, hrIn]⟩
          let later := (go (sIdx + 1) rest).map fun p =>
            ⟨p.stmtIndex, p.heldIndex + 1, p.ty, by simp [held, hrIn, p.atHeld]⟩
          here :: later
        else if hrIn : r ∈ a.holders then
          (go sIdx rest).map fun p =>
            ⟨p.stmtIndex, p.heldIndex + 1, p.ty, by simp [held, hrIn, p.atHeld]⟩
        else
          (go sIdx rest).map fun p =>
            ⟨p.stmtIndex, p.heldIndex, p.ty, by simp [held, hrIn, p.atHeld]⟩

/-! ## Typed function references for Suite and Layout -/

/-- Reference to a total unconditional function in `fns` with exact input and output types. -/
structure TypedFnRef (V : Vocabulary) (fns : List (FnHeader V)) (ins outs : List V.Ty) where
  hdr : FnHeader V
  member : Member fns hdr
  insEq : hdr.ins = ins
  outsEq : hdr.outs = outs
  uncond : hdr.summary.requires = []
  canStopFalse : hdr.canStop = false

/-- Reference to a potentially-rejecting unconditional function in `fns`
(e.g. `LayoutSlot.read`, `recover`). -/
structure SafeFnRef (V : Vocabulary) (fns : List (FnHeader V)) (ins outs : List V.Ty) where
  hdr : FnHeader V
  member : Member fns hdr
  insEq : hdr.ins = ins
  outsEq : hdr.outs = outs
  uncond : hdr.summary.requires = []

/-- Emit a call to a `TypedFnRef` in `localDialect`. -/
def callLocal {V : Vocabulary} {fns : List (FnHeader V)} {ins outs : List V.Ty}
    (ref : TypedFnRef V fns ins outs) : LocalOp V fns ins outs :=
  cast (by rw [ref.insEq, ref.outsEq]) (LocalOp.call ref.member)

/-- Emit a call to a `SafeFnRef` in `localDialect`. -/
def callLocalSafe {V : Vocabulary} {fns : List (FnHeader V)} {ins outs : List V.Ty}
    (ref : SafeFnRef V fns ins outs) : LocalOp V fns ins outs :=
  cast (by rw [ref.insEq, ref.outsEq]) (LocalOp.call ref.member)

/-- Evaluate a `TypedFnRef` directly in `fnTable`. -/
def TypedFnRef.eval {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} {ins outs : List V.Ty}
    (ref : TypedFnRef V fns ins outs) (fnTable : FnTable M fns) (args : HList M.Val ins) :
    Local (HList M.Val outs) :=
  localOp M fnTable (callLocal ref) args

/-- Evaluate a `SafeFnRef` directly in `fnTable`. -/
def SafeFnRef.eval {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} {ins outs : List V.Ty}
    (ref : SafeFnRef V fns ins outs) (fnTable : FnTable M fns) (args : HList M.Val ins) :
    Local (HList M.Val outs) :=
  localOp M fnTable (callLocalSafe ref) args

theorem alone_map_ty {V : Vocabulary} (r : Role) (tys : List V.Ty) :
    (alone r tys).map (·.ty) = tys := by
  simp [alone, Function.comp_def]

theorem alone_mem_holders {V : Vocabulary} (r : Role) (tys : List V.Ty) :
    ∀ a, a ∈ alone r tys → r ∈ a.holders := by
  intro a ha
  simp only [alone, List.mem_map] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact List.mem_singleton_self r

/-- Lift any `LocalOp` to a `RoleOp` at role `r` on `alone r ins`. -/
def computeAlone {V : Vocabulary} {hs : Headers V} (r : Role) {ins outs : List V.Ty}
    (o : LocalOp V hs.fns ins outs) : RoleOp V hs r (alone r ins) (alone r outs) :=
  .compute [r] o (alone r ins) (alone_map_ty r ins) (List.mem_singleton_self r)
    (alone_mem_holders r ins)


end LayerBuild

end Zkc.Core
