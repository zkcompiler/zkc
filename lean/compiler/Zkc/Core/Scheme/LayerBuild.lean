module

public import Zkc.Core.World.Stack
public import Zkc.Core.Scheme.Identity

@[expose] public section

/-!
Typed `Core.Layer` IR term builders and their denotation and event-key lemmas.

Every generated layer (`samples`, `construction`, `idealConstruction`, `layout`) is constructed
here as checked Core IR (`Term (localDialect ...)` and `Term (roleDialect ...)`):
- only total `OwnedOp`s (`makeSeq`, `seqUnsized`, `seqConcat`, `seqLength`, `natEqual`,
  `boolEqual`, `finToNat`, `makeTuple`, `getTuple`, `takeTuple`), `.guard ... .reject`, and calls
  to admitted unconditional functions in `a.program` are emitted, so no generated layer can ever
  stop `.undefined`;
- byte sequences (`sessionId`, site labels) are embedded as single `LocalOp.literal` instructions
  at type `.seq (.fin 256) none`.
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

/-! ## `start`, `again`, `finish` term builders (`localDialect`) -/

/-- Standard `again` term that restores the layer state to its value at attempt entry (`var 1`). -/
def restoreAgain {V : Vocabulary} {fns : List (FnHeader V)} (state : V.Ty) :
    Term (localDialect V fns) (Ctx.positional [.nat, state, state]) [state] :=
  .ret (.cons (posVar ([.nat, state, state] : List V.Ty) 1 rfl) .nil)

/-- Convert a `List V.Ty` to `Tys V.TypeKey`. -/
def tysOfList {V : Vocabulary} : List V.Ty → Tys V.TypeKey
  | [] => .nil
  | t :: ts => .cons t (tysOfList ts)

theorem tysOfList_toList {V : Vocabulary} : ∀ (ts : List V.Ty), (tysOfList ts).toList = ts
  | [] => rfl
  | _ :: ts => congrArg _ (tysOfList_toList ts)

/-- Build positional variables `0, 1, ..., types.length - 1` in `Ctx.positional types`. -/
def positionalVars {T : Type} : (types : List T) → {Γ : Ctx T} →
    (start : Nat) → (∀ k a, types[k]? = some a → Γ.find? (start + k) = some a) →
    HList (Var Γ) types
  | [], _, _, _ => .nil
  | a :: as, _, start, hΓ =>
      .cons ⟨start, hΓ 0 a rfl⟩
        (positionalVars as (start + 1) fun k b hb => by
          have := hΓ (k + 1) b hb
          rwa [show start + (k + 1) = start + 1 + k by omega] at this)

/-- State tuple types for `samples derived by`:
`(attemptNum : nat, callSeq : nat, proverHeld : tuple (held prover ins))`. -/
abbrev samplesStateTys {V : Vocabulary} (heldP : List V.Ty) : Tys V.TypeKey :=
  .cons .nat (.cons .nat (.cons (.tuple (tysOfList heldP)) .nil))

abbrev samplesStateTy {V : Vocabulary} (heldP : List V.Ty) : V.Ty :=
  .tuple (samplesStateTys heldP)

/-- `again` term for `samples derived by`: advances `attemptNum` to the new attempt (`var 0`),
while preserving the monotonically growing `callSeq` and `proverHeld` tuple from `stopState`
(`var 2`), preventing nonce reuse across retries and retries inside loops. -/
def samplesAgain {V : Vocabulary} {fns : List (FnHeader V)} (heldP : List V.Ty)
    (htfree : Tys.anyLinear V (samplesStateTys heldP) = false) :
    Term (localDialect V fns)
      (Ctx.positional [.nat, samplesStateTy heldP, samplesStateTy heldP])
      [samplesStateTy heldP] :=
  let stTy := samplesStateTy heldP
  let tys : List V.Ty := [.nat, stTy, stTy]
  let attVar : Var (Ctx.positional tys) .nat := posVar tys 0 rfl
  let stopVar : Var (Ctx.positional tys) stTy := posVar tys 2 rfl
  letOp1 ⟨0⟩ (.owned (.getTuple (samplesStateTys heldP) (.tail .head) htfree))
      (.cons stopVar .nil) 3 (positional_freshFrom tys) fun _ h1 w01 seqVar =>
  letOp1 ⟨1⟩ (.owned (.getTuple (samplesStateTys heldP) (.tail (.tail .head)) htfree))
      (.cons (stopVar.reindex w01) .nil) 4 h1 fun _ h2 w12 heldVar =>
  letOp1 ⟨2⟩ (.owned (.makeTuple (samplesStateTys heldP)))
      (.cons (attVar.reindex (w01.trans w12)) (.cons (seqVar.reindex w12) (.cons heldVar .nil)))
      5 h2 fun _ _ _ nextStVar =>
  .ret (.cons nextStVar .nil)

/-- `finish` term returning nothing. -/
def emptyFinish {V : Vocabulary} {fns : List (FnHeader V)} (state : V.Ty) :
    Term (localDialect V fns) (Ctx.positional [state]) [] :=
  .ret .nil

/-- `finish` term returning the layer's final state (`var 0`). -/
def identityFinish {V : Vocabulary} {fns : List (FnHeader V)} (state : V.Ty) :
    Term (localDialect V fns) (Ctx.positional [state]) [state] :=
  .ret (.cons (posVar [state] 0 rfl) .nil)

/-- A statement input together with its encoder function and domain label bytes. -/
structure StmtAbsorbItem (V : Vocabulary) (fns : List (FnHeader V)) (unitTy : V.Ty)
    (Γ : Ctx V.Ty) where
  ty : V.Ty
  input : Var Γ ty
  label : List Nat
  labelBytes : ∀ b, b ∈ label → b < 256
  encode : TypedFnRef V fns [ty] [.seq unitTy none]

/-- Fold statement absorptions in `localDialect`, starting from `stVar` in context `Γ` with all
names `< fresh`. -/
def buildAbsorbChain {V : Vocabulary} {fns : List (FnHeader V)} {stateTy unitTy : V.Ty}
    (absorbRef : TypedFnRef V fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    {Γ : Ctx V.Ty} → (fresh : Nat) → FreshFrom Γ fresh →
    Var Γ stateTy → (items : List (StmtAbsorbItem V fns unitTy Γ)) →
    Term (localDialect V fns) Γ [stateTy]
  | _, _, _, stVar, [] => .ret (.cons stVar .nil)
  | _, fresh, hfresh, stVar, item :: rest =>
      letOp1 ⟨fresh⟩ (.literal bytesTy (item.label.length :: item.label)
          (bytesLiteral_reads item.label item.labelBytes)) .nil fresh hfresh fun _ h1 w01 lblVar =>
      letOp1 ⟨fresh + 1⟩ (callLocal item.encode) (.cons (item.input.reindex w01) .nil)
          (fresh + 1) h1 fun _ h2 w12 encVar =>
      letOp1 ⟨fresh + 2⟩ (callLocal absorbRef)
          (.cons (stVar.reindex (w01.trans w12)) (.cons (lblVar.reindex w12) (.cons encVar .nil)))
          (fresh + 2) h2 fun _ h3 w23 nextStVar =>
      let w03 := (w01.trans w12).trans w23
      let rest' := rest.map fun it =>
        ⟨it.ty, it.input.reindex w03, it.label, it.labelBytes, it.encode⟩
      buildAbsorbChain absorbRef (fresh + 3) h3 nextStVar rest'
termination_by _ _ _ _ items => items.length
decreasing_by simp

/-- Build `construction.start`: initialize transcript with `sessionBytes` via `startRef`, then
absorb every statement input in order via `absorbRef`. -/
def constructionStart {V : Vocabulary} {fns : List (FnHeader V)} {stateTy unitTy : V.Ty}
    {r : Role} {ins : List (LTy V)}
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (startRef : TypedFnRef V fns [bytesTy] [stateTy])
    (absorbRef : TypedFnRef V fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (items : List (StmtAbsorbItem V fns unitTy (Ctx.positional (held r ins)))) :
    Term (localDialect V fns) (Ctx.positional (held r ins)) [stateTy] :=
  let base := (held r ins).length
  letOp1 ⟨0⟩ (.literal bytesTy (sessionBytes.length :: sessionBytes)
      (bytesLiteral_reads sessionBytes hsess)) .nil base (positional_freshFrom (held r ins))
      fun _ h1 w01 sessVar =>
  letOp1 ⟨1⟩ (callLocal startRef) (.cons sessVar .nil) (base + 1) h1 fun _ h2 w12 st0Var =>
  let w02 := w01.trans w12
  let items' := items.map fun it =>
    ⟨it.ty, it.input.reindex w02, it.label, it.labelBytes, it.encode⟩
  buildAbsorbChain absorbRef (base + 2) h2 st0Var items'

/-- Build `layoutP.start`: empty proof buffer `[] : [unitTy]`. -/
def layoutPStart {V : Vocabulary} {fns : List (FnHeader V)} {r : Role} {ins : List (LTy V)}
    (unitTy : V.Ty) :
    Term (localDialect V fns) (Ctx.positional (held r ins)) [.seq unitTy none] :=
  let base := (held r ins).length
  letOp1 ⟨0⟩ (.owned (.makeSeq unitTy 0)) .nil base (positional_freshFrom (held r ins))
      fun _ h1 _ v0 =>
  letOp1 ⟨1⟩ (.owned (.seqUnsized unitTy 0)) (.cons v0 .nil) (base + 1) h1 fun _ _ _ v1 =>
  .ret (.cons v1 .nil)

/-- Streaming verifier layout state type: `(proof : [unitTy], offset : nat)`. -/
abbrev streamStateTys {V : Vocabulary} (unitTy : V.Ty) : Tys V.TypeKey :=
  .cons (.seq unitTy none) (.cons .nat .nil)

abbrev streamStateTy {V : Vocabulary} (unitTy : V.Ty) : V.Ty :=
  .tuple (streamStateTys unitTy)

/-- Build `layoutV.start`: initialize streaming cursor `(proof, 0)`. -/
def layoutVStart {V : Vocabulary} {fns : List (FnHeader V)} {r : Role} {ins : List (LTy V)}
    (unitTy : V.Ty) :
    Term (localDialect V fns) (Ctx.positional (.seq unitTy none :: held r ins))
      [streamStateTy unitTy] :=
  let tys := .seq unitTy none :: held r ins
  let base := tys.length
  let proofVar : Var (Ctx.positional tys) (.seq unitTy none) := posVar tys 0 rfl
  letOp1 ⟨0⟩ (.literal .nat [0] rfl) .nil base (positional_freshFrom tys) fun _ h1 w01 zeroVar =>
  letOp1 ⟨1⟩ (.owned (.makeTuple (streamStateTys unitTy)))
      (.cons (proofVar.reindex w01) (.cons zeroVar .nil)) (base + 1) h1 fun _ _ _ stVar =>
  .ret (.cons stVar .nil)

/-- Build `layoutV.finish`: reject any proof with trailing unread bytes (`offset != length(buf)`). -/
def layoutVFinish {V : Vocabulary} {fns : List (FnHeader V)} (unitTy : V.Ty)
    (hfree : Ty.isLinear V unitTy = false) (guardKey : Key) :
    Term (localDialect V fns) (Ctx.positional [streamStateTy unitTy]) [] :=
  have htfree : Tys.anyLinear V (streamStateTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  let stTy := streamStateTy unitTy
  let stVar : Var (Ctx.positional [stTy]) stTy := posVar [stTy] 0 rfl
  letOp1 ⟨0⟩ (.owned (.getTuple (streamStateTys unitTy) .head htfree))
      (.cons stVar .nil) 1 (positional_freshFrom [stTy]) fun _ h1 w01 bufVar =>
  letOp1 ⟨1⟩ (.owned (.getTuple (streamStateTys unitTy) (.tail .head) htfree))
      (.cons (stVar.reindex w01) .nil) 2 h1 fun _ h2 w12 offVar =>
  letOp1 ⟨2⟩ (.owned (.seqLength unitTy none hfree))
      (.cons (bufVar.reindex w12) .nil) 3 h2 fun _ h3 w23 lenVar =>
  letOp1 ⟨3⟩ (.owned .natEqual)
      (.cons (offVar.reindex w23) (.cons lenVar .nil)) 4 h3 fun _ _ _ eqVar =>
  .guard guardKey () eqVar rfl .reject <|
  .ret .nil

/-- Initial state `(0, 0, proverHeld)` for `samples derived by` layer, capturing all prover secret
and statement inputs from `Ctx.positional (held r ins)`. -/
def samplesStart {V : Vocabulary} {fns : List (FnHeader V)} {r : Role} {ins : List (LTy V)} :
    Term (localDialect V fns) (Ctx.positional (held r ins)) [samplesStateTy (held r ins)] :=
  let heldP := held r ins
  let base := heldP.length
  let inVars : HList (Var (Ctx.positional heldP)) heldP :=
    positionalVars heldP 0 fun k a ha => by rw [Ctx.find?_positional]; simpa using ha
  letOp1 ⟨0⟩ (.literal .nat [0] rfl) .nil base (positional_freshFrom heldP) fun _ h1 w01 z0 =>
  letOp1 ⟨1⟩ (.literal .nat [0] rfl) .nil (base + 1) h1 fun _ h2 w12 z1 =>
  letOp1 ⟨2⟩ (.owned (.makeTuple (tysOfList heldP)))
      (cast (congrArg (HList (Var _)) (tysOfList_toList heldP).symm)
        (inVars.reindex (w01.trans w12)))
      (base + 2) h2 fun _ h3 w23 heldVar =>
  letOp1 ⟨3⟩ (.owned (.makeTuple (samplesStateTys heldP)))
      (.cons (z0.reindex (w12.trans w23)) (.cons (z1.reindex w23) (.cons heldVar .nil)))
      (base + 3) h3 fun _ _ _ stVar =>
  .ret (.cons stVar .nil)

/-! ## Role `Clause` builders (`roleDialect`) -/

/-- Prover construction clause for a prover→verifier message: absorb the message into the
transcript state, then re-emit the `.give` event for the layout layer below. -/
def proverAbsorbClause {V : Vocabulary} {hs : Headers V} {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    Clause V hs prover stateTy where
  site := ⟨site, .give kind getters, [τ], []⟩
  code :=
    let tys := alone prover [τ, stateTy]
    let msgVar : Var (Ctx.positional tys) ⟨τ, [prover]⟩ := alonePosVar prover [τ, stateTy] 0 rfl
    let stVar : Var (Ctx.positional tys) ⟨stateTy, [prover]⟩ := alonePosVar prover [τ, stateTy] 1 rfl
    letOp1 ⟨0⟩ (computeAlone prover (.literal bytesTy (label.length :: label)
        (bytesLiteral_reads label hlabel))) .nil 2 (alone_positional_freshFrom prover [τ, stateTy]) fun _ h1 w01 lblVar =>
    letOp1 ⟨1⟩ (computeAlone prover (callLocal encodeRef))
        (.cons (msgVar.reindex w01) .nil) 3 h1 fun _ h2 w12 encVar =>
    letOp1 ⟨2⟩ (computeAlone prover (callLocal absorbRef))
        (.cons (stVar.reindex (w01.trans w12)) (.cons (lblVar.reindex w12) (.cons encVar .nil)))
        4 h2 fun _ h3 w23 nextStVar =>
    letOp1 site.key (.give kind getters (List.mem_singleton_self prover))
        (.cons (msgVar.reindex ((w01.trans w12).trans w23)) .nil) 5 h3 fun _ _ w34 _ =>
    .ret (.cons (nextStVar.reindex w34) .nil)

/-- Verifier construction clause for a prover→verifier message: obtain the message from the layout
layer below via `.get`, absorb it into the transcript state, and return `(msg, nextState)`. -/
def verifierAbsorbClause {V : Vocabulary} {hs : Headers V} {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    Clause V hs verifier stateTy where
  site := ⟨site, .get kind prover, [], [τ]⟩
  code :=
    let tys := alone verifier [stateTy]
    let stVar : Var (Ctx.positional tys) ⟨stateTy, [verifier]⟩ := alonePosVar verifier [stateTy] 0 rfl
    have hVIn : verifier ∈ Holders.ofList ([verifier] ++ [prover]) ↔
        verifier ∈ ([verifier] : Holders) := by
      simp [Holders.mem_ofList]
    letOp1 site.key (.get τ [prover] kind prover [verifier] (List.mem_singleton_self verifier))
        .nil 1 (alone_positional_freshFrom verifier [stateTy]) fun _ h1 w01 rawVar =>
    letOp1 ⟨0⟩ (.keep [verifier] hVIn) (.cons rawVar .nil) 2 h1 fun _ h2 w12 msgVar =>
    letOp1 ⟨1⟩ (computeAlone verifier (.literal bytesTy (label.length :: label)
        (bytesLiteral_reads label hlabel))) .nil 3 h2 fun _ h3 w23 lblVar =>
    letOp1 ⟨2⟩ (computeAlone verifier (callLocal encodeRef))
        (.cons (msgVar.reindex w23) .nil) 4 h3 fun _ h4 w34 encVar =>
    letOp1 ⟨3⟩ (computeAlone verifier (callLocal absorbRef))
        (.cons (stVar.reindex (((w01.trans w12).trans w23).trans w34))
          (.cons (lblVar.reindex w34) (.cons encVar .nil)))
        5 h4 fun _ _ w45 nextStVar =>
    .ret (.cons (msgVar.reindex ((w23.trans w34).trans w45)) (.cons nextStVar .nil))

/-- Helper to extract positional variables for `takes` (indices `0 .. takes.length - 1`) in
`Ctx.positional (alone r (takes ++ [stateTy]))`. -/
def takeVars {V : Vocabulary} (r : Role) (stateTy : V.Ty) :
    (prefix_ takes : List V.Ty) →
    HList (Var (Ctx.positional (alone r (prefix_ ++ takes ++ [stateTy])))) (alone r takes)
  | _, [] => .nil
  | pref, t :: ts =>
      have hAt : (alone r (pref ++ (t :: ts) ++ [stateTy]))[pref.length]? = some ⟨t, [r]⟩ := by
        simp [alone]
      have hAssoc : pref ++ (t :: ts) ++ [stateTy] = (pref ++ [t]) ++ ts ++ [stateTy] := by
        simp [List.append_assoc]
      .cons (posVar _ pref.length hAt)
        (hAssoc ▸ takeVars r stateTy (pref ++ [t]) ts)

/-- Build a construction draw clause for either prover (`.hear`) or verifier (`.own`):
calls `deriveRef (state, label, drawArgs...)` → `(coin, nextState)`, tells `coin` to the layout
layer below at fresh key `toldKey`, and returns `(coin, nextState)`. -/
def deriveClause {V : Vocabulary} {hs : Headers V} {stateTy τ : V.Ty}
    (r peer : Role) (site : Site) (part : Part V) (drawIns : List V.Ty)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (deriveRef : TypedFnRef V hs.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]) :
    Clause V hs r stateTy where
  site := ⟨site, part, drawIns, [τ]⟩
  code :=
    let tys := alone r (drawIns ++ [stateTy])
    let base := (drawIns ++ [stateTy]).length
    have hStAt : tys[drawIns.length]? = some ⟨stateTy, [r]⟩ := by
      simp [tys, alone]
    let stVar : Var (Ctx.positional tys) ⟨stateTy, [r]⟩ := posVar tys drawIns.length hStAt
    let argVars : HList (Var (Ctx.positional tys)) (alone r drawIns) := by
      simpa [tys] using takeVars r stateTy [] drawIns
    letOp1 ⟨0⟩ (computeAlone r (.literal bytesTy (label.length :: label)
        (bytesLiteral_reads label hlabel))) .nil base (alone_positional_freshFrom r (drawIns ++ [stateTy]))
        fun _ h1 w01 lblVar =>
    letOp2 ⟨1⟩ (computeAlone r (callLocal deriveRef))
        (.cons (stVar.reindex w01) (.cons lblVar (argVars.reindex w01))) (base + 1) h1
        fun _ h3 _ coinVar nextStVar =>
    letOp1 toldKey (.give .message [peer] (List.mem_singleton_self r))
        (.cons coinVar .nil) (base + 3) h3 fun _ _ w34 _ =>
    .ret (.cons (coinVar.reindex w34) (.cons (nextStVar.reindex w34) .nil))

/-- Sequence of tagged metadata byte strings (`List (List Nat)`). -/
abbrev metaLogTy {V : Vocabulary} : V.Ty := .seq bytesTy none

/-- Sequence of encoded unit sequences (`List (List (M.Val unitTy))`). -/
abbrev dataLogTy {V : Vocabulary} (unitTy : V.Ty) : V.Ty := .seq (.seq unitTy none) none

/-- Pure collision-free ideal transcript path type `(metaLog, dataLog)` for any non-linear `unitTy`,
completely independent of any concrete hash/sponge `SuiteSlot.start` or `SuiteSlot.absorb`. -/
abbrev idealPathTys {V : Vocabulary} (unitTy : V.Ty) : Tys V.TypeKey :=
  .cons metaLogTy (.cons (dataLogTy unitTy) .nil)

abbrev idealPathTy {V : Vocabulary} (unitTy : V.Ty) : V.Ty :=
  .tuple (idealPathTys unitTy)

/-- Request payload type for an ideal random-oracle query: `(idealPath, drawLabel)`. -/
abbrev idealQueryTys {V : Vocabulary} (unitTy : V.Ty) : Tys V.TypeKey :=
  .cons (idealPathTy unitTy) (.cons bytesTy .nil)

abbrev idealQueryTy {V : Vocabulary} (unitTy : V.Ty) : V.Ty :=
  .tuple (idealQueryTys unitTy)

/-- Initial pure ideal transcript path `([0 :: sessionBytes], [])`. -/
def idealPathInit {V : Vocabulary} (M : Model V) (unitTy : V.Ty) (sessionBytes : List Nat) :
    M.Val (idealPathTy unitTy) :=
  ([0 :: sessionBytes], ([], ()))

/-- Pure ideal transcript path extension appending `(tagLbl, encVal)` to `(metaLog, dataLog)`. -/
def idealPathPush {V : Vocabulary} (M : Model V) {unitTy : V.Ty}
    (st : M.Val (idealPathTy unitTy)) (tagLbl : List Nat) (encVal : List (M.Val unitTy)) :
    M.Val (idealPathTy unitTy) :=
  (st.1 ++ [tagLbl], (st.2.1 ++ [encVal], ()))

/-- A partial ideal random oracle keyed by `(idealPath, drawLabel, τ)`. Partiality keeps models
with uninhabited types non-vacuous: `ro` only needs to answer types actually drawn by the
protocol (`IdealRO.AnswersDraws`). -/
abbrev IdealRO {V : Vocabulary} (M : Model V) (unitTy : V.Ty) : Type :=
  M.Val (idealPathTy unitTy) → List Nat → (τ : V.Ty) → Option (M.Val τ)

/-- Lift an `IdealRO` into a service oracle answering `[idealQueryTy unitTy]` requests. -/
def IdealRO.asOracle {V : Vocabulary} (M : Model V) {unitTy : V.Ty} (ro : IdealRO M unitTy) :
    (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ)
  | [ty], .cons q .nil, τ =>
      if h : ty = idealQueryTy unitTy then
        let q' : M.Val (idealQueryTy unitTy) := cast (congrArg M.Val h) q
        ro q'.1 q'.2.1 τ
      else none
  | _, _, _ => none

/-- An ideal random oracle answers every verifier-owned heard coin draw in `events` with a valid
value on every valid ideal transcript path and valid byte label. -/
def IdealRO.AnswersDraws {V : Vocabulary} (M : Model V) {unitTy : V.Ty}
    (prover verifier : Role) (events : List (ShapeEvent V)) (ro : IdealRO M unitTy) : Prop :=
  ∀ e ∈ events, ∀ law hearers,
    e.cls = .given (.coin law) verifier hearers → prover ∈ hearers →
    ∀ (st : M.Val (idealPathTy unitTy)) (lbl : List Nat),
      M.Valid (idealPathTy unitTy) st → (∀ b, b ∈ lbl → b < 256) →
      ∃ v, ro st lbl e.τ = some v ∧ M.Valid e.τ v

/-- Pure local combinator appending `(tagLblVar, encVar)` onto `stVar : idealPathTy unitTy`. -/
def appendIdealPathLocal {V : Vocabulary} {fns : List (FnHeader V)} {unitTy : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    {Γ : Ctx V.Ty} {outs : List V.Ty} (fresh : Nat) (hfresh : FreshFrom Γ fresh)
    (stVar : Var Γ (idealPathTy unitTy)) (tagLblVar : Var Γ bytesTy)
    (encVar : Var Γ (.seq unitTy none))
    (rest : (Γ' : Ctx V.Ty) → FreshFrom Γ' (fresh + 9) → Γ.Within Γ' →
      Var Γ' (idealPathTy unitTy) → Term (localDialect V fns) Γ' outs) :
    Term (localDialect V fns) Γ outs :=
  have htfree : Tys.anyLinear V (idealPathTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  letOp1 ⟨fresh⟩ (.owned (.getTuple (idealPathTys unitTy) .head htfree))
      (.cons stVar .nil) fresh hfresh fun _ h1 w01 metaVar =>
  letOp1 ⟨fresh + 1⟩ (.owned (.getTuple (idealPathTys unitTy) (.tail .head) htfree))
      (.cons (stVar.reindex w01) .nil) (fresh + 1) h1 fun _ h2 w12 dataVar =>
  letOp1 ⟨fresh + 2⟩ (.owned (.makeSeq bytesTy 1))
      (.cons (tagLblVar.reindex (w01.trans w12)) .nil) (fresh + 2) h2 fun _ h3 w23 mArr =>
  letOp1 ⟨fresh + 3⟩ (.owned (.seqUnsized bytesTy 1))
      (.cons mArr .nil) (fresh + 3) h3 fun _ h4 w34 mSingle =>
  letOp1 ⟨fresh + 4⟩ (.owned (.seqConcat bytesTy none none))
      (.cons (metaVar.reindex ((w12.trans w23).trans w34)) (.cons mSingle .nil))
      (fresh + 4) h4 fun _ h5 w45 nextMeta =>
  letOp1 ⟨fresh + 5⟩ (.owned (.makeSeq (.seq unitTy none) 1))
      (.cons (encVar.reindex ((((w01.trans w12).trans w23).trans w34).trans w45)) .nil)
      (fresh + 5) h5 fun _ h6 w56 dArr =>
  letOp1 ⟨fresh + 6⟩ (.owned (.seqUnsized (.seq unitTy none) 1))
      (.cons dArr .nil) (fresh + 6) h6 fun _ h7 w67 dSingle =>
  letOp1 ⟨fresh + 7⟩ (.owned (.seqConcat (.seq unitTy none) none none))
      (.cons (dataVar.reindex (((((w23.trans w34).trans w45).trans w56).trans w67)))
        (.cons dSingle .nil))
      (fresh + 7) h7 fun _ h8 w78 nextData =>
  letOp1 ⟨fresh + 8⟩ (.owned (.makeTuple (idealPathTys unitTy)))
      (.cons (nextMeta.reindex ((w56.trans w67).trans w78)) (.cons nextData .nil))
      (fresh + 8) h8 fun Γ9 h9 w89 nextSt =>
  let wAll : Γ.Within Γ9 := (((((((w01.trans w12).trans w23).trans w34).trans w45).trans w56).trans w67).trans w78).trans w89
  rest Γ9 h9 wAll nextSt

/-- Fold statement entries onto a pure ideal path `(metaLog, dataLog)` using tag byte `1`. -/
def buildIdealPathChain {V : Vocabulary} {fns : List (FnHeader V)} {unitTy : V.Ty}
    (hfree : Ty.isLinear V unitTy = false) :
    {Γ : Ctx V.Ty} → (fresh : Nat) → FreshFrom Γ fresh →
    Var Γ (idealPathTy unitTy) → (items : List (StmtAbsorbItem V fns unitTy Γ)) →
    Term (localDialect V fns) Γ [idealPathTy unitTy]
  | _, _, _, stVar, [] => .ret (.cons stVar .nil)
  | _, fresh, hfresh, stVar, item :: rest =>
      have hTagLbl : ∀ b, b ∈ (1 :: item.label) → b < 256 := fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hmem
        · decide
        · exact item.labelBytes b hmem
      letOp1 ⟨fresh⟩ (.literal bytesTy ((1 :: item.label).length :: (1 :: item.label))
          (bytesLiteral_reads (1 :: item.label) hTagLbl)) .nil fresh hfresh fun _ h1 w01 lblVar =>
      letOp1 ⟨fresh + 1⟩ (callLocal item.encode) (.cons (item.input.reindex w01) .nil)
          (fresh + 1) h1 fun _ h2 w12 encVar =>
      appendIdealPathLocal hfree (fresh + 2) h2 (stVar.reindex (w01.trans w12))
          (lblVar.reindex w12) encVar fun _ h11 w211 nextSt =>
      let wAll := (w01.trans w12).trans w211
      let rest' := rest.map fun it =>
        ⟨it.ty, it.input.reindex wAll, it.label, it.labelBytes, it.encode⟩
      buildIdealPathChain hfree (fresh + 11) h11 nextSt rest'
termination_by _ _ _ _ items => items.length
decreasing_by simp

/-- Build pure ideal `construction.start`: initialize `(metaLog, dataLog)` to `([0 :: sessionBytes], [])`,
then append `(1 :: stmtLabel i, encode(stmt_i))` for every statement input. Uses zero concrete
hash/sponge functions (`SuiteSlot.start`, `SuiteSlot.absorb`). -/
def idealStart {V : Vocabulary} {fns : List (FnHeader V)} {unitTy : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    {r : Role} {ins : List (LTy V)}
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (items : List (StmtAbsorbItem V fns unitTy (Ctx.positional (held r ins)))) :
    Term (localDialect V fns) (Ctx.positional (held r ins)) [idealPathTy unitTy] :=
  let base := (held r ins).length
  have hTagSess : ∀ b, b ∈ (0 :: sessionBytes) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hmem
    · decide
    · exact hsess b hmem
  letOp1 ⟨0⟩ (.literal bytesTy ((0 :: sessionBytes).length :: (0 :: sessionBytes))
      (bytesLiteral_reads (0 :: sessionBytes) hTagSess)) .nil base (positional_freshFrom (held r ins))
      fun _ h1 w01 sessVar =>
  letOp1 ⟨1⟩ (.owned (.makeSeq bytesTy 1)) (.cons sessVar .nil) (base + 1) h1 fun _ h2 w12 mArr =>
  letOp1 ⟨2⟩ (.owned (.seqUnsized bytesTy 1)) (.cons mArr .nil) (base + 2) h2 fun _ h3 w23 m0 =>
  letOp1 ⟨3⟩ (.owned (.makeSeq (.seq unitTy none) 0)) .nil (base + 3) h3 fun _ h4 w34 dArr =>
  letOp1 ⟨4⟩ (.owned (.seqUnsized (.seq unitTy none) 0)) (.cons dArr .nil) (base + 4) h4 fun _ h5 w45 d0 =>
  letOp1 ⟨5⟩ (.owned (.makeTuple (idealPathTys unitTy)))
      (.cons (m0.reindex (w34.trans w45)) (.cons d0 .nil)) (base + 5) h5 fun _ h6 w56 st0 =>
  let wAll := ((((w01.trans w12).trans w23).trans w34).trans w45).trans w56
  let items' := items.map fun it =>
    ⟨it.ty, it.input.reindex wAll, it.label, it.labelBytes, it.encode⟩
  buildIdealPathChain hfree (base + 6) h6 st0 items'

/-- Pure role-dialect combinator appending `(tagLblVar, encVar)` onto `stVar : idealPathTy unitTy`. -/
def appendIdealPathRole {V : Vocabulary} {hs : Headers V} {unitTy : V.Ty}
    (hfree : Ty.isLinear V unitTy = false) (r : Role)
    {Γ : Ctx (LTy V)} {outs : List (LTy V)} (fresh : Nat) (hfresh : FreshFrom Γ fresh)
    (stVar : Var Γ ⟨idealPathTy unitTy, [r]⟩) (tagLblVar : Var Γ ⟨bytesTy, [r]⟩)
    (encVar : Var Γ ⟨.seq unitTy none, [r]⟩)
    (rest : (Γ' : Ctx (LTy V)) → FreshFrom Γ' (fresh + 9) → Γ.Within Γ' →
      Var Γ' ⟨idealPathTy unitTy, [r]⟩ → Term (roleDialect V hs r) Γ' outs) :
    Term (roleDialect V hs r) Γ outs :=
  have htfree : Tys.anyLinear V (idealPathTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  letOp1 ⟨fresh⟩ (computeAlone r (.owned (.getTuple (idealPathTys unitTy) .head htfree)))
      (.cons stVar .nil) fresh hfresh fun _ h1 w01 metaVar =>
  letOp1 ⟨fresh + 1⟩ (computeAlone r (.owned (.getTuple (idealPathTys unitTy) (.tail .head) htfree)))
      (.cons (stVar.reindex w01) .nil) (fresh + 1) h1 fun _ h2 w12 dataVar =>
  letOp1 ⟨fresh + 2⟩ (computeAlone r (.owned (.makeSeq bytesTy 1)))
      (.cons (tagLblVar.reindex (w01.trans w12)) .nil) (fresh + 2) h2 fun _ h3 w23 mArr =>
  letOp1 ⟨fresh + 3⟩ (computeAlone r (.owned (.seqUnsized bytesTy 1)))
      (.cons mArr .nil) (fresh + 3) h3 fun _ h4 w34 mSingle =>
  letOp1 ⟨fresh + 4⟩ (computeAlone r (.owned (.seqConcat bytesTy none none)))
      (.cons (metaVar.reindex ((w12.trans w23).trans w34)) (.cons mSingle .nil))
      (fresh + 4) h4 fun _ h5 w45 nextMeta =>
  letOp1 ⟨fresh + 5⟩ (computeAlone r (.owned (.makeSeq (.seq unitTy none) 1)))
      (.cons (encVar.reindex ((((w01.trans w12).trans w23).trans w34).trans w45)) .nil)
      (fresh + 5) h5 fun _ h6 w56 dArr =>
  letOp1 ⟨fresh + 6⟩ (computeAlone r (.owned (.seqUnsized (.seq unitTy none) 1)))
      (.cons dArr .nil) (fresh + 6) h6 fun _ h7 w67 dSingle =>
  letOp1 ⟨fresh + 7⟩ (computeAlone r (.owned (.seqConcat (.seq unitTy none) none none)))
      (.cons (dataVar.reindex (((((w23.trans w34).trans w45).trans w56).trans w67)))
        (.cons dSingle .nil))
      (fresh + 7) h7 fun _ h8 w78 nextData =>
  letOp1 ⟨fresh + 8⟩ (computeAlone r (.owned (.makeTuple (idealPathTys unitTy))))
      (.cons (nextMeta.reindex ((w56.trans w67).trans w78)) (.cons nextData .nil))
      (fresh + 8) h8 fun Γ9 h9 w89 nextSt =>
  let wAll : Γ.Within Γ9 := (((((((w01.trans w12).trans w23).trans w34).trans w45).trans w56).trans w67).trans w78).trans w89
  rest Γ9 h9 wAll nextSt

/-- Ideal random-oracle verifier message clause: delegates `.get` to the layout layer below,
encodes `msg`, and appends `(2 :: label, encode(msg))` onto the pure transcript path
`(metaLog, dataLog)`. -/
def idealAbsorbClause {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Clause V hs verifier (idealPathTy unitTy) where
  site := ⟨site, .get kind prover, [], [τ]⟩
  code :=
    let stTy := idealPathTy unitTy
    let tys := alone verifier [stTy]
    let stVar : Var (Ctx.positional tys) ⟨stTy, [verifier]⟩ := alonePosVar verifier [stTy] 0 rfl
    have hKeep : verifier ∈ Holders.ofList [verifier] ↔ verifier ∈ ([verifier] : Holders) := by
      simp [Holders.mem_ofList]
    have hTagLbl : ∀ b, b ∈ (2 :: label) → b < 256 := fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hmem
      · decide
      · exact hlabel b hmem
    letOp1 site.key (.get τ [] kind prover [verifier] (List.mem_singleton_self verifier)) .nil
        1 (alone_positional_freshFrom verifier [stTy]) fun _ h1 w01 rawMsgVar =>
    letOp1 ⟨0⟩ (.keep [verifier] hKeep) (.cons rawMsgVar .nil) 2 h1 fun _ h2 w12 msgVar =>
    letOp1 ⟨1⟩ (computeAlone verifier (.literal bytesTy ((2 :: label).length :: (2 :: label))
        (bytesLiteral_reads (2 :: label) hTagLbl))) .nil 3 h2 fun _ h3 w23 lblVar =>
    letOp1 ⟨2⟩ (computeAlone verifier (callLocal encodeRef))
        (.cons (msgVar.reindex w23) .nil) 4 h3 fun _ h4 w34 encVar =>
    appendIdealPathRole hfree verifier 5 h4
        (stVar.reindex (((w01.trans w12).trans w23).trans w34))
        (lblVar.reindex w34) encVar fun _ _ w413 nextStVar =>
    .ret (.cons (msgVar.reindex ((w23.trans w34).trans w413)) (.cons nextStVar .nil))

/-- Ideal random-oracle construction clause at a verifier draw: requests the coin from `serviceKey`
on `(idealPath, label)` at fresh key `reqKey`, tells the coin below at `toldKey`, appends
`(3 :: label, encode(coin))` onto the pure transcript path (so consecutive draws query distinct
collision-free paths without calling any concrete hash/sponge), and returns `(coin, nextPath)`. -/
def idealDeriveClause {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (part : Part V) (drawIns : List V.Ty)
    (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Clause V hs verifier (idealPathTy unitTy) where
  site := ⟨site, part, drawIns, [τ]⟩
  code :=
    let stTy := idealPathTy unitTy
    let tys := alone verifier (drawIns ++ [stTy])
    let base := (drawIns ++ [stTy]).length
    have hStAt : tys[drawIns.length]? = some ⟨stTy, [verifier]⟩ := by
      simp [tys, alone]
    let stVar : Var (Ctx.positional tys) ⟨stTy, [verifier]⟩ := posVar tys drawIns.length hStAt
    have hKeep : verifier ∈ Holders.ofList [verifier] ↔ verifier ∈ ([verifier] : Holders) := by
      simp [Holders.mem_ofList]
    have hTagLbl : ∀ b, b ∈ (3 :: label) → b < 256 := fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hmem
      · decide
      · exact hlabel b hmem
    letOp1 ⟨0⟩ (computeAlone verifier (.literal bytesTy (label.length :: label)
        (bytesLiteral_reads label hlabel))) .nil base (alone_positional_freshFrom verifier (drawIns ++ [stTy]))
        fun _ h1 w01 lblVar =>
    letOp1 ⟨1⟩ (computeAlone verifier (.owned (.makeTuple (idealQueryTys unitTy))))
        (.cons (stVar.reindex w01) (.cons lblVar .nil)) (base + 1) h1
        fun _ h2 w12 queryVar =>
    letOp1 reqKey (.own (.request serviceKey) [] [⟨idealQueryTy unitTy, [verifier]⟩] τ rfl
        (fun a ha => by simp at ha; subst ha; exact List.mem_singleton_self verifier))
        (.cons queryVar .nil) (base + 2) h2 fun _ h3 w23 rawCoinVar =>
    letOp1 ⟨2⟩ (.keep [verifier] hKeep) (.cons rawCoinVar .nil) (base + 3) h3
        fun _ h4 w34 coinVar =>
    letOp1 toldKey (.give .message [prover] (List.mem_singleton_self verifier))
        (.cons coinVar .nil) (base + 4) h4 fun _ h5 w45 _ =>
    letOp1 ⟨3⟩ (computeAlone verifier (.literal bytesTy ((3 :: label).length :: (3 :: label))
        (bytesLiteral_reads (3 :: label) hTagLbl))) .nil (base + 5) h5
        fun _ h6 w56 tagLblVar =>
    letOp1 ⟨4⟩ (computeAlone verifier (callLocal encodeRef))
        (.cons (coinVar.reindex (w45.trans w56)) .nil) (base + 6) h6 fun _ h7 w67 encVar =>
    appendIdealPathRole hfree verifier (base + 7) h7
        (stVar.reindex ((((((w01.trans w12).trans w23).trans w34).trans w45).trans w56).trans w67))
        (tagLblVar.reindex w67) encVar fun _ _ w716 nextStVar =>
    .ret (.cons (coinVar.reindex (((w45.trans w56).trans w67).trans w716)) (.cons nextStVar .nil))

/-- Prover layout clause: serialize a message/draw with `writeRef` and append to proof buffer. -/
def layoutPWriteClause {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (writeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Clause V hs prover (.seq unitTy none) where
  site := ⟨site, .give kind getters, [τ], []⟩
  code :=
    let bufTy : V.Ty := .seq unitTy none
    let tys := alone prover [τ, bufTy]
    let msgVar : Var (Ctx.positional tys) ⟨τ, [prover]⟩ := alonePosVar prover [τ, bufTy] 0 rfl
    let bufVar : Var (Ctx.positional tys) ⟨bufTy, [prover]⟩ := alonePosVar prover [τ, bufTy] 1 rfl
    letOp1 ⟨0⟩ (computeAlone prover (callLocal writeRef))
        (.cons msgVar .nil) 2 (alone_positional_freshFrom prover [τ, bufTy]) fun _ h1 w01 chunkVar =>
    letOp1 ⟨1⟩ (computeAlone prover (.owned (.seqConcat unitTy none none)))
        (.cons (bufVar.reindex w01) (.cons chunkVar .nil)) 3 h1 fun _ _ _ nextBufVar =>
    .ret (.cons nextBufVar .nil)

/-- Layout drop clause (prover or verifier): consume a `.give` event without modifying state. -/
def layoutDropClause {V : Vocabulary} {hs : Headers V} {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role) :
    Clause V hs r stateTy where
  site := ⟨site, .give kind getters, [τ], []⟩
  code :=
    .ret (.cons (alonePosVar r [τ, stateTy] 1 rfl) .nil)

/-- Verifier streaming layout clause: read a message of type `τ` at `(buf, offset)` via `readRef`
and advance cursor to `(buf, nextOffset)`. -/
def layoutVReadClause {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat]) :
    Clause V hs verifier (streamStateTy unitTy) where
  site := ⟨site, .get kind prover, [], [τ]⟩
  code :=
    have htfree : Tys.anyLinear V (streamStateTys unitTy) = false := by
      simp [Tys.anyLinear, Ty.isLinear, hfree]
    let stTy : V.Ty := streamStateTy unitTy
    let tys := alone verifier [stTy]
    let stVar : Var (Ctx.positional tys) ⟨stTy, [verifier]⟩ := alonePosVar verifier [stTy] 0 rfl
    letOp1 ⟨0⟩ (computeAlone verifier (.owned (.getTuple (streamStateTys unitTy) .head htfree)))
        (.cons stVar .nil) 1 (alone_positional_freshFrom verifier [stTy]) fun _ h1 w01 bufVar =>
    letOp1 ⟨1⟩ (computeAlone verifier (.owned (.getTuple (streamStateTys unitTy) (.tail .head) htfree)))
        (.cons (stVar.reindex w01) .nil) 2 h1 fun _ h2 w12 offVar =>
    letOp2 ⟨2⟩ (computeAlone verifier (callLocalSafe readRef))
        (.cons (bufVar.reindex w12) (.cons offVar .nil)) 3 h2 fun _ h4 w24 valVar nextOffVar =>
    letOp1 ⟨3⟩ (computeAlone verifier (.owned (.makeTuple (streamStateTys unitTy))))
        (.cons (bufVar.reindex (w12.trans w24)) (.cons nextOffVar .nil)) 5 h4
        fun _ _ w45 nextStVar =>
    .ret (.cons (valVar.reindex w45) (.cons nextStVar .nil))

/-- Verifier streaming layout clause for a carried draw (`carry` without `recover`): read the
carried draw from `(buf, offset)` via `readRef`, check equality with the derived draw `var 0`
using `eqRef`, reject if unequal, and advance cursor to `(buf, nextOffset)`. -/
def layoutVCarryClause {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    Clause V hs verifier (streamStateTy unitTy) where
  site := ⟨toldSite, .give .message [prover], [τ], []⟩
  code :=
    have htfree : Tys.anyLinear V (streamStateTys unitTy) = false := by
      simp [Tys.anyLinear, Ty.isLinear, hfree]
    let stTy : V.Ty := streamStateTy unitTy
    let tys := alone verifier [τ, stTy]
    let derivedVar : Var (Ctx.positional tys) ⟨τ, [verifier]⟩ := alonePosVar verifier [τ, stTy] 0 rfl
    let stVar : Var (Ctx.positional tys) ⟨stTy, [verifier]⟩ := alonePosVar verifier [τ, stTy] 1 rfl
    letOp1 ⟨0⟩ (computeAlone verifier (.owned (.getTuple (streamStateTys unitTy) .head htfree)))
        (.cons stVar .nil) 2 (alone_positional_freshFrom verifier [τ, stTy]) fun _ h1 w01 bufVar =>
    letOp1 ⟨1⟩ (computeAlone verifier (.owned (.getTuple (streamStateTys unitTy) (.tail .head) htfree)))
        (.cons (stVar.reindex w01) .nil) 3 h1 fun _ h2 w12 offVar =>
    letOp2 ⟨2⟩ (computeAlone verifier (callLocalSafe readRef))
        (.cons (bufVar.reindex w12) (.cons offVar .nil)) 4 h2 fun _ h4 w24 carriedVar nextOffVar =>
    letOp1 ⟨3⟩ (computeAlone verifier (callLocal eqRef))
        (.cons (derivedVar.reindex ((w01.trans w12).trans w24)) (.cons carriedVar .nil)) 6 h4
        fun _ h5 w45 eqVar =>
    .guard guardKey [verifier] eqVar ⟨rfl, List.mem_singleton_self verifier,
        List.mem_singleton_self verifier⟩ .reject <|
    letOp1 ⟨4⟩ (computeAlone verifier (.owned (.makeTuple (streamStateTys unitTy))))
        (.cons (bufVar.reindex ((w12.trans w24).trans w45)) (.cons (nextOffVar.reindex w45) .nil))
        7 h5 fun _ _ _ nextStVar =>
    .ret (.cons nextStVar .nil)

/-- Prover `samples derived by` clause: derives a private coin from all prover inputs
(secret witness and public statement), the resolved session bytes, the full canonical site bytes
(`through` and `key`), the attempt number, and a monotonically increasing sample sequence counter
(`callSeq`), incrementing `callSeq` on every invocation to prevent nonce reuse across witnesses,
statements, applications, sub-protocols, loops, and retries. -/
def proverSampleClause {V : Vocabulary} {hs : Headers V} {heldP : List V.Ty} {τ : V.Ty}
    (htfree : Tys.anyLinear V (samplesStateTys heldP) = false)
    (prover : Role) (site : Site) (law : V.LawKey)
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (siteBytes : List Nat) (hsite : ∀ b, b ∈ siteBytes → b < 256)
    (sampleRef : TypedFnRef V hs.fns (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) :
    Clause V hs prover (samplesStateTy heldP) where
  site := ⟨site, .own (.coin law) [], [], [τ]⟩
  code :=
    let stTy := samplesStateTy heldP
    let tys := alone prover [stTy]
    let stVar : Var (Ctx.positional tys) ⟨stTy, [prover]⟩ := alonePosVar prover [stTy] 0 rfl
    letOp1 ⟨0⟩ (computeAlone prover (.owned (.getTuple (samplesStateTys heldP) .head htfree)))
        (.cons stVar .nil) 1 (alone_positional_freshFrom prover [stTy]) fun _ h1 w01 attVar =>
    letOp1 ⟨1⟩ (computeAlone prover (.owned (.getTuple (samplesStateTys heldP) (.tail .head) htfree)))
        (.cons (stVar.reindex w01) .nil) 2 h1 fun _ h2 w12 seqVar =>
    letOp1 ⟨2⟩ (computeAlone prover (.owned (.getTuple (samplesStateTys heldP) (.tail (.tail .head)) htfree)))
        (.cons (stVar.reindex (w01.trans w12)) .nil) 3 h2 fun Γ3 h3 w23 heldVar =>
    let fields := alone prover (tysOfList heldP).toList
    let fieldNames : Names fields := Names.counting 4 fields
    let Γ4 := Γ3.extend fieldNames
    have hW34 : Γ3.Within Γ4 := by
      intro name a ha
      rw [show Γ4 = Γ3.extend (Names.counting 4 fields) from rfl, Ctx.find?_extend_counting]
      have hlt : name < 4 := by
        cases Nat.lt_or_ge name 4 with
        | inl h => exact h
        | inr h => rw [h3 name h] at ha; cases ha
      have hout : ¬ (4 ≤ name ∧ name < 4 + fields.length) := fun hm =>
        Nat.not_le_of_lt hlt hm.1
      rw [ite_eq_right hout]; exact ha
    have hFieldsIn : ∀ k a, fields[k]? = some a → Γ4.find? (4 + k) = some a := by
      intro k a ha
      have hlt : k < fields.length := by
        cases Nat.lt_or_ge k fields.length with
        | inl h => exact h
        | inr h => rw [List.getElem?_eq_none h] at ha; cases ha
      rw [show Γ4 = Γ3.extend (Names.counting 4 fields) from rfl, Ctx.find?_extend_counting]
      have hbounds : 4 ≤ 4 + k ∧ 4 + k < 4 + fields.length :=
        ⟨Nat.le_add_right 4 k, Nat.add_lt_add_left hlt 4⟩
      rw [ite_eq_left hbounds, Nat.add_sub_cancel_left]; exact ha
    have hFresh4 : FreshFrom Γ4 (4 + fields.length) := by
      intro k hk
      rw [show Γ4 = Γ3.extend (Names.counting 4 fields) from rfl, Ctx.find?_extend_counting]
      have hout : ¬ (4 ≤ k ∧ k < 4 + fields.length) := fun hm =>
        Nat.not_lt_of_ge hk hm.2
      rw [ite_eq_right hout]
      exact h3 k (Nat.le_trans (Nat.le_add_right 4 fields.length) hk)
    let fVars : HList (Var Γ4) (alone prover heldP) :=
      cast (congrArg (fun ts => HList (Var Γ4) (alone prover ts)) (tysOfList_toList heldP))
        (positionalVars fields 4 hFieldsIn)
    let fBase := 4 + fields.length
    .op ⟨3⟩ (computeAlone prover (.owned (.takeTuple (tysOfList heldP))))
        (.cons heldVar .nil) fieldNames <|
    letOp1 ⟨4⟩ (computeAlone prover (.literal bytesTy (sessionBytes.length :: sessionBytes)
        (bytesLiteral_reads sessionBytes hsess))) .nil fBase hFresh4
        fun _ h5 w45 sessVar =>
    letOp1 ⟨5⟩ (computeAlone prover (.literal bytesTy (siteBytes.length :: siteBytes)
        (bytesLiteral_reads siteBytes hsite))) .nil (fBase + 1) h5
        fun Γ6 h6 w56 siteVar =>
    let w46 := w45.trans w56
    let w36 := hW34.trans w46
    let tailArgs : HList (Var Γ6) (alone prover [bytesTy, bytesTy, .nat, .nat]) :=
      .cons (sessVar.reindex w56)
        (.cons siteVar
          (.cons (attVar.reindex ((w12.trans w23).trans w36))
            (.cons (seqVar.reindex (w23.trans w36)) .nil)))
    have hApp : alone prover (heldP ++ [bytesTy, bytesTy, .nat, .nat]) =
        alone prover heldP ++ alone prover [bytesTy, bytesTy, .nat, .nat] := by
      simp [alone, List.map_append]
    let allArgs : HList (Var Γ6) (alone prover (heldP ++ [bytesTy, bytesTy, .nat, .nat])) :=
      cast (congrArg (HList (Var Γ6)) hApp.symm) (HList.append (fVars.reindex w46) tailArgs)
    letOp1 ⟨6⟩ (computeAlone prover (callLocal sampleRef)) allArgs (fBase + 2) h6
        fun _ h7 w67 coinVar =>
    letOp1 ⟨7⟩ (computeAlone prover (.literal .nat [1] rfl)) .nil (fBase + 3) h7
        fun _ h8 w78 oneVar =>
    letOp1 ⟨8⟩ (computeAlone prover (.owned .natAdd))
        (.cons (seqVar.reindex (((w23.trans w36).trans w67).trans w78)) (.cons oneVar .nil))
        (fBase + 4) h8 fun _ h9 w89 nextSeqVar =>
    letOp1 ⟨9⟩ (computeAlone prover (.owned (.makeTuple (samplesStateTys heldP))))
        (.cons (attVar.reindex (((((w12.trans w23).trans w36).trans w67).trans w78).trans w89))
          (.cons nextSeqVar
            (.cons (heldVar.reindex (((w36.trans w67).trans w78).trans w89)) .nil)))
        (fBase + 5) h9 fun _ _ w910 nextStVar =>
    .ret (.cons (coinVar.reindex ((w78.trans w89).trans w910)) (.cons nextStVar .nil))

/-! ## Compact layout (`carry` + `recover`) builders -/

/-- Build `compactLayoutV.start`: sequentially parse every wire item from `(proof, 0)`, reject any
trailing bytes, and pack all parsed wire items (plus verifier statement inputs) into the tuple
state. -/
def buildCompactParse {V : Vocabulary} {fns : List (FnHeader V)} (unitTy : V.Ty)
    (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (wireTys : List V.Ty) :
    {Γ : Ctx V.Ty} → (fresh : Nat) → FreshFrom Γ fresh →
    Var Γ (.seq unitTy none) → Var Γ .nat →
    (parsedAcc : List V.Ty) → HList (Var Γ) parsedAcc →
    (readers : List ((τ : V.Ty) × SafeFnRef V fns [.seq unitTy none, .nat] [τ, .nat])) →
    (hMatch : parsedAcc ++ readers.map Sigma.fst = wireTys) →
    Term (localDialect V fns) Γ [.tuple (tysOfList wireTys)]
  | _, fresh, hfresh, bufVar, offVar, parsedAcc, accVars, [], hMatch =>
      let hEq : parsedAcc = wireTys := by simpa using hMatch
      letOp1 ⟨fresh⟩ (.owned (.seqLength unitTy none hfree)) (.cons bufVar .nil) fresh hfresh
          fun _ h1 w01 lenVar =>
      letOp1 ⟨fresh + 1⟩ (.owned .natEqual) (.cons (offVar.reindex w01) (.cons lenVar .nil))
          (fresh + 1) h1 fun Γ2 h2 w12 eqVar =>
      .guard guardKey () eqVar rfl .reject <|
      letOp1 ⟨fresh + 2⟩ (.owned (.makeTuple (tysOfList wireTys)))
          (cast (congrArg (HList (Var Γ2)) (by rw [tysOfList_toList, hEq]))
            (accVars.reindex (w01.trans w12)))
          (fresh + 2) h2 fun _ _ _ tupleVar =>
      .ret (.cons tupleVar .nil)
  | _, fresh, hfresh, bufVar, offVar, parsedAcc, accVars, ⟨τ, readRef⟩ :: rest, hMatch =>
      letOp2 ⟨fresh⟩ (callLocalSafe readRef) (.cons bufVar (.cons offVar .nil)) fresh hfresh
          fun _ h2 w02 valVar nextOffVar =>
      let nextAcc := HList.append (accVars.reindex w02) (.cons valVar .nil)
      have hMatch' : (parsedAcc ++ [τ]) ++ rest.map Sigma.fst = wireTys := by
        simpa [List.append_assoc] using hMatch
      buildCompactParse unitTy hfree guardKey wireTys (fresh + 2) h2
        (bufVar.reindex w02) nextOffVar (parsedAcc ++ [τ]) nextAcc rest hMatch'

/-- Build `compactLayoutV.start`: prepend statement inputs (held by verifier) and all parsed wire
items into one tuple state. -/
def compactLayoutVStart {V : Vocabulary} {fns : List (FnHeader V)} {r : Role} {ins : List (LTy V)}
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (stmtItems : List ((τ : V.Ty) × Var (Ctx.positional (.seq unitTy none :: held r ins)) τ))
    (readers : List ((τ : V.Ty) × SafeFnRef V fns [.seq unitTy none, .nat] [τ, .nat])) :
    Term (localDialect V fns) (Ctx.positional (.seq unitTy none :: held r ins))
      [.tuple (tysOfList (stmtItems.map Sigma.fst ++ readers.map Sigma.fst))] :=
  let tys := .seq unitTy none :: held r ins
  let base := tys.length
  let proofVar : Var (Ctx.positional tys) (.seq unitTy none) := posVar tys 0 rfl
  letOp1 ⟨0⟩ (.literal .nat [0] rfl) .nil base (positional_freshFrom tys) fun Γ1 h1 w01 zeroVar =>
  let rec packStmts : (xs : List ((τ : V.Ty) × Var (Ctx.positional tys) τ)) →
      HList (Var Γ1) (xs.map Sigma.fst)
    | [] => .nil
    | ⟨_, v⟩ :: rest => .cons (v.reindex w01) (packStmts rest)
  buildCompactParse unitTy hfree guardKey (stmtItems.map Sigma.fst ++ readers.map Sigma.fst)
    (base + 1) h1 (proofVar.reindex w01) zeroVar (stmtItems.map Sigma.fst) (packStmts stmtItems)
    readers rfl

/-- Compact verifier layout clause for a retained message: read slot `pos` from tuple state. -/
def compactReadSlotClause {V : Vocabulary} {hs : Headers V} {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ) :
    Clause V hs verifier (.tuple stateTys) where
  site := ⟨site, .get kind prover, [], [τ]⟩
  code :=
    let stTy : V.Ty := .tuple stateTys
    let tys := alone verifier [stTy]
    let stVar : Var (Ctx.positional tys) ⟨stTy, [verifier]⟩ := alonePosVar verifier [stTy] 0 rfl
    letOp1 ⟨0⟩ (computeAlone verifier (.owned (.getTuple stateTys pos htfree)))
        (.cons stVar .nil) 1 (alone_positional_freshFrom verifier [stTy]) fun _ _ w01 valVar =>
    .ret (.cons valVar (.cons (stVar.reindex w01) .nil))

/-- Compact verifier layout clause for a carried draw: compare derived `var 0` against tuple slot
`pos` via `eqRef` and reject if unequal. -/
def compactCompareClause {V : Vocabulary} {hs : Headers V} {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ)
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    Clause V hs verifier (.tuple stateTys) where
  site := ⟨toldSite, .give .message [prover], [τ], []⟩
  code :=
    let stTy : V.Ty := .tuple stateTys
    let tys := alone verifier [τ, stTy]
    let derivedVar : Var (Ctx.positional tys) ⟨τ, [verifier]⟩ := alonePosVar verifier [τ, stTy] 0 rfl
    let stVar : Var (Ctx.positional tys) ⟨stTy, [verifier]⟩ := alonePosVar verifier [τ, stTy] 1 rfl
    letOp1 ⟨0⟩ (computeAlone verifier (.owned (.getTuple stateTys pos htfree)))
        (.cons stVar .nil) 2 (alone_positional_freshFrom verifier [τ, stTy]) fun _ h1 w01 carriedVar =>
    letOp1 ⟨1⟩ (computeAlone verifier (callLocal eqRef))
        (.cons (derivedVar.reindex w01) (.cons carriedVar .nil)) 3 h1 fun _ _ w12 eqVar =>
    .guard guardKey [verifier] eqVar ⟨rfl, List.mem_singleton_self verifier,
        List.mem_singleton_self verifier⟩ .reject <|
    .ret (.cons (stVar.reindex (w01.trans w12)) .nil)

/-- Compact verifier layout clause for a recovered message: unpack the tuple state fields
`(stmt..., wire...)` with `takeTuple`, invoke `recoverRef`, and return `(recovered, state)`. -/
def compactRecoverClause {V : Vocabulary} {hs : Headers V} {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recoverRef : SafeFnRef V hs.fns stateTys.toList [τ]) :
    Clause V hs verifier (.tuple stateTys) where
  site := ⟨site, .get kind prover, [], [τ]⟩
  code :=
    let stTy : V.Ty := .tuple stateTys
    let tys := alone verifier [stTy]
    let Γ0 := Ctx.positional tys
    let h0 : FreshFrom Γ0 1 := alone_positional_freshFrom verifier [stTy]
    let stVar : Var Γ0 ⟨stTy, [verifier]⟩ := alonePosVar verifier [stTy] 0 rfl
    let fields := alone verifier stateTys.toList
    let fieldNames : Names fields := Names.counting 1 fields
    let Γ1 := Γ0.extend fieldNames
    let rec buildFieldVars (start : Nat) :
        {Γ : Ctx (LTy V)} → (rem : List (LTy V)) →
        (hΓ : ∀ k a, rem[k]? = some a → Γ.find? (start + k) = some a) →
        HList (Var Γ) rem
      | _, [], _ => .nil
      | _, a :: as, hΓ =>
          .cons ⟨start, hΓ 0 a rfl⟩
            (buildFieldVars (start + 1) as fun k b hb => by
              have := hΓ (k + 1) b hb
              rwa [show start + (k + 1) = start + 1 + k by omega] at this)
    have hFieldsIn : ∀ k a, fields[k]? = some a → Γ1.find? (1 + k) = some a := by
      intro k a ha
      have hlt : k < fields.length := by
        cases Nat.lt_or_ge k fields.length with
        | inl h => exact h
        | inr h => rw [List.getElem?_eq_none h] at ha; cases ha
      rw [show Γ1 = Γ0.extend (Names.counting 1 fields) from rfl, Ctx.find?_extend_counting]
      have hbounds : 1 ≤ 1 + k ∧ 1 + k < 1 + fields.length :=
        ⟨Nat.le_add_right 1 k, Nat.add_lt_add_left hlt 1⟩
      rw [ite_eq_left hbounds, Nat.add_sub_cancel_left]
      exact ha
    have hStIn1 : Γ1.find? 0 = some ⟨stTy, [verifier]⟩ := by
      rw [show Γ1 = Γ0.extend (Names.counting 1 fields) from rfl, Ctx.find?_extend_counting]
      have hout : ¬ (1 ≤ 0 ∧ 0 < 1 + fields.length) := by omega
      rw [ite_eq_right hout]
      exact stVar.typed
    have hFresh1 : FreshFrom Γ1 (1 + fields.length) := by
      intro k hk
      rw [show Γ1 = Γ0.extend (Names.counting 1 fields) from rfl, Ctx.find?_extend_counting]
      have hout : ¬ (1 ≤ k ∧ k < 1 + fields.length) := by omega
      rw [ite_eq_right hout]
      exact h0 k (by omega)
    let fVars : HList (Var Γ1) fields := buildFieldVars 1 fields hFieldsIn
    let stVar1 : Var Γ1 ⟨stTy, [verifier]⟩ := ⟨0, hStIn1⟩
    .op ⟨0⟩ (computeAlone verifier (.owned (.takeTuple stateTys)))
        (.cons stVar .nil) fieldNames <|
    letOp1 ⟨1⟩ (computeAlone verifier (callLocalSafe recoverRef))
        fVars (1 + fields.length) hFresh1 fun _ _ w12 recVar =>
    .ret (.cons recVar (.cons (stVar1.reindex w12) .nil))

end LayerBuild

end Zkc.Core
