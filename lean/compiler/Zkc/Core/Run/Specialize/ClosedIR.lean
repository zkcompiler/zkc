module

public import Zkc.Core.Run.Specialize.HeldView

@[expose] public section

/-!
Residual closed IR (`ClosedTerm`, `ClosedProcs`, `ClosedRole`) and exact finite role permutations
(`FinPerm`) for DAG-preserving handler specialization.

`ClosedTerm V fns procs σ Γ outs` represents a handler-free, plain-typed imperative role term
threading layer states `σ : List V.Ty` and calling shared earlier procedures in `procs : List
(ClosedProcSig V)` via `ClosedTerm.call`. `ClosedProcs` mirrors `Defs V` bottom-up so every call
graph is acyclic by construction with zero `partial` definitions and zero fuel.
-/

namespace Zkc.Core

/-! ## Exact canonical finite role permutations (`FinPerm`) -/

section FinPermDef

/-- A finite permutation of `Role` values, stored as a prefix `[p 0, p 1, ..., p (n - 1)]` with
all `q ≥ n` fixed (`q ↦ q`), normalized by trimming trailing fixed points. -/
abbrev FinPerm := List Role

/-- The identity role permutation. -/
def FinPerm.identity : FinPerm := []

/-- Apply a `FinPerm` to a role number. -/
def FinPerm.apply (p : FinPerm) (q : Role) : Role := p.getD q q

/-- Trim trailing fixed points `r = idx` so equal permutations share the same list representation. -/
def FinPerm.trimAux : List Role → Nat → List Role
  | [], _ => []
  | r :: rest, idx =>
      let t := FinPerm.trimAux rest (idx + 1)
      if t.isEmpty && r == idx then [] else r :: t

/-- Normalize a role image table into a canonical `FinPerm`. -/
def FinPerm.normalize (l : List Role) : FinPerm := FinPerm.trimAux l 0

theorem FinPerm.apply_identity (q : Role) : FinPerm.identity.apply q = q := rfl

private theorem list_getD_eq_default {α : Type} {l : List α} {i : Nat} {d : α} (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none h]

private theorem FinPerm.trimAux_getD : ∀ (l : List Role) (idx q : Nat),
    idx ≤ q → (FinPerm.trimAux l idx).getD (q - idx) q = l.getD (q - idx) q
  | [], _, _, _ => rfl
  | r :: rest, idx, q, hle => by
      dsimp only [FinPerm.trimAux]
      by_cases hCond : (FinPerm.trimAux rest (idx + 1)).isEmpty && r == idx
      · rw [ite_eq_left hCond]
        have hSplit := Bool.and_eq_true _ _ |>.mp hCond
        have hEmp : FinPerm.trimAux rest (idx + 1) = [] := List.isEmpty_iff.mp hSplit.1
        have hEqR : r = idx := beq_iff_eq.mp hSplit.2
        by_cases hQ : q = idx
        · subst hQ; simp [List.getD, hEqR]
        · have hGt : idx + 1 ≤ q := by omega
          have hSub : q - idx = (q - (idx + 1)) + 1 := by omega
          rw [hSub]
          have ih := FinPerm.trimAux_getD rest (idx + 1) q hGt
          rw [hEmp] at ih
          simpa [List.getD] using ih
      · rw [ite_eq_right hCond]
        by_cases hQ : q = idx
        · subst hQ; simp [List.getD]
        · have hGt : idx + 1 ≤ q := by omega
          have hSub : q - idx = (q - (idx + 1)) + 1 := by omega
          rw [hSub]
          have ih := FinPerm.trimAux_getD rest (idx + 1) q hGt
          simpa [List.getD] using ih

theorem FinPerm.apply_normalize (l : List Role) (q : Role) :
    (FinPerm.normalize l).apply q = l.getD q q := by
  simpa [FinPerm.normalize, FinPerm.apply] using FinPerm.trimAux_getD l 0 q (Nat.zero_le q)

/-- Compose two finite permutations: `(p₁.comp p₂).apply q = p₁.apply (p₂.apply q)`. -/
def FinPerm.comp (p₁ p₂ : FinPerm) : FinPerm :=
  let n := Nat.max p₁.length p₂.length
  FinPerm.normalize ((List.range n).map fun q => p₁.apply (p₂.apply q))

theorem FinPerm.apply_comp (p₁ p₂ : FinPerm) (q : Role) :
    (p₁.comp p₂).apply q = p₁.apply (p₂.apply q) := by
  unfold FinPerm.comp
  rw [FinPerm.apply_normalize]
  by_cases hLt : q < Nat.max p₁.length p₂.length
  · simp [List.getD, List.getElem?_map, List.getElem?_range hLt]
  · have hGe : Nat.max p₁.length p₂.length ≤ q := Nat.le_of_not_lt hLt
    have hGe1 : p₁.length ≤ q := Nat.le_trans (Nat.le_max_left _ _) hGe
    have hGe2 : p₂.length ≤ q := Nat.le_trans (Nat.le_max_right _ _) hGe
    rw [list_getD_eq_default (by simp [hGe])]
    unfold FinPerm.apply
    rw [list_getD_eq_default hGe2, list_getD_eq_default hGe1]

/-- Upper bound strictly above every role moved by `RoleMap.ofList roles distinct`. -/
def finPermBound (roles : List Role) : Nat :=
  Nat.max roles.length (roles.foldl (fun acc r => Nat.max acc (r + 1)) 0)

private theorem foldl_max_ge : ∀ (l : List Role) (acc : Nat),
    acc ≤ l.foldl (fun a r => Nat.max a (r + 1)) acc
  | [], _ => Nat.le_refl _
  | r :: rest, acc =>
      Nat.le_trans (Nat.le_max_left acc (r + 1)) (foldl_max_ge rest (Nat.max acc (r + 1)))

private theorem foldl_max_mem : ∀ (l : List Role) (acc : Nat) {r : Role},
    r ∈ l → r + 1 ≤ l.foldl (fun a x => Nat.max a (x + 1)) acc
  | [], _, _, h => nomatch h
  | x :: rest, acc, r, h => by
      cases h with
      | head =>
          exact Nat.le_trans (Nat.le_max_right acc (x + 1)) (foldl_max_ge rest (Nat.max acc (x + 1)))
      | tail _ hm =>
          exact foldl_max_mem rest (Nat.max acc (x + 1)) hm

private theorem roleMap_fill_preserves_bound :
    ∀ (rest : List Role) (start : Nat) (ρ : RoleMap) (B : Nat),
      start + rest.length ≤ B →
      (∀ r ∈ rest, r < B) →
      (∀ j, B ≤ j → ρ.to j = j) →
      (∀ j, j < B → ρ.to j < B) →
      (∀ j, B ≤ j → (RoleMap.fill rest start ρ).to j = j) ∧
      (∀ j, j < B → (RoleMap.fill rest start ρ).to j < B)
  | [], _, _, _, _, _, hFix, hLt => ⟨hFix, hLt⟩
  | r :: rest, start, ρ, B, hLen, hMem, hFix, hLt => by
      have hStartLt : start < B := by simp at hLen; omega
      have hRLt : r < B := hMem r List.mem_cons_self
      have hImgLt : ρ.to start < B := hLt start hStartLt
      refine roleMap_fill_preserves_bound rest (start + 1) (ρ.swap (ρ.to start) r) B
        (by simp at hLen ⊢; omega)
        (fun x hx => hMem x (List.mem_cons_of_mem _ hx)) ?_ ?_
      · intro j hj
        change swapRoles (ρ.to start) r (ρ.to j) = j
        rw [hFix j hj]
        have hNe1 : j ≠ ρ.to start := Nat.ne_of_gt (Nat.lt_of_lt_of_le hImgLt hj)
        have hNe2 : j ≠ r := Nat.ne_of_gt (Nat.lt_of_lt_of_le hRLt hj)
        simp [swapRoles, hNe1, hNe2]
      · intro j hj
        change swapRoles (ρ.to start) r (ρ.to j) < B
        unfold swapRoles
        split
        · exact hRLt
        · split
          · exact hImgLt
          · exact hLt j hj

/-- Canonical `FinPerm` realizing `(RoleMap.ofList roles distinct).to` on every role. -/
def FinPerm.ofList (roles : List Role) (distinct : roles.Nodup) : FinPerm :=
  let rm := RoleMap.ofList roles distinct
  let n := finPermBound roles
  FinPerm.normalize ((List.range n).map rm.to)

theorem FinPerm.apply_ofList (roles : List Role) (distinct : roles.Nodup) (q : Role) :
    (FinPerm.ofList roles distinct).apply q = (RoleMap.ofList roles distinct).to q := by
  unfold FinPerm.ofList
  rw [FinPerm.apply_normalize]
  by_cases hLt : q < finPermBound roles
  · simp [List.getD, List.getElem?_map, List.getElem?_range hLt]
  · have hGe : finPermBound roles ≤ q := Nat.le_of_not_lt hLt
    rw [list_getD_eq_default (by simp [hGe])]
    have hBound := roleMap_fill_preserves_bound roles 0 RoleMap.identity (finPermBound roles)
      (by simp only [Nat.zero_add, finPermBound]; exact Nat.le_max_left _ _)
      (fun r hr => Nat.lt_of_lt_of_le (foldl_max_mem roles 0 hr)
        (Nat.le_max_right roles.length (roles.foldl (fun a x => Nat.max a (x + 1)) 0)))
      (fun _ _ => rfl) (fun _ hj => hj)
    exact (hBound.1 q hGe).symm

end FinPermDef

/-! ## Residual effects -/

/-- A role effect statically described by its kind, peers, payload types, and reply types.
At the bottom of a specialized handler stack (`σ = []`), unhandled effects remain as
`ClosedTerm.effect` nodes (for a covered non-interactive deployment, only private coins,
service requests, and local attempt marks). -/
inductive ResidualOp (V : Vocabulary) : List V.Ty → List V.Ty → Type where
  | give (kind : FlowKind) (getters : List Role) (τ : V.Ty) : ResidualOp V [τ] []
  | get (kind : FlowKind) (giver : Role) (τ : V.Ty) : ResidualOp V [] [τ]
  | own (kind : GivenKind V) (hearers : List Role) (ins : List V.Ty) (τ : V.Ty) :
      ResidualOp V ins [τ]
  | hear (kind : GivenKind V) (owner : Role) (τ : V.Ty) : ResidualOp V [] [τ]
  | begin : ResidualOp V [] [.nat]
  | settle : ResidualOp V [] []

/-- The role's `Part` corresponding to a static effect description. -/
def ResidualOp.part {V : Vocabulary} {ins res : List V.Ty} : ResidualOp V ins res → Option (Part V)
  | .give kind getters _ => some (.give kind getters)
  | .get kind giver _ => some (.get kind giver)
  | .own kind hearers _ _ => some (.own kind hearers)
  | .hear kind owner _ => some (.hear kind owner)
  | .begin => none
  | .settle => none

/-- Rename peer roles in a static effect description, matching `mapR`. -/
def ResidualOp.mapPeers {V : Vocabulary} (ρ : Role → Role) {ins res : List V.Ty} :
    ResidualOp V ins res → ResidualOp V ins res
  | .give kind getters τ => .give kind (getters.map ρ) τ
  | .get kind giver τ => .get kind (ρ giver) τ
  | .own kind hearers ins τ => .own kind (hearers.map ρ) ins τ
  | .hear kind owner τ => .hear kind (ρ owner) τ
  | .begin => .begin
  | .settle => .settle

section ResidualOpSemantics
variable {V : Vocabulary} (M : Model V)

/-- Instantiate a static effect description at an occurrence and payload into an `ROp M`. -/
def ResidualOp.toROp {ins res : List V.Ty} (at_ : Occurrence) :
    ResidualOp V ins res → HList M.Val ins → ROp M
  | .give kind getters τ, .cons v .nil => .give kind getters at_ τ v
  | .get kind giver τ, .nil => .get kind giver at_ τ
  | .own kind hearers _ τ, vs => .own kind hearers at_ _ vs τ
  | .hear kind owner τ, .nil => .hear kind owner at_ τ
  | .begin, .nil => .begin at_
  | .settle, .nil => .settle at_

/-- Package a reply from `RSig M` into the result `HList M.Val res` of a static effect. -/
def ResidualOp.replyOf {ins res : List V.Ty} (at_ : Occurrence) :
    (op : ResidualOp V ins res) → (vs : HList M.Val ins) →
    (RSig M).Reply (op.toROp M at_ vs) → HList M.Val res
  | .give _ _ _, .cons _ .nil, _ => .nil
  | .get _ _ _, .nil, v => .cons v .nil
  | .own _ _ _ _, _, v => .cons v .nil
  | .hear _ _ _, .nil, v => .cons v .nil
  | .begin, .nil, n => .cons n .nil
  | .settle, .nil, _ => .nil

theorem ResidualOp.toROp_occurrence {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.occurrence M (op.toROp M at_ vs) = at_ := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_part {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.part M (op.toROp M at_ vs) = op.part := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_takes {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.takes M (op.toROp M at_ vs) = ins := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_gives {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.gives M (op.toROp M at_ vs) = res := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_payload {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    cast (congrArg (HList M.Val) (op.toROp_takes M at_ vs)) (ROp.payload M (op.toROp M at_ vs)) = vs := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.replyOf_reply {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) (out : HList M.Val res) :
    op.replyOf M at_ vs (ROp.reply M (op.toROp M at_ vs)
      (cast (congrArg (HList M.Val) (op.toROp_gives M at_ vs).symm) out)) = out := by
  cases op with
  | give _ _ _ => cases vs with | cons _ r => cases r; cases out; rfl
  | get _ _ _ => cases vs; cases out with | cons _ r => cases r; rfl
  | own _ _ _ _ => cases out with | cons _ r => cases r; rfl
  | hear _ _ _ => cases vs; cases out with | cons _ r => cases r; rfl
  | begin => cases vs; cases out with | cons _ r => cases r; rfl
  | settle => cases vs; cases out; rfl

end ResidualOpSemantics

/-! ## Residual closed IR (`ClosedProcSig`, `ClosedTerm`, `ClosedProcs`, `ClosedRole`) -/

/-- Loop iteration count for a specialized closed term. -/
inductive ClosedTimes {V : Vocabulary} (Γ : Ctx V.Ty) where
  | fixed (n : Nat)
  | value (count : Var Γ .nat)

/-- Static size of a closed loop count, when fixed. -/
def ClosedTimes.size {V : Vocabulary} {Γ : Ctx V.Ty} : ClosedTimes Γ → Option Nat
  | .fixed n => some n
  | .value _ => none

/-- The `again` local terms of a handler stack, one per layer state type in `σ`. -/
abbrev StackAgain (V : Vocabulary) (fns : List (FnHeader V)) (σ : List V.Ty) : Type :=
  HList (fun τ => Term (localDialect V fns) (Ctx.positional [.nat, τ, τ]) [τ]) σ

/-- The `start` local terms of a handler stack, initializing `σ` from `taken` and `heldIns`. -/
inductive StackInit (V : Vocabulary) (fns : List (FnHeader V)) (heldIns : List V.Ty) :
    List V.Ty → List V.Ty → Type where
  | nil : StackInit V fns heldIns [] []
  | cons {τ : V.Ty} {takes : List V.Ty} {σ_rest takes_rest : List V.Ty}
      (start : Term (localDialect V fns) (Ctx.positional (takes ++ heldIns)) [τ])
      (rest : StackInit V fns heldIns σ_rest takes_rest) :
      StackInit V fns heldIns (τ :: σ_rest) (takes ++ takes_rest)

/-- The `finish` local terms of a handler stack, producing `gives` from final states `σ`. -/
inductive StackFinish (V : Vocabulary) (fns : List (FnHeader V)) :
    List V.Ty → List V.Ty → Type where
  | nil : StackFinish V fns [] []
  | cons {τ : V.Ty} {gives : List V.Ty} {σ_rest gives_rest : List V.Ty}
      (finish : Term (localDialect V fns) (Ctx.positional [τ]) gives)
      (rest : StackFinish V fns σ_rest gives_rest) :
      StackFinish V fns (τ :: σ_rest) (gives ++ gives_rest)

/-- Context extended with an optional loop index name and carried variable names. -/
def loopBodyCtx {V : Vocabulary} (Γ : Ctx V.Ty) (idxName : Option Name) {carried : List V.Ty}
    (carriedNames : Names carried) : Ctx V.Ty :=
  (match idxName with | some nm => Γ.insert nm .nat | none => Γ).extend carriedNames

/-- Signature of a shared specialized closed procedure: threaded states, inputs, and outputs. -/
structure ClosedProcSig (V : Vocabulary) where
  states : List V.Ty
  ins : List V.Ty
  outs : List V.Ty

mutual
  /-- A handler-free, plain-typed imperative role term threading layer states `σ : List V.Ty`
  and optionally invoking shared procedures in `procs : List (ClosedProcSig V)`. -/
  inductive ClosedTerm (V : Vocabulary) (fns : List (FnHeader V))
      (procs : List (ClosedProcSig V)) :
      List V.Ty → Ctx V.Ty → List V.Ty → Type where
    | ret {σ Γ outs} (exit : HList (Var Γ) outs) : ClosedTerm V fns procs σ Γ outs
    | letBind {σ Γ outs mid} (first : ClosedTerm V fns procs σ Γ mid)
        (results : Names mid) (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    /-- Run `first`, then run `second` for its effects/state updates, returning `first`'s values. -/
    | seq {σ Γ mid} (first : ClosedTerm V fns procs σ Γ mid)
        (second : ClosedTerm V fns procs σ Γ []) :
        ClosedTerm V fns procs σ Γ mid
    | alias {σ Γ outs τ} (x : Var Γ τ) (name : Name)
        (rest : ClosedTerm V fns procs σ (Γ.insert name τ) outs) :
        ClosedTerm V fns procs σ Γ outs
    | localOp {σ Γ outs ins res} (key : Key) (o : LocalOp V fns ins res)
        (operands : HList (Var Γ) ins) (results : Names res)
        (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    | guard {σ Γ outs} (key : Key) (c : Var Γ .bool) (why : Reason)
        (rest : ClosedTerm V fns procs σ Γ outs) :
        ClosedTerm V fns procs σ Γ outs
    | choose {σ Γ outs mid} (key : Key) (c : Var Γ .bool)
        (onTrue onFalse : ClosedTerm V fns procs σ Γ mid) (results : Names mid)
        (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    | cases {σ Γ outs mid vkey alts} (key : Key) (x : Var Γ (.variant vkey alts))
        (arms : ClosedArms V fns procs σ Γ mid alts.toList) (results : Names mid)
        (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    | loop {σ Γ outs carried each} (key : Key) (times : ClosedTimes Γ)
        (initial : HList (Var Γ) carried) (idxName : Option Name) (carriedNames : Names carried)
        (body : ClosedTerm V fns procs σ (loopBodyCtx Γ idxName carriedNames) (carried ++ each))
        (results : Names (carried ++ each.map (fun τ => .seq τ times.size)))
        (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    | block {σ Γ outs mid} (key : Key) (number : Nat)
        (body : ClosedTerm V fns procs σ Γ mid) (results : Names mid)
        (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    /-- Inlined protocol call frame (pushing `.application key` onto the path when `appKey = some key`). -/
    | frame {σ Γ outs argTys mid} (appKey : Option Key)
        (args : HList (Var Γ) argTys) (inputs : Names argTys)
        (body : ClosedTerm V fns procs σ (Ctx.empty.extend inputs) mid)
        (results : Names mid) (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    /-- DAG-shared call to an earlier specialized procedure in `procs` (pushing `.application key`
    when `appKey = some key`). Avoids exponential duplication on diamond protocol call graphs. -/
    | call {σ Γ outs argTys mid} (appKey : Option Key)
        (callee : Member procs ⟨σ, argTys, mid⟩)
        (args : HList (Var Γ) argTys) (results : Names mid)
        (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs
    /-- Inlined clause of the top layer `τ` executing over lower layer states `σ_rest`.
    On halt, preserves the top layer's state before the clause, matching `Clause.answer`. -/
    | withLayer {τ : V.Ty} {σ_rest : List V.Ty} {Γ argTys mid}
        (args : HList (Var Γ) argTys) (inputs : Names (argTys ++ [τ]))
        (body : ClosedTerm V fns procs σ_rest (Ctx.empty.extend inputs) (mid ++ [τ])) :
        ClosedTerm V fns procs (τ :: σ_rest) Γ mid
    /-- Delegate an unhandled effect at the top layer `τ` to the lower layers `σ_rest`. -/
    | underLayer {τ : V.Ty} {σ_rest : List V.Ty} {Γ mid}
        (inner : ClosedTerm V fns procs σ_rest Γ mid) :
        ClosedTerm V fns procs (τ :: σ_rest) Γ mid
    /-- Unhandled residual effect reaching the bottom of the stack (`σ = []`). -/
    | effect {Γ ins res} (key : Key) (op : ResidualOp V ins res)
        (operands : HList (Var Γ) ins) : ClosedTerm V fns procs [] Γ res
    /-- Structured bounded retry loop lowered from a retried `.attempt`. -/
    | retry {σ Γ outs mid} (key : Key) (bound : Nat) (again : StackAgain V fns σ)
        (inputs : Names [.nat]) (body : ClosedTerm V fns procs σ (Γ.extend inputs) mid)
        (results : Names mid) (rest : ClosedTerm V fns procs σ (Γ.extend results) outs) :
        ClosedTerm V fns procs σ Γ outs

  /-- Variant case arms for `ClosedTerm.cases`. -/
  inductive ClosedArms (V : Vocabulary) (fns : List (FnHeader V))
      (procs : List (ClosedProcSig V)) :
      List V.Ty → Ctx V.Ty → List V.Ty → List V.Ty → Type where
    | nil {σ Γ mid} : ClosedArms V fns procs σ Γ mid []
    | cons {σ Γ mid payload payloads} (inputs : Names [payload])
        (arm : ClosedTerm V fns procs σ (Γ.extend inputs) mid)
        (rest : ClosedArms V fns procs σ Γ mid payloads) :
        ClosedArms V fns procs σ Γ mid (payload :: payloads)
end

/-- Acyclic bottom-up table of shared specialized procedures. Each procedure body may call only
procedures declared strictly earlier in `rest`, ensuring total termination without fuel. -/
inductive ClosedProcs (V : Vocabulary) (fns : List (FnHeader V)) :
    List (ClosedProcSig V) → Type where
  | nil : ClosedProcs V fns []
  | cons {σ ins outs : List V.Ty} {rest : List (ClosedProcSig V)}
      (inputs : Names ins)
      (body : ClosedTerm V fns rest σ (Ctx.empty.extend inputs) outs)
      (tail : ClosedProcs V fns rest) :
      ClosedProcs V fns (⟨σ, ins, outs⟩ :: rest)

/-- Cast a `ClosedTerm` across equal context and output types. -/
def ClosedTerm.castCT {V : Vocabulary} {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    {σ : List V.Ty} {Γ₁ Γ₂ : Ctx V.Ty} {outs₁ outs₂ : List V.Ty}
    (hΓ : Γ₁ = Γ₂) (hOut : outs₁ = outs₂) (t : ClosedTerm V fns procs σ Γ₁ outs₁) :
    ClosedTerm V fns procs σ Γ₂ outs₂ :=
  hΓ ▸ hOut ▸ t

mutual
  /-- Weaken a `ClosedTerm`'s procedure references along an embedding `pLift`. -/
  def ClosedTerm.liftProcs {V : Vocabulary} {fns : List (FnHeader V)}
      {procs₁ procs₂ : List (ClosedProcSig V)}
      (pLift : ∀ {sig}, Member procs₁ sig → Member procs₂ sig) :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {outs : List V.Ty} →
      ClosedTerm V fns procs₁ σ Γ outs → ClosedTerm V fns procs₂ σ Γ outs
    | _, _, _, .ret exit => .ret exit
    | _, _, _, .letBind first results rest =>
        .letBind (first.liftProcs pLift) results (rest.liftProcs pLift)
    | _, _, _, .seq first second =>
        .seq (first.liftProcs pLift) (second.liftProcs pLift)
    | _, _, _, .alias x name rest => .alias x name (rest.liftProcs pLift)
    | _, _, _, .localOp key o operands results rest =>
        .localOp key o operands results (rest.liftProcs pLift)
    | _, _, _, .guard key c why rest => .guard key c why (rest.liftProcs pLift)
    | _, _, _, .choose key c onTrue onFalse results rest =>
        .choose key c (onTrue.liftProcs pLift) (onFalse.liftProcs pLift) results (rest.liftProcs pLift)
    | _, _, _, .cases key x arms results rest =>
        .cases key x (arms.liftProcs pLift) results (rest.liftProcs pLift)
    | _, _, _, .loop key times init idxNm cNames body results rest =>
        .loop key times init idxNm cNames (body.liftProcs pLift) results (rest.liftProcs pLift)
    | _, _, _, .block key number body results rest =>
        .block key number (body.liftProcs pLift) results (rest.liftProcs pLift)
    | _, _, _, .frame appKey args inputs body results rest =>
        .frame appKey args inputs (body.liftProcs pLift) results (rest.liftProcs pLift)
    | _, _, _, .call appKey callee args results rest =>
        .call appKey (pLift callee) args results (rest.liftProcs pLift)
    | _, _, _, .withLayer args inputs body =>
        .withLayer args inputs (body.liftProcs pLift)
    | _, _, _, .underLayer inner => .underLayer (inner.liftProcs pLift)
    | _, _, _, .effect key op operands => .effect key op operands
    | _, _, _, .retry key bound again inputs body results rest =>
        .retry key bound again inputs (body.liftProcs pLift) results (rest.liftProcs pLift)

  /-- Weaken `ClosedArms`'s procedure references along an embedding `pLift`. -/
  def ClosedArms.liftProcs {V : Vocabulary} {fns : List (FnHeader V)}
      {procs₁ procs₂ : List (ClosedProcSig V)}
      (pLift : ∀ {sig}, Member procs₁ sig → Member procs₂ sig) :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {mid payloads : List V.Ty} →
      ClosedArms V fns procs₁ σ Γ mid payloads → ClosedArms V fns procs₂ σ Γ mid payloads
    | _, _, _, _, .nil => .nil
    | _, _, _, _, .cons inputs arm rest =>
        .cons inputs (arm.liftProcs pLift) (rest.liftProcs pLift)
end

/-- A specialized, handler-free role program ready for direct execution, carrying its DAG of
shared helper procedures `procs`. -/
structure ClosedRole (V : Vocabulary) (fns : List (FnHeader V)) (r : Role)
    (ins outs : List (LTy V)) (taken gives : List V.Ty) where
  states : List V.Ty
  procSigs : List (ClosedProcSig V)
  procs : ClosedProcs V fns procSigs
  inputs : Names (held r ins)
  start : StackInit V fns (held r ins) states taken
  body : ClosedTerm V fns procSigs states (Ctx.empty.extend inputs) (held r outs)
  finish : StackFinish V fns states gives

/-! ## AST size metrics (DAG compactness) -/

mutual
  /-- Node count of a `ClosedTerm`. -/
  def ClosedTerm.astSize {V : Vocabulary} {fns : List (FnHeader V)}
      {procs : List (ClosedProcSig V)} :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {outs : List V.Ty} →
      ClosedTerm V fns procs σ Γ outs → Nat
    | _, _, _, .ret _ => 1
    | _, _, _, .letBind first _ rest => 1 + first.astSize + rest.astSize
    | _, _, _, .seq first second => 1 + first.astSize + second.astSize
    | _, _, _, .alias _ _ rest => 1 + rest.astSize
    | _, _, _, .localOp _ _ _ _ rest => 1 + rest.astSize
    | _, _, _, .guard _ _ _ rest => 1 + rest.astSize
    | _, _, _, .choose _ _ t f _ rest => 1 + t.astSize + f.astSize + rest.astSize
    | _, _, _, .cases _ _ arms _ rest => 1 + arms.astSize + rest.astSize
    | _, _, _, .loop _ _ _ _ _ body _ rest => 1 + body.astSize + rest.astSize
    | _, _, _, .block _ _ body _ rest => 1 + body.astSize + rest.astSize
    | _, _, _, .frame _ _ _ body _ rest => 1 + body.astSize + rest.astSize
    | _, _, _, .call _ _ _ _ rest => 1 + rest.astSize
    | _, _, _, .withLayer _ _ body => 1 + body.astSize
    | _, _, _, .underLayer inner => 1 + inner.astSize
    | _, _, _, .effect _ _ _ => 1
    | _, _, _, .retry _ _ _ _ body _ rest => 1 + body.astSize + rest.astSize

  /-- Node count of `ClosedArms`. -/
  def ClosedArms.astSize {V : Vocabulary} {fns : List (FnHeader V)}
      {procs : List (ClosedProcSig V)} :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {mid payloads : List V.Ty} →
      ClosedArms V fns procs σ Γ mid payloads → Nat
    | _, _, _, _, .nil => 0
    | _, _, _, _, .cons _ arm rest => arm.astSize + rest.astSize
end

/-- Total AST node count of all shared helper procedures in `ClosedProcs`. -/
def ClosedProcs.astSize {V : Vocabulary} {fns : List (FnHeader V)} :
    {procs : List (ClosedProcSig V)} → ClosedProcs V fns procs → Nat
  | [], .nil => 0
  | _ :: _, .cons _ body tail => body.astSize + tail.astSize

/-- Total AST node count of a `ClosedRole` (all shared helper procedures plus the entry body). -/
def ClosedRole.astSize {V : Vocabulary} {fns : List (FnHeader V)} {r : Role}
    {ins outs : List (LTy V)} {taken gives : List V.Ty}
    (cr : ClosedRole V fns r ins outs taken gives) : Nat :=
  cr.procs.astSize + cr.body.astSize

/-! ## Denotational semantics of `ClosedTerm`, `ClosedProcs`, and `ClosedRole` -/

section ClosedSemantics
variable {V : Vocabulary} (M : Model V)

/-- Evaluate a stack's `again` terms on `(i, entry, stop)`. -/
def StackAgain.eval {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
    {σ : List V.Ty} → StackAgain V fns σ → Nat → HList M.Val σ → HList M.Val σ →
    Except Stop (HList M.Val σ)
  | [], .nil, _, .nil, .nil => .ok .nil
  | _ :: _, .cons ag rest, i, .cons e es, .cons t ts =>
      match ag.denote (localSem M fns fnTable) []
          (Env.positional (.cons (i : Nat) (.cons e (.cons t .nil)))) with
      | .done (.cons next .nil) =>
          (StackAgain.eval fnTable rest i es ts).map fun more => .cons next more
      | .halt why => .error why
      | .call op _ => nomatch op

/-- Evaluate `StackInit` to produce the initial stack state. -/
def StackInit.denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) {heldIns : List V.Ty} :
    {σ taken : List V.Ty} → StackInit V fns heldIns σ taken →
    HList M.Val heldIns → HList M.Val taken → Program M (HList M.Val σ)
  | [], [], .nil, _, .nil => .done .nil
  | _ :: _, _, .cons (takes := takes) st rest, ins, taken =>
      let parts := HList.split takes taken
      (liftLocal id (st.denote (localSem M fns fnTable) []
        (Env.positional (HList.append parts.1 ins)))).bind fun first =>
        (rest.denote fnTable ins parts.2).map fun others => .cons first.single others

/-- Evaluate `StackFinish` on the final stack state to produce what the layers give. -/
def StackFinish.denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
    {σ gives : List V.Ty} → StackFinish V fns σ gives →
    HList M.Val σ → Program M (HList M.Val gives)
  | [], [], .nil, .nil => .done .nil
  | _ :: _, _, .cons fin rest, .cons s states =>
      (liftLocal id (fin.denote (localSem M fns fnTable) [] (Env.positional (.cons s .nil)))).bind
        fun mine => (rest.denote fnTable states).map fun others => HList.append mine others

/-- Evaluate a `ClosedTimes` count in a plain environment. -/
def ClosedTimes.eval {Γ : Ctx V.Ty} (env : Env M.Val Γ) : ClosedTimes Γ → Nat
  | .fixed n => n
  | .value count => env.get count

/-- Extend an environment for a `ClosedTerm.loop` body iteration. -/
def loopBodyEnv {Γ : Ctx V.Ty} (env : Env M.Val Γ) (idxName : Option Name) (i : Nat)
    {carried : List V.Ty} (carriedNames : Names carried) (vals : HList M.Val carried) :
    Env M.Val (loopBodyCtx Γ idxName carriedNames) :=
  match idxName with
  | some nm => (env.insert nm (i : Nat)).extend carriedNames vals
  | none => env.extend carriedNames vals

/-- Structured retry loop over a body returning `Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ)`. -/
def retryAttempts {σ : List V.Ty} {A : Type} (exhausted : Stop)
    (again : Nat → HList M.Val σ → HList M.Val σ → Except Stop (HList M.Val σ))
    (body : Nat → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ))
    (entry : HList M.Val σ) :
    Nat → Nat → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ)
  | 0, _, s => .halt (exhausted, s)
  | n + 1, i, s => (body i s).recover fun stop =>
      if Stop.isAbort stop.1 then
        match n with
        | 0 => .halt (exhausted, stop.2)
        | _ + 1 =>
            match again (i + 1) entry stop.2 with
            | .ok next => retryAttempts exhausted again body entry n (i + 1) next
            | .error why => .halt (why, stop.2)
      else .halt stop

/-- Semantic lookup table for a list of shared closed procedure signatures. -/
abbrev ClosedProcTable (procs : List (ClosedProcSig V)) : Type :=
  (sig : ClosedProcSig V) → Member procs sig →
    List Frame → HList M.Val sig.ins → HList M.Val sig.states →
    Process (RSig M) (Stop × HList M.Val sig.states) (HList M.Val sig.outs × HList M.Val sig.states)

/-- Empty procedure table for `procs = []`. -/
def ClosedProcTable.empty : ClosedProcTable M [] := fun _ m => nomatch m

mutual
  /-- Denotation of a `ClosedTerm`, threading stack states `HList M.Val σ`. -/
  def ClosedTerm.denote {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
      (fnTable : FnTable M fns) (procTable : ClosedProcTable M procs) :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {outs : List V.Ty} →
      ClosedTerm V fns procs σ Γ outs → List Frame → Env M.Val Γ → HList M.Val σ →
      Process (RSig M) (Stop × HList M.Val σ) (HList M.Val outs × HList M.Val σ)
    | _, _, _, .ret exit, _, env, st => .done (env.all exit, st)
    | _, _, _, .letBind first results rest, path, env, st =>
        (first.denote fnTable procTable path env st).bind fun out =>
          rest.denote fnTable procTable path (env.extend results out.1) out.2
    | _, _, _, .seq first second, path, env, st =>
        (first.denote fnTable procTable path env st).bind fun out =>
          (second.denote fnTable procTable path env out.2).map fun out2 => (out.1, out2.2)
    | _, _, _, .alias x name rest, path, env, st =>
        rest.denote fnTable procTable path (env.insert name (env.get x)) st
    | _, _, _, .localOp _ o operands results rest, path, env, st =>
        (liftLocal (fun why => (why, st)) (localOp M fnTable o (env.all operands))).bind fun vs =>
          rest.denote fnTable procTable path (env.extend results vs) st
    | _, _, _, .guard key c why rest, path, env, st =>
        bif env.get c then rest.denote fnTable procTable path env st
        else .halt (.declared why ⟨path, key⟩, st)
    | _, _, _, .choose _ c onTrue onFalse results rest, path, env, st =>
        (bif env.get c then onTrue.denote fnTable procTable path env st
         else onFalse.denote fnTable procTable path env st).bind fun out =>
          rest.denote fnTable procTable path (env.extend results out.1) out.2
    | _, _, _, .cases (alts := alts) _ x arms results rest, path, env, st =>
        (arms.denote fnTable procTable path env st (Tys.pick M alts (env.get x))).bind fun out =>
          rest.denote fnTable procTable path (env.extend results out.1) out.2
    | σ, _, _, .loop (carried := carried) (each := each) key times initial idxName carriedNames
        body results rest, path, env, st =>
        let step := fun (i : Nat)
            (ls : (HList M.Val carried × HList (fun τ => List (M.Val τ)) each) × HList M.Val σ) =>
          (body.denote fnTable procTable (path ++ [.iteration key i])
              (loopBodyEnv M env idxName i carriedNames ls.1.1) ls.2).bind fun out =>
            let sp := HList.split carried out.1
            .done ((sp.1, ls.1.2.push sp.2), out.2)
        (Process.iterate (times.eval M env) step 0 ((env.all initial, HList.empties each), st)).bind
          fun ls =>
            rest.denote fnTable procTable path
              (env.extend results (ls.1.1.append (closedCollected M times.size ls.1.2))) ls.2
    | _, _, _, .block key number body results rest, path, env, st =>
        (body.denote fnTable procTable (path ++ [.iteration key number]) env st).bind fun out =>
          rest.denote fnTable procTable path (env.extend results out.1) out.2
    | _, _, _, .frame appKey args inputs body results rest, path, env, st =>
        let subPath := match appKey with | some k => path ++ [.application k] | none => path
        (body.denote fnTable procTable subPath (Env.empty.extend inputs (env.all args)) st).bind fun out =>
          rest.denote fnTable procTable path (env.extend results out.1) out.2
    | _, _, _, .call appKey callee args results rest, path, env, st =>
        let subPath := match appKey with | some k => path ++ [.application k] | none => path
        (procTable _ callee subPath (env.all args) st).bind fun out =>
          rest.denote fnTable procTable path (env.extend results out.1) out.2
    | _ :: _, _, _, .withLayer (mid := mid) args inputs body, path, env, .cons mine below =>
        ((body.denote fnTable procTable path
            (Env.empty.extend inputs ((env.all args).append (.cons mine .nil))) below).mapHalt
            fun stop => (stop.1, .cons mine stop.2)).map fun out =>
          let sp := HList.split mid out.1
          (sp.1, .cons sp.2.single out.2)
    | _ :: _, _, _, .underLayer inner, path, env, .cons mine below =>
        ((inner.denote fnTable procTable path env below).mapHalt
            fun stop => (stop.1, .cons mine stop.2)).map fun out =>
          (out.1, .cons mine out.2)
    | [], _, _, .effect key op operands, path, env, .nil =>
        .call (op.toROp M ⟨path, key⟩ (env.all operands)) fun reply =>
          .done (op.replyOf M ⟨path, key⟩ (env.all operands) reply, .nil)
    | _, _, _, .retry key bound again inputs body results rest, path, env, st =>
        (retryAttempts M (.declared .exhausted ⟨path, key⟩)
          (StackAgain.eval M fnTable again)
          (fun i s' => Process.markOwn M (.attempt key i)
            (body.denote fnTable procTable path (env.extend inputs (.cons (i : Nat) .nil)) s'))
          st bound 0 st).bind fun out =>
          rest.denote fnTable procTable path (env.extend results out.1) out.2

  /-- Denotation of `ClosedArms`. -/
  def ClosedArms.denote {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
      (fnTable : FnTable M fns) (procTable : ClosedProcTable M procs) :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {mid payloads : List V.Ty} →
      ClosedArms V fns procs σ Γ mid payloads → List Frame → Env M.Val Γ → HList M.Val σ →
      Pick M.Val payloads →
      Process (RSig M) (Stop × HList M.Val σ) (HList M.Val mid × HList M.Val σ)
    | _, _, _, _, .cons inputs arm _, path, env, st, .here v =>
        arm.denote fnTable procTable path (env.extend inputs (.cons v .nil)) st
    | _, _, _, _, .cons _ _ rest, path, env, st, .there p =>
        rest.denote fnTable procTable path env st p
end

/-- Bottom-up denotation of a `ClosedProcs` DAG into a `ClosedProcTable`. -/
def ClosedProcs.denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
    {procs : List (ClosedProcSig V)} → ClosedProcs V fns procs → ClosedProcTable M procs
  | [], .nil, _, m => nomatch m
  | _ :: _, .cons inputs body tail, _, .head =>
      fun path args st => body.denote M fnTable (tail.denote fnTable) path (Env.empty.extend inputs args) st
  | _ :: _, .cons _ _ tail, _, .tail m => tail.denote fnTable _ m

/-- Denotation of a `ClosedRole` directly on plain held inputs and outputs (no `RV`/`LTy`). -/
def ClosedRole.denoteHeld {fns : List (FnHeader V)} {r : Role}
    {ins outs : List (LTy V)} {taken gives : List V.Ty}
    (fnTable : FnTable M fns) (cr : ClosedRole V fns r ins outs taken gives)
    (heldIns : HList M.Val (held r ins)) (takenVals : HList M.Val taken) :
    Process (RSig M) Stop (HList M.Val (held r outs) × HList M.Val gives) :=
  (cr.start.denote M fnTable heldIns takenVals).bind fun st0 =>
    ((cr.body.denote M fnTable (cr.procs.denote M fnTable) []
        (Env.empty.extend cr.inputs heldIns) st0).mapHalt Prod.fst).bind
      fun out => (cr.finish.denote M fnTable out.2).map fun g => (out.1, g)

/-- Denotation of a `ClosedRole` matching `Deployed.run`'s signature. -/
def ClosedRole.denote {fns : List (FnHeader V)} {r : Role}
    {ins outs : List (LTy V)} {taken gives : List V.Ty}
    (fnTable : FnTable M fns) (cr : ClosedRole V fns r ins outs taken gives)
    (inputVals : HList (RV M r) ins) (takenVals : HList M.Val taken) :
    Process (RSig M) Stop (HList (RV M r) outs × HList M.Val gives) :=
  (cr.denoteHeld M fnTable (heldValues M r inputVals) takenVals).map fun out =>
    (unheldValues M r out.1, out.2)

/-! ### `castCT` and `liftProcs` denotation lemmas -/

theorem closedTerm_denote_castCT {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fnTable : FnTable M fns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} {Γ₁ Γ₂ : Ctx V.Ty} {outs₁ outs₂ : List V.Ty}
    (hΓ : Γ₁ = Γ₂) (hOut : outs₁ = outs₂) (t : ClosedTerm V fns procs σ Γ₁ outs₁)
    (path : List Frame) (env : Env M.Val Γ₂) (s : HList M.Val σ) :
    (t.castCT hΓ hOut).denote M fnTable procTable path env s =
      (t.denote M fnTable procTable path (cast (congrArg (Env M.Val) hΓ.symm) env) s).map fun out =>
        (cast (congrArg (HList M.Val) hOut) out.1, out.2) := by
  subst hΓ; subst hOut
  exact (Process.map_id' _).symm

theorem closedTerm_denote_castExt {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fnTable : FnTable M fns) (procTable : ClosedProcTable M procs)
    {σ : List V.Ty} {Δ : Ctx V.Ty} {as bs : List V.Ty} (h : as = bs)
    (ns : Names as) (vs : HList M.Val as) {outs : List V.Ty}
    (t : ClosedTerm V fns procs σ (Δ.extend ns) outs)
    (path : List Frame) (cenv : Env M.Val Δ) (s : HList M.Val σ) :
    (t.castCT (ctx_extend_cast Δ h ns).symm rfl).denote M fnTable procTable path
        (cenv.extend (cast (congrArg Names h) ns) (cast (congrArg (HList M.Val) h) vs)) s =
      t.denote M fnTable procTable path (cenv.extend ns vs) s := by
  subst h; rfl

mutual
  theorem closedTerm_denote_liftProcs {fns : List (FnHeader V)}
      {procs₁ procs₂ : List (ClosedProcSig V)}
      (fnTable : FnTable M fns)
      (pt₁ : ClosedProcTable M procs₁) (pt₂ : ClosedProcTable M procs₂)
      (pLift : ∀ {sig}, Member procs₁ sig → Member procs₂ sig)
      (hLift : ∀ sig (m : Member procs₁ sig), pt₂ sig (pLift m) = pt₁ sig m) :
      ∀ {σ : List V.Ty} {Γ : Ctx V.Ty} {outs : List V.Ty}
        (t : ClosedTerm V fns procs₁ σ Γ outs)
        (path : List Frame) (env : Env M.Val Γ) (s : HList M.Val σ),
        (t.liftProcs pLift).denote M fnTable pt₂ path env s =
          t.denote M fnTable pt₁ path env s
    | _, _, _, .ret _, _, _, _ => rfl
    | _, _, _, .letBind first _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift first]
        congr 1; funext out
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest _ _ _
    | _, _, _, .seq first second, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift first]
        congr 1; funext out
        rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift second]
    | _, _, _, .alias _ _ rest, path, env, s =>
        closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ s
    | _, _, _, .localOp _ _ _ _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        congr 1; funext vs
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ s
    | _, _, _, .guard _ c _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        cases env.get c with
        | false => rfl
        | true => exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path env s
    | _, _, _, .choose _ c onTrue onFalse _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        cases env.get c with
        | false =>
            dsimp only [cond]
            rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift onFalse]
            congr 1; funext out
            exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ out.2
        | true =>
            dsimp only [cond]
            rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift onTrue]
            congr 1; funext out
            exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ out.2
    | _, _, _, .cases _ _ arms _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        rw [closedArms_denote_liftProcs fnTable pt₁ pt₂ pLift hLift arms]
        congr 1; funext out
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ out.2
    | σ, _, _, .loop (carried := carried) (each := each) key times _ idxName carriedNames body _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        have hStep : (fun (i : Nat)
              (ls : (HList M.Val carried × HList (fun τ => List (M.Val τ)) each) × HList M.Val σ) =>
              ((body.liftProcs pLift).denote M fnTable pt₂ (path ++ [.iteration key i])
                (loopBodyEnv M env idxName i carriedNames ls.1.1) ls.2).bind fun out =>
                let sp := HList.split carried out.1; .done ((sp.1, ls.1.2.push sp.2), out.2)) =
            (fun (i : Nat)
              (ls : (HList M.Val carried × HList (fun τ => List (M.Val τ)) each) × HList M.Val σ) =>
              (body.denote M fnTable pt₁ (path ++ [.iteration key i])
                (loopBodyEnv M env idxName i carriedNames ls.1.1) ls.2).bind fun out =>
                let sp := HList.split carried out.1; .done ((sp.1, ls.1.2.push sp.2), out.2)) := by
          funext i ls
          rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift body]
        rw [hStep]
        congr 1; funext ls
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ ls.2
    | _, _, _, .block _ _ body _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift body]
        congr 1; funext out
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ out.2
    | _, _, _, .frame _ _ _ body _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift body]
        congr 1; funext out
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ out.2
    | _, _, _, .call _ callee _ _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        rw [hLift _ callee]
        congr 1; funext out
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ out.2
    | _ :: _, _, _, .withLayer _ _ body, path, env, .cons mine below => by
        rw [ClosedTerm.liftProcs, ClosedTerm.denote, ClosedTerm.denote,
          closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift body]
    | _ :: _, _, _, .underLayer inner, path, env, .cons mine below => by
        rw [ClosedTerm.liftProcs, ClosedTerm.denote, ClosedTerm.denote,
          closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift inner]
    | [], _, _, .effect _ _ _, _, _, .nil => rfl
    | σ, _, _, .retry key _ _ inputs body _ rest, path, env, s => by
        dsimp only [ClosedTerm.liftProcs, ClosedTerm.denote]
        have hBodyEq : (fun (i : Nat) (s' : HList M.Val σ) => Process.markOwn M (.attempt key i)
              ((body.liftProcs pLift).denote M fnTable pt₂ path (env.extend inputs (.cons (i : Nat) .nil)) s')) =
            (fun (i : Nat) (s' : HList M.Val σ) => Process.markOwn M (.attempt key i)
              (body.denote M fnTable pt₁ path (env.extend inputs (.cons (i : Nat) .nil)) s')) := by
          funext i s'
          rw [closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift body]
        rw [hBodyEq]
        congr 1; funext out
        exact closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path _ out.2

  theorem closedArms_denote_liftProcs {fns : List (FnHeader V)}
      {procs₁ procs₂ : List (ClosedProcSig V)}
      (fnTable : FnTable M fns)
      (pt₁ : ClosedProcTable M procs₁) (pt₂ : ClosedProcTable M procs₂)
      (pLift : ∀ {sig}, Member procs₁ sig → Member procs₂ sig)
      (hLift : ∀ sig (m : Member procs₁ sig), pt₂ sig (pLift m) = pt₁ sig m) :
      ∀ {σ : List V.Ty} {Γ : Ctx V.Ty} {mid payloads : List V.Ty}
        (arms : ClosedArms V fns procs₁ σ Γ mid payloads)
        (path : List Frame) (env : Env M.Val Γ) (s : HList M.Val σ) (pk : Pick M.Val payloads),
        (arms.liftProcs pLift).denote M fnTable pt₂ path env s pk =
          arms.denote M fnTable pt₁ path env s pk
    | _, _, _, _, .nil, _, _, _, pk => nomatch pk
    | _, _, _, _, .cons _ arm _, path, _env, s, .here _ =>
        closedTerm_denote_liftProcs fnTable pt₁ pt₂ pLift hLift arm path _ s
    | _, _, _, _, .cons _ _ rest, path, env, s, .there pk =>
        closedArms_denote_liftProcs fnTable pt₁ pt₂ pLift hLift rest path env s pk
end

end ClosedSemantics

end Zkc.Core
