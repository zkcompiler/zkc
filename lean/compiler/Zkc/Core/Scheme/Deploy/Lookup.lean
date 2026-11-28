module

public import Zkc.Core.Scheme.Layer.Combinators
public import Zkc.Core.World.Network

@[expose] public section

/-!
Strict unique module slot resolution (including distribution-aware `V.LawKey`-keyed
`SuiteSlot.derive` lookup without silent fallback on invalid or duplicate explicit bindings),
used-law encoder distinctness and ideal `serviceKey` freshness checks, deterministic fresh-key
allocation, trailing-message absorption analysis (Chiesa and Orrù (2025), Construction 4.3),
and selected-function suite lawfulness (`Deployed.SuiteLawfulFor`).
-/

namespace Zkc.Core

open LayerBuild

/-! ## Strict unique module lookup helpers -/

section
variable {V : Vocabulary}

/-- Decide equality inside `Option`, returning a proof witness in `PLift`. -/
def guardEq {α : Type} [DecidableEq α] (a b : α) : Option (PLift (a = b)) :=
  if h : a = b then some ⟨h⟩ else none

/-- Return the unique matching result in `xs`, or `none` if zero or multiple entries match. -/
def findUnique {α β : Type} (xs : List α) (pick : α → Option β) : Option β :=
  match xs.filterMap pick with
  | [x] => some x
  | _ => none

/-- Resolve a concrete total unconditional function reference by key and exact signature. -/
def findTypedFnRef (a : Admitted V) (key : Key) (ins outs : List V.Ty) :
    Option (TypedFnRef V a.program.headers.fns ins outs) := do
  let .fn (hdr := hdr) member ← a.program.find key | none
  let ⟨hIn⟩ ← guardEq hdr.ins ins
  let ⟨hOut⟩ ← guardEq hdr.outs outs
  let ⟨hUncond⟩ ← guardEq hdr.summary.requires []
  let ⟨hStop⟩ ← guardEq hdr.canStop false
  pure ⟨hdr, member, hIn, hOut, hUncond, hStop⟩

/-- Resolve a potentially-stopping unconditional function reference by key and exact signature. -/
def findSafeFnRef (a : Admitted V) (key : Key) (ins outs : List V.Ty) :
    Option (SafeFnRef V a.program.headers.fns ins outs) := do
  let .fn (hdr := hdr) member ← a.program.find key | none
  let ⟨hIn⟩ ← guardEq hdr.ins ins
  let ⟨hOut⟩ ← guardEq hdr.outs outs
  let ⟨hUncond⟩ ← guardEq hdr.summary.requires []
  pure ⟨hdr, member, hIn, hOut, hUncond⟩

/-- Find the unique member of `m` at `slot` matching `pick`. Refuses ambiguity whenever more than
one member at `slot` matches `pick`. -/
def findSlotMember {α : Type} (m : ModuleRef) (slot : Key) (pick : Key → Option α) : Option α :=
  findUnique m.members fun (s, defKey) => if s = slot then pick defKey else none

/-- Resolve `SuiteSlot.start : [bytesTy] → [stateTy]`. -/
def findSuiteStart (a : Admitted V) (suite : ModuleRef) :
    Option ((stateTy : V.Ty) × TypedFnRef V a.program.headers.fns [bytesTy] [stateTy]) :=
  findSlotMember suite SuiteSlot.start fun defKey => do
    let .fn (hdr := hdr) member ← a.program.find defKey | none
    match hIn : hdr.ins, hOut : hdr.outs with
    | [inTy], [stateTy] =>
        let ⟨hBytes⟩ ← guardEq inTy bytesTy
        let ⟨hUncond⟩ ← guardEq hdr.summary.requires []
        let ⟨hStop⟩ ← guardEq hdr.canStop false
        pure ⟨stateTy, ⟨hdr, member, by rw [hIn, hBytes], hOut, hUncond, hStop⟩⟩
    | _, _ => none

/-- Resolve `SuiteSlot.absorb : [stateTy, bytesTy, .seq unitTy none] → [stateTy]`. -/
def findSuiteAbsorb (a : Admitted V) (suite : ModuleRef) (stateTy : V.Ty) :
    Option ((unitTy : V.Ty) ×
      TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :=
  findSlotMember suite SuiteSlot.absorb fun defKey => do
    let .fn (hdr := hdr) member ← a.program.find defKey | none
    match hIn : hdr.ins, hOut : hdr.outs with
    | [stIn, lblIn, .seq unitTy none], [stOut] =>
        let ⟨hSt1⟩ ← guardEq stIn stateTy
        let ⟨hLbl⟩ ← guardEq lblIn bytesTy
        let ⟨hSt2⟩ ← guardEq stOut stateTy
        let ⟨hUncond⟩ ← guardEq hdr.summary.requires []
        let ⟨hStop⟩ ← guardEq hdr.canStop false
        pure ⟨unitTy, ⟨hdr, member, by rw [hIn, hSt1, hLbl], by rw [hOut, hSt2], hUncond, hStop⟩⟩
    | _, _ => none

/-- Resolve `SuiteSlot.encode : [τ] → [.seq unitTy none]`. -/
def findSuiteEncode (a : Admitted V) (suite : ModuleRef) (unitTy τ : V.Ty) :
    Option (TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]) :=
  findSlotMember suite SuiteSlot.encode fun defKey =>
    findTypedFnRef a defKey [τ] [.seq unitTy none]

/-- Resolve `SuiteSlot.derive : (stateTy :: bytesTy :: drawIns) → [τ, stateTy]` for sampling law
`law`:
- If `suite.lawMembers` declares one or more `(SuiteSlot.derive, enc.lawKey law, defKey)` entries,
  there must be exactly one such entry and it must resolve to the exact expected signature (never
  silently falling back to `suite.members` on a wrong-typed or duplicate explicit binding).
- Otherwise, there must be a unique matching `(SuiteSlot.derive, defKey)` entry in
  `suite.members`. -/
def findSuiteDerive (enc : VocabEncoder V) (a : Admitted V) (suite : ModuleRef)
    (stateTy : V.Ty) (law : V.LawKey) (drawIns : List V.Ty) (τ : V.Ty) :
    Option (TypedFnRef V a.program.headers.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]) :=
  let explicitKeys : List Key :=
    suite.lawMembers.filterMap fun (s, lb, defKey) =>
      if s = SuiteSlot.derive ∧ lb = enc.lawKey law then some defKey else none
  match explicitKeys with
  | [defKey] => findTypedFnRef a defKey (stateTy :: bytesTy :: drawIns) [τ, stateTy]
  | _ :: _ :: _ => none
  | [] =>
      findSlotMember suite SuiteSlot.derive fun defKey =>
        findTypedFnRef a defKey (stateTy :: bytesTy :: drawIns) [τ, stateTy]

/-- Return the unique unit type appearing in `us` (defaulting to `byteTy` when `us = []`),
or `none` if entries disagree on the unit type. -/
def uniqueUnitTy (us : List V.Ty) : Option V.Ty :=
  match us with
  | [] => some byteTy
  | u :: rest => if rest.all (fun u' => decide (u' = u)) then some u else none

/-- Determine the suite's absorbed unit type from its `SuiteSlot.encode` entries (defaulting to
`byteTy` when no entries are present, refusing conflicting unit types), requiring a non-linear
unit type. Used by pure-path `deployIdeal` without touching concrete `start` or `absorb`. -/
def findSuiteUnit (a : Admitted V) (suite : ModuleRef) :
    Option ((unitTy : V.Ty) × PLift (Ty.isLinear V unitTy = false)) := do
  let units := suite.members.filterMap fun (s, defKey) =>
    if s = SuiteSlot.encode then
      match a.program.find defKey with
      | some (.fn (hdr := hdr) _) =>
          match hdr.outs with
          | [.seq unitTy none] => some unitTy
          | _ => none
      | _ => none
    else none
  let u ← uniqueUnitTy units
  if hfree : Ty.isLinear V u = false then some ⟨u, ⟨hfree⟩⟩ else none

/-- Determine the layout's unit type from its `LayoutSlot.write` / `LayoutSlot.read` entries
(defaulting to `byteTy` when no typed entries are present, refusing conflicting unit types),
requiring a non-linear unit type. -/
def findLayoutUnit (a : Admitted V) (layout : ModuleRef) :
    Option ((unitTy : V.Ty) × PLift (Ty.isLinear V unitTy = false)) := do
  let writeUnits := layout.members.filterMap fun (s, defKey) =>
    if s = LayoutSlot.write then
      match a.program.find defKey with
      | some (.fn (hdr := hdr) _) =>
          match hdr.outs with
          | [.seq unitTy none] => some unitTy
          | _ => none
      | _ => none
    else none
  let readUnits := layout.members.filterMap fun (s, defKey) =>
    if s = LayoutSlot.read then
      match a.program.find defKey with
      | some (.fn (hdr := hdr) _) =>
          match hdr.ins with
          | [.seq unitTy none, .nat] => some unitTy
          | _ => none
      | _ => none
    else none
  let u ← uniqueUnitTy (writeUnits ++ readUnits)
  if hfree : Ty.isLinear V u = false then some ⟨u, ⟨hfree⟩⟩ else none

/-- Resolve `LayoutSlot.write : [τ] → [.seq unitTy none]`. -/
def findLayoutWrite (a : Admitted V) (layout : ModuleRef) (unitTy τ : V.Ty) :
    Option (TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]) :=
  findSlotMember layout LayoutSlot.write fun defKey =>
    findTypedFnRef a defKey [τ] [.seq unitTy none]

/-- Resolve `LayoutSlot.read : [.seq unitTy none, .nat] → [τ, .nat]`. -/
def findLayoutRead (a : Admitted V) (layout : ModuleRef) (unitTy τ : V.Ty) :
    Option (SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]) :=
  findSlotMember layout LayoutSlot.read fun defKey =>
    findSafeFnRef a defKey [.seq unitTy none, .nat] [τ, .nat]

/-- Resolve `LayoutSlot.equal : [τ, τ] → [.bool]`. -/
def findLayoutEqual (a : Admitted V) (layout : ModuleRef) (τ : V.Ty) :
    Option (TypedFnRef V a.program.headers.fns [τ, τ] [.bool]) :=
  findSlotMember layout LayoutSlot.equal fun defKey =>
    findTypedFnRef a defKey [τ, τ] [.bool]

/-! ## Lookup soundness lemmas -/

theorem findUnique_some {α β : Type} {xs : List α} {pick : α → Option β} {y : β}
    (h : findUnique xs pick = some y) :
    ∃ x, x ∈ xs ∧ pick x = some y := by
  unfold findUnique at h
  cases hfm : xs.filterMap pick with
  | nil => rw [hfm] at h; cases h
  | cons z rest =>
      cases rest with
      | cons _ _ => rw [hfm] at h; cases h
      | nil =>
          rw [hfm] at h
          have hy : z = y := Option.some.inj h
          subst hy
          have hmem : z ∈ xs.filterMap pick := by rw [hfm]; exact List.mem_cons_self
          exact List.mem_filterMap.mp hmem

/-- `findSlotMember` returning `some x` witnesses a member `(slot, defKey) ∈ m.members`. -/
theorem findSlotMember_some {α : Type} {m : ModuleRef} {slot : Key} {pick : Key → Option α}
    {x : α} (h : findSlotMember m slot pick = some x) :
    ∃ defKey, (slot, defKey) ∈ m.members ∧ pick defKey = some x := by
  obtain ⟨⟨s, defKey⟩, hIn, hPick⟩ := findUnique_some h
  by_cases hs : s = slot
  · subst hs
    simp only [↓reduceIte] at hPick
    exact ⟨defKey, hIn, hPick⟩
  · simp only [hs, ↓reduceIte] at hPick
    cases hPick

theorem findTypedFnRef_some {a : Admitted V} {defKey : Key} {ins outs : List V.Ty}
    {ref : TypedFnRef V a.program.headers.fns ins outs}
    (h : findTypedFnRef a defKey ins outs = some ref) :
    a.program.find defKey = some (.fn ref.member) := by
  unfold findTypedFnRef at h
  cases hf : a.program.find defKey with
  | none => rw [hf] at h; cases h
  | some found =>
      rw [hf] at h
      cases found with
      | protocol _ => cases h
      | fn member =>
          dsimp only [bind, pure] at h
          rw [Option.bind_some] at h
          dsimp only at h
          obtain ⟨⟨_⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨_⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨_⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨_⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
          cases h; rfl

theorem findSafeFnRef_some {a : Admitted V} {defKey : Key} {ins outs : List V.Ty}
    {ref : SafeFnRef V a.program.headers.fns ins outs}
    (h : findSafeFnRef a defKey ins outs = some ref) :
    a.program.find defKey = some (.fn ref.member) := by
  unfold findSafeFnRef at h
  cases hf : a.program.find defKey with
  | none => rw [hf] at h; cases h
  | some found =>
      rw [hf] at h
      cases found with
      | protocol _ => cases h
      | fn member =>
          dsimp only [bind, pure] at h
          rw [Option.bind_some] at h
          dsimp only at h
          obtain ⟨⟨_⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨_⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨_⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
          cases h; rfl

theorem findSuiteEncode_some {a : Admitted V} {suite : ModuleRef} {unitTy τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]}
    (h : findSuiteEncode a suite unitTy τ = some ref) :
    ∃ defKey, (SuiteSlot.encode, defKey) ∈ suite.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

theorem findSuiteDerive_some {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy : V.Ty} {law : V.LawKey} {drawIns : List V.Ty} {τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]}
    (h : findSuiteDerive enc a suite stateTy law drawIns τ = some ref) :
    ∃ defKey, ((SuiteSlot.derive, enc.lawKey law, defKey) ∈ suite.lawMembers ∨
        (SuiteSlot.derive, defKey) ∈ suite.members) ∧
      a.program.find defKey = some (.fn ref.member) := by
  unfold findSuiteDerive at h
  dsimp only at h
  cases hExp : suite.lawMembers.filterMap (fun x =>
      if x.1 = SuiteSlot.derive ∧ x.2.1 = enc.lawKey law then some x.2.2 else none) with
  | nil =>
      rw [hExp] at h
      obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
      exact ⟨defKey, .inr hIn, findTypedFnRef_some hRef⟩
  | cons defKey rest =>
      cases rest with
      | cons _ _ => rw [hExp] at h; cases h
      | nil =>
          rw [hExp] at h
          have hMem : defKey ∈ suite.lawMembers.filterMap (fun x =>
              if x.1 = SuiteSlot.derive ∧ x.2.1 = enc.lawKey law then some x.2.2 else none) := by
            rw [hExp]; exact List.mem_cons_self
          obtain ⟨⟨s, lb, dk⟩, hIn, hCond⟩ := List.mem_filterMap.mp hMem
          by_cases hc : s = SuiteSlot.derive ∧ lb = enc.lawKey law
          · rcases hc with ⟨rfl, rfl⟩
            simp only [and_self, ↓reduceIte, Option.some.injEq] at hCond
            subst hCond
            exact ⟨dk, .inl hIn, findTypedFnRef_some h⟩
          · simp only [hc, ↓reduceIte] at hCond
            cases hCond

theorem findLayoutWrite_some {a : Admitted V} {layout : ModuleRef} {unitTy τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]}
    (h : findLayoutWrite a layout unitTy τ = some ref) :
    ∃ defKey, (LayoutSlot.write, defKey) ∈ layout.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

theorem findLayoutRead_some {a : Admitted V} {layout : ModuleRef} {unitTy τ : V.Ty}
    {ref : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
    (h : findLayoutRead a layout unitTy τ = some ref) :
    ∃ defKey, (LayoutSlot.read, defKey) ∈ layout.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findSafeFnRef_some hRef⟩

theorem findLayoutEqual_some {a : Admitted V} {layout : ModuleRef} {τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns [τ, τ] [.bool]}
    (h : findLayoutEqual a layout τ = some ref) :
    ∃ defKey, (LayoutSlot.equal, defKey) ∈ layout.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

/-! ## Used-law encoder distinctness and ideal `serviceKey` freshness -/

/-- Sampling laws of all verifier-owned coins heard exclusively by `prover` in `events`. -/
def usedHeardLaws (prover verifier : Role) (events : List (ShapeEvent V)) : List V.LawKey :=
  events.filterMap fun e =>
    match e.cls with
    | .given (.coin law) owner hearers =>
        if owner = verifier ∧ hearers = [prover] then some law else none
    | _ => none

/-- Decidable check that `enc.lawKey` maps all distinct used laws to distinct byte sequences.
Refuses non-injective encoders that collapse two distinct used sampling laws onto one key. -/
def checkUsedLawsDistinct (enc : VocabEncoder V) (laws : List V.LawKey) : Bool :=
  laws.all fun l₁ =>
    laws.all fun l₂ =>
      if enc.lawKey l₁ = enc.lawKey l₂ then decide (l₁ = l₂) else true

theorem checkUsedLawsDistinct_sound (enc : VocabEncoder V) (laws : List V.LawKey)
    (h : checkUsedLawsDistinct enc laws = true) :
    ∀ l₁ ∈ laws, ∀ l₂ ∈ laws, enc.lawKey l₁ = enc.lawKey l₂ → l₁ = l₂ := by
  intro l₁ hl₁ l₂ hl₂ hEq
  have h1 := List.all_eq_true.mp h l₁ hl₁
  have h2 := List.all_eq_true.mp h1 l₂ hl₂
  simp only [hEq, ↓reduceIte, decide_eq_true_eq] at h2
  exact h2

/-- Decidable check that no `.given (.request svc)` event in `events` uses `serviceKey`,
preventing collisions between application service requests and the ideal random-oracle service. -/
def checkServiceKeyFresh (events : List (ShapeEvent V)) (serviceKey : Key) : Bool :=
  events.all fun e =>
    match e.cls with
    | .given (.request svc) _ _ => decide (svc ≠ serviceKey)
    | _ => true

theorem checkServiceKeyFresh_sound (events : List (ShapeEvent V)) (serviceKey : Key)
    (h : checkServiceKeyFresh events serviceKey = true) :
    ∀ e ∈ events, ∀ svc owner hearers,
      e.cls = .given (.request svc) owner hearers → svc ≠ serviceKey := by
  intro e he svc owner hearers hCls
  have hall := List.all_eq_true.mp h e he
  rw [hCls] at hall
  exact of_decide_eq_true hall

/-! ## Event classification and fresh-key allocation -/

/-- The maximum event key number occurring in `events`. -/
def maxEventKey (events : List (ShapeEvent V)) : Nat :=
  (events.map (·.site.key.number)).foldl max 0

theorem foldl_max_ge_init : ∀ (xs : List Nat) (init : Nat), init ≤ xs.foldl max init
  | [], _ => Nat.le_refl _
  | x :: xs, init =>
      Nat.le_trans (Nat.le_max_left init x) (foldl_max_ge_init xs (max init x))

theorem foldl_max_ge_mem : ∀ (xs : List Nat) (init x : Nat), x ∈ xs → x ≤ xs.foldl max init
  | [], _, _, h => nomatch h
  | y :: xs, init, x, h => by
      rcases List.mem_cons.mp h with rfl | hmem
      · exact Nat.le_trans (Nat.le_max_right init x) (foldl_max_ge_init xs (max init x))
      · exact foldl_max_ge_mem xs (max init y) x hmem

/-- Every event key in `events` has number at most `maxEventKey events`. -/
theorem event_key_le_max (events : List (ShapeEvent V)) (k : Key)
    (hk : k ∈ events.map (·.site.key)) : k.number ≤ maxEventKey events := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
  exact foldl_max_ge_mem (events.map (·.site.key.number)) 0 e.site.key.number
    (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- A key strictly above `maxEventKey events` cannot occur in `events.map (·.site.key)`. -/
theorem key_gt_max_not_mem (events : List (ShapeEvent V)) (k : Key)
    (hgt : maxEventKey events < k.number) : k ∉ events.map (·.site.key) := by
  intro hmem
  have hle := event_key_le_max events k hmem
  omega

/-- Deterministic fresh key for telling a derived draw at event index `idx` to the layout below. -/
def drawToldKey (events : List (ShapeEvent V)) (idx : Nat) : Key :=
  ⟨maxEventKey events + 1 + idx⟩

/-- Deterministic fresh key for an ideal random-oracle service request at event index `idx`. -/
def idealReqKey (events : List (ShapeEvent V)) (idx : Nat) : Key :=
  ⟨maxEventKey events + 1 + events.length + idx⟩

/-- Deterministic guard key for a layout clause at event index `idx`. -/
def layoutGuardKey (events : List (ShapeEvent V)) (idx : Nat) : Key :=
  ⟨maxEventKey events + 1 + 2 * events.length + idx⟩

/-- Deterministic guard key for the verifier layout's trailing-byte check. -/
def finishGuardKey (events : List (ShapeEvent V)) : Key :=
  ⟨maxEventKey events + 1 + 3 * events.length⟩

theorem drawToldKey_fresh (events : List (ShapeEvent V)) (idx : Nat) :
    drawToldKey events idx ∉ events.map (·.site.key) :=
  key_gt_max_not_mem events _ (by simp [drawToldKey]; omega)

theorem idealReqKey_fresh (events : List (ShapeEvent V)) (idx : Nat) :
    idealReqKey events idx ∉ events.map (·.site.key) :=
  key_gt_max_not_mem events _ (by simp [idealReqKey]; omega)

/-! ## Trailing-message absorption analysis (Chiesa and Orrù (2025), Construction 4.3) -/

mutual
  /-- Whether `s` contains any verifier-owned coin draw heard exclusively by `prover` under role
  renaming `rename`. -/
  def Shape.hasHeardDraw (prover verifier : Role) (rename : Role → Role) : Shape V → Bool
    | .nil => false
    | .event _ cls _ rest =>
        (match cls.rename rename with
         | .given (.coin _) owner hearers => decide (owner = verifier ∧ hearers = [prover])
         | _ => false) || Shape.hasHeardDraw prover verifier rename rest
    | .choice _ _ arms rest =>
        Shapes.hasHeardDraw prover verifier rename arms ||
          Shape.hasHeardDraw prover verifier rename rest
    | .loop _ _ body rest =>
        Shape.hasHeardDraw prover verifier rename body ||
          Shape.hasHeardDraw prover verifier rename rest
    | .apply _ _ roles inner rest =>
        Shape.hasHeardDraw prover verifier (fun j => rename (roles.getD j j)) inner ||
          Shape.hasHeardDraw prover verifier rename rest
    | .block _ _ body rest =>
        Shape.hasHeardDraw prover verifier rename body ||
          Shape.hasHeardDraw prover verifier rename rest
    | .guard _ _ _ rest => Shape.hasHeardDraw prover verifier rename rest
    | .attempt _ _ body rest =>
        Shape.hasHeardDraw prover verifier rename body ||
          Shape.hasHeardDraw prover verifier rename rest

  def Shapes.hasHeardDraw (prover verifier : Role) (rename : Role → Role) : Shapes V → Bool
    | .nil => false
    | .cons arm rest =>
        Shape.hasHeardDraw prover verifier rename arm ||
          Shapes.hasHeardDraw prover verifier rename rest
end

mutual
  /-- Raw structural pass pairing every `ShapeEvent` of `s` with a boolean indicating whether a
  verifier draw heard exclusively by `prover` can occur after it (conservatively `true` inside any
  loop containing a draw). -/
  def Shape.eventsWithAbsorbRaw (prover verifier : Role) (through : List Key) (rename : Role → Role)
      (drawAfter : Bool) : Shape V → List (ShapeEvent V × Bool)
    | .nil => []
    | .event key cls τ rest =>
        let need := drawAfter || Shape.hasHeardDraw prover verifier rename rest
        (⟨⟨through, key⟩, cls.rename rename, τ⟩, need) ::
          Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter rest
    | .choice _ _ arms rest =>
        let afterArm := drawAfter || Shape.hasHeardDraw prover verifier rename rest
        Shapes.eventsWithAbsorbRaw prover verifier through rename afterArm arms ++
          Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter rest
    | .loop _ _ body rest =>
        let afterBody := drawAfter || Shape.hasHeardDraw prover verifier rename rest ||
          Shape.hasHeardDraw prover verifier rename body
        Shape.eventsWithAbsorbRaw prover verifier through rename afterBody body ++
          Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter rest
    | .apply key _ roles inner rest =>
        let afterInner := drawAfter || Shape.hasHeardDraw prover verifier rename rest
        Shape.eventsWithAbsorbRaw prover verifier (through ++ [key])
            (fun j => rename (roles.getD j j)) afterInner inner ++
          Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter rest
    | .block _ _ body rest =>
        let afterBody := drawAfter || Shape.hasHeardDraw prover verifier rename rest
        Shape.eventsWithAbsorbRaw prover verifier through rename afterBody body ++
          Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter rest
    | .guard _ _ _ rest =>
        Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter rest
    | .attempt _ _ body rest =>
        let afterBody := drawAfter || Shape.hasHeardDraw prover verifier rename rest
        Shape.eventsWithAbsorbRaw prover verifier through rename afterBody body ++
          Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter rest

  def Shapes.eventsWithAbsorbRaw (prover verifier : Role) (through : List Key) (rename : Role → Role)
      (drawAfter : Bool) : Shapes V → List (ShapeEvent V × Bool)
    | .nil => []
    | .cons arm rest =>
        Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter arm ++
          Shapes.eventsWithAbsorbRaw prover verifier through rename drawAfter rest
end

/-- Monotonic closure of absorption flags over `(site, kind, ty)`: if any prover→verifier flow at
`(site, kind, ty)` precedes a heard draw (e.g. across blocks of a stepped loop that reuse a key),
every occurrence of `(site, kind, ty)` is absorbed uniformly on both prover and verifier. -/
def closeAbsorbSites (prover verifier : Role) (es : List (ShapeEvent V × Bool)) :
    List (ShapeEvent V × Bool) :=
  let absorbed : List (Site × FlowKind × V.Ty) := es.filterMap fun p =>
    if p.2 then
      match p.1.cls with
      | .flow kind giver getters =>
          if giver = prover ∧ getters = [verifier] then some (p.1.site, kind, p.1.τ) else none
      | _ => none
    else none
  es.map fun p =>
    match p.1.cls with
    | .flow kind giver getters =>
        if giver = prover ∧ getters = [verifier] then
          (p.1, decide ((p.1.site, kind, p.1.τ) ∈ absorbed))
        else p
    | _ => p

/-- Enumerate every `ShapeEvent` of `s` paired with a site-consistent boolean indicating whether
a verifier draw heard exclusively by `prover` can occur after it. Trailing prover messages with
`needAbsorb = false` are not hashed into the transcript (Chiesa and Orrù (2025), Construction 4.3). -/
def Shape.eventsWithAbsorb (prover verifier : Role) (through : List Key) (rename : Role → Role)
    (drawAfter : Bool) (s : Shape V) : List (ShapeEvent V × Bool) :=
  closeAbsorbSites prover verifier (Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter s)

mutual
  theorem eventsWithAbsorbRaw_fst (prover verifier : Role) (through : List Key) (rename : Role → Role)
      (drawAfter : Bool) : ∀ (s : Shape V),
      (Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter s).map Prod.fst =
        Shape.events through rename s
    | .nil => rfl
    | .event _ _ _ rest =>
        congrArg _ (eventsWithAbsorbRaw_fst prover verifier through rename drawAfter rest)
    | .choice _ _ arms rest => by
        simp only [Shape.eventsWithAbsorbRaw, Shape.events, List.map_append]
        rw [shapesEventsWithAbsorbRaw_fst, eventsWithAbsorbRaw_fst]
    | .loop _ _ body rest => by
        simp only [Shape.eventsWithAbsorbRaw, Shape.events, List.map_append]
        rw [eventsWithAbsorbRaw_fst, eventsWithAbsorbRaw_fst]
    | .apply _ _ _ inner rest => by
        simp only [Shape.eventsWithAbsorbRaw, Shape.events, List.map_append]
        rw [eventsWithAbsorbRaw_fst, eventsWithAbsorbRaw_fst]
    | .block _ _ body rest => by
        simp only [Shape.eventsWithAbsorbRaw, Shape.events, List.map_append]
        rw [eventsWithAbsorbRaw_fst, eventsWithAbsorbRaw_fst]
    | .guard _ _ _ rest =>
        eventsWithAbsorbRaw_fst prover verifier through rename drawAfter rest
    | .attempt _ _ body rest => by
        simp only [Shape.eventsWithAbsorbRaw, Shape.events, List.map_append]
        rw [eventsWithAbsorbRaw_fst, eventsWithAbsorbRaw_fst]

  theorem shapesEventsWithAbsorbRaw_fst (prover verifier : Role) (through : List Key)
      (rename : Role → Role) (drawAfter : Bool) : ∀ (ss : Shapes V),
      (Shapes.eventsWithAbsorbRaw prover verifier through rename drawAfter ss).map Prod.fst =
        Shapes.events through rename ss
    | .nil => rfl
    | .cons arm rest => by
        simp only [Shapes.eventsWithAbsorbRaw, Shapes.events, List.map_append]
        rw [eventsWithAbsorbRaw_fst, shapesEventsWithAbsorbRaw_fst]
end

theorem closeAbsorbSites_fst (prover verifier : Role) (es : List (ShapeEvent V × Bool)) :
    (closeAbsorbSites prover verifier es).map Prod.fst = es.map Prod.fst := by
  unfold closeAbsorbSites
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  dsimp only [Function.comp_def]
  cases h : p.1.cls with
  | flow kind giver getters =>
      dsimp only
      split <;> rfl
  | given _ _ _ => rfl

/-- Projecting the first component of `eventsWithAbsorb` yields `Shape.events` identically. -/
theorem eventsWithAbsorb_fst (prover verifier : Role) (through : List Key) (rename : Role → Role)
    (drawAfter : Bool) (s : Shape V) :
    (Shape.eventsWithAbsorb prover verifier through rename drawAfter s).map Prod.fst =
      Shape.events through rename s :=
  (closeAbsorbSites_fst prover verifier _).trans
    (eventsWithAbsorbRaw_fst prover verifier through rename drawAfter s)

/-- Any two prover→verifier flow events in `eventsWithAbsorb` at the same `(site, kind, ty)` carry
the exact same absorption flag, guaranteeing lockstep prover/verifier absorption even across
stepped-loop blocks that reuse keys. -/
theorem eventsWithAbsorb_flow_consistent (prover verifier : Role) (through : List Key)
    (rename : Role → Role) (drawAfter : Bool) (s : Shape V)
    {e₁ e₂ : ShapeEvent V} {b₁ b₂ : Bool}
    (h₁ : (e₁, b₁) ∈ s.eventsWithAbsorb prover verifier through rename drawAfter)
    (h₂ : (e₂, b₂) ∈ s.eventsWithAbsorb prover verifier through rename drawAfter)
    {kind : FlowKind}
    (hSite : e₁.site = e₂.site) (hTy : e₁.τ = e₂.τ)
    (hCls₁ : e₁.cls = .flow kind prover [verifier])
    (hCls₂ : e₂.cls = .flow kind prover [verifier]) :
    b₁ = b₂ := by
  unfold Shape.eventsWithAbsorb closeAbsorbSites at h₁ h₂
  obtain ⟨p₁, _, hp₁⟩ := List.mem_map.mp h₁
  obtain ⟨p₂, _, hp₂⟩ := List.mem_map.mp h₂
  have hb₁ : b₁ = decide ((e₁.site, kind, e₁.τ) ∈
      (Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter s).filterMap fun p =>
        if p.2 then match p.1.cls with
          | .flow k g gs => if g = prover ∧ gs = [verifier] then some (p.1.site, k, p.1.τ) else none
          | _ => none
        else none) := by
    have hfst₁ : p₁.1 = e₁ := by
      cases h : p₁.1.cls with
      | flow k g gs =>
          rw [h] at hp₁; dsimp only at hp₁
          split at hp₁ <;> exact congrArg Prod.fst hp₁
      | given _ _ _ => rw [h] at hp₁; exact congrArg Prod.fst hp₁
    rw [hfst₁, hCls₁] at hp₁; dsimp only at hp₁
    rw [ite_eq_left ⟨rfl, rfl⟩] at hp₁
    exact (congrArg Prod.snd hp₁).symm
  have hb₂ : b₂ = decide ((e₂.site, kind, e₂.τ) ∈
      (Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter s).filterMap fun p =>
        if p.2 then match p.1.cls with
          | .flow k g gs => if g = prover ∧ gs = [verifier] then some (p.1.site, k, p.1.τ) else none
          | _ => none
        else none) := by
    have hfst₂ : p₂.1 = e₂ := by
      cases h : p₂.1.cls with
      | flow k g gs =>
          rw [h] at hp₂; dsimp only at hp₂
          split at hp₂ <;> exact congrArg Prod.fst hp₂
      | given _ _ _ => rw [h] at hp₂; exact congrArg Prod.fst hp₂
    rw [hfst₂, hCls₂] at hp₂; dsimp only at hp₂
    rw [ite_eq_left ⟨rfl, rfl⟩] at hp₂
    exact (congrArg Prod.snd hp₂).symm
  rw [hb₁, hb₂, hSite, hTy]

/-! ## Selected-function suite lawfulness (`Deployed.SuiteLawfulFor`) -/

/-- Selected-function lawfulness for a deployed Fiat–Shamir suite under `enc` in model `M`:
1. For every heard coin event `e` in `d.entry.shape` and the suite's resolved `stateTy`, ONLY the
   exact `SuiteSlot.derive` function selected by `findSuiteDerive enc d.admitted suite stateTy law
   drawIns e.τ` is required to produce values in `Allows M (.coin law)` on valid inputs. Shadowed
   generic defaults in `suite.members` are not charged when an explicit `suite.lawMembers` binding
   overrides `law`.
2. Every `SuiteSlot.encode` function in `suite.members` is injective on valid values. -/
def Deployed.SuiteLawfulFor (enc : VocabEncoder V) (M : Model V) (d : Deployed V) : Prop :=
  ∀ suite sessionTag, d.declaration.construction = .derived suite sessionTag →
    (∀ (e : ShapeEvent V) (law : V.LawKey) (owner h0 : Role) (hs : List Role)
        (drawIns : List V.Ty) (stateTy : V.Ty)
        (startRef : TypedFnRef V d.admitted.program.headers.fns [bytesTy] [stateTy])
        (derRef : TypedFnRef V d.admitted.program.headers.fns
          (stateTy :: bytesTy :: drawIns) [e.τ, stateTy]),
        findSuiteStart d.admitted suite = some ⟨stateTy, startRef⟩ →
        e ∈ d.entry.shape.events [] id →
        e.cls = .given (.coin law) owner (h0 :: hs) →
        V.law law = some ⟨drawIns, e.τ⟩ →
        findSuiteDerive enc d.admitted suite stateTy law drawIns e.τ = some derRef →
        ∀ (st : M.Val stateTy) (label : List (M.Val (.fin 256)))
          (payload : HList M.Val drawIns) (coin : M.Val e.τ) (st' : M.Val stateTy),
          M.Valid stateTy st →
          (∀ b, b ∈ label → b < 256) →
          payload.All M.Valid →
          Defs.fnTable M d.admitted.program.defs derRef.hdr derRef.member
            (cast (congrArg (HList M.Val) derRef.insEq.symm) (.cons st (.cons label payload))) =
            .done (cast (congrArg (HList M.Val) derRef.outsEq.symm) (.cons coin (.cons st' .nil))) →
          Allows M (.coin law) drawIns payload e.τ coin) ∧
    (∀ eKey, (SuiteSlot.encode, eKey) ∈ suite.members →
      ∀ (hdr : FnHeader V) (f : Member d.admitted.program.headers.fns hdr),
        d.admitted.program.find eKey = some (.fn f) →
        ∀ (unitTy τ : V.Ty) (hIn : hdr.ins = [τ]) (hOut : hdr.outs = [.seq unitTy none])
          (v₁ v₂ : M.Val τ) (u : List (M.Val unitTy)),
          M.Valid τ v₁ → M.Valid τ v₂ →
          Defs.fnTable M d.admitted.program.defs hdr f
            (cast (congrArg (HList M.Val) hIn.symm) (.cons v₁ .nil)) =
            .done (cast (congrArg (HList M.Val) hOut.symm) (.cons u .nil)) →
          Defs.fnTable M d.admitted.program.defs hdr f
            (cast (congrArg (HList M.Val) hIn.symm) (.cons v₂ .nil)) =
            .done (cast (congrArg (HList M.Val) hOut.symm) (.cons u .nil)) →
          v₁ = v₂)

/-- The stronger encoder-independent `Deployed.SuiteLawful` implies `Deployed.SuiteLawfulFor`
for every encoder `enc`. -/
theorem Deployed.SuiteLawful.toFor {d : Deployed V} (enc : VocabEncoder V) (M : Model V)
    (h : d.SuiteLawful M) : d.SuiteLawfulFor enc M := by
  intro suite sessionTag hCon
  obtain ⟨hDer, hEnc⟩ := h suite sessionTag hCon
  refine ⟨?_, hEnc⟩
  intro e law owner h0 hs drawIns stateTy _ derRef _ hE hCls hLaw hFind st label payload coin st'
    hSt hLbl hPay hFn
  obtain ⟨defKey, hInSuite, hProgFind⟩ := findSuiteDerive_some hFind
  have hIn : (SuiteSlot.derive, defKey) ∈ suite.members ∨
      ∃ lb, (SuiteSlot.derive, lb, defKey) ∈ suite.lawMembers := by
    rcases hInSuite with hL | hM
    · exact .inr ⟨enc.lawKey law, hL⟩
    · exact .inl hM
  exact hDer defKey hIn derRef.hdr derRef.member hProgFind stateTy drawIns e law owner h0 hs
    hE hCls hLaw derRef.insEq derRef.outsEq st label payload coin st' hSt hLbl hPay hFn

end

end Zkc.Core
