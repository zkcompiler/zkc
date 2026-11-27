module

public import Zkc.Core.Scheme.Layer.Combinators
public import Zkc.Core.World.Network

@[expose] public section

/-!
Module slot resolution (including distribution-aware `V.LawKey`-keyed `SuiteSlot.derive` lookup),
deterministic fresh-key allocation, and trailing-message absorption analysis
(Chiesa and Orrù (2025), Construction 4.3).
-/

namespace Zkc.Core

open LayerBuild

/-! ## Module lookup helpers -/

section
variable {V : Vocabulary}

/-- Decide equality inside `Option`, returning a proof witness in `PLift`. -/
def guardEq {α : Type} [DecidableEq α] (a b : α) : Option (PLift (a = b)) :=
  if h : a = b then some ⟨h⟩ else none

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

/-- Find the first member of `m` at `slot` matching a predicate `pick`. -/
def findSlotMember {α : Type} (m : ModuleRef) (slot : Key) (pick : Key → Option α) : Option α :=
  m.members.findSome? fun (s, defKey) => if s = slot then pick defKey else none

/-- Find the first law-specific member of `m` at `(slot, lawBytes)` matching `pick`. -/
def findLawSlotMember {α : Type} (m : ModuleRef) (slot : Key) (lawBytes : List Nat)
    (pick : Key → Option α) : Option α :=
  m.lawMembers.findSome? fun (s, lb, defKey) =>
    if s = slot ∧ lb = lawBytes then pick defKey else none

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
`law`. Prefers an explicit `(SuiteSlot.derive, enc.lawKey law, defKey)` binding in
`suite.lawMembers`, falling back to `suite.members` when no law-specific entry matches. -/
def findSuiteDerive (enc : VocabEncoder V) (a : Admitted V) (suite : ModuleRef)
    (stateTy : V.Ty) (law : V.LawKey) (drawIns : List V.Ty) (τ : V.Ty) :
    Option (TypedFnRef V a.program.headers.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]) :=
  (findLawSlotMember suite SuiteSlot.derive (enc.lawKey law) fun defKey =>
    findTypedFnRef a defKey (stateTy :: bytesTy :: drawIns) [τ, stateTy]) <|>
  (findSlotMember suite SuiteSlot.derive fun defKey =>
    findTypedFnRef a defKey (stateTy :: bytesTy :: drawIns) [τ, stateTy])

/-- Determine the suite's absorbed unit type from its `SuiteSlot.encode` entries (defaulting to
`byteTy`), requiring a non-linear unit type. Used by pure-path `deployIdeal` without touching any
concrete `SuiteSlot.start` or `SuiteSlot.absorb` function. -/
def findSuiteUnit (a : Admitted V) (suite : ModuleRef) :
    Option ((unitTy : V.Ty) × PLift (Ty.isLinear V unitTy = false)) :=
  let inferred : Option V.Ty :=
    findSlotMember suite SuiteSlot.encode fun defKey =>
      match a.program.find defKey with
      | some (.fn (hdr := hdr) _) =>
          match hdr.outs with
          | [.seq unitTy none] => some unitTy
          | _ => none
      | _ => none
  let u := inferred.getD byteTy
  if hfree : Ty.isLinear V u = false then some ⟨u, ⟨hfree⟩⟩ else none

/-- Determine the layout's unit type from its `LayoutSlot.write` / `LayoutSlot.read` entries,
defaulting to `byteTy` when the module has no typed entries. Requires a non-linear unit type. -/
def findLayoutUnit (a : Admitted V) (layout : ModuleRef) :
    Option ((unitTy : V.Ty) × PLift (Ty.isLinear V unitTy = false)) :=
  let inferred : Option V.Ty :=
    (findSlotMember layout LayoutSlot.write fun defKey =>
      match a.program.find defKey with
      | some (.fn (hdr := hdr) _) =>
          match hdr.outs with
          | [.seq unitTy none] => some unitTy
          | _ => none
      | _ => none) <|>
    (findSlotMember layout LayoutSlot.read fun defKey =>
      match a.program.find defKey with
      | some (.fn (hdr := hdr) _) =>
          match hdr.ins with
          | [.seq unitTy none, .nat] => some unitTy
          | _ => none
      | _ => none)
  let u := inferred.getD byteTy
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
  /-- Whether `s` contains any verifier-owned coin draw heard by `prover` under role renaming
  `rename`. -/
  def Shape.hasHeardDraw (prover verifier : Role) (rename : Role → Role) : Shape V → Bool
    | .nil => false
    | .event _ cls _ rest =>
        (match cls.rename rename with
         | .given (.coin _) owner hearers => decide (owner = verifier ∧ prover ∈ hearers)
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
  verifier draw heard by `prover` can occur after it (conservatively `true` inside any loop
  containing a draw). -/
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
          if giver = prover ∧ verifier ∈ getters then some (p.1.site, kind, p.1.τ) else none
      | _ => none
    else none
  es.map fun p =>
    match p.1.cls with
    | .flow kind giver getters =>
        if giver = prover ∧ verifier ∈ getters then
          (p.1, decide ((p.1.site, kind, p.1.τ) ∈ absorbed))
        else p
    | _ => p

/-- Enumerate every `ShapeEvent` of `s` paired with a site-consistent boolean indicating whether
a verifier draw heard by `prover` can occur after it. Trailing prover messages with
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
    {kind : FlowKind} {gs₁ gs₂ : List Role}
    (hSite : e₁.site = e₂.site) (hTy : e₁.τ = e₂.τ)
    (hCls₁ : e₁.cls = .flow kind prover gs₁) (hV₁ : verifier ∈ gs₁)
    (hCls₂ : e₂.cls = .flow kind prover gs₂) (hV₂ : verifier ∈ gs₂) :
    b₁ = b₂ := by
  unfold Shape.eventsWithAbsorb closeAbsorbSites at h₁ h₂
  obtain ⟨p₁, _, hp₁⟩ := List.mem_map.mp h₁
  obtain ⟨p₂, _, hp₂⟩ := List.mem_map.mp h₂
  have hb₁ : b₁ = decide ((e₁.site, kind, e₁.τ) ∈
      (Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter s).filterMap fun p =>
        if p.2 then match p.1.cls with
          | .flow k g gs => if g = prover ∧ verifier ∈ gs then some (p.1.site, k, p.1.τ) else none
          | _ => none
        else none) := by
    have hfst₁ : p₁.1 = e₁ := by
      cases h : p₁.1.cls with
      | flow k g gs =>
          rw [h] at hp₁; dsimp only at hp₁
          split at hp₁ <;> exact congrArg Prod.fst hp₁
      | given _ _ _ => rw [h] at hp₁; exact congrArg Prod.fst hp₁
    rw [hfst₁, hCls₁] at hp₁; dsimp only at hp₁
    rw [ite_eq_left ⟨rfl, hV₁⟩] at hp₁
    exact (congrArg Prod.snd hp₁).symm
  have hb₂ : b₂ = decide ((e₂.site, kind, e₂.τ) ∈
      (Shape.eventsWithAbsorbRaw prover verifier through rename drawAfter s).filterMap fun p =>
        if p.2 then match p.1.cls with
          | .flow k g gs => if g = prover ∧ verifier ∈ gs then some (p.1.site, k, p.1.τ) else none
          | _ => none
        else none) := by
    have hfst₂ : p₂.1 = e₂ := by
      cases h : p₂.1.cls with
      | flow k g gs =>
          rw [h] at hp₂; dsimp only at hp₂
          split at hp₂ <;> exact congrArg Prod.fst hp₂
      | given _ _ _ => rw [h] at hp₂; exact congrArg Prod.fst hp₂
    rw [hfst₂, hCls₂] at hp₂; dsimp only at hp₂
    rw [ite_eq_left ⟨rfl, hV₂⟩] at hp₂
    exact (congrArg Prod.snd hp₂).symm
  rw [hb₁, hb₂, hSite, hTy]


end

end Zkc.Core
