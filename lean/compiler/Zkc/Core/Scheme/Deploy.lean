module

public import Zkc.Core.Scheme.LayerBuild
public import Zkc.Core.Admission.Theorems
public import Zkc.Core.Projection.Theorem

@[expose] public section

/-!
Non-interactive and interactive scheme deployment over an admitted core program (`deploy`,
`deployIdeal`).

`deploy` produces an official `Deployed V` whose per-role `Layer` stacks are checked Core IR
(`Term (localDialect ...)` and `Term (roleDialect ...)`):
- `[samples?, construction, layout]` for a `derived` scheme's prover;
- `[construction, layout]` for a `derived` scheme's verifier;
- `[samples?, layout]` for an `authored` scheme;
- `[]` for an `interactive` scheme.

Both source suites (functions defined in `.zkc`) and catalogue suites (bound through
`Zkc.Vocabulary.Project.Bindings`) enter uniformly through `Declaration`'s `ModuleRef`, keeping
`Zkc.Core` completely vocabulary- and suite-agnostic.
-/

namespace Zkc.Core

open LayerBuild

/-! ## Module lookup helpers -/

section
variable {V : Vocabulary}

/-- Resolve a concrete total unconditional function reference by key and exact signature. -/
def findTypedFnRef (a : Admitted V) (key : Key) (ins outs : List V.Ty) :
    Option (TypedFnRef V a.program.headers.fns ins outs) :=
  match a.program.find key with
  | some (.fn (hdr := hdr) member) =>
      if hIn : hdr.ins = ins then
        if hOut : hdr.outs = outs then
          if hUncond : hdr.summary.requires = [] then
            if hStop : hdr.canStop = false then
              some ⟨hdr, member, hIn, hOut, hUncond, hStop⟩
            else none
          else none
        else none
      else none
  | _ => none

/-- Resolve a potentially-stopping unconditional function reference by key and exact signature. -/
def findSafeFnRef (a : Admitted V) (key : Key) (ins outs : List V.Ty) :
    Option (SafeFnRef V a.program.headers.fns ins outs) :=
  match a.program.find key with
  | some (.fn (hdr := hdr) member) =>
      if hIn : hdr.ins = ins then
        if hOut : hdr.outs = outs then
          if hUncond : hdr.summary.requires = [] then
            some ⟨hdr, member, hIn, hOut, hUncond⟩
          else none
        else none
      else none
  | _ => none

/-- Find the first member of `m` at `slot` matching a predicate `pick`. -/
def findSlotMember {α : Type} (m : ModuleRef) (slot : Key) (pick : Key → Option α) : Option α :=
  m.members.findSome? fun (s, defKey) => if s = slot then pick defKey else none

/-- Resolve `SuiteSlot.start : [bytesTy] → [stateTy]`. -/
def findSuiteStart (a : Admitted V) (suite : ModuleRef) :
    Option ((stateTy : V.Ty) × TypedFnRef V a.program.headers.fns [bytesTy] [stateTy]) :=
  findSlotMember suite SuiteSlot.start fun defKey =>
    match a.program.find defKey with
    | some (.fn (hdr := hdr) member) =>
        match hIn : hdr.ins, hOut : hdr.outs with
        | [inTy], [stateTy] =>
            if hBytes : inTy = bytesTy then
              if hUncond : hdr.summary.requires = [] then
                if hStop : hdr.canStop = false then
                  some ⟨stateTy, ⟨hdr, member, by rw [hIn, hBytes], hOut, hUncond, hStop⟩⟩
                else none
              else none
            else none
        | _, _ => none
    | _ => none

/-- Resolve `SuiteSlot.absorb : [stateTy, bytesTy, .seq unitTy none] → [stateTy]`. -/
def findSuiteAbsorb (a : Admitted V) (suite : ModuleRef) (stateTy : V.Ty) :
    Option ((unitTy : V.Ty) ×
      TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :=
  findSlotMember suite SuiteSlot.absorb fun defKey =>
    match a.program.find defKey with
    | some (.fn (hdr := hdr) member) =>
        match hIn : hdr.ins, hOut : hdr.outs with
        | [stIn, lblIn, .seq unitTy none], [stOut] =>
            if hSt1 : stIn = stateTy then
              if hLbl : lblIn = bytesTy then
                if hSt2 : stOut = stateTy then
                  if hUncond : hdr.summary.requires = [] then
                    if hStop : hdr.canStop = false then
                      some ⟨unitTy, ⟨hdr, member, by rw [hIn, hSt1, hLbl], by rw [hOut, hSt2],
                        hUncond, hStop⟩⟩
                    else none
                  else none
                else none
              else none
            else none
        | _, _ => none
    | _ => none

/-- Resolve `SuiteSlot.encode : [τ] → [.seq unitTy none]`. -/
def findSuiteEncode (a : Admitted V) (suite : ModuleRef) (unitTy τ : V.Ty) :
    Option (TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]) :=
  findSlotMember suite SuiteSlot.encode fun defKey =>
    findTypedFnRef a defKey [τ] [.seq unitTy none]

/-- Resolve `SuiteSlot.derive : (stateTy :: bytesTy :: drawIns) → [τ, stateTy]`. -/
def findSuiteDerive (a : Admitted V) (suite : ModuleRef) (stateTy : V.Ty)
    (drawIns : List V.Ty) (τ : V.Ty) :
    Option (TypedFnRef V a.program.headers.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]) :=
  findSlotMember suite SuiteSlot.derive fun defKey =>
    findTypedFnRef a defKey (stateTy :: bytesTy :: drawIns) [τ, stateTy]

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

/-- Deterministic fresh key for an ideal RO service request at event index `idx`. -/
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

/-- Deterministic ASCII domain label for a statement input at index `i`. -/
def stmtLabel (i : Nat) : List Nat := encodeLabelBytes s!"stmt:{i}"

/-- Deterministic ASCII domain label for a message at site `s`. -/
def msgLabel (s : Site) : List Nat := encodeLabelBytes s!"msg:{s.key.number}"

/-- Deterministic ASCII domain label for a draw at site `s`. -/
def drawLabel (s : Site) : List Nat := encodeLabelBytes s!"draw:{s.key.number}"

theorem stmtLabel_bytes (i : Nat) : ∀ b, b ∈ stmtLabel i → b < 256 :=
  encodeLabelBytes_bytes _

theorem msgLabel_bytes (s : Site) : ∀ b, b ∈ msgLabel s → b < 256 :=
  encodeLabelBytes_bytes _

theorem drawLabel_bytes (s : Site) : ∀ b, b ∈ drawLabel s → b < 256 :=
  encodeLabelBytes_bytes _

/-! ## Refusal helper -/

def deployErr (declKey : Key) (rule : Rule) : List (ProgramRefusal V) :=
  [refuseWhole declKey rule .nothing]

/-- Check whether `declaration.retry` and `abortsOutside` satisfy `Deployed.Scoped`. -/
def checkScope (hdr : ProtocolHeader V) (declaration : Declaration) : Bool :=
  (match declaration.retry with
   | none => true
   | some (_, site) => decide (site ∈ hdr.shape.attemptSites [])) &&
  (hdr.shape.abortsOutside [] false).isEmpty

theorem checkScope_sound (hdr : ProtocolHeader V) (declaration : Declaration)
    (h : checkScope hdr declaration = true) :
    (∀ bound site, declaration.retry = some (bound, site) → site ∈ hdr.shape.attemptSites []) ∧
      hdr.shape.abortsOutside [] false = [] := by
  simp only [checkScope, Bool.and_eq_true, List.isEmpty_iff] at h
  refine ⟨?_, h.2⟩
  intro bound site hretry
  rw [hretry] at h
  exact of_decide_eq_true h.1

/-! ## Building statement absorption items -/

/-- Resolve `SuiteSlot.encode` for every statement input visible to role `r`. -/
def buildStmtAbsorbItems (a : Admitted V) (suite : ModuleRef) (unitTy : V.Ty)
    (r prover verifier : Role) (hr : r = prover ∨ r = verifier) (ins : List (LTy V))
    (declKey : Key) :
    Except (List (ProgramRefusal V))
      (List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held r ins)))) :=
  (statementPositions r prover verifier hr ins).mapM fun sp =>
    match findSuiteEncode a suite unitTy sp.ty with
    | some encRef =>
        .ok ⟨sp.ty, posVar (held r ins) sp.heldIndex sp.atHeld,
          stmtLabel sp.stmtIndex, stmtLabel_bytes sp.stmtIndex, encRef⟩
    | none => .error (deployErr declKey .callee)

/-! ## Building construction, samples, and layout clauses -/

/-- Classify and build the `construction` and `samples` clauses for both online roles. -/
def buildConstructionClauses (a : Admitted V) (suite : ModuleRef) (stateTy unitTy : V.Ty)
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (prover verifier : Role) (samplesKey : Option Key) (declKey : Key)
    (events : List (ShapeEvent V)) :
    Except (List (ProgramRefusal V))
      (List (Clause V a.program.headers prover stateTy) ×
       List (Clause V a.program.headers verifier stateTy) ×
       List (Clause V a.program.headers prover .nat)) :=
  go 0 events
where
  go (idx : Nat) : List (ShapeEvent V) →
      Except (List (ProgramRefusal V))
        (List (Clause V a.program.headers prover stateTy) ×
         List (Clause V a.program.headers verifier stateTy) ×
         List (Clause V a.program.headers prover .nat))
    | [] => .ok ([], [], [])
    | e :: rest => do
        let (pRest, vRest, sRest) ← go (idx + 1) rest
        match e.cls with
        | .flow kind giver getters =>
            if giver = prover ∧ verifier ∈ getters then
              match findSuiteEncode a suite unitTy e.τ with
              | none => .error (deployErr declKey .callee)
              | some encRef =>
                  let cP := proverAbsorbClause prover e.site kind getters
                    (msgLabel e.site) (msgLabel_bytes e.site) encRef absorbRef
                  let cV := verifierAbsorbClause verifier prover e.site kind
                    (msgLabel e.site) (msgLabel_bytes e.site) encRef absorbRef
                  .ok (cP :: pRest, cV :: vRest, sRest)
            else if giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters then
              .ok (pRest, vRest, sRest)
            else
              .error (deployErr declKey .protocol)
        | .given (.coin law) owner hearers =>
            if owner = verifier ∧ prover ∈ hearers then
              match V.law law with
              | none => .error (deployErr declKey .row)
              | some sig =>
                  if sig.out = e.τ then
                    match findSuiteDerive a suite stateTy sig.ins e.τ with
                    | none => .error (deployErr declKey .callee)
                    | some derRef =>
                        let tk := drawToldKey events idx
                        let cV := deriveClause verifier prover e.site (.own (.coin law) hearers)
                          sig.ins tk (drawLabel e.site) (drawLabel_bytes e.site) derRef
                        -- Prover hears the coin with empty operand list; when `sig.ins = []`,
                        -- `derRef` matches directly.
                        match hIns : sig.ins with
                        | [] =>
                            let derRefP : TypedFnRef V a.program.headers.fns
                                [stateTy, bytesTy] [e.τ, stateTy] := hIns ▸ derRef
                            let cP := deriveClause prover verifier e.site (.hear (.coin law) verifier)
                              [] tk (drawLabel e.site) (drawLabel_bytes e.site) derRefP
                            .ok (cP :: pRest, cV :: vRest, sRest)
                        | _ :: _ => .error (deployErr declKey .operands)
                  else
                    .error (deployErr declKey .operands)
            else if hearers = [] then
              if owner = prover then
                match samplesKey with
                | none => .ok (pRest, vRest, sRest)
                | some sKey =>
                    match findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                    | some sRef =>
                        let cS := proverSampleClause prover e.site law sRef
                        .ok (pRest, vRest, cS :: sRest)
                    | none => .error (deployErr declKey .callee)
              else
                .ok (pRest, vRest, sRest)
            else
              .error (deployErr declKey .protocol)
        | .given (.request _) owner hearers =>
            if (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) then
              .ok (pRest, vRest, sRest)
            else
              .error (deployErr declKey .protocol)

/-- Build ideal-RO verifier construction clauses: same statement/message absorption, with every
verifier draw answered by `.own (.request serviceKey)` at fresh `idealReqKey` and absorbed into
the transcript path state. -/
def buildIdealVerifierClauses (a : Admitted V) (suite : ModuleRef) (stateTy unitTy : V.Ty)
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (serviceKey : Key) (prover verifier : Role) (declKey : Key)
    (events : List (ShapeEvent V)) :
    Except (List (ProgramRefusal V)) (List (Clause V a.program.headers verifier stateTy)) :=
  go 0 events
where
  go (idx : Nat) : List (ShapeEvent V) →
      Except (List (ProgramRefusal V)) (List (Clause V a.program.headers verifier stateTy))
    | [] => .ok []
    | e :: rest => do
        let vRest ← go (idx + 1) rest
        match e.cls with
        | .flow kind giver getters =>
            if giver = prover ∧ verifier ∈ getters then
              match findSuiteEncode a suite unitTy e.τ with
              | none => .error (deployErr declKey .callee)
              | some encRef =>
                  let cV := verifierAbsorbClause verifier prover e.site kind
                    (msgLabel e.site) (msgLabel_bytes e.site) encRef absorbRef
                  .ok (cV :: vRest)
            else if giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters then
              .ok vRest
            else
              .error (deployErr declKey .protocol)
        | .given (.coin law) owner hearers =>
            if owner = verifier ∧ prover ∈ hearers then
              match V.law law with
              | none => .error (deployErr declKey .row)
              | some sig =>
                  if sig.out = e.τ then
                    match sig.ins with
                    | [] =>
                        match findSuiteEncode a suite unitTy e.τ with
                        | none => .error (deployErr declKey .callee)
                        | some encRef =>
                            let rk := idealReqKey events idx
                            let tk := drawToldKey events idx
                            let cV := idealDeriveClause verifier prover e.site
                              (.own (.coin law) hearers) [] serviceKey rk tk
                              (drawLabel e.site) (drawLabel_bytes e.site) encRef absorbRef
                            .ok (cV :: vRest)
                    | _ :: _ => .error (deployErr declKey .operands)
                  else
                    .error (deployErr declKey .operands)
            else if hearers = [] then
              .ok vRest
            else
              .error (deployErr declKey .protocol)
        | .given (.request _) owner hearers =>
            if (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) then
              .ok vRest
            else
              .error (deployErr declKey .protocol)

/-- Build streaming layout clauses (supporting plain sequential layouts and streaming `carry`
without `recover`). -/
def buildStreamingLayoutClauses (a : Admitted V) (layout : Layout)
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V)) :
    Except (List (ProgramRefusal V))
      (List (Clause V a.program.headers prover (.seq unitTy none)) ×
       List (Clause V a.program.headers verifier (streamStateTy unitTy))) :=
  go 0 events
where
  go (idx : Nat) : List (ShapeEvent V) →
      Except (List (ProgramRefusal V))
        (List (Clause V a.program.headers prover (.seq unitTy none)) ×
         List (Clause V a.program.headers verifier (streamStateTy unitTy)))
    | [] => .ok ([], [])
    | e :: rest => do
        let (pRest, vRest) ← go (idx + 1) rest
        match e.cls with
        | .flow kind giver getters =>
            if giver = prover ∧ verifier ∈ getters then
              match findLayoutWrite a layout.module unitTy e.τ,
                    findLayoutRead a layout.module unitTy e.τ with
              | some wRef, some rRef =>
                  let cP := layoutPWriteClause prover e.site kind getters wRef
                  let cV := layoutVReadClause hfree verifier prover e.site kind rRef
                  .ok (cP :: pRest, cV :: vRest)
              | _, _ => .error (deployErr declKey .callee)
            else
              .ok (pRest, vRest)
        | .given (.coin _) owner hearers =>
            if owner = verifier ∧ prover ∈ hearers then
              let toldSite : Site := ⟨e.site.through, drawToldKey events idx⟩
              if e.site ∈ layout.carry then
                match findLayoutWrite a layout.module unitTy e.τ,
                      findLayoutRead a layout.module unitTy e.τ,
                      findLayoutEqual a layout.module e.τ with
                | some wRef, some rRef, some eqRef =>
                    let cP := layoutPWriteClause prover toldSite .message [verifier] wRef
                    let cV := layoutVCarryClause hfree verifier prover toldSite
                      (layoutGuardKey events idx) rRef eqRef
                    .ok (cP :: pRest, cV :: vRest)
                | _, _, _ => .error (deployErr declKey .callee)
              else
                let cP := layoutDropClause (stateTy := .seq unitTy none) prover toldSite
                  .message [verifier] (τ := e.τ)
                let cV := layoutDropClause (stateTy := streamStateTy unitTy) verifier toldSite
                  .message [prover] (τ := e.τ)
                .ok (cP :: pRest, cV :: vRest)
            else
              .ok (pRest, vRest)
        | .given (.request _) _ _ => .ok (pRest, vRest)

/-! ## Compact layout (`carry` + `recover`) construction -/

/-- A single item serialized on the wire in a compact layout. -/
structure WireSpec (V : Vocabulary) (fns : List (FnHeader V)) (unitTy : V.Ty) where
  site : Site
  ty : V.Ty
  readRef : SafeFnRef V fns [.seq unitTy none, .nat] [ty, .nat]

/-- Look up the `Member` position of a site inside `wireSpecs` shifted by `stmtCount`. -/
def findWireMember {V : Vocabulary} {fns : List (FnHeader V)} {unitTy : V.Ty}
    (targetSite : Site) (targetTy : V.Ty) :
    (specs : List (WireSpec V fns unitTy)) →
    Option (Member (specs.map (·.ty)) targetTy)
  | [] => none
  | s :: rest =>
      if h : s.site = targetSite ∧ s.ty = targetTy then
        some (h.2 ▸ Member.head)
      else
        (findWireMember targetSite targetTy rest).map Member.tail

/-- Lift a `Member bs τ` to `Member (as ++ bs) τ`. -/
def memberAppendRight {α : Type} {τ : α} :
    (as : List α) → {bs : List α} → Member bs τ → Member (as ++ bs) τ
  | [], _, m => m
  | _ :: as, _, m => .tail (memberAppendRight as m)

/-- Collect wire items and prover clauses in event order for a compact layout. -/
def collectCompactWire (a : Admitted V) (layout : Layout) (unitTy : V.Ty)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V)) :
    Nat → List (ShapeEvent V) →
    Except (List (ProgramRefusal V))
      (List (WireSpec V a.program.headers.fns unitTy) ×
       List (Clause V a.program.headers prover (.seq unitTy none)))
  | _, [] => .ok ([], [])
  | idx, e :: rest => do
      let (wRest, pRest) ← collectCompactWire a layout unitTy prover verifier declKey events (idx + 1) rest
      match e.cls with
      | .flow kind giver getters =>
          if giver = prover ∧ verifier ∈ getters then
            match layout.recover.lookup e.site with
            | some _ =>
                let cP := layoutDropClause (stateTy := .seq unitTy none) prover e.site
                  kind getters (τ := e.τ)
                .ok (wRest, cP :: pRest)
            | none =>
                match findLayoutWrite a layout.module unitTy e.τ,
                      findLayoutRead a layout.module unitTy e.τ with
                | some wRef, some rRef =>
                    let cP := layoutPWriteClause prover e.site kind getters wRef
                    .ok (⟨e.site, e.τ, rRef⟩ :: wRest, cP :: pRest)
                | _, _ => .error (deployErr declKey .callee)
          else
            .ok (wRest, pRest)
      | .given (.coin _) owner hearers =>
          if owner = verifier ∧ prover ∈ hearers then
            let toldSite : Site := ⟨e.site.through, drawToldKey events idx⟩
            if e.site ∈ layout.carry then
              match findLayoutWrite a layout.module unitTy e.τ,
                    findLayoutRead a layout.module unitTy e.τ with
              | some wRef, some rRef =>
                  let cP := layoutPWriteClause prover toldSite .message [verifier] wRef
                  .ok (⟨toldSite, e.τ, rRef⟩ :: wRest, cP :: pRest)
              | _, _ => .error (deployErr declKey .callee)
            else
              let cP := layoutDropClause (stateTy := .seq unitTy none) prover toldSite
                .message [verifier] (τ := e.τ)
              .ok (wRest, cP :: pRest)
          else
            .ok (wRest, pRest)
      | .given (.request _) _ _ => .ok (wRest, pRest)

/-- Build verifier clauses for a compact layout from the collected wire specification. -/
def buildCompactVClauses (a : Admitted V) (layout : Layout) (unitTy : V.Ty)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V))
    (stmtTys : List V.Ty) (wireSpecs : List (WireSpec V a.program.headers.fns unitTy))
    (htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false) :
    Nat → List (ShapeEvent V) →
    Except (List (ProgramRefusal V))
      (List (Clause V a.program.headers verifier (.tuple (tysOfList (stmtTys ++ wireSpecs.map (·.ty))))))
  | _, [] => .ok []
  | idx, e :: rest => do
      let vRest ← buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys
        wireSpecs htfree (idx + 1) rest
      match e.cls with
      | .flow kind giver getters =>
          if giver = prover ∧ verifier ∈ getters then
            match layout.recover.lookup e.site with
            | some recKey =>
                match findSafeFnRef a recKey (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                | some recRef =>
                    let cV := compactRecoverClause verifier prover e.site kind recRef
                    .ok (cV :: vRest)
                | none => .error (deployErr declKey .callee)
            | none =>
                match findWireMember e.site e.τ wireSpecs with
                | some mWire =>
                    have mState : Member (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList e.τ := by
                      rw [tysOfList_toList]
                      exact memberAppendRight stmtTys mWire
                    let cV := compactReadSlotClause htfree verifier prover e.site kind mState
                    .ok (cV :: vRest)
                | none => .error (deployErr declKey .protocol)
          else
            .ok vRest
      | .given (.coin _) owner hearers =>
          if owner = verifier ∧ prover ∈ hearers then
            let toldSite : Site := ⟨e.site.through, drawToldKey events idx⟩
            if e.site ∈ layout.carry then
              match findWireMember toldSite e.τ wireSpecs,
                    findLayoutEqual a layout.module e.τ with
              | some mWire, some eqRef =>
                  have mState : Member (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList e.τ := by
                    rw [tysOfList_toList]
                    exact memberAppendRight stmtTys mWire
                  let cV := compactCompareClause htfree verifier prover toldSite
                    (layoutGuardKey events idx) mState eqRef
                  .ok (cV :: vRest)
              | _, _ => .error (deployErr declKey .callee)
            else
              let cV := layoutDropClause (stateTy := .tuple (tysOfList (stmtTys ++ wireSpecs.map (·.ty))))
                verifier toldSite .message [prover] (τ := e.τ)
              .ok (cV :: vRest)
          else
            .ok vRest
      | .given (.request _) _ _ => .ok vRest

/-- Build the compact verifier layout (when `layout.recover ≠ []`): parses all retained messages
and carried draws in `start`, checks trailing bytes, recovers omitted messages via `recoverFn`,
and compares carried draws against derived draws. -/
def buildCompactLayoutLayers (a : Admitted V) (entry : ProtocolHeader V) (layout : Layout)
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V)) :
    Except (List (ProgramRefusal V))
      (Layer V a.program.headers prover entry.ins ×
       Layer V a.program.headers verifier entry.ins) := do
  -- 1. Collect wire items & prover clauses in event order
  let (wireSpecs, pClauses) ← collectCompactWire a layout unitTy prover verifier declKey events 0 events
  -- 2. Statement variables held by verifier (shifted by +1 for proof input at index 0)
  let vTys := .seq unitTy none :: held verifier entry.ins
  let stmtPos := statementPositions verifier prover verifier (.inr rfl) entry.ins
  let stmtItems : List ((τ : V.Ty) × Var (Ctx.positional vTys) τ) :=
    stmtPos.map fun sp =>
      ⟨sp.ty, posVar vTys (sp.heldIndex + 1) (by simpa [vTys] using sp.atHeld)⟩
  let stmtTys := stmtItems.map Sigma.fst
  let wireTys := wireSpecs.map (·.ty)
  let stateList := stmtTys ++ wireTys
  let stateTys := tysOfList stateList
  if htfree : Tys.anyLinear V stateTys = false then
    let readers : List ((τ : V.Ty) × SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]) :=
      wireSpecs.map fun ws => ⟨ws.ty, ws.readRef⟩
    have hMapReaders : readers.map Sigma.fst = wireTys := by
      simp [readers, wireTys]
    let startTerm : Term (localDialect V a.program.headers.fns)
        (Ctx.positional (.seq unitTy none :: held verifier entry.ins)) [.tuple stateTys] :=
      have hTys : stmtItems.map Sigma.fst ++ readers.map Sigma.fst = stateList := by
        rw [hMapReaders]
      cast (congrArg (fun ts => Term (localDialect V a.program.headers.fns)
        (Ctx.positional (.seq unitTy none :: held verifier entry.ins)) [.tuple (tysOfList ts)]) hTys)
        (compactLayoutVStart unitTy hfree (finishGuardKey events) stmtItems readers)
    -- 3. Build verifier clauses
    let vClauses ← buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys
      wireSpecs htfree 0 events
    let layP : Layer V a.program.headers prover entry.ins := {
      line := .layout
      state := .seq unitTy none
      takes := []
      gives := [.seq unitTy none]
      clauses := pClauses
      again := restoreAgain (.seq unitTy none)
      start := layoutPStart unitTy
      finish := identityFinish (.seq unitTy none)
    }
    let layV : Layer V a.program.headers verifier entry.ins := {
      line := .layout
      state := .tuple stateTys
      takes := [.seq unitTy none]
      gives := []
      clauses := vClauses
      again := restoreAgain (.tuple stateTys)
      start := startTerm
      finish := emptyFinish (.tuple stateTys)
    }
    .ok (layP, layV)
  else
    .error (deployErr declKey .linear)

/-! ## Main deployment functions (`deploy` and `deployIdeal`) -/

/-- Resolve the published or derived session-identity bytes for a `.derived` scheme. -/
def resolveSessionBytes (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (sessionTag : Option (List Nat)) :
    Except (List (ProgramRefusal V)) ((bs : List Nat) ×' (∀ b, b ∈ bs → b < 256)) :=
  match sessionTag with
  | some tag =>
      if hOk : ∀ b, b ∈ tag → b < 256 then .ok ⟨tag, hOk⟩
      else .error (deployErr declaration.key .literal)
  | none =>
      .ok ⟨schemeIdentity enc a declaration, schemeIdentity_bytes enc a declaration⟩

/-- Build the proof layout layers for prover and verifier (streaming when `recover = []`,
compact when `recover ≠ []`). -/
def buildLayoutLayers (a : Admitted V) (entry : ProtocolHeader V) (layout : Layout)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V)) :
    Except (List (ProgramRefusal V))
      (Layer V a.program.headers prover entry.ins ×
       Layer V a.program.headers verifier entry.ins) := do
  let some ⟨unitTy, ⟨hfree⟩⟩ := findLayoutUnit a layout.module
    | .error (deployErr declKey .linear)
  if layout.recover.isEmpty then
    let (pClauses, vClauses) ←
      buildStreamingLayoutClauses a layout unitTy hfree prover verifier declKey events
    let layP : Layer V a.program.headers prover entry.ins := {
      line := .layout
      state := .seq unitTy none
      takes := []
      gives := [.seq unitTy none]
      clauses := pClauses
      again := restoreAgain (.seq unitTy none)
      start := layoutPStart unitTy
      finish := identityFinish (.seq unitTy none)
    }
    let layV : Layer V a.program.headers verifier entry.ins := {
      line := .layout
      state := streamStateTy unitTy
      takes := [.seq unitTy none]
      gives := []
      clauses := vClauses
      again := restoreAgain (streamStateTy unitTy)
      start := layoutVStart unitTy
      finish := layoutVFinish unitTy hfree (finishGuardKey events)
    }
    .ok (layP, layV)
  else
    buildCompactLayoutLayers a entry layout unitTy hfree prover verifier declKey events

/-- Validate authored-scheme event discipline and build optional `samples` clauses for prover. -/
def checkAuthoredEvents (a : Admitted V) (prover verifier : Role) (samplesKey : Option Key)
    (declKey : Key) : List (ShapeEvent V) →
    Except (List (ProgramRefusal V)) (List (Clause V a.program.headers prover .nat))
  | [] => .ok []
  | e :: rest => do
      let sRest ← checkAuthoredEvents a prover verifier samplesKey declKey rest
      match e.cls with
      | .flow _ giver getters =>
          if (giver = prover ∧ verifier ∈ getters) ∨
              (giver ≠ prover ∧ giver ≠ verifier ∧
                prover ∉ getters ∧ verifier ∉ getters) then
            .ok sRest
          else
            .error (deployErr declKey .protocol)
      | .given (.coin law) owner hearers =>
          if hearers = [] then
            if owner = prover then
              match samplesKey with
              | none => .ok sRest
              | some sKey =>
                  match findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                  | some sRef =>
                      .ok (proverSampleClause prover e.site law sRef :: sRest)
                  | none => .error (deployErr declKey .callee)
            else
              .ok sRest
          else
            .error (deployErr declKey .protocol)
      | .given (.request _) owner hearers =>
          if (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) then
            .ok sRest
          else
            .error (deployErr declKey .protocol)

/-- Official core deployment (`Functions.deploy`): validates `declaration` against `a : Admitted V`
and generates the checked `Core.Layer` IR stack for every role inside `Deployed V`. -/
def deploy (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration) :
    Except (List (ProgramRefusal V)) (Deployed V) := do
  match hFound : a.program.findProtocol declaration.entry with
  | none => .error (deployErr declaration.key .callee)
  | some foundPair =>
      let entry := foundPair.1
      have hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [hFound]; rfl
      have hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = entry := by
        simp [hFound, entry]
      if !checkScope entry declaration then
        .error (deployErr declaration.key .attempt)
      else
        match declaration.construction with
        | .interactive =>
            .ok {
              admitted := a
              declaration := declaration
              found := hIsSome
              stack := fun _ => []
            }
        | .authored =>
            match proverAndVerifier entry declaration with
            | none => .error (deployErr declaration.key .protocol)
            | some (prover, verifier) =>
                if hEq : prover = verifier then
                  .error (deployErr declaration.key .protocol)
                else
                  let events := entry.shape.events [] id
                  let sClauses ← checkAuthoredEvents a prover verifier declaration.samples
                    declaration.key events
                  match declaration.layout with
                  | none => .error (deployErr declaration.key .callee)
                  | some layout => do
                      let (layP, layV) ←
                        buildLayoutLayers a entry layout prover verifier declaration.key events
                      let proverStack : List (Layer V a.program.headers prover entry.ins) :=
                        match declaration.samples with
                        | none => [layP]
                        | some _ =>
                            let sampP : Layer V a.program.headers prover entry.ins := {
                              line := .samples
                              state := .nat
                              takes := []
                              gives := []
                              clauses := sClauses
                              again := attemptNumAgain
                              start := samplesStart
                              finish := emptyFinish .nat
                            }
                            [sampP, layP]
                      .ok {
                        admitted := a
                        declaration := declaration
                        found := hIsSome
                        stack := fun r =>
                          if hP : r = prover then
                            hP ▸ hEntryEq ▸ proverStack
                          else if hV : r = verifier then
                            hV ▸ hEntryEq ▸ [layV]
                          else []
                      }
        | .derived suite sessionTag =>
            match proverAndVerifier entry declaration with
            | none => .error (deployErr declaration.key .protocol)
            | some (prover, verifier) =>
                if hEq : prover = verifier then
                  .error (deployErr declaration.key .protocol)
                else
                  match declaration.layout with
                  | none => .error (deployErr declaration.key .callee)
                  | some layout =>
                      match findSuiteStart a suite with
                      | none => .error (deployErr declaration.key .callee)
                      | some ⟨stateTy, startRef⟩ =>
                          match findSuiteAbsorb a suite stateTy with
                          | none => .error (deployErr declaration.key .callee)
                          | some ⟨suiteUnitTy, absorbRef⟩ => do
                              let events := entry.shape.events [] id
                              let ⟨sessBytes, hSessBytes⟩ ←
                                resolveSessionBytes enc a declaration sessionTag
                              let stmtP ← buildStmtAbsorbItems a suite suiteUnitTy
                                prover prover verifier (.inl rfl) entry.ins declaration.key
                              let stmtV ← buildStmtAbsorbItems a suite suiteUnitTy
                                verifier prover verifier (.inr rfl) entry.ins declaration.key
                              let (cPClauses, cVClauses, sClauses) ←
                                buildConstructionClauses a suite stateTy suiteUnitTy absorbRef
                                  prover verifier declaration.samples declaration.key events
                              let (layP, layV) ←
                                buildLayoutLayers a entry layout prover verifier
                                  declaration.key events
                              let conP : Layer V a.program.headers prover entry.ins := {
                                line := .construction
                                state := stateTy
                                takes := []
                                gives := []
                                clauses := cPClauses
                                again := restoreAgain stateTy
                                start := constructionStart sessBytes hSessBytes startRef
                                  absorbRef stmtP
                                finish := emptyFinish stateTy
                              }
                              let conV : Layer V a.program.headers verifier entry.ins := {
                                line := .construction
                                state := stateTy
                                takes := []
                                gives := []
                                clauses := cVClauses
                                again := restoreAgain stateTy
                                start := constructionStart sessBytes hSessBytes startRef
                                  absorbRef stmtV
                                finish := emptyFinish stateTy
                              }
                              let proverStack : List (Layer V a.program.headers prover entry.ins) :=
                                match declaration.samples with
                                | none => [conP, layP]
                                | some _ =>
                                    let sampP : Layer V a.program.headers prover entry.ins := {
                                      line := .samples
                                      state := .nat
                                      takes := []
                                      gives := []
                                      clauses := sClauses
                                      again := attemptNumAgain
                                      start := samplesStart
                                      finish := emptyFinish .nat
                                    }
                                    [sampP, conP, layP]
                              let verifierStack : List (Layer V a.program.headers verifier entry.ins) :=
                                [conV, layV]
                              .ok {
                                admitted := a
                                declaration := declaration
                                found := hIsSome
                                stack := fun r =>
                                  if hP : r = prover then
                                    hP ▸ hEntryEq ▸ proverStack
                                  else if hV : r = verifier then
                                    hV ▸ hEntryEq ▸ verifierStack
                                  else []
                              }

/-- Ideal random-oracle deployment (`SCHEMES-AND-FIAT-SHAMIR.md` §3.2 & §9.2):
replaces the verifier's concrete `derive` calls with `.own (.request serviceKey)` on the
accumulated transcript state (session identity + statement + messages + prior draws), keeping the
exact same absorption schedule and proof layout layer as `deploy`. -/
def deployIdeal (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) : Except (List (ProgramRefusal V)) (Deployed V) := do
  match hFound : a.program.findProtocol declaration.entry with
  | none => .error (deployErr declaration.key .callee)
  | some foundPair =>
      let entry := foundPair.1
      have hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [hFound]; rfl
      have hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = entry := by
        simp [hFound, entry]
      if !checkScope entry declaration then
        .error (deployErr declaration.key .attempt)
      else
        match declaration.construction with
        | .derived suite sessionTag =>
            match proverAndVerifier entry declaration with
            | none => .error (deployErr declaration.key .protocol)
            | some (prover, verifier) =>
                if hEq : prover = verifier then
                  .error (deployErr declaration.key .protocol)
                else
                  match declaration.layout with
                  | none => .error (deployErr declaration.key .callee)
                  | some layout =>
                      match findSuiteStart a suite with
                      | none => .error (deployErr declaration.key .callee)
                      | some ⟨stateTy, startRef⟩ =>
                          match findSuiteAbsorb a suite stateTy with
                          | none => .error (deployErr declaration.key .callee)
                          | some ⟨suiteUnitTy, absorbRef⟩ => do
                              let events := entry.shape.events [] id
                              let ⟨sessBytes, hSessBytes⟩ ←
                                resolveSessionBytes enc a declaration sessionTag
                              let stmtV ← buildStmtAbsorbItems a suite suiteUnitTy
                                verifier prover verifier (.inr rfl) entry.ins declaration.key
                              let idealVClauses ←
                                buildIdealVerifierClauses a suite stateTy suiteUnitTy absorbRef
                                  serviceKey prover verifier declaration.key events
                              let (_, layV) ←
                                buildLayoutLayers a entry layout prover verifier
                                  declaration.key events
                              let idealConV : Layer V a.program.headers verifier entry.ins := {
                                line := .construction
                                state := stateTy
                                takes := []
                                gives := []
                                clauses := idealVClauses
                                again := restoreAgain stateTy
                                start := constructionStart sessBytes hSessBytes startRef
                                  absorbRef stmtV
                                finish := emptyFinish stateTy
                              }
                              .ok {
                                admitted := a
                                declaration := declaration
                                found := hIsSome
                                stack := fun r =>
                                  if hV : r = verifier then
                                    hV ▸ hEntryEq ▸ [idealConV, layV]
                                  else []
                              }
        | _ => .error (deployErr declaration.key .protocol)

end

end Zkc.Core
