module

public import Zkc.Core.Scheme.Layer.Builders
public import Zkc.Core.Scheme.Deploy.Lookup

@[expose] public section

/-!
Non-interactive and ideal random-oracle scheme deployment (`deploy`, `deployIdeal`), fail-closed
declaration/scope/layout validation, shared `DerivedPrepared` preparation, and the bare ideal
verifier specification (`BareIdealReturn`).
-/

namespace Zkc.Core

open LayerBuild

section
variable {V : Vocabulary}

/-! ## Fail-closed declaration, scope, and layout validation -/

def deployErr (declKey : Key) (rule : Rule) : List (ProgramRefusal V) :=
  [refuseWhole declKey rule .nothing]

/-- Decidable list duplicate-freedom check. -/
def listNodupBool {A : Type} [DecidableEq A] : List A → Bool
  | [] => true
  | x :: xs => !decide (x ∈ xs) && listNodupBool xs

/-- Fail-closed validation of `declaration`: rejects unsupported declaration fields (`context`,
`grinds`, `commits`, `pins`) and mismatched role-kind counts instead of silently ignoring them. -/
def checkDeclarationSupported (hdr : ProtocolHeader V) (declaration : Declaration) : Bool :=
  decide (declaration.kinds.length = hdr.roles) &&
  declaration.context.isEmpty &&
  declaration.grinds.isEmpty &&
  declaration.commits.isEmpty &&
  declaration.pins.isEmpty

/-- Fail-closed validation of interactive-scheme declaration fields: rejects `layout`, `samples`,
fewer than two online roles, or an out-of-range / non-online declared `prover`. -/
def checkInteractive (declaration : Declaration) : Bool :=
  let onlineCount :=
    ((List.range declaration.kinds.length).filter
      (fun i => declaration.kinds[i]? == some .online)).length
  declaration.layout.isNone &&
  declaration.samples.isNone &&
  decide (2 ≤ onlineCount) &&
  declaration.prover.all (fun p => declaration.kinds[p]? == some .online)

/-- Check retry/abort scope for an interactive scheme: no retry may be declared, and every
`abort` guard in the shape must lie inside an attempt. -/
def checkInteractiveScope (hdr : ProtocolHeader V) (declaration : Declaration) : Bool :=
  declaration.retry.isNone && (hdr.shape.abortsOutside [] false).isEmpty

theorem checkInteractiveScope_sound (hdr : ProtocolHeader V) (declaration : Declaration)
    (h : checkInteractiveScope hdr declaration = true) :
    declaration.retry = none ∧
    (∀ bound site, declaration.retry = some (bound, site) → site ∈ hdr.shape.attemptSites []) ∧
      hdr.shape.abortsOutside [] false = [] := by
  simp only [checkInteractiveScope, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  refine ⟨h.1, ?_, h.2⟩
  intro _ _ hretry
  rw [h.1] at hretry; cases hretry

/-- Check retry/abort scope for a non-interactive scheme with prover `prover`:
- when `retry = none`, every `abort` guard must lie inside an attempt;
- when `retry = some (bound, site)`, `0 < bound`, `site` must be an attempt owned exclusively
  by `prover`, `site` must not nest inside itself, and every `abort` guard must lie inside `site`. -/
def checkNonInteractiveScope (hdr : ProtocolHeader V) (prover : Role)
    (declaration : Declaration) : Bool :=
  match declaration.retry with
  | none => (hdr.shape.abortsOutside [] false).isEmpty
  | some (bound, site) =>
      decide (0 < bound) &&
      decide (site ∈ hdr.shape.proverAttemptSites prover []) &&
      hdr.shape.noNestedAttempt site [] &&
      (hdr.shape.abortsOutsideTarget site [] false).isEmpty

theorem checkNonInteractiveScope_sound (hdr : ProtocolHeader V) (prover : Role)
    (declaration : Declaration) (h : checkNonInteractiveScope hdr prover declaration = true) :
    (∀ bound site, declaration.retry = some (bound, site) → site ∈ hdr.shape.attemptSites []) ∧
      hdr.shape.abortsOutside [] false = [] := by
  unfold checkNonInteractiveScope at h
  cases hretry : declaration.retry with
  | none =>
      rw [hretry, List.isEmpty_iff] at h
      exact ⟨(fun _ _ hEq => by cases hEq), h⟩
  | some p =>
      cases p with
      | mk bound site =>
          rw [hretry] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
          refine ⟨fun b s hEq => ?_, Shape.abortsOutside_eq_nil_of_target site [] false hdr.shape h.2⟩
          cases hEq
          exact Shape.proverAttemptSites_subset prover [] hdr.shape h.1.1.2

theorem checkNonInteractiveScope_wellNested (hdr : ProtocolHeader V) (prover : Role)
    (declaration : Declaration) (h : checkNonInteractiveScope hdr prover declaration = true) :
    ∀ bound site, declaration.retry = some (bound, site) →
      Shape.noNestedAttempt site [] hdr.shape = true := by
  unfold checkNonInteractiveScope at h
  intro bound site hretry
  rw [hretry] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- Strict fail-closed validation of `layout.carry` and `layout.recover`:
1. Every carried site must be a distinct verifier→prover heard-coin site of `events`.
2. Every recovered site must be a distinct prover→verifier flow site of `events`.
3. When `layout.recover ≠ []`, the protocol shape must be straight-line (no `.choice`/`.loop`)
   and have distinct event sites so compact pre-parsing matches prover wire order unconditionally. -/
def checkLayoutSites (entry : ProtocolHeader V) (events : List (ShapeEvent V))
    (prover verifier : Role) (layout : Layout) : Bool :=
  let heardSites := events.filterMap fun e =>
    match e.cls with
    | .given (.coin _) owner hearers =>
        if owner = verifier ∧ hearers = [prover] then some e.site else none
    | _ => none
  let flowSites := events.filterMap fun e =>
    match e.cls with
    | .flow _ giver getters =>
        if giver = prover ∧ getters = [verifier] then some e.site else none
    | _ => none
  let carryOk := layout.carry.all (fun s => decide (s ∈ heardSites)) && listNodupBool layout.carry
  let recSites := layout.recover.map Prod.fst
  let recoverOk := recSites.all (fun s => decide (s ∈ flowSites)) && listNodupBool recSites
  let compactShapeOk :=
    if layout.recover.isEmpty then true
    else entry.shape.isStraightLine && listNodupBool (events.map (·.site))
  carryOk && recoverOk && compactShapeOk

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

/-- Build `samples derived by` clauses for every private prover coin in `events`, passing all
prover inputs (`held prover ins`), the resolved session bytes, the full canonical site bytes,
the attempt number, and the monotonic call sequence counter. -/
def buildSamplesClauses (a : Admitted V) (heldP : List V.Ty)
    (htfree : Tys.anyLinear V (samplesStateTys heldP) = false)
    (prover : Role) (sKey : Key)
    (sessBytes : List Nat) (hSessBytes : ∀ b, b ∈ sessBytes → b < 256)
    (declKey : Key) : List (ShapeEvent V) →
    Except (List (ProgramRefusal V)) (List (Clause V a.program.headers prover (samplesStateTy heldP)))
  | [] => .ok []
  | e :: rest => do
      let sRest ← buildSamplesClauses a heldP htfree prover sKey sessBytes hSessBytes declKey rest
      match e.cls with
      | .given (.coin law) owner [] =>
          if owner = prover then
            match V.law law with
            | some ⟨[], outTy⟩ =>
                if outTy = e.τ then
                  match findTypedFnRef a sKey (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [e.τ] with
                  | some sRef =>
                      let cS := proverSampleClause htfree prover e.site law
                        sessBytes hSessBytes (encodeSite e.site) (encodeSite_bytes e.site) sRef
                      .ok (cS :: sRest)
                  | none => .error (deployErr declKey .callee)
                else
                  .error (deployErr declKey .operands)
            | some ⟨_ :: _, _⟩ => .error (deployErr declKey .operands)
            | none => .error (deployErr declKey .row)
          else
            .ok sRest
      | _ => .ok sRest

/-- Validate `declaration.samples` and build the prover `samples` layer when present.
Verifies that the named function exists in `a.program`, that prover inputs are non-linear, and
that every private prover coin matches the derived-sample signature. -/
def buildSamplesLayer (a : Admitted V) (entry : ProtocolHeader V) (prover : Role)
    (samplesKey : Option Key)
    (sessBytes : List Nat) (hSessBytes : ∀ b, b ∈ sessBytes → b < 256)
    (declKey : Key) (events : List (ShapeEvent V)) :
    Except (List (ProgramRefusal V)) (Option (Layer V a.program.headers prover entry.ins)) :=
  match samplesKey with
  | none => .ok none
  | some sKey =>
      match a.program.find sKey with
      | some (.fn _) =>
          let heldP := held prover entry.ins
          if htfree : Tys.anyLinear V (samplesStateTys heldP) = false then do
            let sClauses ← buildSamplesClauses a heldP htfree prover sKey sessBytes hSessBytes
              declKey events
            .ok (some {
              line := .samples
              state := samplesStateTy heldP
              takes := []
              gives := []
              clauses := sClauses
              again := samplesAgain heldP htfree
              start := samplesStart
              finish := emptyFinish (samplesStateTy heldP)
            })
          else
            .error (deployErr declKey .linear)
      | _ => .error (deployErr declKey .callee)

/-- Classify and build the `construction` clauses for both online roles.
Trailing prover messages with `needAbs = false` (no draw reachable afterwards) are passed directly
through to the layout layer without wasted hashing (Chiesa and Orrù (2025), Construction 4.3). -/
def buildConstructionClauses (enc : VocabEncoder V) (a : Admitted V) (suite : ModuleRef) (stateTy unitTy : V.Ty)
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (prover verifier : Role) (declKey : Key)
    (events : List (ShapeEvent V)) (eventsAbs : List (ShapeEvent V × Bool)) :
    Except (List (ProgramRefusal V))
      (List (Clause V a.program.headers prover stateTy) ×
       List (Clause V a.program.headers verifier stateTy)) :=
  go 0 eventsAbs
where
  go (idx : Nat) : List (ShapeEvent V × Bool) →
      Except (List (ProgramRefusal V))
        (List (Clause V a.program.headers prover stateTy) ×
         List (Clause V a.program.headers verifier stateTy))
    | [] => .ok ([], [])
    | (e, needAbs) :: rest => do
        let (pRest, vRest) ← go (idx + 1) rest
        match e.cls with
        | .flow kind giver getters =>
            if giver = prover ∧ getters = [verifier] then
              if needAbs then
                match findSuiteEncode a suite unitTy e.τ with
                | none => .error (deployErr declKey .callee)
                | some encRef =>
                    let cP := proverAbsorbClause prover e.site kind getters
                      (msgLabel e.site) (msgLabel_bytes e.site) encRef absorbRef
                    let cV := verifierAbsorbClause verifier prover e.site kind
                      (msgLabel e.site) (msgLabel_bytes e.site) encRef absorbRef
                    .ok (cP :: pRest, cV :: vRest)
              else
                .ok (pRest, vRest)
            else if giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters then
              .ok (pRest, vRest)
            else
              .error (deployErr declKey .protocol)
        | .given (.coin law) owner hearers =>
            if owner = verifier ∧ hearers = [prover] then
              match V.law law with
              | none => .error (deployErr declKey .row)
              | some sig =>
                  if sig.out = e.τ then
                    match findSuiteDerive enc a suite stateTy law sig.ins e.τ with
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
                            .ok (cP :: pRest, cV :: vRest)
                        | _ :: _ => .error (deployErr declKey .operands)
                  else
                    .error (deployErr declKey .operands)
            else if hearers = [] then
              .ok (pRest, vRest)
            else
              .error (deployErr declKey .protocol)
        | .given (.request _) owner hearers =>
            if (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) then
              .ok (pRest, vRest)
            else
              .error (deployErr declKey .protocol)

/-- Build pure collision-free ideal random-oracle verifier construction clauses over
`idealPathTy unitTy`: appends encoded messages onto `(metaLog, dataLog)` (when `needAbs = true`)
and answers every verifier draw via `.own (.request serviceKey)` on `(idealPath, drawLabel)`
without touching any concrete `SuiteSlot.start` or `SuiteSlot.absorb`. -/
def buildIdealVerifierClauses (a : Admitted V) (suite : ModuleRef) (unitTy : V.Ty)
    (hfree : Ty.isLinear V unitTy = false)
    (serviceKey : Key) (prover verifier : Role) (declKey : Key)
    (events : List (ShapeEvent V)) (eventsAbs : List (ShapeEvent V × Bool)) :
    Except (List (ProgramRefusal V)) (List (Clause V a.program.headers verifier (idealPathTy unitTy))) :=
  go 0 eventsAbs
where
  go (idx : Nat) : List (ShapeEvent V × Bool) →
      Except (List (ProgramRefusal V)) (List (Clause V a.program.headers verifier (idealPathTy unitTy)))
    | [] => .ok []
    | (e, needAbs) :: rest => do
        let vRest ← go (idx + 1) rest
        match e.cls with
        | .flow kind giver getters =>
            if giver = prover ∧ getters = [verifier] then
              if needAbs then
                match findSuiteEncode a suite unitTy e.τ with
                | none => .error (deployErr declKey .callee)
                | some encRef =>
                    let cV := idealAbsorbClause hfree verifier prover e.site kind
                      (msgLabel e.site) (msgLabel_bytes e.site) encRef
                    .ok (cV :: vRest)
              else
                .ok vRest
            else if giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters then
              .ok vRest
            else
              .error (deployErr declKey .protocol)
        | .given (.coin law) owner hearers =>
            if owner = verifier ∧ hearers = [prover] then
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
                            let cV := idealDeriveClause hfree verifier prover e.site
                              (.own (.coin law) hearers) [] serviceKey rk tk
                              (drawLabel e.site) (drawLabel_bytes e.site) encRef
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
            if giver = prover ∧ getters = [verifier] then
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
            if owner = verifier ∧ hearers = [prover] then
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
          if giver = prover ∧ getters = [verifier] then
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
          if owner = verifier ∧ hearers = [prover] then
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
          if giver = prover ∧ getters = [verifier] then
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
          if owner = verifier ∧ hearers = [prover] then
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

/-- Resolve the domain-separated session-identity bytes for a `.derived` scheme.
Always binds `schemeIdentity enc a declaration` (which includes `declaration.application`, entry,
suite, layout, and reachable definitions). An explicit `sessionTag` must be non-empty valid bytes
(`< 256`) and is encoded as a prefix-free domain tag ahead of `schemeIdentity`. -/
def resolveSessionBytes (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (sessionTag : Option (List Nat)) :
    Except (List (ProgramRefusal V)) ((bs : List Nat) ×' (∀ b, b ∈ bs → b < 256)) :=
  let idBytes := schemeIdentity enc a declaration
  let hId := schemeIdentity_bytes enc a declaration
  match sessionTag with
  | none =>
      .ok ⟨0 :: idBytes, fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hmem
        · decide
        · exact hId b hmem⟩
  | some [] =>
      .error (deployErr declaration.key .literal)
  | some (b0 :: rest) =>
      let tag := b0 :: rest
      if hOk : ∀ b, b ∈ tag → b < 256 then
        let tagBytes := encodeList encodeNat tag
        .ok ⟨1 :: tagBytes ++ idBytes, fun b hb => by
          rcases List.mem_cons.mp hb with rfl | hmem
          · decide
          · rcases List.mem_append.mp hmem with ht | hi
            · exact encodeList_bytes encodeNat encodeNat_bytes tag b ht
            · exact hId b hi⟩
      else
        .error (deployErr declaration.key .literal)

/-- `resolveSessionBytes` is injective: equal session bytes imply equal `sessionTag`, equal
`declaration` (including `application`), and literally equal `canonicalClosureDefs`. -/
theorem resolveSessionBytes_injective (enc : VocabEncoder V) (hEnc : enc.Injective)
    {a₁ a₂ : Admitted V} {decl₁ decl₂ : Declaration}
    {tag₁ tag₂ : Option (List Nat)} {bs : List Nat}
    {h₁ h₂ : ∀ b, b ∈ bs → b < 256}
    (hRes₁ : resolveSessionBytes enc a₁ decl₁ tag₁ = .ok ⟨bs, h₁⟩)
    (hRes₂ : resolveSessionBytes enc a₂ decl₂ tag₂ = .ok ⟨bs, h₂⟩) :
    tag₁ = tag₂ ∧ decl₁ = decl₂ ∧
      canonicalClosureDefs a₁ decl₁ = canonicalClosureDefs a₂ decl₂ := by
  unfold resolveSessionBytes at hRes₁ hRes₂
  cases tag₁ with
  | none =>
      have hBs₁ : 0 :: schemeIdentity enc a₁ decl₁ = bs := congrArg PSigma.fst (Except.ok.inj hRes₁)
      cases tag₂ with
      | none =>
          have hBs₂ : 0 :: schemeIdentity enc a₂ decl₂ = bs := congrArg PSigma.fst (Except.ok.inj hRes₂)
          have hId : schemeIdentity enc a₁ decl₁ = schemeIdentity enc a₂ decl₂ :=
            (List.cons.inj (hBs₁.trans hBs₂.symm)).2
          exact ⟨rfl, schemeIdentity_injective enc hEnc a₁ a₂ decl₁ decl₂ hId⟩
      | some t₂ =>
          cases t₂ with
          | nil => cases hRes₂
          | cons b₂ r₂ =>
              dsimp only at hRes₂
              split at hRes₂
              · have hBs₂ : 1 :: encodeList encodeNat (b₂ :: r₂) ++ schemeIdentity enc a₂ decl₂ = bs :=
                  congrArg PSigma.fst (Except.ok.inj hRes₂)
                have h01 := (List.cons.inj (hBs₁.trans hBs₂.symm)).1
                cases h01
              · cases hRes₂
  | some t₁ =>
      cases t₁ with
      | nil => cases hRes₁
      | cons b₁ r₁ =>
          dsimp only at hRes₁
          split at hRes₁
          · have hBs₁ : 1 :: encodeList encodeNat (b₁ :: r₁) ++ schemeIdentity enc a₁ decl₁ = bs :=
              congrArg PSigma.fst (Except.ok.inj hRes₁)
            cases tag₂ with
            | none =>
                have hBs₂ : 0 :: schemeIdentity enc a₂ decl₂ = bs := congrArg PSigma.fst (Except.ok.inj hRes₂)
                have h10 := (List.cons.inj (hBs₁.trans hBs₂.symm)).1
                cases h10
            | some t₂ =>
                cases t₂ with
                | nil => cases hRes₂
                | cons b₂ r₂ =>
                    dsimp only at hRes₂
                    split at hRes₂
                    · have hBs₂ : 1 :: encodeList encodeNat (b₂ :: r₂) ++ schemeIdentity enc a₂ decl₂ = bs :=
                        congrArg PSigma.fst (Except.ok.inj hRes₂)
                      have hTail := (List.cons.inj (hBs₁.trans hBs₂.symm)).2
                      have ⟨hTagEq, hIdEq⟩ :=
                        encodeList_prefixFree encodeNat_prefixFree (b₁ :: r₁) (b₂ :: r₂)
                          (schemeIdentity enc a₁ decl₁) (schemeIdentity enc a₂ decl₂) hTail
                      exact ⟨congrArg some hTagEq,
                        schemeIdentity_injective enc hEnc a₁ a₂ decl₁ decl₂ hIdEq⟩
                    · cases hRes₂
          · cases hRes₁

/-- Site- and session-bound lawfulness for a deployment's deterministic prover-sampling function
(`samples derived by`) under encoder `enc` in model `M`: charges `sKey` only on the deployment's
actual resolved `sessBytes` and each prover private coin's actual `encodeSite e.site` (accepting
site-sensitive samplers that dispatch on site bytes). -/
def Deployed.SamplesLawfulFor (enc : VocabEncoder V) (M : Model V) (d : Deployed V) : Prop :=
  ∀ sKey prover verifier suite sessionTag sessBytes hSess,
    d.declaration.samples = some sKey →
    d.declaration.construction = .derived suite sessionTag →
    d.roles = some (prover, verifier) →
    resolveSessionBytes enc d.admitted d.declaration sessionTag = .ok ⟨sessBytes, hSess⟩ →
    ∀ (hdr : FnHeader V) (f : Member d.admitted.program.headers.fns hdr),
      d.admitted.program.find sKey = some (.fn f) →
      ∀ (e : ShapeEvent V) (law : V.LawKey),
        e ∈ d.entry.shape.events [] id →
        e.cls = .given (.coin law) prover [] →
        V.law law = some ⟨[], e.τ⟩ →
        ∀ (hins : hdr.ins = held prover d.entry.ins ++ [.seq (.fin 256) none, .seq (.fin 256) none, .nat, .nat])
          (houts : hdr.outs = [e.τ])
          (heldVals : HList M.Val (held prover d.entry.ins))
          (attemptNum callSeq : Nat) (coin : M.Val e.τ),
          heldVals.All M.Valid →
          Defs.fnTable M d.admitted.program.defs hdr f
            (cast (congrArg (HList M.Val) hins.symm)
              (HList.append heldVals
                (.cons sessBytes (.cons (encodeSite e.site)
                  (.cons (a := Ty.nat) attemptNum (.cons (a := Ty.nat) callSeq .nil)))))) =
            .done (cast (congrArg (HList M.Val) houts.symm) (.cons coin .nil)) →
          Allows M (.coin law) [] .nil e.τ coin

/-- The stronger site-agnostic `Deployed.SamplesLawful` implies `Deployed.SamplesLawfulFor` for
every encoder `enc`. -/
theorem Deployed.SamplesLawful.toFor {d : Deployed V} (enc : VocabEncoder V) (M : Model V)
    (h : d.SamplesLawful M) : d.SamplesLawfulFor enc M := by
  intro sKey prover verifier _ _ sessBytes hSess hSamp _ hRoles _ hdr f hFind e law hE hCls
    hLaw hins houts heldVals att seq coin hHeldV hFn
  exact h sKey prover verifier hSamp hRoles hdr f hFind e law [] hE hCls hLaw hins houts heldVals
    sessBytes (encodeSite e.site) att seq .nil coin hHeldV hSess (encodeSite_bytes e.site)
    trivial hFn

/-- Build the proof layout layers for prover and verifier (streaming when `recover = []`,
compact when `recover ≠ []`), strictly validating `carry`, `recover`, and straight-line shape. -/
def buildLayoutLayers (a : Admitted V) (entry : ProtocolHeader V) (layout : Layout)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V)) :
    Except (List (ProgramRefusal V))
      (Layer V a.program.headers prover entry.ins ×
       Layer V a.program.headers verifier entry.ins) := do
  if !checkLayoutSites entry events prover verifier layout then
    .error (deployErr declKey .protocol)
  else
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

/-- Validate authored-scheme event discipline: only single-recipient prover→verifier flows,
non-online flows, private coins (`hearers = []`), and properly scoped service requests may appear. -/
def checkAuthoredEvents (prover verifier : Role) (declKey : Key) : List (ShapeEvent V) →
    Except (List (ProgramRefusal V)) Unit
  | [] => .ok ()
  | e :: rest => do
      checkAuthoredEvents prover verifier declKey rest
      match e.cls with
      | .flow _ giver getters =>
          if (giver = prover ∧ getters = [verifier]) ∨
              (giver ≠ prover ∧ giver ≠ verifier ∧
                prover ∉ getters ∧ verifier ∉ getters) then
            .ok ()
          else
            .error (deployErr declKey .protocol)
      | .given (.coin _) _ hearers =>
          if hearers = [] then .ok ()
          else .error (deployErr declKey .protocol)
      | .given (.request _) owner hearers =>
          if (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) then
            .ok ()
          else
            .error (deployErr declKey .protocol)

/-- Shared validated data produced by `prepareDerivedBody` for both `deploy` (`.derived`) and
`deployIdeal`, ensuring identical role, retry-scope, used-law encoder distinctness, session-tag,
derived-sample, and layout validation across concrete and ideal deployments. -/
structure DerivedPrepared (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (entry : ProtocolHeader V) (sessionTag : Option (List Nat)) where
  prover : Role
  verifier : Role
  hPV : proverAndVerifier entry declaration = some (prover, verifier)
  hNe : prover ≠ verifier
  hScope : checkNonInteractiveScope entry prover declaration = true
  hLawsDist : checkUsedLawsDistinct enc (usedHeardLaws prover verifier (entry.shape.events [] id)) = true
  layout : Layout
  hLayOpt : declaration.layout = some layout
  sessBytes : List Nat
  hSessBytes : ∀ b, b ∈ sessBytes → b < 256
  hSess : resolveSessionBytes enc a declaration sessionTag = .ok ⟨sessBytes, hSessBytes⟩
  sampLayer : Option (Layer V a.program.headers prover entry.ins)
  hSamp : buildSamplesLayer a entry prover declaration.samples sessBytes hSessBytes
    declaration.key (entry.shape.events [] id) = .ok sampLayer
  layP : Layer V a.program.headers prover entry.ins
  layV : Layer V a.program.headers verifier entry.ins
  hLay : buildLayoutLayers a entry layout prover verifier declaration.key
    (entry.shape.events [] id) = .ok (layP, layV)

/-- Shared validation and layer-building prologue for `.derived` schemes in both `deploy` and
`deployIdeal`. -/
def prepareDerivedBody (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (entry : ProtocolHeader V) (sessionTag : Option (List Nat)) :
    Except (List (ProgramRefusal V)) (DerivedPrepared enc a declaration entry sessionTag) :=
  match hPV : proverAndVerifier entry declaration with
  | none => .error (deployErr declaration.key .protocol)
  | some (prover, verifier) =>
      if hEq : prover = verifier then
        .error (deployErr declaration.key .protocol)
      else if hScope : checkNonInteractiveScope entry prover declaration then
        let events := entry.shape.events [] id
        if hLawsDist : checkUsedLawsDistinct enc (usedHeardLaws prover verifier events) then
          match hLayOpt : declaration.layout with
          | none => .error (deployErr declaration.key .callee)
          | some layout =>
              match hSess : resolveSessionBytes enc a declaration sessionTag with
              | .error errs => .error errs
              | .ok ⟨sessBytes, hSessBytes⟩ =>
                  match hSamp : buildSamplesLayer a entry prover declaration.samples
                      sessBytes hSessBytes declaration.key events with
                  | .error errs => .error errs
                  | .ok sampLayer =>
                      match hLay : buildLayoutLayers a entry layout prover verifier
                          declaration.key events with
                      | .error errs => .error errs
                      | .ok (layP, layV) =>
                          .ok ⟨prover, verifier, hPV, hEq, hScope, hLawsDist, layout, hLayOpt,
                            sessBytes, hSessBytes, hSess, sampLayer, hSamp, layP, layV, hLay⟩
        else
          .error (deployErr declaration.key .protocol)
      else
        .error (deployErr declaration.key .attempt)

/-- Official core deployment (`Functions.deploy`): validates `declaration` fail-closed against
`a : Admitted V`, binds `identity := schemeIdentity enc a declaration`, and generates the checked
`Core.Layer` IR stack for every role inside `Deployed V`. -/
def deploy (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration) :
    Except (List (ProgramRefusal V)) (Deployed V) := do
  match hFound : a.program.findProtocol declaration.entry with
  | none => .error (deployErr declaration.key .callee)
  | some foundPair =>
      let entry := foundPair.1
      have hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [hFound]; rfl
      have hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = entry := by
        simp [hFound, entry]
      if !checkDeclarationSupported entry declaration then
        .error (deployErr declaration.key .protocol)
      else
        match declaration.construction with
        | .interactive =>
            if !checkInteractive declaration then
              .error (deployErr declaration.key .protocol)
            else if !checkInteractiveScope entry declaration then
              .error (deployErr declaration.key .attempt)
            else
              .ok {
                admitted := a
                declaration := declaration
                found := hIsSome
                stack := fun _ => []
                identity := schemeIdentity enc a declaration
              }
        | .authored =>
            if !declaration.samples.isNone then
              .error (deployErr declaration.key .protocol)
            else
              match proverAndVerifier entry declaration with
              | none => .error (deployErr declaration.key .protocol)
              | some (prover, verifier) =>
                  if hEq : prover = verifier then
                    .error (deployErr declaration.key .protocol)
                  else if !checkNonInteractiveScope entry prover declaration then
                    .error (deployErr declaration.key .attempt)
                  else
                    let events := entry.shape.events [] id
                    let () ← checkAuthoredEvents prover verifier declaration.key events
                    match declaration.layout with
                    | none => .error (deployErr declaration.key .callee)
                    | some layout => do
                        let (layP, layV) ←
                          buildLayoutLayers a entry layout prover verifier declaration.key events
                        .ok {
                          admitted := a
                          declaration := declaration
                          found := hIsSome
                          stack := fun r =>
                            if hP : r = prover then
                              hP ▸ hEntryEq ▸ [layP]
                            else if hV : r = verifier then
                              hV ▸ hEntryEq ▸ [layV]
                            else []
                          identity := schemeIdentity enc a declaration
                        }
        | .derived suite sessionTag => do
            let ⟨prover, verifier, _, _, _, _, _, _, sessBytes, hSessBytes, _, sampLayer, _, layP, layV, _⟩ ←
              prepareDerivedBody enc a declaration entry sessionTag
            match findSuiteStart a suite with
            | none => .error (deployErr declaration.key .callee)
            | some ⟨stateTy, startRef⟩ =>
                match findSuiteAbsorb a suite stateTy with
                | none => .error (deployErr declaration.key .callee)
                | some ⟨suiteUnitTy, absorbRef⟩ => do
                    let events := entry.shape.events [] id
                    let eventsAbs := entry.shape.eventsWithAbsorb prover verifier [] id false
                    let stmtP ← buildStmtAbsorbItems a suite suiteUnitTy
                      prover prover verifier (.inl rfl) entry.ins declaration.key
                    let stmtV ← buildStmtAbsorbItems a suite suiteUnitTy
                      verifier prover verifier (.inr rfl) entry.ins declaration.key
                    let (cPClauses, cVClauses) ←
                      buildConstructionClauses enc a suite stateTy suiteUnitTy absorbRef
                        prover verifier declaration.key events eventsAbs
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
                      match sampLayer with
                      | none => [conP, layP]
                      | some sampP => [sampP, conP, layP]
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
                      identity := schemeIdentity enc a declaration
                    }

/-- Pure collision-free ideal random-oracle deployment: shares all declaration, scope, used-law
distinctness, session, derived-sample, and layout validation with `deploy`, enforces deploy-time
freshness of `serviceKey` against all protocol service requests (`checkServiceKeyFresh`), binds
`identity := schemeIdentity enc a declaration`, and constructs an injective `(metaLog, dataLog)`
path over `idealPathTy suiteUnitTy` without calling any concrete `SuiteSlot.start` or
`SuiteSlot.absorb`, answering every verifier draw via `.own (.request serviceKey)` on
`(idealPath, drawLabel)`. -/
def deployIdeal (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) : Except (List (ProgramRefusal V)) (Deployed V) := do
  match hFound : a.program.findProtocol declaration.entry with
  | none => .error (deployErr declaration.key .callee)
  | some foundPair =>
      let entry := foundPair.1
      have hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [hFound]; rfl
      have hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = entry := by
        simp [hFound, entry]
      if !checkDeclarationSupported entry declaration then
        .error (deployErr declaration.key .protocol)
      else
        match declaration.construction with
        | .derived suite sessionTag => do
            let ⟨prover, verifier, _, _, _, _, _, _, sessBytes, hSessBytes, _, _, _, _, layV, _⟩ ←
              prepareDerivedBody enc a declaration entry sessionTag
            let events := entry.shape.events [] id
            if !checkServiceKeyFresh events serviceKey then
              .error (deployErr declaration.key .protocol)
            else
              match findSuiteUnit a suite with
              | none => .error (deployErr declaration.key .linear)
              | some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩ => do
                  let eventsAbs := entry.shape.eventsWithAbsorb prover verifier [] id false
                  let stmtV ← buildStmtAbsorbItems a suite suiteUnitTy
                    verifier prover verifier (.inr rfl) entry.ins declaration.key
                  let idealVClauses ←
                    buildIdealVerifierClauses a suite suiteUnitTy hSuiteFree
                      serviceKey prover verifier declaration.key events eventsAbs
                  let idealConV : Layer V a.program.headers verifier entry.ins := {
                    line := .construction
                    state := idealPathTy suiteUnitTy
                    takes := []
                    gives := []
                    clauses := idealVClauses
                    again := restoreAgain (idealPathTy suiteUnitTy)
                    start := idealStart hSuiteFree sessBytes hSessBytes stmtV
                    finish := emptyFinish (idealPathTy suiteUnitTy)
                  }
                  .ok {
                    admitted := a
                    declaration := declaration
                    found := hIsSome
                    stack := fun r =>
                      if hV : r = verifier then
                        hV ▸ hEntryEq ▸ [idealConV, layV]
                      else []
                    identity := schemeIdentity enc a declaration
                  }
        | _ => .error (deployErr declaration.key .protocol)

/-! ## Ideal random-oracle verifier specification -/

/-- Whether the single-recipient prover→verifier flow `(site, kind, τ)` is marked for transcript
absorption in `eventsAbs` (false for trailing messages elided under Chiesa and Orrù (2025),
Construction 4.3). -/
def needIdealAbsorb (prover verifier : Role) (eventsAbs : List (ShapeEvent V × Bool))
    (site : Site) (kind : FlowKind) (τ : V.Ty) : Bool :=
  eventsAbs.any fun p =>
    p.2 && decide (p.1.site = site) && decide (p.1.τ = τ) &&
      match p.1.cls with
      | .flow k g gs => decide (k = kind ∧ g = prover ∧ gs = [verifier])
      | _ => false

/-- Pure specification of the canonical initial collision-free ideal transcript path: starts from
`([0 :: sessBytes], [])` and appends `(1 :: stmtLabel i, encode(stmt_i))` for every statement
input in signature order. -/
def idealInitialPath (M : Model V) (a : Admitted V) (suite : ModuleRef) (suiteUnitTy : V.Ty)
    (prover verifier : Role) {ins : List (LTy V)}
    (sessBytes : List Nat) (vals : HList (RV M verifier) ins) :
    Option (M.Val (idealPathTy suiteUnitTy)) :=
  go (idealPathInit M suiteUnitTy sessBytes)
    (statementPositions verifier prover verifier (.inr rfl) ins)
where
  go (st : M.Val (idealPathTy suiteUnitTy)) :
      List (StmtPos V verifier ins) → Option (M.Val (idealPathTy suiteUnitTy))
    | [] => some st
    | sp :: rest =>
        match findSuiteEncode a suite suiteUnitTy sp.ty with
        | none => none
        | some encRef =>
            let v := (Env.positional (heldValues M verifier vals)).get
              (posVar (held verifier ins) sp.heldIndex sp.atHeld)
            match encRef.eval M (Defs.fnTable M a.program.defs) (.cons v .nil) with
            | .done res =>
                go (idealPathPush M st (1 :: stmtLabel sp.stmtIndex) res.single) rest
            | _ => none

/-- Direct relational acceptance semantics for a bare verifier role program `p : Program M A`
under a non-carry streaming ideal random-oracle deployment without retry, parameterized by the
ideal transcript path `st`, proof buffer `buf`, read cursor `off`, world `source`, service key
`serviceKey`, and partial random oracle `ro`. Completely independent of `Layer`, `Stack`,
`Handler`, `Clause`, and concrete `SuiteSlot.start`/`SuiteSlot.absorb`. -/
inductive BareIdealReturn (M : Model V) (a : Admitted V)
    (suite : ModuleRef) (layout : Layout) {suiteUnitTy unitTy : V.Ty}
    (serviceKey : Key) (prover verifier : Role)
    (eventsAbs : List (ShapeEvent V × Bool))
    (source : Source M) (ro : IdealRO M suiteUnitTy)
    {A : Type} :
    Program M A → M.Val (idealPathTy suiteUnitTy) → List (M.Val unitTy) → Nat → A → Prop where
  | done {outV : A} {st : M.Val (idealPathTy suiteUnitTy)}
      {buf : List (M.Val unitTy)} {off : Nat}
      (hLen : off = buf.length) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.done outV) st buf off outV
  | getAbsorb {kind : FlowKind} {at_ : Occurrence} {τ : V.Ty} {k : M.Val τ → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off nextOff : Nat}
      {msg : M.Val τ} {enc : List (M.Val suiteUnitTy)} {outV : A}
      {rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
      {encRef : TypedFnRef V a.program.headers.fns [τ] [.seq suiteUnitTy none]}
      (hNeed : needIdealAbsorb prover verifier eventsAbs at_.site kind τ = true)
      (hRead : findLayoutRead a layout.module unitTy τ = some rRef)
      (hEvalR : rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) =
        .done (.cons msg (.cons nextOff .nil)))
      (hEnc : findSuiteEncode a suite suiteUnitTy τ = some encRef)
      (hEvalE : encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil) =
        .done (.cons enc .nil))
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k msg) (idealPathPush M st (2 :: msgLabel at_.site) enc) buf nextOff outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.get kind prover at_ τ) k) st buf off outV
  | getElided {kind : FlowKind} {at_ : Occurrence} {τ : V.Ty} {k : M.Val τ → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off nextOff : Nat}
      {msg : M.Val τ} {outV : A}
      {rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
      (hNoNeed : needIdealAbsorb prover verifier eventsAbs at_.site kind τ = false)
      (hRead : findLayoutRead a layout.module unitTy τ = some rRef)
      (hEvalR : rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) =
        .done (.cons msg (.cons nextOff .nil)))
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k msg) st buf nextOff outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.get kind prover at_ τ) k) st buf off outV
  | draw {law : V.LawKey} {h0 : Role} {hs : List Role} {at_ : Occurrence} {τ : V.Ty}
      {k : M.Val τ → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off : Nat}
      {coin : M.Val τ} {enc : List (M.Val suiteUnitTy)} {outV : A}
      {encRef : TypedFnRef V a.program.headers.fns [τ] [.seq suiteUnitTy none]}
      (hRo : ro st (drawLabel at_.site) τ = some coin)
      (hEnc : findSuiteEncode a suite suiteUnitTy τ = some encRef)
      (hEvalE : encRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil) =
        .done (.cons enc .nil))
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k coin) (idealPathPush M st (3 :: drawLabel at_.site) enc) buf off outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.own (.coin law) (h0 :: hs) at_ [] .nil τ) k) st buf off outV
  | privateCoin {law : V.LawKey} {at_ : Occurrence} {gIns : List V.Ty}
      {payload : HList M.Val gIns} {τ : V.Ty} {k : M.Val τ → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off : Nat}
      {v : M.Val τ} {outV : A}
      (hSrc : source at_ τ = some v)
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k v) st buf off outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.own (.coin law) [] at_ gIns payload τ) k) st buf off outV
  | requestOracle {svc : Key} {hearers : List Role} {at_ : Occurrence} {gIns : List V.Ty}
      {payload : HList M.Val gIns} {τ : V.Ty} {k : M.Val τ → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off : Nat}
      {v : M.Val τ} {outV : A}
      (hSvc : svc = serviceKey)
      (hAns : IdealRO.asOracle M ro gIns payload τ = some v)
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k v) st buf off outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.own (.request svc) hearers at_ gIns payload τ) k) st buf off outV
  | requestSource {svc : Key} {hearers : List Role} {at_ : Occurrence} {gIns : List V.Ty}
      {payload : HList M.Val gIns} {τ : V.Ty} {k : M.Val τ → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off : Nat}
      {v : M.Val τ} {outV : A}
      (hNot : svc ≠ serviceKey ∨ IdealRO.asOracle M ro gIns payload τ = none)
      (hSrc : source at_ τ = some v)
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k v) st buf off outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.own (.request svc) hearers at_ gIns payload τ) k) st buf off outV
  | «begin» {at_ : Occurrence} {k : Nat → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off : Nat} {outV : A}
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k 0) st buf off outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.begin at_) k) st buf off outV
  | settle {at_ : Occurrence} {k : Unit → Program M A}
      {st : M.Val (idealPathTy suiteUnitTy)} {buf : List (M.Val unitTy)} {off : Nat} {outV : A}
      (hRest : BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (k ()) st buf off outV) :
      BareIdealReturn M a suite layout serviceKey prover verifier eventsAbs source ro
        (.call (.settle at_) k) st buf off outV

end

end Zkc.Core
