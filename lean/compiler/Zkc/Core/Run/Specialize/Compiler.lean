module

public import Zkc.Core.Run.Specialize.ClosedIR

@[expose] public section

/-!
DAG-preserving multi-procedure handler specialization compiler (`Deployed V → ClosedRole`).

Given a `Deployed V` and role `r`:
1. Computes the static set of active sites (`stackActiveSites (d.stack r) d.retry`): every handler
   clause site in the role's layer stack plus any retry site.
2. Collects shared protocol demands at every call site whose subtree is disjoint from all active
   sites (`subtreeFree activeSites through = true`), where handler dispatch is path-independent
   (`unhandledSpecOp`) and retry never triggers.
3. Builds an acyclic bottom-up `ClosedProcs` table structurally along `Defs V` (`buildSharedProcs`),
   deduplicating `(FinPerm, Role)` per protocol so diamond call graphs compile in linear size
   instead of exponential tree size.
4. Specializes the entry protocol (`specializeProtocolInDefs`), emitting `ClosedTerm.call` for
   shared procedures and falling back to path-sensitive `ClosedTerm.frame` inlining wherever a
   layer clause or retry site intercepts inside the callee's subtree.
-/

namespace Zkc.Core

section Specializer
variable {V : Vocabulary}

/-! ## Active sites and subtree-disjointness -/

/-- All clause sites occurring in a layer stack. -/
def stackClauseSites {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    List (Layer V hs r ins) → List Site
  | [] => []
  | l :: rest => l.clauses.map (fun c => c.site.site) ++ stackClauseSites rest

/-- All sites where either a layer clause or retry handler can intercept execution. -/
def stackActiveSites {hs : Headers V} {r : Role} {ins : List (LTy V)}
    (layers : List (Layer V hs r ins)) (retry : Option (Nat × Site)) : List Site :=
  match retry with
  | none => stackClauseSites layers
  | some (_, site) => site :: stackClauseSites layers

/-- True when no active handler clause or retry site lies under the call-path prefix `through`. -/
def subtreeFree (activeSites : List Site) (through : List Key) : Bool :=
  activeSites.all fun s => !(through.isPrefixOf s.through)

theorem subtreeFree_nil_active (through : List Key) : subtreeFree [] through = true := rfl

theorem list_isPrefixOf_append_left {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (a b c : List α), (a ++ b).isPrefixOf c = true → a.isPrefixOf c = true
  | [], _, _, _ => rfl
  | x :: xs, b, [], h => by simp at h
  | x :: xs, b, y :: ys, h => by
      simp only [List.cons_append, List.isPrefixOf, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, list_isPrefixOf_append_left xs b ys h.2⟩

theorem subtreeFree_append (activeSites : List Site) (through more : List Key)
    (h : subtreeFree activeSites through = true) :
    subtreeFree activeSites (through ++ more) = true := by
  unfold subtreeFree at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro s hs
  have hNot := h s hs
  simp only [Bool.not_eq_true'] at hNot ⊢
  cases hPref : (through ++ more).isPrefixOf s.through with
  | false => rfl
  | true =>
      have hPre := list_isPrefixOf_append_left through more s.through hPref
      rw [hPre] at hNot
      cases hNot

theorem subtreeFree_not_mem (activeSites : List Site) (through : List Key)
    (h : subtreeFree activeSites through = true) {s : Site} (hs : s ∈ activeSites) :
    ¬ (through.isPrefixOf s.through = true) := by
  unfold subtreeFree at h
  have h1 := List.all_eq_true.mp h s hs
  simp only [Bool.not_eq_true'] at h1
  intro hPre
  rw [hPre] at h1
  cases h1

theorem list_isPrefixOf_self {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (xs : List α), xs.isPrefixOf xs = true
  | [] => rfl
  | x :: xs => by simp [List.isPrefixOf, list_isPrefixOf_self xs]

theorem subtreeFree_ne_through (activeSites : List Site) (through : List Key)
    (h : subtreeFree activeSites through = true) {s : Site} (hs : s ∈ activeSites) :
    s.through ≠ through := by
  intro hEq
  exact subtreeFree_not_mem activeSites through h hs (by rw [hEq]; exact list_isPrefixOf_self through)

/-! ## Effect specializer, stack combinators, and `ApplyTarget` -/

/-- Static effect specializer targeting layer states `σ` and shared procedures `procs`. -/
abbrev EffectSpecializer (V : Vocabulary) (fns : List (FnHeader V))
    (procs : List (ClosedProcSig V)) (σ : List V.Ty) : Type :=
  List Key → Key → {ins res : List V.Ty} →
    ResidualOp V ins res → {Δ : Ctx V.Ty} → HList (Var Δ) ins →
    ClosedTerm V fns procs σ Δ res

/-- Path-independent fallback specializer delegating every effect straight through `σ` layers
to `.effect` at the bottom of the stack. -/
def unhandledSpecOp {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)} :
    (σ : List V.Ty) → EffectSpecializer V fns procs σ
  | [] => fun _ key {_ _} op {_} args => .effect key op args
  | _ :: rest => fun through key {_ _} op {_} args =>
      .underLayer (unhandledSpecOp rest through key op args)

/-- Trivial embedding of the empty procedure signature list into any `procs`. -/
def emptyProcLift {procs : List (ClosedProcSig V)} {sig : ClosedProcSig V} (m : Member [] sig) :
    Member procs sig :=
  nomatch m

/-- Lift an `EffectSpecializer` along a procedure-table embedding `pLift`. -/
def EffectSpecializer.liftProcs {fns : List (FnHeader V)}
    {procs₁ procs₂ : List (ClosedProcSig V)} {σ : List V.Ty}
    (pLift : ∀ {sig}, Member procs₁ sig → Member procs₂ sig)
    (specOp : EffectSpecializer V fns procs₁ σ) :
    EffectSpecializer V fns procs₂ σ :=
  fun through key {_ _} op {_} args => (specOp through key op args).liftProcs pLift

/-- Extract the `StackAgain` terms of a layer stack. -/
def stackAgain {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    (layers : List (Layer V hs r ins)) → StackAgain V hs.fns (Stack.States layers)
  | [] => .nil
  | l :: rest => .cons l.again (stackAgain rest)

/-- Extract the `StackInit` terms of a layer stack. -/
def stackInit {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    (layers : List (Layer V hs r ins)) →
    StackInit V hs.fns (held r ins) (Stack.States layers) (Stack.Takes layers)
  | [] => .nil
  | l :: rest => .cons l.start (stackInit rest)

/-- Extract the `StackFinish` terms of a layer stack. -/
def stackFinish {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    (layers : List (Layer V hs r ins)) →
    StackFinish V hs.fns (Stack.States layers) (Stack.Gives layers)
  | [] => .nil
  | l :: rest => .cons l.finish (stackFinish rest)

/-- Convert a role `Times` into a `ClosedTimes`. -/
def specializeTimes {hs : Headers V} {r : Role} {w : Holders} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) : Times (roleDialect V hs r) w Γ → ClosedTimes Δ
  | .fixed n => .fixed n
  | .value count ok => .value (cast (congrArg (Var Δ) ok.1) (varHeld hCtx count ok.2.1))

theorem specializeTimes_size {hs : Headers V} {r : Role} {w : Holders} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) (times : Times (roleDialect V hs r) w Γ) :
    (specializeTimes hCtx times).size = times.size := by
  cases times <;> rfl

/-- Result of specializing a protocol call site: either a DAG-shared procedure reference (`shared`)
or an inline call frame (`inlined`). -/
inductive ApplyTarget (V : Vocabulary) (fns : List (FnHeader V))
    (procs : List (ClosedProcSig V)) (σ : List V.Ty) (ins outs : List V.Ty) where
  | shared (callee : Member procs ⟨σ, ins, outs⟩)
  | inlined (inputs : Names ins) (body : ClosedTerm V fns procs σ (Ctx.empty.extend inputs) outs)

/-! ## Term specialization (`specializeTerm`, `specializeArms`) -/

section TermSpec
variable {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)} {σ : List V.Ty}
  {hs : Headers V}
  (specOp : EffectSpecializer V fullFns procs σ)
  (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
  (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
    {hdr : ProtocolHeader V} → Member hs.protocols hdr →
    List Key → FinPerm → (r : Role) →
    ApplyTarget V fullFns procs σ (held r hdr.ins) (held r hdr.outs))

mutual
  def specializeTerm (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
      (through : List Key) (perm : FinPerm) (r : Role) :
      {Γ : Ctx (LTy V)} → {Δ : Ctx V.Ty} → CtxRel r Γ Δ →
      {outs : List (LTy V)} → Term (roleDialect V hs r) Γ outs →
      ClosedTerm V fullFns procs σ Δ (held r outs)
    | _, _, hCtx, _, .ret exit => .ret (varsHeld hCtx exit)
    | _, Δ, hCtx, _, .op key o operands results rest =>
        match o with
        | .compute R lo _ types mine here =>
            let hRes : held r (List.map (fun τ => ⟨τ, R⟩) _) = _ :=
              held_map_holders r R mine _
            let resNames := cast (congrArg Names hRes) (heldNames r results)
            let args := cast (congrArg (HList (Var Δ)) types) (varsAllHeld hCtx here operands)
            let k := specializeTerm retryCfg through perm r (hCtx.extend results) rest
            .localOp key (lo.lift fnLift) args resNames
              (k.castCT (ctx_extend_cast Δ hRes (heldNames r results)).symm rfl)
        | .absent items out =>
            let hEmpty : held r items = [] := held_all_out r items out
            let hExt : Δ.extend (heldNames r results) = Δ := by
              have hNil : cast (congrArg Names hEmpty) (heldNames r results) = .nil := by
                cases cast (congrArg Names hEmpty) (heldNames r results); rfl
              rw [← ctx_extend_cast Δ hEmpty (heldNames r results), hNil]; rfl
            (specializeTerm retryCfg through perm r (hCtx.extend results) rest).castCT hExt rfl
        | .give (τ := τ) (H := H) kind getters here =>
            match operands, results with
            | .cons x .nil, .cons resName .nil =>
                let v := varHeld hCtx x here
                let hIn : r ∈ Holders.ofList (getters ++ H) :=
                  Holders.mem_ofList.mpr (List.mem_append_right _ here)
                let hExt : Δ.extend (heldNames r (.cons resName .nil)) = Δ.insert resName τ := by
                  rw [heldNames_cons_pos hIn,
                    ctx_extend_cast Δ (held_cons_pos r _ [] hIn).symm]; rfl
                let k := (specializeTerm retryCfg through perm r (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl
                .letBind (specOp through key ((ResidualOp.give kind getters τ).mapPeers perm.apply) (.cons v .nil))
                  .nil (.alias v resName k)
        | .get τ H kind giver getters mine =>
            match results with
            | .cons resName .nil =>
                let hIn : r ∈ Holders.ofList (getters ++ H) :=
                  Holders.mem_ofList.mpr (List.mem_append_left _ mine)
                let hRes : held r [⟨τ, Holders.ofList (getters ++ H)⟩] = [τ] := by
                  simp [held, hIn]
                let resNames := cast (congrArg Names hRes) (heldNames r (.cons resName .nil))
                let k := specializeTerm retryCfg through perm r (hCtx.extend (.cons resName .nil)) rest
                .letBind (specOp through key ((ResidualOp.get kind giver τ).mapPeers perm.apply) .nil)
                  resNames
                  (k.castCT (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl)
        | .keep (τ := τ) (H := H) H' same =>
            match operands, results with
            | .cons x .nil, .cons resName .nil =>
                if h : r ∈ H then
                  let h' : r ∈ H' := same.mp h
                  let hExt : Δ.extend (heldNames r (.cons resName .nil)) = Δ.insert resName τ := by
                    rw [heldNames_cons_pos h',
                      ctx_extend_cast Δ (held_cons_pos r _ [] h').symm]; rfl
                  let k := (specializeTerm retryCfg through perm r (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl
                  .alias (varHeld hCtx x h) resName k
                else
                  let h' : r ∉ H' := fun m => h (same.mpr m)
                  let hExt : Δ.extend (heldNames r (.cons resName .nil)) = Δ := by
                    rw [heldNames_cons_neg h',
                      ctx_extend_cast Δ (held_cons_neg r _ [] h').symm]; rfl
                  (specializeTerm retryCfg through perm r (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl
        | .own kind hearers opTys τ _ here =>
            match results with
            | .cons resName .nil =>
                let hIn : r ∈ Holders.ofList (r :: hearers) :=
                  Holders.mem_ofList.mpr List.mem_cons_self
                let hRes : held r [⟨τ, Holders.ofList (r :: hearers)⟩] = [τ] := by
                  simp [held, hIn]
                let resNames := cast (congrArg Names hRes) (heldNames r (.cons resName .nil))
                let args := varsAllHeld hCtx here operands
                let k := specializeTerm retryCfg through perm r (hCtx.extend (.cons resName .nil)) rest
                .letBind (specOp through key
                    ((ResidualOp.own kind hearers (opTys.map LTy.ty) τ).mapPeers perm.apply) args)
                  resNames
                  (k.castCT (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl)
        | .hear kind owner hearers τ mine =>
            match results with
            | .cons resName .nil =>
                let hIn : r ∈ Holders.ofList (owner :: hearers) :=
                  Holders.mem_ofList.mpr (List.mem_cons_of_mem _ mine)
                let hRes : held r [⟨τ, Holders.ofList (owner :: hearers)⟩] = [τ] := by
                  simp [held, hIn]
                let resNames := cast (congrArg Names hRes) (heldNames r (.cons resName .nil))
                let k := specializeTerm retryCfg through perm r (hCtx.extend (.cons resName .nil)) rest
                .letBind (specOp through key ((ResidualOp.hear kind owner τ).mapPeers perm.apply) .nil)
                  resNames
                  (k.castCT (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl)
        | .apply callee roles distinct _ _ fits =>
            let rm := RoleMap.ofList roles distinct
            let r' := rm.back r
            let fitArgs := fitVars hCtx rm fits operands
            let hOut : held r (_ : List (LTy V)) = held r' _ := held_map_roleMap rm r _
            let resNames := cast (congrArg Names hOut) (heldNames r results)
            let k := (specializeTerm retryCfg through perm r (hCtx.extend results) rest).castCT
              (ctx_extend_cast Δ hOut (heldNames r results)).symm rfl
            match specApply retryCfg callee (through ++ [key])
                (perm.comp (FinPerm.ofList roles distinct)) r' with
            | .shared mem => .call (some key) mem fitArgs resNames k
            | .inlined calleeIns calleeBody =>
                .frame (some key) fitArgs calleeIns calleeBody resNames k
    | _, Δ, hCtx, _, .guard key _ c ok why rest =>
        let cv : Var Δ .bool := cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)
        .guard key cv why (specializeTerm retryCfg through perm r hCtx rest)
    | _, Δ, hCtx, _, .choose key _ c ok _ onTrue onFalse results rest =>
        let cv : Var Δ .bool := cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)
        .choose key cv
          (specializeTerm retryCfg through perm r hCtx onTrue)
          (specializeTerm retryCfg through perm r hCtx onFalse)
          (heldNames r results)
          (specializeTerm retryCfg through perm r (hCtx.extend results) rest)
    | _, Δ, hCtx, _, .cases (t := t) (payloads := payloads) key ps x ok _ arms results rest =>
        let hv : ∃ k alts, t.ty = .variant k alts ∧ payloads = alts.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨k, alts, he, hp, _⟩ := ok; exact ⟨k, alts, he, hp⟩
        let hEq : t.ty = .variant t.ty.variantKey t.ty.alternatives := Ty.eq_variant hv
        let hPay : payloads = t.ty.alternatives.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨_, alts, he, hp⟩ := hv; rw [Ty.alternatives_of he, hp]
        let hrT : r ∈ t.holders := by obtain ⟨_, _, _, _, h1, _⟩ := ok; exact h1
        let hrPs : r ∈ ps := by obtain ⟨_, _, _, _, _, h2⟩ := ok; exact h2
        let xv : Var Δ (.variant t.ty.variantKey t.ty.alternatives) :=
          cast (congrArg (Var Δ) hEq) (varHeld hCtx x hrT)
        let armsC := specializeArms retryCfg through perm r ps hrPs hCtx arms hPay
        .cases key xv armsC (heldNames r results)
          (specializeTerm retryCfg through perm r (hCtx.extend results) rest)
    | Γ, Δ, hCtx, _, .loop (carried := carried) (each := each) key ps times _ initial inputs body results rest =>
        match inputs with
        | .cons idxNm carriedInNames =>
            let cTimes := specializeTimes hCtx times
            let hSize : cTimes.size = times.size := specializeTimes_size hCtx times
            let hBodyOut : held r (carried ++ each) = held r carried ++ held r each :=
              held_append r carried each
            let hResTy : held r (carried ++ each.map (LTy.collected times.size)) =
                held r carried ++ (held r each).map (fun τ => .seq τ cTimes.size) := by
              rw [held_append, held_map_collected, hSize]
            let cNames := heldNames r carriedInNames
            let resNames := cast (congrArg Names hResTy) (heldNames r results)
            let k := specializeTerm retryCfg through perm r (hCtx.extend results) rest
            if hIn : r ∈ ps then
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm carriedInNames))
                  (loopBodyCtx Δ (some idxNm) cNames) := by
                simpa [Ctx.extend, loopBodyCtx, LTy.index] using
                  (hCtx.insert_held idxNm (a := LTy.index ps)).extend carriedInNames
              let bodyC := (specializeTerm retryCfg through perm r hCtxB body).castCT rfl hBodyOut
              .loop key cTimes (varsHeld hCtx initial) (some idxNm) cNames bodyC resNames
                (k.castCT (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl)
            else
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm carriedInNames))
                  (loopBodyCtx Δ none cNames) := by
                simpa [Ctx.extend, loopBodyCtx, LTy.index] using
                  (hCtx.insert_unheld idxNm (a := LTy.index ps) hIn).extend carriedInNames
              let bodyC := (specializeTerm retryCfg through perm r hCtxB body).castCT rfl hBodyOut
              .loop key cTimes (varsHeld hCtx initial) none cNames bodyC resNames
                (k.castCT (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl)
    | _, _, hCtx, _, .block key number body results rest =>
        .block key number
          (specializeTerm retryCfg through perm r hCtx body)
          (heldNames r results)
          (specializeTerm retryCfg through perm r (hCtx.extend results) rest)
    | Γ, Δ, hCtx, _, .attempt key w _ inputs body results rest =>
        match inputs with
        | .cons idxNm .nil =>
            let k := specializeTerm retryCfg through perm r (hCtx.extend results) rest
            if hw : r ∈ w then
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm .nil)) (Δ.extend (.cons idxNm .nil)) := by
                simpa [Ctx.extend, LTy.index] using hCtx.insert_held idxNm (a := LTy.index w)
              match retryCfg with
              | some (bound, retrySite, again) =>
                  if ⟨through, key⟩ = retrySite then
                    let bodyC := specializeTerm none through perm r hCtxB body
                    .retry key bound again (.cons idxNm .nil) bodyC (heldNames r results) k
                  else
                    let bodyC := specializeTerm retryCfg through perm r hCtxB body
                    .letBind
                      (.letBind (specOp through key .begin .nil) (.cons idxNm .nil)
                        (.seq bodyC (specOp through key .settle .nil)))
                      (heldNames r results) k
              | none =>
                  let bodyC := specializeTerm none through perm r hCtxB body
                  .letBind
                    (.letBind (specOp through key .begin .nil) (.cons idxNm .nil)
                      (.seq bodyC (specOp through key .settle .nil)))
                    (heldNames r results) k
            else
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm .nil)) Δ := by
                simpa [Ctx.extend, LTy.index] using hCtx.insert_unheld idxNm (a := LTy.index w) hw
              let bodyC := specializeTerm retryCfg through perm r hCtxB body
              .letBind bodyC (heldNames r results) k

  def specializeArms (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
      (through : List Key) (perm : FinPerm) (r : Role) (ps : Holders) (hrPs : r ∈ ps) :
      {Γ : Ctx (LTy V)} → {Δ : Ctx V.Ty} → CtxRel r Γ Δ →
      {mid payloads : List (LTy V)} →
      Arms (roleDialect V hs r) Γ mid payloads →
      {alts : List V.Ty} → payloads = alts.map (fun τ => ⟨τ, ps⟩) →
      ClosedArms V fullFns procs σ Δ (held r mid) alts
    | _, _, _, _, _, .nil, [], _ => .nil
    | _, _, _, _, _, .nil, _ :: _, hPay => nomatch hPay
    | _, _, _, _, _, .cons _ _ _, [], hPay => nomatch hPay
    | Γ, Δ, hCtx, _, a :: _, .cons (.cons nm .nil) arm rest, τ :: _, hPay =>
        let hHead : a = ⟨τ, ps⟩ := (List.cons.inj hPay).1
        let hTail := (List.cons.inj hPay).2
        let hCtxA : CtxRel r (Γ.extend (.cons nm .nil)) (Δ.extend (.cons nm .nil)) := by
          rw [show Γ.extend (.cons nm .nil) = Γ.insert nm ⟨τ, ps⟩ by rw [Ctx.extend, Ctx.extend, hHead]]
          exact hCtx.insert_held nm (a := ⟨τ, ps⟩)
        .cons (.cons nm .nil)
          (specializeTerm retryCfg through perm r hCtxA arm)
          (specializeArms retryCfg through perm r ps hrPs hCtx rest hTail)
end

end TermSpec

/-! ## Inline protocol specialization (`specializeProtocolInDefs`) -/

/-- Structural recursion on `defs : Defs V hs` specializing any referenced protocol against
`specOp`, consulting an optional shared-procedure lookup whenever `subtreeFree activeSites through`
holds and falling back to inline `.frame` specialization otherwise. -/
def specializeProtocolInDefs {fullFns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    {σ : List V.Ty}
    (specOp : EffectSpecializer V fullFns procs σ)
    (activeSites : List Site) :
    {hs : Headers V} → Defs V hs →
    (∀ {hdr}, Member hs.fns hdr → Member fullFns hdr) →
    ({hdr : ProtocolHeader V} → Member hs.protocols hdr → FinPerm → (r : Role) →
      Option (Member procs ⟨σ, held r hdr.ins, held r hdr.outs⟩)) →
    Option (Nat × Site × StackAgain V fullFns σ) →
    {hdr : ProtocolHeader V} → Member hs.protocols hdr →
    (through : List Key) → (perm : FinPerm) → (r : Role) →
    (inputs : Names (held r hdr.ins)) ×
      ClosedTerm V fullFns procs σ (Ctx.empty.extend inputs) (held r hdr.outs)
  | _, .nil, _, _, _, _, m, _, _, _ => nomatch m
  | _, .fn _ _ _ _ rest _, fnLift, sharedLookup, retryCfg, _, m, through, perm, r =>
      specializeProtocolInDefs specOp activeSites rest (fun f => fnLift (.tail f))
        sharedLookup retryCfg m through perm r
  | _, .protocol (hs := hsRest) _ inputs body _ rest, fnLift, sharedLookup, retryCfg, _, .head,
      through, perm, r =>
      let restLookup : {hdr' : ProtocolHeader V} → Member hsRest.protocols hdr' → FinPerm → (r' : Role) →
          Option (Member procs ⟨σ, held r' hdr'.ins, held r' hdr'.outs⟩) :=
        fun m' p' r' => sharedLookup (.tail m') p' r'
      let specApply : Option (Nat × Site × StackAgain V fullFns σ) →
          {hdr' : ProtocolHeader V} → Member hsRest.protocols hdr' →
          List Key → FinPerm → (r' : Role) →
          ApplyTarget V fullFns procs σ (held r' hdr'.ins) (held r' hdr'.outs) :=
        fun rc {_} m' th' p' r' =>
          if subtreeFree activeSites th' then
            match restLookup m' p' r' with
            | some mem => .shared mem
            | none =>
                let res := specializeProtocolInDefs specOp activeSites rest fnLift restLookup rc m' th' p' r'
                .inlined res.1 res.2
          else
            let res := specializeProtocolInDefs specOp activeSites rest fnLift restLookup rc m' th' p' r'
            .inlined res.1 res.2
      ⟨heldNames r inputs,
        @specializeTerm V fullFns procs σ hsRest specOp fnLift specApply
          retryCfg through perm r _ _ ((CtxRel.empty r).extend inputs) _ (project r body)⟩
  | _, .protocol _ _ _ _ rest, fnLift, sharedLookup, retryCfg, _, .tail m, through, perm, r =>
      specializeProtocolInDefs specOp activeSites rest fnLift
        (fun m' p' r' => sharedLookup (.tail m') p' r') retryCfg m through perm r

/-! ## Layer-stack specialization (`specializeClauses`, `specializeStack`) -/

/-- Walk a layer's clauses to find the first matching clause for `(through, key, op)` and inline
its body against the strictly shorter layer stack below. -/
def specializeClauses {hs : Headers V} (defs : Defs V hs) {r_top : Role} {state : V.Ty}
    {σ_rest : List V.Ty}
    (specBelow : EffectSpecializer V hs.fns [] σ_rest)
    (through : List Key) (key : Key) {ins res : List V.Ty} (op : ResidualOp V ins res)
    {Δ : Ctx V.Ty} (args : HList (Var Δ) ins) :
    List (Clause V hs r_top state) → ClosedTerm V hs.fns [] (state :: σ_rest) Δ res
  | [] => .underLayer (specBelow through key op args)
  | c :: cs =>
      if h : c.site.site = ⟨through, key⟩ ∧ some c.site.part = op.part ∧
          c.site.takes = ins ∧ c.site.gives = res then
        let hIn : Ctx.positional (c.site.takes ++ [state]) = Ctx.positional (ins ++ [state]) := by
          rw [h.2.2.1]
        let hOut : held r_top (alone r_top (c.site.gives ++ [state])) = res ++ [state] := by
          rw [held_alone, h.2.2.2]
        let bodyC : ClosedTerm V hs.fns [] σ_rest (Ctx.positional (ins ++ [state])) (res ++ [state]) :=
          (specializeTerm specBelow id
            (fun rc {_} m th perm' r' =>
              let r0 := specializeProtocolInDefs specBelow [] defs id (fun _ _ _ => none) rc m th perm' r'
              .inlined r0.1 r0.2)
            none through FinPerm.identity r_top
            (CtxRel.positional_alone r_top (c.site.takes ++ [state]))
            c.code).castCT hIn hOut
        .withLayer args (Names.counting 0 (ins ++ [state])) bodyC
      else
        specializeClauses defs specBelow through key op args cs

/-- Outer structural recursion on the layer stack `layers`. -/
def specializeStack {hs : Headers V} (defs : Defs V hs) {r_top : Role} {ins_top : List (LTy V)} :
    (layers : List (Layer V hs r_top ins_top)) → EffectSpecializer V hs.fns [] (Stack.States layers)
  | [] => fun _ key {_ _} op {_} args => .effect key op args
  | l :: rest =>
      let specBelow := specializeStack defs rest
      fun through key {_ _} op {_} args => specializeClauses defs specBelow through key op args l.clauses

/-! ## DAG-preserving shared-procedure construction (`buildSharedProcs`) -/

/-- A request for a shared procedure for protocol `callee` under permutation `perm` and role `role`. -/
structure SharedDemand (V : Vocabulary) (protos : List (ProtocolHeader V)) where
  hdr : ProtocolHeader V
  callee : Member protos hdr
  perm : FinPerm
  role : Role

/-- Insert a `(perm, role)` key into a deduplicated list. -/
def insertUniqueKey (k : FinPerm × Role) (ks : List (FinPerm × Role)) : List (FinPerm × Role) :=
  if k ∈ ks then ks else k :: ks

mutual
  /-- Collect direct protocol applications from a **role-projected** term (`Term (roleDialect V hs r)`),
  skipping branches and loops that role `r` does not participate in (eliminating dead procedures). -/
  def collectDirectAppliesTerm {hs : Headers V} (perm : FinPerm) (r : Role) :
      {Γ outs : _} → Term (roleDialect V hs r) Γ outs → List (SharedDemand V hs.protocols)
    | _, _, .ret _ => []
    | _, _, .op _ o _ _ rest =>
        let here := match o with
          | .apply callee roles distinct _ _ _ =>
              let rm := RoleMap.ofList roles distinct
              [⟨_, callee, perm.comp (FinPerm.ofList roles distinct), rm.back r⟩]
          | _ => []
        here ++ collectDirectAppliesTerm perm r rest
    | _, _, .guard _ _ _ _ _ rest => collectDirectAppliesTerm perm r rest
    | _, _, .choose _ _ _ _ _ t f _ rest =>
        collectDirectAppliesTerm perm r t ++ collectDirectAppliesTerm perm r f ++
          collectDirectAppliesTerm perm r rest
    | _, _, .cases _ _ _ _ _ arms _ rest =>
        collectDirectAppliesArms perm r arms ++ collectDirectAppliesTerm perm r rest
    | _, _, .loop _ _ _ _ _ _ body _ rest =>
        collectDirectAppliesTerm perm r body ++ collectDirectAppliesTerm perm r rest
    | _, _, .block _ _ body _ rest =>
        collectDirectAppliesTerm perm r body ++ collectDirectAppliesTerm perm r rest
    | _, _, .attempt _ _ _ _ body _ rest =>
        collectDirectAppliesTerm perm r body ++ collectDirectAppliesTerm perm r rest

  /-- Collect direct protocol applications across role-projected `Arms`. -/
  def collectDirectAppliesArms {hs : Headers V} (perm : FinPerm) (r : Role) :
      {Γ mid payloads : _} → Arms (roleDialect V hs r) Γ mid payloads →
      List (SharedDemand V hs.protocols)
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest =>
        collectDirectAppliesTerm perm r arm ++ collectDirectAppliesArms perm r rest
end

mutual
  /-- Walk a **role-projected** entry term (`Term (roleDialect V hs r)`) along non-free call paths
  to collect only reachable root shared demands where `subtreeFree activeSites (through ++ [key])`
  first becomes true, ignoring branches erased by `project r`. -/
  def collectEntryDemandsTerm {hs : Headers V} (activeSites : List Site)
      (onNonFree : {hdr : ProtocolHeader V} → Member hs.protocols hdr →
        List Key → FinPerm → Role → List (SharedDemand V hs.protocols))
      (through : List Key) (perm : FinPerm) (r : Role) :
      {Γ outs : _} → Term (roleDialect V hs r) Γ outs → List (SharedDemand V hs.protocols)
    | _, _, .ret _ => []
    | _, _, .op key o _ _ rest =>
        let here := match o with
          | .apply callee roles distinct _ _ _ =>
              let rm := RoleMap.ofList roles distinct
              let through' := through ++ [key]
              let perm' := perm.comp (FinPerm.ofList roles distinct)
              let r' := rm.back r
              if subtreeFree activeSites through' then
                [⟨_, callee, perm', r'⟩]
              else
                onNonFree callee through' perm' r'
          | _ => []
        here ++ collectEntryDemandsTerm activeSites onNonFree through perm r rest
    | _, _, .guard _ _ _ _ _ rest =>
        collectEntryDemandsTerm activeSites onNonFree through perm r rest
    | _, _, .choose _ _ _ _ _ t f _ rest =>
        collectEntryDemandsTerm activeSites onNonFree through perm r t ++
          collectEntryDemandsTerm activeSites onNonFree through perm r f ++
          collectEntryDemandsTerm activeSites onNonFree through perm r rest
    | _, _, .cases _ _ _ _ _ arms _ rest =>
        collectEntryDemandsArms activeSites onNonFree through perm r arms ++
          collectEntryDemandsTerm activeSites onNonFree through perm r rest
    | _, _, .loop _ _ _ _ _ _ body _ rest =>
        collectEntryDemandsTerm activeSites onNonFree through perm r body ++
          collectEntryDemandsTerm activeSites onNonFree through perm r rest
    | _, _, .block _ _ body _ rest =>
        collectEntryDemandsTerm activeSites onNonFree through perm r body ++
          collectEntryDemandsTerm activeSites onNonFree through perm r rest
    | _, _, .attempt _ _ _ _ body _ rest =>
        collectEntryDemandsTerm activeSites onNonFree through perm r body ++
          collectEntryDemandsTerm activeSites onNonFree through perm r rest

  /-- Variant arms helper for `collectEntryDemandsTerm`. -/
  def collectEntryDemandsArms {hs : Headers V} (activeSites : List Site)
      (onNonFree : {hdr : ProtocolHeader V} → Member hs.protocols hdr →
        List Key → FinPerm → Role → List (SharedDemand V hs.protocols))
      (through : List Key) (perm : FinPerm) (r : Role) :
      {Γ mid payloads : _} → Arms (roleDialect V hs r) Γ mid payloads →
      List (SharedDemand V hs.protocols)
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest =>
        collectEntryDemandsTerm activeSites onNonFree through perm r arm ++
          collectEntryDemandsArms activeSites onNonFree through perm r rest
end

/-- Lift a `SharedDemand` from `rest` to `hdr :: rest`. -/
def SharedDemand.tail {hdr : ProtocolHeader V} {protos : List (ProtocolHeader V)}
    (d : SharedDemand V protos) : SharedDemand V (hdr :: protos) :=
  ⟨d.hdr, .tail d.callee, d.perm, d.role⟩

/-- Collect root shared demands reachable from `(callee, through, perm, r)` structurally on `defs`,
walking `project r body` so unreachable branches never spawn dead procedures. -/
def collectEntryDemands (activeSites : List Site) :
    {hs : Headers V} → Defs V hs → {hdr : ProtocolHeader V} → Member hs.protocols hdr →
    List Key → FinPerm → Role → List (SharedDemand V hs.protocols)
  | _, .nil, _, m, _, _, _ => nomatch m
  | _, .fn (hs := hsRest) _ _ _ _ rest _, _, m, through, perm, r =>
      collectEntryDemands activeSites (hs := hsRest) rest m through perm r
  | _, .protocol (hs := hsRest) _ _ body _ rest, _, .head, through, perm, r =>
      let raw := collectEntryDemandsTerm activeSites
        (fun {_} m' th' p' r' => collectEntryDemands activeSites (hs := hsRest) rest m' th' p' r')
        through perm r (project r body)
      raw.map SharedDemand.tail
  | _, .protocol (hs := hsRest) _ _ _ _ rest, _, .tail m, through, perm, r =>
      (collectEntryDemands activeSites (hs := hsRest) rest m through perm r).map SharedDemand.tail

/-- Result of bottom-up shared procedure compilation over `protos`. -/
structure SharedPool (V : Vocabulary) (fullFns : List (FnHeader V))
    (protos : List (ProtocolHeader V)) (σ : List V.Ty) where
  sigs : List (ClosedProcSig V)
  procs : ClosedProcs V fullFns sigs
  lookup : {hdr : ProtocolHeader V} → Member protos hdr → FinPerm → (r : Role) →
    Option (Member sigs ⟨σ, held r hdr.ins, held r hdr.outs⟩)

/-- Partition demands for `hdr :: protos` into deduplicated keys for `.head` and remaining demands
for `.tail`. -/
def partitionDemands {hdr : ProtocolHeader V} {protos : List (ProtocolHeader V)} :
    List (SharedDemand V (hdr :: protos)) → List (FinPerm × Role) × List (SharedDemand V protos)
  | [] => ([], [])
  | ⟨hdrD, calleeD, permD, roleD⟩ :: ds =>
      let (here, later) := partitionDemands ds
      match calleeD with
      | .head => (insertUniqueKey (permD, roleD) here, later)
      | .tail m => (here, ⟨hdrD, m, permD, roleD⟩ :: later)

/-- Append shared entries for each `(perm, r') ∈ keys` of protocol `hdrP` on top of `restPool`,
compiling each body once against `unhandledSpecOp σ` and `restPool`. -/
def addSharedForProto {fullFns : List (FnHeader V)} {σ : List V.Ty} {hsRest : Headers V}
    (hdrP : ProtocolHeader V) (inputsP : Names hdrP.ins)
    (bodyP : Term (protocolDialect V hsRest) (Ctx.empty.extend inputsP) hdrP.outs)
    (rest : Defs V hsRest)
    (fnLift : ∀ {hdr}, Member hsRest.fns hdr → Member fullFns hdr)
    (restPool : SharedPool V fullFns hsRest.protocols σ) :
    List (FinPerm × Role) →
    (sigs : List (ClosedProcSig V)) ×
      (ClosedProcs V fullFns sigs) ×
      (∀ {sig}, Member restPool.sigs sig → Member sigs sig) ×
      (FinPerm → (r : Role) → Option (Member sigs ⟨σ, held r hdrP.ins, held r hdrP.outs⟩))
  | [] => ⟨restPool.sigs, restPool.procs, fun m => m, fun _ _ => none⟩
  | (perm, r') :: more =>
      let ⟨curSigs, curProcs, embed, prevLookup⟩ :=
        addSharedForProto hdrP inputsP bodyP rest fnLift restPool more
      let specApply : Option (Nat × Site × StackAgain V fullFns σ) →
          {hdr' : ProtocolHeader V} → Member hsRest.protocols hdr' →
          List Key → FinPerm → (r'' : Role) →
          ApplyTarget V fullFns curSigs σ (held r'' hdr'.ins) (held r'' hdr'.outs) :=
        fun rc {_} m' th' p' r'' =>
          match restPool.lookup m' p' r'' with
          | some mem => .shared (embed mem)
          | none =>
              let res := specializeProtocolInDefs (unhandledSpecOp σ) [] rest fnLift
                (fun m2 p2 r2 => (restPool.lookup m2 p2 r2).map embed) rc m' th' p' r''
              .inlined res.1 res.2
      let bodyC : ClosedTerm V fullFns curSigs σ (Ctx.empty.extend (heldNames r' inputsP)) (held r' hdrP.outs) :=
        @specializeTerm V fullFns curSigs σ hsRest (unhandledSpecOp σ) fnLift specApply
          none [] perm r' _ _ ((CtxRel.empty r').extend inputsP) _ (project r' bodyP)
      let newProcs : ClosedProcs V fullFns (⟨σ, held r' hdrP.ins, held r' hdrP.outs⟩ :: curSigs) :=
        .cons (heldNames r' inputsP) bodyC curProcs
      let newLookup : FinPerm → (r : Role) →
          Option (Member (⟨σ, held r' hdrP.ins, held r' hdrP.outs⟩ :: curSigs)
            ⟨σ, held r hdrP.ins, held r hdrP.outs⟩) :=
        fun p r =>
          if hEq : p = perm ∧ r = r' then
            some (hEq.2 ▸ .head)
          else
            (prevLookup p r).map .tail
      ⟨⟨σ, held r' hdrP.ins, held r' hdrP.outs⟩ :: curSigs, newProcs,
        fun m => .tail (embed m), newLookup⟩

/-- Bottom-up topological construction of `ClosedProcs` structurally along `defs : Defs V hs`.
Processes each protocol level once with deduplicated `(FinPerm, Role)` keys, compiling diamond
DAGs in linear size without `partial` or fuel. -/
def buildSharedProcs {fullFns : List (FnHeader V)} (σ : List V.Ty) :
    {hs : Headers V} → Defs V hs →
    (∀ {hdr}, Member hs.fns hdr → Member fullFns hdr) →
    List (SharedDemand V hs.protocols) →
    SharedPool V fullFns hs.protocols σ
  | _, .nil, _, _ => ⟨[], .nil, fun {_} m _ _ => nomatch m⟩
  | _, .fn (hs := hsRest) _ _ _ _ rest _, fnLift, demands =>
      buildSharedProcs σ (hs := hsRest) rest (fun f => fnLift (.tail f)) demands
  | _, .protocol (hs := hsRest) hdrP inputsP bodyP _ rest, fnLift, demands =>
      let (here, later) := partitionDemands demands
      let subDemands := here.flatMap fun (perm, r') => collectDirectAppliesTerm perm r' (project r' bodyP)
      let restPool := buildSharedProcs σ (hs := hsRest) rest fnLift (subDemands ++ later)
      let ⟨newSigs, newProcs, embed, headLookup⟩ :=
        addSharedForProto hdrP inputsP bodyP rest fnLift restPool here
      let fullLookup : {hdr : ProtocolHeader V} → Member (hdrP :: hsRest.protocols) hdr → FinPerm → (r : Role) →
          Option (Member newSigs ⟨σ, held r hdr.ins, held r hdr.outs⟩) :=
        fun {_} m p r =>
          match m with
          | .head => headLookup p r
          | .tail m' => (restPool.lookup m' p r).map embed
      ⟨newSigs, newProcs, fullLookup⟩

/-! ## Top-level `specialize` entry point -/

/-- Specialize a deployed scheme `d` for role `r` into a self-contained, handler-free,
DAG-preserving `ClosedRole`. -/
def specialize (d : Deployed V) (r : Role) :
    ClosedRole V d.admitted.program.headers.fns r d.entry.ins d.entry.outs
      (Stack.Takes (d.stack r)) (Stack.Gives (d.stack r)) :=
  let defs := d.admitted.program.defs
  let layers := d.stack r
  let σ := Stack.States layers
  let activeSites := stackActiveSites layers d.retry
  let rootDemands := collectEntryDemands activeSites defs d.callee [] FinPerm.identity r
  let pool := buildSharedProcs σ defs id rootDemands
  let specOp := (specializeStack defs layers).liftProcs emptyProcLift
  let retryCfg := d.retry.map fun (bound, site) => (bound, site, stackAgain layers)
  let res :=
    specializeProtocolInDefs specOp activeSites defs id pool.lookup retryCfg d.callee [] FinPerm.identity r
  { states := σ
    procSigs := pool.sigs
    procs := pool.procs
    inputs := res.1
    start := stackInit layers
    body := res.2
    finish := stackFinish layers }

end Specializer

end Zkc.Core
