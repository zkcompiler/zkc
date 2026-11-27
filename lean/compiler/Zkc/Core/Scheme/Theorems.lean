module

public import Zkc.Core.Scheme.Deploy
public import Zkc.Core.Scheme.LayerLemmas
public import Zkc.Core.Scheme.RoleLemmas
public import Zkc.Core.Statements
public import Zkc.Core.Run.Execute

@[expose] public section

/-!
Formal verification of all deployment theorems in `Zkc.Core.Statements` plus ideal-RO linkage
(`deployIdeal_link`), strictly within the core's two-axiom boundary (`propext`, `Quot.sound`):

- `canonicalFormat_formats` (`Statements.formats`)
- `deployedIdentity_identityReads` (`Statements.identityReads`)
- `deploy_keeps` (`Statements.deployKeeps`)
- `deploy_findsRoles` (`Statements.deployFindsRoles`)
- `deploy_matches` (`Statements.deployMatches`)
- `deploy_scoped` (`Statements.deployScoped`) & `deployIdeal_scoped`
- `deploy_fresh` (`Statements.deployFresh`) & `deployIdeal_fresh`
- `deploy_safe` (`Statements.deployedSafe`) & `deployIdeal_safe`
- `deploy_coverage` (`Statements.deployCoverage`) & `deployIdeal_coverage`
- `deploy_complete` (`Statements.complete`)
- `deployIdeal_link` (direct state-machine characterization of `Process.answerService` on
  `deployIdeal`'s verifier)
-/

namespace Zkc.Core

open LayerBuild

/-! ## Section 1: Generic lookup, cast, and stack-composition helpers -/

section Helpers

variable {V : Vocabulary}

/-- Eliminate simultaneous `ProtocolHeader` and `Role` equality transports on a layer stack. -/
private theorem cast_layer_stack_elim {hs : Headers V}
    {hdr₁ hdr₂ : ProtocolHeader V} (hHdr : hdr₁ = hdr₂)
    {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins))
    (P : ∀ (hdr : ProtocolHeader V) (r : Role), List (Layer V hs r hdr.ins) → Prop)
    (h : P hdr₂ r₂ layers) :
    P hdr₁ r₁ (hr ▸ hHdr ▸ layers) := by
  subst hHdr; subst hr; exact h

/-- Eliminate a `ProtocolHeader` equality transport on a layer stack. -/
private theorem cast_hdr_stack_elim {hs : Headers V}
    {hdr₁ hdr₂ : ProtocolHeader V} (hHdr : hdr₁ = hdr₂) {r : Role}
    (layers : List (Layer V hs r hdr₂.ins))
    (P : ∀ (hdr : ProtocolHeader V), List (Layer V hs r hdr.ins) → Prop)
    (h : P hdr₂ layers) :
    P hdr₁ (hHdr ▸ layers) := by
  subst hHdr; exact h

/-- `findSlotMember` returning `some x` witnesses a member `(slot, defKey) ∈ m.members`. -/
private theorem findSlotMember_some {α : Type} {m : ModuleRef} {slot : Key} {pick : Key → Option α}
    {x : α} (h : findSlotMember m slot pick = some x) :
    ∃ defKey, (slot, defKey) ∈ m.members ∧ pick defKey = some x := by
  unfold findSlotMember at h
  have hmem := List.exists_of_findSome?_eq_some h
  obtain ⟨⟨s, defKey⟩, hIn, hPick⟩ := hmem
  by_cases hs : s = slot
  · subst hs
    simp only [↓reduceIte] at hPick
    exact ⟨defKey, hIn, hPick⟩
  · simp only [hs, ↓reduceIte] at hPick
    cases hPick

private theorem findTypedFnRef_some {a : Admitted V} {defKey : Key} {ins outs : List V.Ty}
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
          dsimp only at h
          split at h
          · split at h
            · split at h
              · split at h
                · cases h; rfl
                · cases h
              · cases h
            · cases h
          · cases h

private theorem findSafeFnRef_some {a : Admitted V} {defKey : Key} {ins outs : List V.Ty}
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
          dsimp only at h
          split at h
          · split at h
            · split at h
              · cases h; rfl
              · cases h
            · cases h
          · cases h

private theorem findSuiteDerive_some {a : Admitted V} {suite : ModuleRef} {stateTy : V.Ty}
    {drawIns : List V.Ty} {τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]}
    (h : findSuiteDerive a suite stateTy drawIns τ = some ref) :
    ∃ defKey, (SuiteSlot.derive, defKey) ∈ suite.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

private theorem findLayoutWrite_some {a : Admitted V} {layout : ModuleRef} {unitTy τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]}
    (h : findLayoutWrite a layout unitTy τ = some ref) :
    ∃ defKey, (LayoutSlot.write, defKey) ∈ layout.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

private theorem findLayoutRead_some {a : Admitted V} {layout : ModuleRef} {unitTy τ : V.Ty}
    {ref : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
    (h : findLayoutRead a layout unitTy τ = some ref) :
    ∃ defKey, (LayoutSlot.read, defKey) ∈ layout.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findSafeFnRef_some hRef⟩

private theorem findLayoutEqual_some {a : Admitted V} {layout : ModuleRef} {τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns [τ, τ] [.bool]}
    (h : findLayoutEqual a layout τ = some ref) :
    ∃ defKey, (LayoutSlot.equal, defKey) ∈ layout.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

private theorem hlist_all_cast {T : Type} {F : T → Type} {P : ∀ t, F t → Prop}
    {as bs : List T} (h : as = bs) {xs : HList F as} (hx : xs.All P) :
    (cast (congrArg (HList F) h) xs).All P := by
  subst h; exact hx

private theorem hlist_append_nil {T : Type} {F : T → Type} {bs : List T} (ys : HList F bs) :
    HList.append .nil ys = ys := rfl

private theorem hlist_append_cons {T : Type} {F : T → Type} {a : T} {as bs : List T}
    (x : F a) (xs : HList F as) (ys : HList F bs) :
    HList.append (.cons x xs) ys = .cons x (HList.append xs ys) := rfl

private theorem hlist_all_append {T : Type} {F : T → Type} {P : ∀ t, F t → Prop} :
    ∀ {as bs : List T} {xs : HList F as} {ys : HList F bs},
      xs.All P → ys.All P → (xs.append ys).All P
  | [], _, .nil, _, _, hy => hy
  | _ :: _, _, .cons _ _, _, hx, hy => ⟨hx.1, hlist_all_append hx.2 hy⟩

private theorem hlist_split_all {T : Type} {F : T → Type} {P : ∀ t, F t → Prop} :
    ∀ (as : List T) {bs : List T} (vs : HList F (as ++ bs)),
      vs.All P → (HList.split as vs).1.All P ∧ (HList.split as vs).2.All P
  | [], _, _, hv => ⟨trivial, hv⟩
  | _ :: as, _, .cons _ rest, hv =>
      let ⟨h1, h2⟩ := hlist_split_all as rest hv.2
      ⟨⟨hv.1, h1⟩, h2⟩

private theorem allows_valid (M : Model V) {kind : GivenKind V} {ins : List V.Ty}
    {payload : HList M.Val ins} {τ : V.Ty} {v : M.Val τ}
    (h : Allows M kind ins payload τ v) : M.Valid τ v := by
  cases kind with
  | coin _ => exact h.1
  | request _ => exact h

private theorem hideAll_valid (M : Model V) (r : Role) :
    ∀ {ins : List (LTy V)} (vs : HList (LVal M) ins),
      vs.All (fun a v => M.Valid a.ty v) → (hideAll M r vs).All (RV.Valid M r)
  | [], .nil, _ => trivial
  | a :: rest, .cons v vs, hv => by
      refine ⟨fun hIn => ?_, hideAll_valid M r vs hv.2⟩
      show M.Valid a.ty (cast _ (hide M r a v))
      have hrv : cast (by simp [RV, hIn]) (hide M r a v) = v := reveal_hide M hIn v
      rw [hrv]
      exact hv.1

private theorem valid_seq_append (M : Model V) {unitTy : V.Ty}
    {xs ys : List (M.Val unitTy)}
    (hx : M.Valid (.seq unitTy none) xs) (hy : M.Valid (.seq unitTy none) ys) :
    M.Valid (.seq unitTy none) (xs ++ ys) := by
  refine ⟨fun u hu => ?_, (fun _ h => nomatch h)⟩
  rcases List.mem_append.mp hu with h | h
  · exact hx.1 u h
  · exact hy.1 u h

private theorem tys_getAt_valid (M : Model V) :
    ∀ (ts : Tys V.TypeKey) {τ : V.Ty} (pos : Member ts.toList τ) (st : ts.Val M.toCarriers),
      Tys.Valid M.toCarriers ts st → M.Valid τ (Tys.getAt M ts pos st)
  | .nil, _, pos, _, _ => nomatch pos
  | .cons _ _, _, .head, (_, _), hv => hv.1
  | .cons _ rest, _, .tail p, (_, rs), hv => tys_getAt_valid M rest p rs hv.2

private theorem tys_toHList_valid (M : Model V) :
    ∀ (ts : Tys V.TypeKey) (st : ts.Val M.toCarriers),
      Tys.Valid M.toCarriers ts st → (Tys.toHList M ts st).All M.Valid
  | .nil, (), _ => trivial
  | .cons _ rest, (_, rs), hv => ⟨hv.1, tys_toHList_valid M rest rs hv.2⟩

/-- Standalone version of `Deployed.run` parameterized directly by `(hdr, callee, retry, layers)`. -/
private def runStack (a : Admitted V) (M : Model V) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (retry : Option (Nat × Site))
    (r : Role) (layers : List (Layer V a.program.headers r hdr.ins))
    (ins : HList (RV M r) hdr.ins) (taken : HList M.Val (Stack.Takes layers)) :
    Process (RSig M) Stop (HList (RV M r) hdr.outs × HList M.Val (Stack.Gives layers)) :=
  (Stack.start M (Defs.fnTable M a.program.defs) layers ins taken).bind fun first =>
    (((Stack.handler M (Defs.fnTable M a.program.defs)
        (Defs.rTable M a.program.defs) layers).run (retryOf M retry)
        (roleMeaning M a.program callee r [] ins) first).mapHalt Prod.fst).bind fun out =>
      (Stack.finish M (Defs.fnTable M a.program.defs) layers out.2).map
        fun gives => (out.1, gives)

private theorem deployed_run_eq_runStack (d : Deployed V) (M : Model V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    d.run M r ins taken = runStack d.admitted M d.callee d.retry r (d.stack r) ins taken :=
  rfl

private theorem stack_handler_again_cons (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    {r : Role} {ins : List (LTy V)}
    (l : Layer V hs r ins) (rest : List (Layer V hs r ins)) (i : Nat)
    (e : M.Val l.state) (es : HList M.Val (Stack.States rest))
    (t : M.Val l.state) (ts : HList M.Val (Stack.States rest)) :
    (Stack.handler M fnTable rTable (l :: rest)).again i (.cons e es) (.cons t ts) =
      (((Layer.handler M fnTable rTable l).over (Stack.handler M fnTable rTable rest)).again
        i (e, es) (t, ts)).map fun next => .cons next.1 next.2 := rfl

private theorem stack_handler_validSafe_all (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    {r : Role} {ins : List (LTy V)}
    (permitted : ∀ op, (RSig M).Reply op → Prop) (opOk : ROp M → Prop) :
    ∀ (layers : List (Layer V hs r ins)),
      (∀ l ∈ layers, (Layer.handler M fnTable rTable l).SafeWith M permitted (M.Valid l.state) opOk opOk) →
      (Stack.handler M fnTable rTable layers).SafeWith M permitted (HList.All M.Valid) opOk opOk
  | [], _ =>
      { clauseOk := fun _ s ho _ => by cases s; exact ⟨ho, fun _ hr => ⟨hr, trivial⟩⟩
        againOk := fun _ _ _ _ _ => trivial }
  | l :: rest, h => by
      have hl := h l List.mem_cons_self
      have hrest := stack_handler_validSafe_all M fnTable rTable permitted opOk rest
        (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
      have hboth := Handler.SafeWith.over M hl hrest
      refine ⟨?_, ?_⟩
      · intro op st ho hst
        cases st with
        | cons mine below =>
            change (((((Layer.handler M fnTable rTable l).over
              (Stack.handler M fnTable rTable rest)).clause op (mine, below)).mapHalt
                fun stop => (stop.1, HList.cons stop.2.1 stop.2.2)).map
                fun out => (out.1, HList.cons out.2.1 out.2.2)).SafeWith M permitted opOk
                (fun out => permitted op out.1 ∧ HList.All M.Valid out.2)
                (fun stop => stop.1 ≠ .undefined ∧ HList.All M.Valid stop.2)
            rw [Process.safeWith_map, Process.safeWith_mapHalt]
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun out hout => ⟨hout.1, hout.2.1, hout.2.2⟩)
              (fun stop hstop => ⟨hstop.1, hstop.2.1, hstop.2.2⟩)
              (hboth.clauseOk op (mine, below) ho ⟨hst.1, hst.2⟩)
      · intro i entry stop hentry hstop
        cases entry with
        | cons e es =>
            cases stop with
            | cons t ts =>
                have ha := hboth.againOk i (e, es) (t, ts) ⟨hentry.1, hentry.2⟩ ⟨hstop.1, hstop.2⟩
                rw [stack_handler_again_cons]
                cases hres : ((Layer.handler M fnTable rTable l).over
                    (Stack.handler M fnTable rTable rest)).again i (e, es) (t, ts) with
                | error why =>
                    rw [hres] at ha
                    exact ha
                | ok nxt =>
                    rw [hres] at ha
                    exact ⟨ha.1, ha.2⟩

private theorem stack_start_validSafe (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) {r : Role} {ins : List (LTy V)}
    (permitted : ∀ op, (RSig M).Reply op → Prop) (opOk : ROp M → Prop) :
    ∀ (layers : List (Layer V hs r ins)) (inputs : HList (RV M r) ins)
      (taken : HList M.Val (Stack.Takes layers)),
      inputs.All (RV.Valid M r) → taken.All M.Valid →
      (∀ l ∈ layers, ∀ (t : HList M.Val l.takes), t.All M.Valid →
        (l.start.denote (localSem M hs.fns fnTable) []
          (Env.positional (t.append (heldValues M r inputs)))).Every
            (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined)) →
      (Stack.start M fnTable layers inputs taken).SafeWith M permitted opOk
        (HList.All M.Valid) (· ≠ .undefined)
  | [], _, _, _, _, _ => trivial
  | l :: rest, inputs, taken, hin, htak, hstart => by
      have ⟨ht1, ht2⟩ := hlist_split_all l.takes taken htak
      change ((liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
          (Env.positional ((HList.split l.takes taken).1.append (heldValues M r inputs))))).bind
        fun first => (Stack.start M fnTable rest inputs (HList.split l.takes taken).2).map
          fun others => HList.cons first.single others).SafeWith M permitted opOk
        (fun st : HList M.Val (l.state :: Stack.States rest) => st.All M.Valid) (· ≠ .undefined)
      rw [Process.safeWith_bind]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun first hfirst => ?_) (fun _ h => h)
        (Process.safeWith_liftLocal M id _ (hstart l List.mem_cons_self _ ht1))
      rw [Process.safeWith_map]
      have hfirstV : M.Valid l.state first.single := by
        cases first with | cons v vn => cases vn; exact hfirst.1
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun others hothers => ⟨hfirstV, hothers⟩) (fun _ h => h)
        (stack_start_validSafe M fnTable permitted opOk rest inputs (HList.split l.takes taken).2
          hin ht2 (fun l' hl' => hstart l' (List.mem_cons_of_mem _ hl')))

private theorem stack_finish_validSafe (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) {r : Role} {ins : List (LTy V)}
    (permitted : ∀ op, (RSig M).Reply op → Prop) (opOk : ROp M → Prop) :
    ∀ (layers : List (Layer V hs r ins)) (states : HList M.Val (Stack.States layers)),
      states.All M.Valid →
      (∀ l ∈ layers, ∀ (s : M.Val l.state), M.Valid l.state s →
        (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil))).Every
          (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined)) →
      (Stack.finish M fnTable layers states).SafeWith M permitted opOk
        (HList.All M.Valid) (· ≠ .undefined)
  | [], .nil, _, _ => trivial
  | l :: rest, .cons s states, hst, hfin => by
      change ((liftLocal id (l.finish.denote (localSem M hs.fns fnTable) []
          (Env.positional (.cons s .nil)))).bind fun mine =>
        (Stack.finish M fnTable rest states).map fun others => HList.append mine others).SafeWith
        M permitted opOk (fun g : HList M.Val (l.gives ++ Stack.Gives rest) => g.All M.Valid) (· ≠ .undefined)
      rw [Process.safeWith_bind]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun mine hmine => ?_) (fun _ h => h)
        (Process.safeWith_liftLocal M id _ (hfin l List.mem_cons_self s hst.1))
      rw [Process.safeWith_map]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun others hothers => hlist_all_append hmine hothers) (fun _ h => h)
        (stack_finish_validSafe M fnTable permitted opOk rest states hst.2
          (fun l' hl' => hfin l' (List.mem_cons_of_mem _ hl')))

private theorem local_every_true {A : Type} :
    ∀ (p : Local A), p.Every (fun _ _ => True) (fun _ => True) (fun _ => True)
  | .done _ => trivial
  | .halt _ => trivial
  | .call op _ => nomatch op

/-- `Stack.start` never emits any role effect (it is built purely from `liftLocal`). -/
private theorem stack_start_noEffects (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) {r : Role} {ins : List (LTy V)}
    (opOk : ROp M → Prop) :
    ∀ (layers : List (Layer V hs r ins)) (inputs : HList (RV M r) ins)
      (taken : HList M.Val (Stack.Takes layers)),
      (Stack.start M fnTable layers inputs taken).SafeWith M (fun _ _ => True) opOk
        (fun _ => True) (fun _ => True)
  | [], _, _ => trivial
  | l :: rest, inputs, taken => by
      change ((liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
          (Env.positional ((HList.split l.takes taken).1.append (heldValues M r inputs))))).bind
        fun first => (Stack.start M fnTable rest inputs (HList.split l.takes taken).2).map
          fun others => HList.cons first.single others).SafeWith M (fun _ _ => True) opOk
        (fun _ : HList M.Val (l.state :: Stack.States rest) => True) (fun _ => True)
      rw [Process.safeWith_bind]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun _ _ => ?_) (fun _ _ => trivial)
        (Process.safeWith_liftLocal M (onDone := fun _ => True) (onHalt := fun _ => True) id _
          (local_every_true _))
      rw [Process.safeWith_map]
      exact stack_start_noEffects M fnTable opOk rest inputs (HList.split l.takes taken).2

/-- `Stack.finish` never emits any role effect (it is built purely from `liftLocal`). -/
private theorem stack_finish_noEffects (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) {r : Role} {ins : List (LTy V)}
    (opOk : ROp M → Prop) :
    ∀ (layers : List (Layer V hs r ins)) (states : HList M.Val (Stack.States layers)),
      (Stack.finish M fnTable layers states).SafeWith M (fun _ _ => True) opOk
        (fun _ => True) (fun _ => True)
  | [], .nil => trivial
  | l :: rest, .cons s states => by
      change ((liftLocal id (l.finish.denote (localSem M hs.fns fnTable) []
          (Env.positional (.cons s .nil)))).bind fun mine =>
        (Stack.finish M fnTable rest states).map fun others => HList.append mine others).SafeWith
        M (fun _ _ => True) opOk (fun _ : HList M.Val (l.gives ++ Stack.Gives rest) => True) (fun _ => True)
      rw [Process.safeWith_bind]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun _ _ => ?_) (fun _ _ => trivial)
        (Process.safeWith_liftLocal M (onDone := fun _ => True) (onHalt := fun _ => True) id _
          (local_every_true _))
      rw [Process.safeWith_map]
      exact stack_finish_noEffects M fnTable opOk rest states

private theorem layer_again_restore_valid (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    {r : Role} {ins : List (LTy V)} (l : Layer V hs r ins)
    (hAgain : l.again = restoreAgain l.state)
    (i : Nat) (entry stop : M.Val l.state) (hentry : M.Valid l.state entry) :
    match (Layer.handler M fnTable rTable l).again i entry stop with
    | .ok next => M.Valid l.state next
    | .error why => why ≠ .undefined := by
  dsimp only [Layer.handler]
  rw [hAgain, restoreAgain_denote]
  exact hentry

private theorem layer_again_attempt_valid (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    {r : Role} {ins : List (LTy V)} (l : Layer V hs r ins)
    (hState : l.state = .nat) (hAgain : l.again = hState.symm ▸ attemptNumAgain)
    (i : Nat) (entry stop : M.Val l.state) :
    match (Layer.handler M fnTable rTable l).again i entry stop with
    | .ok next => M.Valid l.state next
    | .error why => why ≠ .undefined := by
  cases l with
  | mk line state takes gives clauses again start finish =>
      dsimp only at hState hAgain
      subst hState
      dsimp only at hAgain
      subst hAgain
      dsimp only [Layer.handler]
      rw [attemptNumAgain_denote]
      trivial

end Helpers

/-! ## Section 2: `formats`, `identityReads`, `deployKeeps`, `deployFindsRoles`, `deployMatches`, `deployScoped`, `deployFresh` -/

section StructuralTheorems

variable {V : Vocabulary}

/-- `canonicalFormat` satisfies `Statements.formats`. -/
theorem canonicalFormat_formats (c : Functions V)
    (hfmt : c.format = fun M codecs τ => canonicalFormat M codecs τ) :
    Statements.formats c := by
  intro M codecs τ
  rw [hfmt]
  exact canonicalFormat_lawful M codecs τ

/-- `deployedIdentity` satisfies `Statements.identityReads`. -/
theorem deployedIdentity_identityReads (enc : VocabEncoder V) (c : Functions V)
    (hid : c.identity = deployedIdentity enc) :
    Statements.identityReads c := by
  intro d d' hdecl hdefs
  rw [hid]
  exact deployedIdentity_reads enc d d' hdecl hdefs

/-- `deploy` preserves `admitted`, `declaration`, and `entry.key`. -/
theorem deploy_keeps (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) :
    d.admitted = a ∧ d.declaration = declaration ∧ d.entry.key = declaration.entry := by
  unfold deploy at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    split at h
    · cases h
    · cases hCon : declaration.construction with
      | interactive =>
          rw [hCon] at h
          cases h
          exact ⟨rfl, rfl, Deployed.entry_key _⟩
      | authored =>
          rw [hCon] at h
          dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h
              dsimp only at h
              split at h
              · cases h
              · cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples declaration.key
                    (foundPair.1.shape.events [] id) with
                | error _ => rw [hAuth] at h; cases h
                | ok sClauses =>
                    rw [hAuth] at h
                    dsimp only [bind, Except.bind] at h
                    cases hLayOpt : declaration.layout with
                    | none => rw [hLayOpt] at h; cases h
                    | some layout =>
                        rw [hLayOpt] at h
                        dsimp only at h
                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                            declaration.key (foundPair.1.shape.events [] id) with
                        | error _ => rw [hLay] at h; cases h
                        | ok lays =>
                            rw [hLay] at h
                            cases h
                            exact ⟨rfl, rfl, Deployed.entry_key _⟩
      | derived suite sessionTag =>
          rw [hCon] at h
          dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h
              dsimp only at h
              split at h
              · cases h
              · cases hLayOpt : declaration.layout with
                | none => rw [hLayOpt] at h; cases h
                | some layout =>
                    rw [hLayOpt] at h
                    dsimp only at h
                    cases hStart : findSuiteStart a suite with
                    | none => rw [hStart] at h; cases h
                    | some stPair =>
                        rw [hStart] at h
                        dsimp only at h
                        cases hAbs : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAbs] at h; cases h
                        | some absPair =>
                            rw [hAbs] at h
                            dsimp only at h
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at h; cases h
                            | ok sess =>
                                rw [hSess] at h
                                dsimp only [bind, Except.bind] at h
                                cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1 pv.2
                                    (.inl rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSP] at h; cases h
                                | ok stmtP =>
                                    rw [hSP] at h
                                    dsimp only [bind, Except.bind] at h
                                    cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                        (.inr rfl) foundPair.1.ins declaration.key with
                                    | error _ => rw [hSV] at h; cases h
                                    | ok stmtV =>
                                        rw [hSV] at h
                                        dsimp only [bind, Except.bind] at h
                                        cases hCC : buildConstructionClauses a suite stPair.1 absPair.1
                                            absPair.2 pv.1 pv.2 declaration.samples declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hCC] at h; cases h
                                        | ok cc =>
                                            rw [hCC] at h
                                            dsimp only [bind, Except.bind] at h
                                            cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                                declaration.key (foundPair.1.shape.events [] id) with
                                            | error _ => rw [hLay] at h; cases h
                                            | ok lays =>
                                                rw [hLay] at h
                                                cases h
                                                exact ⟨rfl, rfl, Deployed.entry_key _⟩

theorem statements_deployKeeps (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployKeeps c := by
  intro a decl d h; rw [hdep] at h; exact deploy_keeps enc a decl d h

/-- Every non-interactive deployment resolves `(prover, verifier)`. -/
theorem deploy_findsRoles (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d)
    (hNonInt : declaration.interactive = false) :
    ∃ prover verifier, d.roles = some (prover, verifier) := by
  unfold deploy at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    split at h
    · cases h
    · cases hCon : declaration.construction with
      | interactive =>
          simp [Declaration.interactive, hCon] at hNonInt
      | authored =>
          rw [hCon] at h
          dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h
              dsimp only at h
              split at h
              · cases h
              · cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples declaration.key
                    (foundPair.1.shape.events [] id) with
                | error _ => rw [hAuth] at h; cases h
                | ok sClauses =>
                    rw [hAuth] at h
                    dsimp only [bind, Except.bind] at h
                    cases hLayOpt : declaration.layout with
                    | none => rw [hLayOpt] at h; cases h
                    | some layout =>
                        rw [hLayOpt] at h
                        dsimp only at h
                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                            declaration.key (foundPair.1.shape.events [] id) with
                        | error _ => rw [hLay] at h; cases h
                        | ok lays =>
                            rw [hLay] at h
                            cases h
                            refine ⟨pv.1, pv.2, ?_⟩
                            unfold Deployed.roles Deployed.entry
                            simpa [hFound] using hPV
      | derived suite sessionTag =>
          rw [hCon] at h
          dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h
              dsimp only at h
              split at h
              · cases h
              · cases hLayOpt : declaration.layout with
                | none => rw [hLayOpt] at h; cases h
                | some layout =>
                    rw [hLayOpt] at h
                    dsimp only at h
                    cases hStart : findSuiteStart a suite with
                    | none => rw [hStart] at h; cases h
                    | some stPair =>
                        rw [hStart] at h
                        dsimp only at h
                        cases hAbs : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAbs] at h; cases h
                        | some absPair =>
                            rw [hAbs] at h
                            dsimp only at h
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at h; cases h
                            | ok sess =>
                                rw [hSess] at h
                                dsimp only [bind, Except.bind] at h
                                cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1 pv.2
                                    (.inl rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSP] at h; cases h
                                | ok stmtP =>
                                    rw [hSP] at h
                                    dsimp only [bind, Except.bind] at h
                                    cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                        (.inr rfl) foundPair.1.ins declaration.key with
                                    | error _ => rw [hSV] at h; cases h
                                    | ok stmtV =>
                                        rw [hSV] at h
                                        dsimp only [bind, Except.bind] at h
                                        cases hCC : buildConstructionClauses a suite stPair.1 absPair.1
                                            absPair.2 pv.1 pv.2 declaration.samples declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hCC] at h; cases h
                                        | ok cc =>
                                            rw [hCC] at h
                                            dsimp only [bind, Except.bind] at h
                                            cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                                declaration.key (foundPair.1.shape.events [] id) with
                                            | error _ => rw [hLay] at h; cases h
                                            | ok lays =>
                                                rw [hLay] at h
                                                cases h
                                                refine ⟨pv.1, pv.2, ?_⟩
                                                unfold Deployed.roles Deployed.entry
                                                simpa [hFound] using hPV

theorem statements_deployFindsRoles (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployFindsRoles c := by
  intro a decl d h hni; rw [hdep] at h; exact deploy_findsRoles enc a decl d h hni

/-- Every layout layer pair produced by `buildLayoutLayers` takes `[]` on prover and matches
`layP.gives = layV.takes = [.seq unitTy none]`. -/
private theorem buildLayoutLayers_io {a : Admitted V} {entry : ProtocolHeader V} {layout : Layout}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins}
    (h : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    ∃ unitTy, layP.takes = [] ∧ layP.gives = [.seq unitTy none] ∧
      layV.takes = [.seq unitTy none] ∧ layV.gives = [] := by
  unfold buildLayoutLayers at h
  cases hUnit : findLayoutUnit a layout.module with
  | none => rw [hUnit] at h; cases h
  | some uPair =>
      rw [hUnit] at h
      dsimp only at h
      split at h
      · cases hStr : buildStreamingLayoutClauses a layout uPair.1 uPair.2.down prover verifier
            declKey events with
        | error _ => rw [hStr] at h; cases h
        | ok cs =>
            rw [hStr] at h
            cases h
            exact ⟨uPair.1, rfl, rfl, rfl, rfl⟩
      · unfold buildCompactLayoutLayers at h
        cases hCW : collectCompactWire a layout uPair.1 prover verifier declKey events 0 events with
        | error _ => rw [hCW] at h; cases h
        | ok cw =>
            rw [hCW] at h
            dsimp only [bind, Except.bind] at h
            split at h
            · cases hVC : buildCompactVClauses a layout uPair.1 prover verifier declKey events _ cw.1
                  _ 0 events with
              | error _ => rw [hVC] at h; cases h
              | ok vcs =>
                  rw [hVC] at h
                  cases h
                  exact ⟨uPair.1, rfl, rfl, rfl, rfl⟩
            · cases h

private theorem stack_takes_cast {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins)) :
    Stack.Takes (hr ▸ hHdr ▸ layers) = Stack.Takes layers :=
  cast_layer_stack_elim hHdr hr layers (fun _ _ ls => Stack.Takes ls = Stack.Takes layers) rfl

private theorem stack_takes_cast_hdr {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r : Role}
    (layers : List (Layer V hs r hdr₂.ins)) :
    Stack.Takes (hHdr ▸ layers) = Stack.Takes layers :=
  cast_layer_stack_elim hHdr rfl layers (fun _ _ ls => Stack.Takes ls = Stack.Takes layers) rfl

private theorem stack_gives_cast_hdr {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r : Role}
    (layers : List (Layer V hs r hdr₂.ins)) :
    Stack.Gives (hHdr ▸ layers) = Stack.Gives layers :=
  cast_layer_stack_elim hHdr rfl layers (fun _ _ ls => Stack.Gives ls = Stack.Gives layers) rfl

private theorem stack_gives_cast {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins)) :
    Stack.Gives (hr ▸ hHdr ▸ layers) = Stack.Gives layers :=
  cast_layer_stack_elim hHdr hr layers (fun _ _ ls => Stack.Gives ls = Stack.Gives layers) rfl

/-- Prover's stack takes nothing from outside and its output types equal the verifier's input types. -/
theorem deploy_matches (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d)
    (prover verifier : Role) (hRoles : d.roles = some (prover, verifier)) :
    Stack.Takes (d.stack prover) = [] ∧
      Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier) := by
  unfold deploy at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    split at h
    · cases h
    · cases hCon : declaration.construction with
      | interactive =>
          rw [hCon] at h
          cases h
          exact ⟨rfl, rfl⟩
      | authored =>
          rw [hCon] at h
          dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h
              dsimp only at h
              split at h
              · cases h
              · rename_i hNe
                cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples declaration.key
                    (foundPair.1.shape.events [] id) with
                | error _ => rw [hAuth] at h; cases h
                | ok sClauses =>
                    rw [hAuth] at h
                    dsimp only [bind, Except.bind] at h
                    cases hLayOpt : declaration.layout with
                    | none => rw [hLayOpt] at h; cases h
                    | some layout =>
                        rw [hLayOpt] at h
                        dsimp only at h
                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                            declaration.key (foundPair.1.shape.events [] id) with
                        | error _ => rw [hLay] at h; cases h
                        | ok lays =>
                            rw [hLay] at h
                            cases h
                            have hRolesEq : proverAndVerifier foundPair.1 declaration = some (prover, verifier) := by
                              simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                            rw [hPV] at hRolesEq
                            cases hRolesEq
                            obtain ⟨unitTy, hPt, hPg, hVt, _⟩ := buildLayoutLayers_io hLay
                            have hNeSym : verifier ≠ prover := Ne.symm hNe
                            dsimp only
                            rw [dite_eq_left rfl, dite_eq_right hNeSym, dite_eq_left rfl]
                            rw [stack_takes_cast_hdr (by simp [hFound]),
                              stack_gives_cast_hdr (by simp [hFound]),
                              stack_takes_cast_hdr (by simp [hFound])]
                            cases declaration.samples <;>
                              simp [Stack.Takes, Stack.Gives, hPt, hPg, hVt]
      | derived suite sessionTag =>
          rw [hCon] at h
          dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h
              dsimp only at h
              split at h
              · cases h
              · rename_i hNe
                cases hLayOpt : declaration.layout with
                | none => rw [hLayOpt] at h; cases h
                | some layout =>
                    rw [hLayOpt] at h
                    dsimp only at h
                    cases hStart : findSuiteStart a suite with
                    | none => rw [hStart] at h; cases h
                    | some stPair =>
                        rw [hStart] at h
                        dsimp only at h
                        cases hAbs : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAbs] at h; cases h
                        | some absPair =>
                            rw [hAbs] at h
                            dsimp only at h
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at h; cases h
                            | ok sess =>
                                rw [hSess] at h
                                dsimp only [bind, Except.bind] at h
                                cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1 pv.2
                                    (.inl rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSP] at h; cases h
                                | ok stmtP =>
                                    rw [hSP] at h
                                    dsimp only [bind, Except.bind] at h
                                    cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                        (.inr rfl) foundPair.1.ins declaration.key with
                                    | error _ => rw [hSV] at h; cases h
                                    | ok stmtV =>
                                        rw [hSV] at h
                                        dsimp only [bind, Except.bind] at h
                                        cases hCC : buildConstructionClauses a suite stPair.1 absPair.1
                                            absPair.2 pv.1 pv.2 declaration.samples declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hCC] at h; cases h
                                        | ok cc =>
                                            rw [hCC] at h
                                            dsimp only [bind, Except.bind] at h
                                            cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                                declaration.key (foundPair.1.shape.events [] id) with
                                            | error _ => rw [hLay] at h; cases h
                                            | ok lays =>
                                                rw [hLay] at h
                                                cases h
                                                have hRolesEq : proverAndVerifier foundPair.1 declaration =
                                                    some (prover, verifier) := by
                                                  simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                                                rw [hPV] at hRolesEq
                                                cases hRolesEq
                                                obtain ⟨unitTy, hPt, hPg, hVt, _⟩ := buildLayoutLayers_io hLay
                                                have hNeSym : verifier ≠ prover := Ne.symm hNe
                                                dsimp only
                                                rw [dite_eq_left rfl, dite_eq_right hNeSym, dite_eq_left rfl]
                                                rw [stack_takes_cast_hdr (by simp [hFound]),
                                                  stack_gives_cast_hdr (by simp [hFound]),
                                                  stack_takes_cast_hdr (by simp [hFound])]
                                                cases declaration.samples <;>
                                                  simp [Stack.Takes, Stack.Gives, hPt, hPg, hVt]

theorem statements_deployMatches (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployMatches c := by
  intro a decl d h p v hr; rw [hdep] at h; exact deploy_matches enc a decl d h p v hr

/-- Every accepted deployment satisfies `Deployed.Scoped`. -/
theorem deploy_scoped (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.Scoped := by
  have hKeep := deploy_keeps enc a declaration d h
  unfold deploy at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    split at h
    · cases h
    · rename_i hScope
      have hSc : checkScope foundPair.1 declaration = true := by
        cases hc : checkScope foundPair.1 declaration
        · simp [hc] at hScope
        · rfl
      have hSound := checkScope_sound foundPair.1 declaration hSc
      have hEntry : d.entry = foundPair.1 := by
        cases d with
        | mk adm decl fnd stk =>
            dsimp only [Deployed.entry] at hKeep ⊢
            obtain ⟨rfl, rfl, _⟩ := hKeep
            simp [hFound]
      unfold Deployed.Scoped
      rw [hKeep.2.1, hEntry]
      exact hSound

theorem statements_deployScoped (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployScoped c := by
  intro a decl d h; rw [hdep] at h; exact deploy_scoped enc a decl d h

/-- Every accepted ideal-RO deployment satisfies `Deployed.Scoped`. -/
theorem deployIdeal_scoped (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.Scoped := by
  unfold deployIdeal at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    split at h
    · cases h
    · rename_i hScope
      have hSc : checkScope foundPair.1 declaration = true := by
        cases hc : checkScope foundPair.1 declaration
        · simp [hc] at hScope
        · rfl
      have hSound := checkScope_sound foundPair.1 declaration hSc
      cases hCon : declaration.construction with
      | interactive => rw [hCon] at h; cases h
      | authored => rw [hCon] at h; cases h
      | derived suite sessionTag =>
          rw [hCon] at h; dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h; dsimp only at h
              split at h
              · cases h
              · cases hLO : declaration.layout with
                | none => rw [hLO] at h; cases h
                | some layout =>
                    rw [hLO] at h; dsimp only at h
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at h; cases h
                    | some stPair =>
                        rw [hSt] at h; dsimp only at h
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at h; cases h
                        | some absPair =>
                            rw [hAb] at h; dsimp only at h
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at h; cases h
                            | ok sess =>
                                rw [hSess] at h; dsimp only [bind, Except.bind] at h
                                cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                    (.inr rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSV] at h; cases h
                                | ok stmtV =>
                                    rw [hSV] at h; dsimp only [bind, Except.bind] at h
                                    cases hIV : buildIdealVerifierClauses a suite stPair.1 absPair.1
                                        absPair.2 serviceKey pv.1 pv.2 declaration.key
                                        (foundPair.1.shape.events [] id) with
                                    | error _ => rw [hIV] at h; cases h
                                    | ok idealVClauses =>
                                        rw [hIV] at h; dsimp only [bind, Except.bind] at h
                                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                            declaration.key (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hLay] at h; cases h
                                        | ok lays =>
                                            rw [hLay] at h; cases h
                                            unfold Deployed.Scoped Deployed.entry
                                            simpa [hFound] using hSound

/-! ### Freshness (`Deployed.Fresh`) -/

/-- A single clause satisfies the freshness condition relative to `events`. -/
private def ClauseFresh {hs : Headers V} {r : Role} {state : V.Ty}
    (events : List (ShapeEvent V)) (c : Clause V hs r state) : Prop :=
  ∀ key, key ∈ Term.eventKeys (fun o => RoleOp.isEvent o) c.code → key ≠ c.site.site.key →
    key ∉ events.map (·.site.key)

private theorem buildConstructionClauses_go_fresh {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absorbRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      (∀ c ∈ cP, ClauseFresh events c) ∧
      (∀ c ∈ cV, ClauseFresh events c) ∧
      (∀ c ∈ cS, ClauseFresh events c)
  | _, [], _, _, _, h => by
      cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, cP, cV, cS, h => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absorbRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h
          dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV, ihS⟩ := buildConstructionClauses_go_fresh (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    refine ⟨?_, ?_, ihS⟩
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hmem
                      · intro key hk hne
                        rw [proverAbsorbClause_eventKeys] at hk
                        simp only [List.mem_singleton] at hk
                        exact absurd hk hne
                      · exact ihP c hmem
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hmem
                      · intro key hk hne
                        rw [verifierAbsorbClause_eventKeys] at hk
                        simp only [List.mem_singleton] at hk
                        exact absurd hk hne
                      · exact ihV c hmem
              · split at h
                · cases h; exact ⟨ihP, ihV, ihS⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                refine ⟨?_, ?_, ihS⟩
                                · intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hmem
                                  · intro key hk _
                                    rw [deriveClause_eventKeys] at hk
                                    simp only [List.mem_singleton] at hk
                                    subst hk
                                    exact drawToldKey_fresh events idx
                                  · exact ihP c hmem
                                · intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hmem
                                  · intro key hk _
                                    rw [deriveClause_eventKeys] at hk
                                    simp only [List.mem_singleton] at hk
                                    subst hk
                                    exact drawToldKey_fresh events idx
                                  · exact ihV c hmem
                              · cases h
                        · cases h
                  · split at h
                    · split at h
                      · cases samplesKey with
                        | none => cases h; exact ⟨ihP, ihV, ihS⟩
                        | some sKey =>
                            dsimp only at h
                            cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                            | none => rw [hS] at h; cases h
                            | some sRef =>
                                rw [hS] at h; cases h
                                refine ⟨ihP, ihV, fun c hc => ?_⟩
                                rcases List.mem_cons.mp hc with rfl | hmem
                                · intro key hk _; rw [proverSampleClause_eventKeys] at hk; cases hk
                                · exact ihS c hmem
                      · cases h; exact ⟨ihP, ihV, ihS⟩
                    · cases h
              | request svc =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV, ihS⟩
                  · cases h

private theorem buildIdealVerifierClauses_go_fresh {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildIdealVerifierClauses.go a suite stateTy unitTy absorbRef serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ c ∈ cV, ClauseFresh events c
  | _, [], _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, cV, h => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite stateTy unitTy absorbRef serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihV := buildIdealVerifierClauses_go_fresh (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    intro c hc
                    rcases List.mem_cons.mp hc with rfl | hmem
                    · intro key hk hne
                      rw [verifierAbsorbClause_eventKeys] at hk
                      simp only [List.mem_singleton] at hk
                      exact absurd hk hne
                    · exact ihV c hmem
              · split at h
                · cases h; exact ihV
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hIns : sig.ins with
                          | nil =>
                              rw [hIns] at h; dsimp only at h
                              cases hEnc : findSuiteEncode a suite unitTy e.τ with
                              | none => rw [hEnc] at h; cases h
                              | some encRef =>
                                  rw [hEnc] at h; cases h
                                  intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hmem
                                  · intro key hk _
                                    rw [idealDeriveClause_eventKeys] at hk
                                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
                                    rcases hk with rfl | rfl
                                    · exact idealReqKey_fresh events idx
                                    · exact drawToldKey_fresh events idx
                                  · exact ihV c hmem
                          | cons _ _ => rw [hIns] at h; cases h
                        · cases h
                  · split at h
                    · cases h; exact ihV
                    · cases h
              | request svc =>
                  dsimp only at h
                  split at h
                  · cases h; exact ihV
                  · cases h

private theorem checkAuthoredEvents_fresh {a : Admitted V} {prover verifier : Role}
    {samplesKey : Option Key} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (es : List (ShapeEvent V)) {cS : List (Clause V a.program.headers prover .nat)},
      checkAuthoredEvents a prover verifier samplesKey declKey es = .ok cS →
      ∀ c ∈ cS, ClauseFresh events c
  | [], _, h => by cases h; exact fun _ hc => nomatch hc
  | e :: rest, cS, h => by
      unfold checkAuthoredEvents at h
      cases hRec : checkAuthoredEvents a prover verifier samplesKey declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihS := checkAuthoredEvents_fresh (events := events) rest hRec
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases h; exact ihS
              · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases samplesKey with
                      | none => cases h; exact ihS
                      | some sKey =>
                          dsimp only at h
                          cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                          | none => rw [hS] at h; cases h
                          | some sRef =>
                              rw [hS] at h; cases h
                              intro c hc
                              rcases List.mem_cons.mp hc with rfl | hmem
                              · intro key hk _; rw [proverSampleClause_eventKeys] at hk; cases hk
                              · exact ihS c hmem
                    · cases h; exact ihS
                  · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ihS
                  · cases h

private theorem buildStreamingLayoutClauses_go_fresh {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      (∀ c ∈ pCs, Term.eventKeys (fun o => RoleOp.isEvent o) c.code = []) ∧
      (∀ c ∈ vCs, Term.eventKeys (fun o => RoleOp.isEvent o) c.code = [])
  | _, [], _, _, h => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, pCs, vCs, h => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := buildStreamingLayoutClauses_go_fresh (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · cases h
                  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · exact layoutPWriteClause_eventKeys ..
                    · exact ihP c hm
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · exact layoutVReadClause_eventKeys ..
                    · exact ihV c hm
              · cases h; exact ⟨ihP, ihV⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact layoutPWriteClause_eventKeys ..
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact layoutVCarryClause_eventKeys ..
                          · exact ihV c hm
                    · cases h
                      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact layoutDropClause_eventKeys ..
                        · exact ihP c hm
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact layoutDropClause_eventKeys ..
                        · exact ihV c hm
                  · cases h; exact ⟨ihP, ihV⟩
              | request _ => cases h; exact ⟨ihP, ihV⟩

private theorem collectCompactWire_fresh {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {ws : List (WireSpec V a.program.headers.fns unitTy)}
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))},
      collectCompactWire a layout unitTy prover verifier declKey events idx es = .ok (ws, pCs) →
      ∀ c ∈ pCs, Term.eventKeys (fun o => RoleOp.isEvent o) c.code = []
  | _, [], _, _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, ws, pCs, h => by
      unfold collectCompactWire at h
      cases hRec : collectCompactWire a layout unitTy prover verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihP := collectCompactWire_fresh (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some _ =>
                    rw [hLk] at h; cases h
                    intro c hc
                    rcases List.mem_cons.mp hc with rfl | hm
                    · exact layoutDropClause_eventKeys ..
                    · exact ihP c hm
                | none =>
                    rw [hLk] at h; dsimp only at h
                    cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · exact layoutPWriteClause_eventKeys ..
                      · exact ihP c hm
              · cases h; exact ihP
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                        simp only [hW, hR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · exact layoutPWriteClause_eventKeys ..
                        · exact ihP c hm
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · exact layoutDropClause_eventKeys ..
                      · exact ihP c hm
                  · cases h; exact ihP
              | request _ => cases h; exact ihP

private theorem buildCompactVClauses_fresh {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {stmtTys : List V.Ty} {wireSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {vCs : List (Clause V a.program.headers verifier
        (.tuple (tysOfList (stmtTys ++ wireSpecs.map (·.ty)))))},
      buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs
        htfree idx es = .ok vCs →
      ∀ c ∈ vCs, Term.eventKeys (fun o => RoleOp.isEvent o) c.code = []
  | _, [], _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, vCs, h => by
      unfold buildCompactVClauses at h
      cases hRec : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys
          wireSpecs htfree (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihV := buildCompactVClauses_fresh (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; dsimp only at h
                    cases hRecFn : findSafeFnRef a recKey
                        (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                    | none => rw [hRecFn] at h; cases h
                    | some recRef =>
                        rw [hRecFn] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · exact compactRecoverClause_eventKeys ..
                        · exact ihV c hm
                | none =>
                    rw [hLk] at h; dsimp only at h
                    cases hWM : findWireMember e.site e.τ wireSpecs with
                    | none => rw [hWM] at h; cases h
                    | some mWire =>
                        rw [hWM] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · exact compactReadSlotClause_eventKeys ..
                        · exact ihV c hm
              · cases h; exact ihV
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hWM : findWireMember ⟨e.site.through, drawToldKey events idx⟩ e.τ wireSpecs <;>
                      cases hEq : findLayoutEqual a layout.module e.τ <;>
                        simp only [hWM, hEq] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · exact compactCompareClause_eventKeys ..
                        · exact ihV c hm
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · exact layoutDropClause_eventKeys ..
                      · exact ihV c hm
                  · cases h; exact ihV
              | request _ => cases h; exact ihV

private theorem buildLayoutLayers_fresh {a : Admitted V} {entry : ProtocolHeader V} {layout : Layout}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins}
    (h : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    (∀ c ∈ layP.clauses, ClauseFresh events c) ∧ (∀ c ∈ layV.clauses, ClauseFresh events c) := by
  unfold buildLayoutLayers at h
  cases hUnit : findLayoutUnit a layout.module with
  | none => rw [hUnit] at h; cases h
  | some uPair =>
      rw [hUnit] at h; dsimp only at h
      split at h
      · cases hStr : buildStreamingLayoutClauses a layout uPair.1 uPair.2.down prover verifier
            declKey events with
        | error _ => rw [hStr] at h; cases h
        | ok cs =>
            rw [hStr] at h; cases h
            obtain ⟨hP, hV⟩ := buildStreamingLayoutClauses_go_fresh 0 events hStr
            exact ⟨(fun c hc key hk _ => by rw [hP c hc] at hk; cases hk),
                   (fun c hc key hk _ => by rw [hV c hc] at hk; cases hk)⟩
      · unfold buildCompactLayoutLayers at h
        cases hCW : collectCompactWire a layout uPair.1 prover verifier declKey events 0 events with
        | error _ => rw [hCW] at h; cases h
        | ok cw =>
            rw [hCW] at h; dsimp only [bind, Except.bind] at h
            split at h
            · cases hVC : buildCompactVClauses a layout uPair.1 prover verifier declKey events _ cw.1
                  _ 0 events with
              | error _ => rw [hVC] at h; cases h
              | ok vcs =>
                  rw [hVC] at h; cases h
                  have hP := collectCompactWire_fresh 0 events hCW
                  have hV := buildCompactVClauses_fresh 0 events hVC
                  exact ⟨(fun c hc key hk _ => by rw [hP c hc] at hk; cases hk),
                         (fun c hc key hk _ => by rw [hV c hc] at hk; cases hk)⟩
            · cases h

private theorem stack_fresh_cast {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins))
    (h : ∀ l ∈ layers, ∀ c ∈ l.clauses, ClauseFresh (hdr₂.shape.events [] id) c) :
    ∀ l ∈ (hr ▸ hHdr ▸ layers), ∀ c ∈ l.clauses, ClauseFresh (hdr₁.shape.events [] id) c :=
  cast_layer_stack_elim hHdr hr layers
    (fun hdr _ ls => ∀ l ∈ ls, ∀ c ∈ l.clauses, ClauseFresh (hdr.shape.events [] id) c) h

/-- Every accepted deployment satisfies `Deployed.Fresh`. -/
theorem deploy_fresh (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.Fresh := by
  unfold deploy at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    split at h
    · cases h
    · cases hCon : declaration.construction with
      | interactive =>
          rw [hCon] at h; cases h
          intro _ _ hl; cases hl
      | authored =>
          rw [hCon] at h; dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h; dsimp only at h
              split at h
              · cases h
              · cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples declaration.key
                    (foundPair.1.shape.events [] id) with
                | error _ => rw [hAuth] at h; cases h
                | ok sClauses =>
                    rw [hAuth] at h; dsimp only [bind, Except.bind] at h
                    cases hLO : declaration.layout with
                    | none => rw [hLO] at h; cases h
                    | some layout =>
                        rw [hLO] at h; dsimp only at h
                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                            declaration.key (foundPair.1.shape.events [] id) with
                        | error _ => rw [hLay] at h; cases h
                        | ok lays =>
                            rw [hLay] at h; cases h
                            have hS := checkAuthoredEvents_fresh (events := foundPair.1.shape.events [] id) _ hAuth
                            obtain ⟨hLP, hLV⟩ := buildLayoutLayers_fresh hLay
                            intro r
                            dsimp only [Deployed.entry]
                            by_cases hP : r = pv.1
                            · rw [dite_eq_left hP]
                              apply stack_fresh_cast (by simp [hFound]) hP
                              cases declaration.samples with
                              | none =>
                                  intro l hl
                                  simp only [List.mem_singleton] at hl; subst hl; exact hLP
                              | some _ =>
                                  intro l hl
                                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                  rcases hl with rfl | rfl
                                  · exact hS
                                  · exact hLP
                            · rw [dite_eq_right hP]
                              by_cases hV : r = pv.2
                              · rw [dite_eq_left hV]
                                apply stack_fresh_cast (by simp [hFound]) hV
                                intro l hl
                                simp only [List.mem_singleton] at hl; subst hl; exact hLV
                              · rw [dite_eq_right hV]
                                intro _ hl; cases hl
      | derived suite sessionTag =>
          rw [hCon] at h; dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h; dsimp only at h
              split at h
              · cases h
              · cases hLO : declaration.layout with
                | none => rw [hLO] at h; cases h
                | some layout =>
                    rw [hLO] at h; dsimp only at h
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at h; cases h
                    | some stPair =>
                        rw [hSt] at h; dsimp only at h
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at h; cases h
                        | some absPair =>
                            rw [hAb] at h; dsimp only at h
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at h; cases h
                            | ok sess =>
                                rw [hSess] at h; dsimp only [bind, Except.bind] at h
                                cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1 pv.2
                                    (.inl rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSP] at h; cases h
                                | ok stmtP =>
                                    rw [hSP] at h; dsimp only [bind, Except.bind] at h
                                    cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                        (.inr rfl) foundPair.1.ins declaration.key with
                                    | error _ => rw [hSV] at h; cases h
                                    | ok stmtV =>
                                        rw [hSV] at h; dsimp only [bind, Except.bind] at h
                                        cases hCC : buildConstructionClauses a suite stPair.1 absPair.1
                                            absPair.2 pv.1 pv.2 declaration.samples declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hCC] at h; cases h
                                        | ok cc =>
                                            rw [hCC] at h; dsimp only [bind, Except.bind] at h
                                            cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                                declaration.key (foundPair.1.shape.events [] id) with
                                            | error _ => rw [hLay] at h; cases h
                                            | ok lays =>
                                                rw [hLay] at h; cases h
                                                obtain ⟨hCP, hCV, hCS⟩ :=
                                                  buildConstructionClauses_go_fresh 0 _ hCC
                                                obtain ⟨hLP, hLV⟩ := buildLayoutLayers_fresh hLay
                                                intro r
                                                dsimp only [Deployed.entry]
                                                by_cases hP : r = pv.1
                                                · rw [dite_eq_left hP]
                                                  apply stack_fresh_cast (by simp [hFound]) hP
                                                  cases declaration.samples with
                                                  | none =>
                                                      intro l hl
                                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                                      rcases hl with rfl | rfl
                                                      · exact hCP
                                                      · exact hLP
                                                  | some _ =>
                                                      intro l hl
                                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                                      rcases hl with rfl | rfl | rfl
                                                      · exact hCS
                                                      · exact hCP
                                                      · exact hLP
                                                · rw [dite_eq_right hP]
                                                  by_cases hV : r = pv.2
                                                  · rw [dite_eq_left hV]
                                                    apply stack_fresh_cast (by simp [hFound]) hV
                                                    intro l hl
                                                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                                    rcases hl with rfl | rfl
                                                    · exact hCV
                                                    · exact hLV
                                                  · rw [dite_eq_right hV]
                                                    intro _ hl; cases hl

theorem statements_deployFresh (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployFresh c := by
  intro a decl d h; rw [hdep] at h; exact deploy_fresh enc a decl d h

/-- Every accepted ideal-RO deployment satisfies `Deployed.Fresh`. -/
theorem deployIdeal_fresh (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.Fresh := by
  unfold deployIdeal at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    split at h
    · cases h
    · cases hCon : declaration.construction with
      | interactive => rw [hCon] at h; cases h
      | authored => rw [hCon] at h; cases h
      | derived suite sessionTag =>
          rw [hCon] at h; dsimp only at h
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h; dsimp only at h
              split at h
              · cases h
              · cases hLO : declaration.layout with
                | none => rw [hLO] at h; cases h
                | some layout =>
                    rw [hLO] at h; dsimp only at h
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at h; cases h
                    | some stPair =>
                        rw [hSt] at h; dsimp only at h
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at h; cases h
                        | some absPair =>
                            rw [hAb] at h; dsimp only at h
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at h; cases h
                            | ok sess =>
                                rw [hSess] at h; dsimp only [bind, Except.bind] at h
                                cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                    (.inr rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSV] at h; cases h
                                | ok stmtV =>
                                    rw [hSV] at h; dsimp only [bind, Except.bind] at h
                                    cases hIV : buildIdealVerifierClauses a suite stPair.1 absPair.1
                                        absPair.2 serviceKey pv.1 pv.2 declaration.key
                                        (foundPair.1.shape.events [] id) with
                                    | error _ => rw [hIV] at h; cases h
                                    | ok idealVClauses =>
                                        rw [hIV] at h; dsimp only [bind, Except.bind] at h
                                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                            declaration.key (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hLay] at h; cases h
                                        | ok lays =>
                                            rw [hLay] at h; cases h
                                            have hCV := buildIdealVerifierClauses_go_fresh 0 _ hIV
                                            obtain ⟨_, hLV⟩ := buildLayoutLayers_fresh hLay
                                            intro r
                                            dsimp only [Deployed.entry]
                                            by_cases hV : r = pv.2
                                            · rw [dite_eq_left hV]
                                              apply stack_fresh_cast (by simp [hFound]) hV
                                              intro l hl
                                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                              rcases hl with rfl | rfl
                                              · exact hCV
                                              · exact hLV
                                            · rw [dite_eq_right hV]
                                              intro _ hl; cases hl

end StructuralTheorems

/-! ## Section 3: Validity safety (`deployedSafe`, `deployIdeal_safe`) -/

section ValiditySafety

variable {V : Vocabulary} (M : Model V)

/-- A single clause preserves value validity, emits valid outgoing payloads, and never halts
`.undefined` against any `ValidReply M`. -/
private def ClauseValidSafe {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty}
    (c : Clause V hs r state) : Prop :=
  ∀ (path : List Frame) (args : HList M.Val c.site.takes) (s : M.Val state),
    args.All M.Valid → M.Valid state s →
    (c.code.denote (roleSem M r fnTable rTable) path
      (Env.positional (aloneIn M r (args.append (.cons s .nil))))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M)
      (fun out => (aloneOut M r out).All M.Valid)
      (· ≠ .undefined)

private theorem rop_payload_valid (op : ROp M) (h : ROp.ValidPayload M op) :
    (ROp.payload M op).All M.Valid := by
  cases op with
  | give _ _ _ _ _ => exact ⟨h, trivial⟩
  | get => trivial
  | own => exact h
  | hear => trivial
  | «begin» => trivial
  | settle => trivial

private theorem rop_reply_valid (op : ROp M) (vals : HList M.Val (ROp.gives M op))
    (h : vals.All M.Valid) :
    ValidReply M op (ROp.reply M op vals) := by
  cases op with
  | give => trivial
  | get => cases vals with | cons v vn => cases vn; exact h.1
  | own => cases vals with | cons v vn => cases vn; exact h.1
  | hear => cases vals with | cons v vn => cases vn; exact h.1
  | «begin» => trivial
  | settle => trivial

private theorem clause_answer_validSafe {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty} :
    ∀ (cs : List (Clause V hs r state)),
      (∀ c ∈ cs, ClauseValidSafe M fnTable rTable c) →
      ∀ (op : ROp M) (s : M.Val state),
        ROp.ValidPayload M op → M.Valid state s →
        (Clause.answer M fnTable rTable cs op s).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun out => ValidReply M op out.1 ∧ M.Valid state out.2)
          (fun stop => stop.1 ≠ .undefined ∧ M.Valid state stop.2)
  | [], _, op, s, hop, hs => ⟨hop, fun _ hr => ⟨hr, hs⟩⟩
  | c :: cs, hcs, op, s, hop, hs => by
      unfold Clause.answer
      split
      · rename_i hMatch
        rw [Process.safeWith_map, Process.safeWith_mapHalt]
        have hArgsV : (cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op)).All M.Valid :=
          hlist_all_cast hMatch.2.2.1.symm (rop_payload_valid M op hop)
        have hCode := hcs c List.mem_cons_self (ROp.occurrence M op).path _ s hArgsV hs
        refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun out hout => ?_) (fun why hwhy => ⟨hwhy, hs⟩) hCode
        have ⟨hv1, hv2⟩ := hlist_split_all c.site.gives (aloneOut M r out) hout
        dsimp only
        refine ⟨rop_reply_valid M op _ (hlist_all_cast hMatch.2.2.2 hv1), ?_⟩
        cases h2 : (HList.split c.site.gives (aloneOut M r out)).2 with
        | cons sv sn =>
            cases sn
            rw [h2] at hv2
            exact hv2.1
      · exact clause_answer_validSafe fnTable rTable cs
          (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) op s hop hs

private theorem layoutDropClause_validSafe {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role) :
    ClauseValidSafe M fnTable rTable
      (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters) := by
  intro path args s _ hs
  cases args with
  | cons x xn =>
      cases xn
      show ((layoutDropClause r site kind getters).code.denote (roleSem M r fnTable rTable) path
        (Env.positional (aloneIn M r (.cons x (.cons s .nil))))).SafeWith M
          (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M r out).All M.Valid) (· ≠ .undefined)
      rw [layoutDropClause_denote]
      change (aloneOut M r (aloneIn M r (.cons s .nil))).All M.Valid
      rw [aloneOut_aloneIn]
      exact ⟨hs, trivial⟩

private theorem layoutPWriteClause_validSafe (a : Admitted V) {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (writeRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (layoutPWriteClause prover site kind getters writeRef) := by
  intro path args buf hargs hbuf
  cases args with
  | cons msg mn =>
      cases mn
      show ((layoutPWriteClause prover site kind getters writeRef).code.denote
        (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
        (Env.positional (aloneIn M prover (.cons msg (.cons buf .nil))))).SafeWith M
          (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M prover out).All M.Valid) (· ≠ .undefined)
      rw [layoutPWriteClause_denote]
      obtain ⟨chunk, hch, hchV⟩ := writeRef.eval_done M a (.cons msg .nil) hargs
      rw [hch]
      change (aloneOut M prover (aloneIn M prover (.cons (buf ++ chunk.single) .nil))).All M.Valid
      rw [aloneOut_aloneIn]
      have hchS : M.Valid (.seq unitTy none) chunk.single := by
        cases chunk with | cons c cn => cases cn; exact hchV.1
      exact ⟨valid_seq_append M hbuf hchS, trivial⟩

private theorem layoutVReadClause_validSafe (a : Admitted V) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (readRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (layoutVReadClause hfree verifier prover site kind readRef) := by
  intro path args st _ hst
  cases args
  rcases st with ⟨buf, off, ⟨⟩⟩
  show ((layoutVReadClause hfree verifier prover site kind readRef).code.denote
    (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M verifier (.cons (buf, (off, ())) .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
  rw [layoutVReadClause_denote, Process.safeWith_map]
  have hSafe := readRef.eval_safe M a (.cons buf (.cons off .nil)) ⟨hst.1, hst.2.1, trivial⟩
  refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
    (fun res hres => ?_) (fun _ h => h) (Process.safeWith_liftLocal M id _ hSafe)
  cases res with
  | cons v r1 =>
      cases r1 with
      | cons nextOff r2 =>
          cases r2
          change (aloneOut M verifier (aloneIn M verifier
            (.cons v (.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))).All M.Valid
          rw [aloneOut_aloneIn]
          exact ⟨hres.1, ⟨hst.1, hres.2.1, trivial⟩, trivial⟩

private theorem layoutVCarryClause_validSafe (a : Admitted V) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (readRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V a.program.headers.fns [τ, τ] [.bool]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef) := by
  intro path args st hargs hst
  cases args with
  | cons derived dn =>
      cases dn
      rcases st with ⟨buf, off, ⟨⟩⟩
      show ((layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef).code.denote
        (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
        (Env.positional (aloneIn M verifier (.cons derived (.cons (buf, (off, ())) .nil))))).SafeWith M
          (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
      rw [layoutVCarryClause_denote]
      dsimp only [roleSem, layoutVCarryClause, Clause.site, List.nil_append]
      rw [Process.safeWith_bind]
      have hSafe := readRef.eval_safe M a (.cons buf (.cons off .nil)) ⟨hst.1, hst.2.1, trivial⟩
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun res hres => ?_) (fun _ h => h) (Process.safeWith_liftLocal M id _ hSafe)
      cases res with
      | cons carried r1 =>
          cases r1 with
          | cons nextOff r2 =>
              cases r2
              obtain ⟨eqRes, heq, _⟩ := eqRef.eval_done M a (.cons derived (.cons carried .nil))
                ⟨hargs.1, hres.1, trivial⟩
              change ((liftLocal id (eqRef.eval M (Defs.fnTable M a.program.defs)
                (.cons derived (.cons carried .nil)))).bind fun eqRes =>
                  bif eqRes.single then
                    .done (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))
                  else
                    .halt (.declared .reject ⟨path, guardKey⟩)).SafeWith M
                (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
              rw [heq]
              dsimp only [liftLocal_done, Process.bind]
              cases eqRes.single with
              | false =>
                  intro h; cases h
              | true =>
                  change (aloneOut M verifier (aloneIn M verifier
                    (.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).All M.Valid
                  rw [aloneOut_aloneIn]
                  exact ⟨⟨hst.1, hres.2.1, trivial⟩, trivial⟩

private theorem proverAbsorbClause_validSafe (a : Admitted V) {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (proverAbsorbClause prover site kind getters label hlabel encodeRef absorbRef) := by
  intro path args st hargs hst
  cases args with
  | cons msg mn =>
      cases mn
      show ((proverAbsorbClause prover site kind getters label hlabel encodeRef absorbRef).code.denote
        (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
        (Env.positional (aloneIn M prover (.cons msg (.cons st .nil))))).SafeWith M
          (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M prover out).All M.Valid) (· ≠ .undefined)
      rw [proverAbsorbClause_denote]
      obtain ⟨enc, henc, hencV⟩ := encodeRef.eval_done M a (.cons msg .nil) hargs
      have hlblV : M.Valid bytesTy label := ⟨hlabel, (fun _ h => nomatch h)⟩
      have hencS : M.Valid (.seq unitTy none) enc.single := by
        cases enc with | cons e en => cases en; exact hencV.1
      obtain ⟨nextSt, hnext, hnextV⟩ := absorbRef.eval_done M a
        (.cons st (.cons label (.cons enc.single .nil))) ⟨hst, hlblV, hencS, trivial⟩
      rw [henc]
      dsimp only [liftLocal_done, Process.bind]
      rw [hnext]
      dsimp only [liftLocal_done, Process.bind, Process.SafeWith]
      refine ⟨hargs.1, fun _ _ => ?_⟩
      change (aloneOut M prover (aloneIn M prover nextSt)).All M.Valid
      rw [aloneOut_aloneIn]
      exact hnextV

private theorem verifierAbsorbClause_validSafe (a : Admitted V) {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (verifierAbsorbClause verifier prover site kind label hlabel encodeRef absorbRef) := by
  intro path args st _ hst
  cases args
  show ((verifierAbsorbClause verifier prover site kind label hlabel encodeRef absorbRef).code.denote
    (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
  rw [verifierAbsorbClause_denote]
  refine ⟨trivial, fun msg hmsg => ?_⟩
  dsimp only
  obtain ⟨enc, henc, hencV⟩ := encodeRef.eval_done M a (.cons msg .nil) ⟨hmsg, trivial⟩
  have hlblV : M.Valid bytesTy label := ⟨hlabel, (fun _ h => nomatch h)⟩
  have hencS : M.Valid (.seq unitTy none) enc.single := by
    cases enc with | cons e en => cases en; exact hencV.1
  obtain ⟨nextSt, hnext, hnextV⟩ := absorbRef.eval_done M a
    (.cons st (.cons label (.cons enc.single .nil))) ⟨hst, hlblV, hencS, trivial⟩
  rw [henc]
  dsimp only [liftLocal_done, Process.bind]
  rw [hnext]
  dsimp only [liftLocal_done, Process.map]
  change (aloneOut M verifier (aloneIn M verifier (.cons msg nextSt))).All M.Valid
  rw [aloneOut_aloneIn]
  exact ⟨hmsg, hnextV⟩

private theorem deriveClause_nil_validSafe (a : Admitted V) {stateTy τ : V.Ty}
    (r peer : Role) (site : Site) (part : Part V)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (deriveRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy] [τ, stateTy]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (deriveClause r peer site part [] toldKey label hlabel deriveRef) := by
  intro path args st _ hst
  cases args
  show ((deriveClause r peer site part [] toldKey label hlabel deriveRef).code.denote
    (roleSem M r (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M r (.cons st .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M r out).All M.Valid) (· ≠ .undefined)
  rw [deriveClause_denote_nil]
  have hlblV : M.Valid bytesTy label := ⟨hlabel, (fun _ h => nomatch h)⟩
  obtain ⟨res, hres, hresV⟩ := deriveRef.eval_done M a (.cons st (.cons label .nil))
    ⟨hst, hlblV, trivial⟩
  rw [hres]
  dsimp only [liftLocal_done, Process.bind]
  cases res with
  | cons coin r1 =>
      cases r1 with
      | cons nextSt r2 =>
          cases r2
          refine ⟨hresV.1, fun _ _ => ?_⟩
          change (aloneOut M r (aloneIn M r (.cons coin (.cons nextSt .nil)))).All M.Valid
          rw [aloneOut_aloneIn]
          exact hresV

private theorem idealDeriveClause_nil_validSafe (a : Admitted V) {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (part : Part V)
    (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (idealDeriveClause verifier prover site part [] serviceKey reqKey toldKey
        label hlabel encodeRef absorbRef) := by
  intro path args st _ hst
  cases args
  show ((idealDeriveClause verifier prover site part [] serviceKey reqKey toldKey
      label hlabel encodeRef absorbRef).code.denote
    (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
  rw [idealDeriveClause_denote_nil]
  have hlblV : M.Valid bytesTy label := ⟨hlabel, (fun _ h => nomatch h)⟩
  refine ⟨⟨⟨hst, hlblV, trivial⟩, trivial⟩, fun coin hcoin => ?_⟩
  refine ⟨hcoin, fun _ _ => ?_⟩
  obtain ⟨enc, henc, hencV⟩ := encodeRef.eval_done M a (.cons coin .nil) ⟨hcoin, trivial⟩
  have hencS : M.Valid (.seq unitTy none) enc.single := by
    cases enc with | cons e en => cases en; exact hencV.1
  obtain ⟨nextSt, hnext, hnextV⟩ := absorbRef.eval_done M a
    (.cons st (.cons label (.cons enc.single .nil))) ⟨hst, hlblV, hencS, trivial⟩
  dsimp only
  rw [henc]
  dsimp only [liftLocal_done, Process.bind]
  rw [hnext]
  dsimp only [liftLocal_done, Process.map]
  change (aloneOut M verifier (aloneIn M verifier (.cons coin nextSt))).All M.Valid
  rw [aloneOut_aloneIn]
  exact ⟨hcoin, hnextV⟩

private theorem proverSampleClause_validSafe (a : Admitted V) {τ : V.Ty}
    (prover : Role) (site : Site) (law : V.LawKey)
    (sampleRef : TypedFnRef V a.program.headers.fns [.nat, .nat] [τ]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (proverSampleClause prover site law sampleRef) := by
  intro path args att _ _
  cases args
  show ((proverSampleClause prover site law sampleRef).code.denote
    (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M prover (.cons att .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M prover out).All M.Valid) (· ≠ .undefined)
  rw [proverSampleClause_denote]
  obtain ⟨coin, hcoin, hcoinV⟩ := sampleRef.eval_done M a (.cons att (.cons site.key.number .nil))
    ⟨trivial, trivial, trivial⟩
  rw [hcoin]
  change (aloneOut M prover (aloneIn M prover (.cons coin.single (.cons att .nil)))).All M.Valid
  rw [aloneOut_aloneIn]
  have hcS : M.Valid τ coin.single := by
    cases coin with | cons c cn => cases cn; exact hcoinV.1
  exact ⟨hcS, trivial, trivial⟩

private theorem compactReadSlotClause_validSafe {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ) :
    ClauseValidSafe M fnTable rTable
      (compactReadSlotClause (hs := hs) htfree verifier prover site kind pos) := by
  intro path args st _ hst
  cases args
  show ((compactReadSlotClause htfree verifier prover site kind pos).code.denote
    (roleSem M verifier fnTable rTable) path
    (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
  rw [compactReadSlotClause_denote]
  change (aloneOut M verifier (aloneIn M verifier (.cons (Tys.getAt M stateTys pos st) (.cons (a := Ty.tuple stateTys) st .nil)))).All M.Valid
  rw [aloneOut_aloneIn]
  exact ⟨tys_getAt_valid M stateTys pos st hst, hst, trivial⟩

private theorem compactCompareClause_validSafe (a : Admitted V) {stateTys : Tys V.TypeKey}
    {τ : V.Ty} (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ) (eqRef : TypedFnRef V a.program.headers.fns [τ, τ] [.bool]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef) := by
  intro path args st hargs hst
  cases args with
  | cons derived dn =>
      cases dn
      show ((compactCompareClause htfree verifier prover toldSite guardKey pos eqRef).code.denote
        (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
        (Env.positional (aloneIn M verifier (.cons derived (.cons (a := Ty.tuple stateTys) st .nil))))).SafeWith M
          (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
      rw [compactCompareClause_denote]
      obtain ⟨eqRes, heq, _⟩ := eqRef.eval_done M a
        (.cons derived (.cons (Tys.getAt M stateTys pos st) .nil))
        ⟨hargs.1, tys_getAt_valid M stateTys pos st hst, trivial⟩
      rw [heq]
      dsimp only [liftLocal_done, Process.bind]
      cases eqRes.single with
      | false => intro h; cases h
      | true =>
          change (aloneOut M verifier (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))).All M.Valid
          rw [aloneOut_aloneIn]
          exact ⟨hst, trivial⟩

private theorem compactRecoverClause_validSafe (a : Admitted V) {stateTys : Tys V.TypeKey}
    {τ : V.Ty} (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recoverRef : SafeFnRef V a.program.headers.fns stateTys.toList [τ]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (compactRecoverClause verifier prover site kind recoverRef) := by
  intro path args st _ hst
  cases args
  show ((compactRecoverClause verifier prover site kind recoverRef).code.denote
    (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
  rw [compactRecoverClause_denote]
  dsimp only [roleSem, compactRecoverClause, Clause.site, List.cons_append, List.nil_append]
  rw [Process.safeWith_map]
  have hSafe := recoverRef.eval_safe M a (Tys.toHList M stateTys st)
    (tys_toHList_valid M stateTys st hst)
  refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
    (fun res hres => ?_) (fun _ h => h) (Process.safeWith_liftLocal M id _ hSafe)
  change (aloneOut M verifier (aloneIn M verifier (.cons res.single (.cons (a := Ty.tuple stateTys) st .nil)))).All M.Valid
  rw [aloneOut_aloneIn]
  have hrS : M.Valid τ res.single := by
    cases res with | cons v vn => cases vn; exact hres.1
  exact ⟨hrS, hst, trivial⟩

private theorem buildConstructionClauses_go_validSafe {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absorbRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      (∀ c ∈ cP, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c) ∧
      (∀ c ∈ cV, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c) ∧
      (∀ c ∈ cS, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c)
  | _, [], _, _, _, h => by
      cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, cP, cV, cS, h => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absorbRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV, ihS⟩ := buildConstructionClauses_go_validSafe (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    refine ⟨fun c hc => ?_, fun c hc => ?_, ihS⟩
                    · rcases List.mem_cons.mp hc with rfl | hm
                      · apply proverAbsorbClause_validSafe M a
                      · exact ihP c hm
                    · rcases List.mem_cons.mp hc with rfl | hm
                      · apply verifierAbsorbClause_validSafe M a
                      · exact ihV c hm
              · split at h
                · cases h; exact ⟨ihP, ihV, ihS⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                refine ⟨fun c hc => ?_, fun c hc => ?_, ihS⟩
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · apply deriveClause_nil_validSafe M a
                                  · exact ihP c hm
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · rcases sig with ⟨sIns, sOut⟩
                                    dsimp only at hIns
                                    subst hIns
                                    apply deriveClause_nil_validSafe M a
                                  · exact ihV c hm
                              · cases h
                        · cases h
                  · split at h
                    · split at h
                      · cases samplesKey with
                        | none => cases h; exact ⟨ihP, ihV, ihS⟩
                        | some sKey =>
                            dsimp only at h
                            cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                            | none => rw [hS] at h; cases h
                            | some sRef =>
                                rw [hS] at h; cases h
                                refine ⟨ihP, ihV, fun c hc => ?_⟩
                                rcases List.mem_cons.mp hc with rfl | hm
                                · apply proverSampleClause_validSafe M a
                                · exact ihS c hm
                      · cases h; exact ⟨ihP, ihV, ihS⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV, ihS⟩
                  · cases h

private theorem buildIdealVerifierClauses_go_validSafe {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildIdealVerifierClauses.go a suite stateTy unitTy absorbRef serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ c ∈ cV, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c
  | _, [], _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, cV, h => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite stateTy unitTy absorbRef serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihV := buildIdealVerifierClauses_go_validSafe (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    intro c hc
                    rcases List.mem_cons.mp hc with rfl | hm
                    · apply verifierAbsorbClause_validSafe M a
                    · exact ihV c hm
              · split at h
                · cases h; exact ihV
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hIns : sig.ins with
                          | nil =>
                              rw [hIns] at h; dsimp only at h
                              cases hEnc : findSuiteEncode a suite unitTy e.τ with
                              | none => rw [hEnc] at h; cases h
                              | some encRef =>
                                  rw [hEnc] at h; cases h
                                  intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hm
                                  · apply idealDeriveClause_nil_validSafe M a
                                  · exact ihV c hm
                          | cons _ _ => rw [hIns] at h; cases h
                        · cases h
                  · split at h
                    · cases h; exact ihV
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ihV
                  · cases h

private theorem checkAuthoredEvents_validSafe {a : Admitted V} {prover verifier : Role}
    {samplesKey : Option Key} {declKey : Key} :
    ∀ (es : List (ShapeEvent V)) {cS : List (Clause V a.program.headers prover .nat)},
      checkAuthoredEvents a prover verifier samplesKey declKey es = .ok cS →
      ∀ c ∈ cS, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c
  | [], _, h => by cases h; exact fun _ hc => nomatch hc
  | e :: rest, cS, h => by
      unfold checkAuthoredEvents at h
      cases hRec : checkAuthoredEvents a prover verifier samplesKey declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihS := checkAuthoredEvents_validSafe rest hRec
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases h; exact ihS
              · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases samplesKey with
                      | none => cases h; exact ihS
                      | some sKey =>
                          dsimp only at h
                          cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                          | none => rw [hS] at h; cases h
                          | some sRef =>
                              rw [hS] at h; cases h
                              intro c hc
                              rcases List.mem_cons.mp hc with rfl | hm
                              · apply proverSampleClause_validSafe M a
                              · exact ihS c hm
                    · cases h; exact ihS
                  · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ihS
                  · cases h

private theorem buildStreamingLayoutClauses_go_validSafe {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      (∀ c ∈ pCs, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c) ∧
      (∀ c ∈ vCs, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c)
  | _, [], _, _, h => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, pCs, vCs, h => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := buildStreamingLayoutClauses_go_validSafe (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · cases h
                  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · apply layoutPWriteClause_validSafe M a
                    · exact ihP c hm
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · apply layoutVReadClause_validSafe M a
                    · exact ihV c hm
              · cases h; exact ⟨ihP, ihV⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · apply layoutPWriteClause_validSafe M a
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · apply layoutVCarryClause_validSafe M a
                          · exact ihV c hm
                    · cases h
                      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutDropClause_validSafe M
                        · exact ihP c hm
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutDropClause_validSafe M
                        · exact ihV c hm
                  · cases h; exact ⟨ihP, ihV⟩
              | request _ => cases h; exact ⟨ihP, ihV⟩

private theorem collectCompactWire_validSafe {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {ws : List (WireSpec V a.program.headers.fns unitTy)}
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))},
      collectCompactWire a layout unitTy prover verifier declKey events idx es = .ok (ws, pCs) →
      ∀ c ∈ pCs, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c
  | _, [], _, _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, ws, pCs, h => by
      unfold collectCompactWire at h
      cases hRec : collectCompactWire a layout unitTy prover verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihP := collectCompactWire_validSafe (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some _ =>
                    rw [hLk] at h; cases h
                    intro c hc
                    rcases List.mem_cons.mp hc with rfl | hm
                    · apply layoutDropClause_validSafe M
                    · exact ihP c hm
                | none =>
                    rw [hLk] at h; dsimp only at h
                    cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · apply layoutPWriteClause_validSafe M a
                      · exact ihP c hm
              · cases h; exact ihP
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                        simp only [hW, hR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutPWriteClause_validSafe M a
                        · exact ihP c hm
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · apply layoutDropClause_validSafe M
                      · exact ihP c hm
                  · cases h; exact ihP
              | request _ => cases h; exact ihP

private theorem buildCompactVClauses_validSafe {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {stmtTys : List V.Ty} {wireSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {vCs : List (Clause V a.program.headers verifier
        (.tuple (tysOfList (stmtTys ++ wireSpecs.map (·.ty)))))},
      buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs
        htfree idx es = .ok vCs →
      ∀ c ∈ vCs, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c
  | _, [], _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, vCs, h => by
      unfold buildCompactVClauses at h
      cases hRec : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys
          wireSpecs htfree (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihV := buildCompactVClauses_validSafe (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; dsimp only at h
                    cases hRecFn : findSafeFnRef a recKey
                        (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                    | none => rw [hRecFn] at h; cases h
                    | some recRef =>
                        rw [hRecFn] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply compactRecoverClause_validSafe M a
                        · exact ihV c hm
                | none =>
                    rw [hLk] at h; dsimp only at h
                    cases hWM : findWireMember e.site e.τ wireSpecs with
                    | none => rw [hWM] at h; cases h
                    | some mWire =>
                        rw [hWM] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply compactReadSlotClause_validSafe M
                        · exact ihV c hm
              · cases h; exact ihV
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hWM : findWireMember ⟨e.site.through, drawToldKey events idx⟩ e.τ wireSpecs <;>
                      cases hEq : findLayoutEqual a layout.module e.τ <;>
                        simp only [hWM, hEq] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply compactCompareClause_validSafe M a
                        · exact ihV c hm
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · apply layoutDropClause_validSafe M
                      · exact ihV c hm
                  · cases h; exact ihV
              | request _ => cases h; exact ihV

/-- A layer is validity-safe: its handler, `start`, and `finish` all preserve `M.Valid` and
never stop `.undefined`. -/
private structure LayerValidSafe (a : Admitted V) {r : Role} {ins : List (LTy V)}
    (l : Layer V a.program.headers r ins) : Prop where
  handlerOk : (Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) l).SafeWith
    M (ValidReply M) (M.Valid l.state) (ROp.ValidPayload M) (ROp.ValidPayload M)
  startOk : ∀ (inputs : HList (RV M r) ins) (t : HList M.Val l.takes),
    inputs.All (RV.Valid M r) → t.All M.Valid →
    (l.start.denote (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
      (Env.positional (t.append (heldValues M r inputs)))).Every
        (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined)
  finishOk : ∀ (s : M.Val l.state), M.Valid l.state s →
    (l.finish.denote (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
      (Env.positional (.cons s .nil))).Every
        (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined)

private theorem compactStart_cast_safe {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {Γ : Ctx V.Ty} {ts₁ ts₂ : List V.Ty} (hTys : ts₁ = ts₂)
    (t : Term (localDialect V fns) Γ [.tuple (tysOfList ts₁)]) (env : Env M.Val Γ)
    (hSafe : (t.denote (localSem M fns fnTable) [] env).Every
      (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined)) :
    ((cast (congrArg (fun ts => Term (localDialect V fns) Γ [.tuple (tysOfList ts)]) hTys) t).denote
      (localSem M fns fnTable) [] env).Every
      (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined) := by
  subst hTys; exact hSafe

private theorem buildLayoutLayers_validSafe {a : Admitted V} {entry : ProtocolHeader V}
    {layout : Layout} {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins}
    (h : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    LayerValidSafe M a layP ∧ LayerValidSafe M a layV := by
  unfold buildLayoutLayers at h
  cases hUnit : findLayoutUnit a layout.module with
  | none => rw [hUnit] at h; cases h
  | some uPair =>
      rw [hUnit] at h; dsimp only at h
      split at h
      · cases hStr : buildStreamingLayoutClauses a layout uPair.1 uPair.2.down prover verifier
            declKey events with
        | error _ => rw [hStr] at h; cases h
        | ok cs =>
            rw [hStr] at h; cases h
            obtain ⟨hP, hV⟩ := buildStreamingLayoutClauses_go_validSafe M 0 events hStr
            refine ⟨⟨⟨clause_answer_validSafe M _ _ _ hP,
                      fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩,
                    ⟨⟨clause_answer_validSafe M _ _ _ hV,
                      fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩⟩
            · intro inputs t _ _
              cases t
              dsimp only [HList.append]
              rw [layoutPStart_denote]
              exact ⟨⟨(fun _ hu => nomatch hu), (fun _ hu => nomatch hu)⟩, trivial⟩
            · intro s hs
              rw [identityFinish_denote]
              exact ⟨hs, trivial⟩
            · intro inputs t _ ht
              cases t with
              | cons proof pn =>
                  cases pn
                  change ((layoutVStart uPair.1).denote
                    (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                    (Env.positional (.cons proof (heldValues M verifier inputs)))).Every
                      (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined)
                  rw [layoutVStart_denote]
                  exact ⟨⟨ht.1, trivial, trivial⟩, trivial⟩
            · intro s _
              rcases s with ⟨buf, off, ⟨⟩⟩
              rw [layoutVFinish_denote]
              cases Nat.beq off buf.length with
              | true => trivial
              | false => intro h; cases h
      · unfold buildCompactLayoutLayers at h
        cases hCW : collectCompactWire a layout uPair.1 prover verifier declKey events 0 events with
        | error _ => rw [hCW] at h; cases h
        | ok cw =>
            rw [hCW] at h; dsimp only [bind, Except.bind] at h
            split at h
            · cases hVC : buildCompactVClauses a layout uPair.1 prover verifier declKey events _ cw.1
                  _ 0 events with
              | error _ => rw [hVC] at h; cases h
              | ok vcs =>
                  rw [hVC] at h; cases h
                  have hP := collectCompactWire_validSafe M 0 events hCW
                  have hV := buildCompactVClauses_validSafe M 0 events hVC
                  refine ⟨⟨⟨clause_answer_validSafe M _ _ _ hP,
                            fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩,
                          ⟨⟨clause_answer_validSafe M _ _ _ hV,
                            fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩⟩
                  · intro inputs t _ _
                    cases t
                    dsimp only [HList.append]
                    rw [layoutPStart_denote]
                    exact ⟨⟨(fun _ hu => nomatch hu), (fun _ hu => nomatch hu)⟩, trivial⟩
                  · intro s hs
                    rw [identityFinish_denote]
                    exact ⟨hs, trivial⟩
                  · intro inputs t hin ht
                    cases t with
                    | cons proof pn =>
                        cases pn
                        refine compactStart_cast_safe M (Defs.fnTable M a.program.defs) (by simp) _ _ ?_
                        exact compactLayoutVStart_safe M a uPair.1 uPair.2.down _ _ _ proof ht.1
                          (heldValues M verifier inputs) (heldValues_valid M verifier inputs hin)
                  · intro s _
                    rw [emptyFinish_denote]
                    trivial
            · cases h

private theorem runStack_validSafe {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (hAdmit : admit named assoc = .ok a) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (retry : Option (Nat × Site))
    (r : Role) (layers : List (Layer V a.program.headers r hdr.ins))
    (hLayers : ∀ l ∈ layers, LayerValidSafe M a l)
    (ins : HList (RV M r) hdr.ins) (taken : HList M.Val (Stack.Takes layers))
    (hIns : ins.All (RV.Valid M r)) (hTaken : taken.All M.Valid) :
    (runStack a M callee retry r layers ins taken).StopsWhen (Permitted M) (· ≠ .undefined) := by
  unfold runStack
  have hRole := roleMeaning_safeWith_valid M hAdmit callee r [] ins hIns
  have hStackH := stack_handler_validSafe_all M (Defs.fnTable M a.program.defs)
    (Defs.rTable M a.program.defs) (ValidReply M) (ROp.ValidPayload M) layers
    (fun l hl => (hLayers l hl).handlerOk)
  have hStart := stack_start_validSafe M (Defs.fnTable M a.program.defs) (ValidReply M)
    (ROp.ValidPayload M) layers ins taken hIns hTaken
    (fun l hl t ht => (hLayers l hl).startOk ins t hIns ht)
  have hRun : (Process.bind (Stack.start M (Defs.fnTable M a.program.defs) layers ins taken) fun first =>
      Process.bind (((Stack.handler M (Defs.fnTable M a.program.defs)
        (Defs.rTable M a.program.defs) layers).run (retryOf M retry)
        (roleMeaning M a.program callee r [] ins) first).mapHalt Prod.fst) fun out =>
        (Stack.finish M (Defs.fnTable M a.program.defs) layers out.2).map
          fun gives => (out.1, gives)).SafeWith M (ValidReply M) (ROp.ValidPayload M)
        (fun _ => True) (· ≠ .undefined) := by
    rw [Process.safeWith_bind]
    refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
      (fun first hfirst => ?_) (fun _ h => h) hStart
    rw [Process.safeWith_bind, Process.safeWith_mapHalt]
    have hRunH := Handler.SafeWith.run M hStackH retry
      (fun _ _ _ _ _ _ _ hr => hr) (fun _ _ _ _ _ _ ho => ho)
      (fun _ _ => trivial) (fun _ => trivial) hRole hfirst
    refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
      (fun out hout => ?_) (fun stop hstop => hstop.1) hRunH
    rw [Process.safeWith_map]
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
      (fun _ _ => trivial) (fun _ h => h)
      (stack_finish_validSafe M (Defs.fnTable M a.program.defs) (ValidReply M)
        (ROp.ValidPayload M) layers out.2 hout.2
        (fun l hl => (hLayers l hl).finishOk))
  exact Process.safeWith_every M
    (Process.safeWith_mono M (permitted_implies_validReply M) (fun _ h => h)
      (fun _ _ => trivial) (fun _ h => h) hRun)

private theorem layer_validSafe_construction {a : Admitted V} {stateTy unitTy : V.Ty}
    {r : Role} {ins : List (LTy V)}
    (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
    (startRef : TypedFnRef V a.program.headers.fns [bytesTy] [stateTy])
    (absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (stmtItems : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held r ins))))
    (clauses : List (Clause V a.program.headers r stateTy))
    (hClauses : ∀ c ∈ clauses, ClauseValidSafe M (Defs.fnTable M a.program.defs)
      (Defs.rTable M a.program.defs) c) :
    LayerValidSafe M a
      ({ line := .construction, state := stateTy, takes := [], gives := [],
         clauses := clauses, again := restoreAgain stateTy,
         start := constructionStart sessBytes hSess startRef absorbRef stmtItems,
         finish := emptyFinish stateTy } : Layer V a.program.headers r ins) := by
  refine ⟨⟨clause_answer_validSafe M _ _ _ hClauses,
            fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩
  · intro inputs t hin _
    cases t
    dsimp only [HList.append]
    obtain ⟨stEnd, hDone, hStV⟩ := constructionStart_done M a sessBytes hSess startRef absorbRef
      stmtItems (heldValues M r inputs) (heldValues_valid M r inputs hin)
    rw [hDone]
    exact ⟨hStV, trivial⟩
  · intro s _
    rw [emptyFinish_denote]
    trivial

private theorem layer_validSafe_samples {a : Admitted V} {r : Role} {ins : List (LTy V)}
    (clauses : List (Clause V a.program.headers r .nat))
    (hClauses : ∀ c ∈ clauses, ClauseValidSafe M (Defs.fnTable M a.program.defs)
      (Defs.rTable M a.program.defs) c) :
    LayerValidSafe M a
      ({ line := .samples, state := .nat, takes := [], gives := [],
         clauses := clauses, again := attemptNumAgain,
         start := samplesStart, finish := emptyFinish .nat } : Layer V a.program.headers r ins) := by
  refine ⟨⟨clause_answer_validSafe M _ _ _ hClauses,
            fun _ _ _ _ _ => by dsimp only [Layer.handler]; rw [attemptNumAgain_denote]; trivial⟩, ?_, ?_⟩
  · intro inputs t _ _
    cases t
    dsimp only [HList.append]
    rw [samplesStart_denote]
    exact ⟨trivial, trivial⟩
  · intro s _
    rw [emptyFinish_denote]
    trivial

private theorem layer_validSafe_cast {a : Admitted V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V a.program.headers r₂ hdr₂.ins))
    (h : ∀ l ∈ layers, LayerValidSafe M a l) :
    ∀ l ∈ (hr ▸ hHdr ▸ layers), LayerValidSafe M a l :=
  cast_layer_stack_elim hHdr hr layers (fun _ _ ls => ∀ l ∈ ls, LayerValidSafe M a l) h

/-- Every deployed role of an admitted program never stops `.undefined` on valid inputs, valid
taken values, and permitted replies (even without requiring `Unconditional`). -/
theorem deploy_safe (enc : VocabEncoder V) {named : NamedProgram V} {assoc : Association}
    {a : Admitted V} (hAdmit : admit named assoc = .ok a)
    {declaration : Declaration} {d : Deployed V}
    (hDep : deploy enc a declaration = .ok d)
    (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r)))
    (hIns : ins.All (RV.Valid M r)) (hTaken : taken.All M.Valid) :
    (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined) := by
  have hKeep := deploy_keeps enc a declaration d hDep
  rw [deployed_run_eq_runStack]
  have hAdmitD : admit named assoc = .ok d.admitted := by rw [hKeep.1]; exact hAdmit
  apply runStack_validSafe M hAdmitD d.callee d.retry r (d.stack r) _ ins taken hIns hTaken
  unfold deploy at hDep
  split at hDep
  · cases hDep
  · rename_i foundPair hFound
    dsimp only at hDep
    split at hDep
    · cases hDep
    · cases hCon : declaration.construction with
      | interactive =>
          rw [hCon] at hDep; cases hDep
          intro _ hl; cases hl
      | authored =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples declaration.key
                    (foundPair.1.shape.events [] id) with
                | error _ => rw [hAuth] at hDep; cases hDep
                | ok sClauses =>
                    rw [hAuth] at hDep; dsimp only [bind, Except.bind] at hDep
                    cases hLO : declaration.layout with
                    | none => rw [hLO] at hDep; cases hDep
                    | some layout =>
                        rw [hLO] at hDep; dsimp only at hDep
                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                            declaration.key (foundPair.1.shape.events [] id) with
                        | error _ => rw [hLay] at hDep; cases hDep
                        | ok lays =>
                            rw [hLay] at hDep; cases hDep
                            have hS := checkAuthoredEvents_validSafe M _ hAuth
                            obtain ⟨hLP, hLV⟩ := buildLayoutLayers_validSafe M hLay
                            dsimp only [Deployed.entry]
                            by_cases hP : r = pv.1
                            · rw [dite_eq_left hP]
                              apply layer_validSafe_cast M (by simp [hFound]) hP
                              cases declaration.samples with
                              | none =>
                                  intro l hl
                                  simp only [List.mem_singleton] at hl; subst hl; exact hLP
                              | some _ =>
                                  intro l hl
                                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                  rcases hl with rfl | rfl
                                  · exact layer_validSafe_samples M sClauses hS
                                  · exact hLP
                            · rw [dite_eq_right hP]
                              by_cases hV : r = pv.2
                              · rw [dite_eq_left hV]
                                apply layer_validSafe_cast M (by simp [hFound]) hV
                                intro l hl
                                simp only [List.mem_singleton] at hl; subst hl; exact hLV
                              · rw [dite_eq_right hV]
                                intro _ hl; cases hl
      | derived suite sessionTag =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · cases hLO : declaration.layout with
                | none => rw [hLO] at hDep; cases hDep
                | some layout =>
                    rw [hLO] at hDep; dsimp only at hDep
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at hDep; cases hDep
                    | some stPair =>
                        rw [hSt] at hDep; dsimp only at hDep
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at hDep; cases hDep
                        | some absPair =>
                            rw [hAb] at hDep; dsimp only at hDep
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at hDep; cases hDep
                            | ok sess =>
                                rw [hSess] at hDep; dsimp only [bind, Except.bind] at hDep
                                cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1 pv.2
                                    (.inl rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSP] at hDep; cases hDep
                                | ok stmtP =>
                                    rw [hSP] at hDep; dsimp only [bind, Except.bind] at hDep
                                    cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                        (.inr rfl) foundPair.1.ins declaration.key with
                                    | error _ => rw [hSV] at hDep; cases hDep
                                    | ok stmtV =>
                                        rw [hSV] at hDep; dsimp only [bind, Except.bind] at hDep
                                        cases hCC : buildConstructionClauses a suite stPair.1 absPair.1
                                            absPair.2 pv.1 pv.2 declaration.samples declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hCC] at hDep; cases hDep
                                        | ok cc =>
                                            rw [hCC] at hDep; dsimp only [bind, Except.bind] at hDep
                                            cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                                declaration.key (foundPair.1.shape.events [] id) with
                                            | error _ => rw [hLay] at hDep; cases hDep
                                            | ok lays =>
                                                rw [hLay] at hDep; cases hDep
                                                obtain ⟨hCP, hCV, hCS⟩ :=
                                                  buildConstructionClauses_go_validSafe M 0 _ hCC
                                                obtain ⟨hLP, hLV⟩ := buildLayoutLayers_validSafe M hLay
                                                dsimp only [Deployed.entry]
                                                by_cases hP : r = pv.1
                                                · rw [dite_eq_left hP]
                                                  apply layer_validSafe_cast M (by simp [hFound]) hP
                                                  cases declaration.samples with
                                                  | none =>
                                                      intro l hl
                                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                                      rcases hl with rfl | rfl
                                                      · exact layer_validSafe_construction M _ _ _ _ _ _ hCP
                                                      · exact hLP
                                                  | some _ =>
                                                      intro l hl
                                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                                      rcases hl with rfl | rfl | rfl
                                                      · exact layer_validSafe_samples M _ hCS
                                                      · exact layer_validSafe_construction M _ _ _ _ _ _ hCP
                                                      · exact hLP
                                                · rw [dite_eq_right hP]
                                                  by_cases hV : r = pv.2
                                                  · rw [dite_eq_left hV]
                                                    apply layer_validSafe_cast M (by simp [hFound]) hV
                                                    intro l hl
                                                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                                    rcases hl with rfl | rfl
                                                    · exact layer_validSafe_construction M _ _ _ _ _ _ hCV
                                                    · exact hLV
                                                  · rw [dite_eq_right hV]
                                                    intro _ hl; cases hl

theorem statements_deployedSafe (enc : VocabEncoder V) (c : Functions V)
    (hadm : c.admit = admit) (hdep : c.deploy = deploy enc) : Statements.deployedSafe c := by
  intro named assoc a hA _ decl d hD M r ins taken hIns hTaken
  rw [hadm] at hA; rw [hdep] at hD
  exact deploy_safe M enc hA hD r ins taken hIns hTaken

private theorem deployIdeal_admitted (enc : VocabEncoder V) (serviceKey : Key)
    (a : Admitted V) (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.admitted = a := by
  unfold deployIdeal at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases hCon : declaration.construction with
      | interactive => rw [hCon] at h; cases h
      | authored => rw [hCon] at h; cases h
      | derived suite sessionTag =>
          rw [hCon] at h; dsimp only at h
          cases hPV : proverAndVerifier _ declaration with
          | none => rw [hPV] at h; cases h
          | some pv =>
              rw [hPV] at h; dsimp only at h
              split at h
              · cases h
              · cases hLO : declaration.layout with
                | none => rw [hLO] at h; cases h
                | some layout =>
                    rw [hLO] at h; dsimp only at h
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at h; cases h
                    | some stPair =>
                        rw [hSt] at h; dsimp only at h
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at h; cases h
                        | some absPair =>
                            rw [hAb] at h; dsimp only at h
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at h; cases h
                            | ok sess =>
                                rw [hSess] at h; dsimp only [bind, Except.bind] at h
                                cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                    (.inr rfl) _ declaration.key with
                                | error _ => rw [hSV] at h; cases h
                                | ok stmtV =>
                                    rw [hSV] at h; dsimp only [bind, Except.bind] at h
                                    cases hIV : buildIdealVerifierClauses a suite stPair.1 absPair.1
                                        absPair.2 serviceKey pv.1 pv.2 declaration.key _ with
                                    | error _ => rw [hIV] at h; cases h
                                    | ok idealVClauses =>
                                        rw [hIV] at h; dsimp only [bind, Except.bind] at h
                                        cases hLay : buildLayoutLayers a _ layout pv.1 pv.2
                                            declaration.key _ with
                                        | error _ => rw [hLay] at h; cases h
                                        | ok lays => rw [hLay] at h; cases h; rfl

/-- Every role of an ideal-RO deployment never stops `.undefined` on valid inputs, valid taken
values, and permitted replies. -/
theorem deployIdeal_safe (enc : VocabEncoder V) (serviceKey : Key)
    {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (hAdmit : admit named assoc = .ok a)
    {declaration : Declaration} {d : Deployed V}
    (hDep : deployIdeal enc serviceKey a declaration = .ok d)
    (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r)))
    (hIns : ins.All (RV.Valid M r)) (hTaken : taken.All M.Valid) :
    (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined) := by
  have hAd : d.admitted = a := deployIdeal_admitted enc serviceKey a declaration d hDep
  rw [deployed_run_eq_runStack]
  have hAdmitD : admit named assoc = .ok d.admitted := by rw [hAd]; exact hAdmit
  apply runStack_validSafe M hAdmitD d.callee d.retry r (d.stack r) _ ins taken hIns hTaken
  unfold deployIdeal at hDep
  split at hDep
  · cases hDep
  · rename_i foundPair hFound
    dsimp only at hDep
    split at hDep
    · cases hDep
    · cases hCon : declaration.construction with
      | interactive => rw [hCon] at hDep; cases hDep
      | authored => rw [hCon] at hDep; cases hDep
      | derived suite sessionTag =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · cases hLO : declaration.layout with
                | none => rw [hLO] at hDep; cases hDep
                | some layout =>
                    rw [hLO] at hDep; dsimp only at hDep
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at hDep; cases hDep
                    | some stPair =>
                        rw [hSt] at hDep; dsimp only at hDep
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at hDep; cases hDep
                        | some absPair =>
                            rw [hAb] at hDep; dsimp only at hDep
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at hDep; cases hDep
                            | ok sess =>
                                rw [hSess] at hDep; dsimp only [bind, Except.bind] at hDep
                                cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                    (.inr rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSV] at hDep; cases hDep
                                | ok stmtV =>
                                    rw [hSV] at hDep; dsimp only [bind, Except.bind] at hDep
                                    cases hIV : buildIdealVerifierClauses a suite stPair.1 absPair.1
                                        absPair.2 serviceKey pv.1 pv.2 declaration.key
                                        (foundPair.1.shape.events [] id) with
                                    | error _ => rw [hIV] at hDep; cases hDep
                                    | ok idealVClauses =>
                                        rw [hIV] at hDep; dsimp only [bind, Except.bind] at hDep
                                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                            declaration.key (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hLay] at hDep; cases hDep
                                        | ok lays =>
                                            rw [hLay] at hDep; cases hDep
                                            have hCV := buildIdealVerifierClauses_go_validSafe M 0 _ hIV
                                            obtain ⟨_, hLV⟩ := buildLayoutLayers_validSafe M hLay
                                            dsimp only [Deployed.entry]
                                            by_cases hV : r = pv.2
                                            · rw [dite_eq_left hV]
                                              apply layer_validSafe_cast M (by simp [hFound]) hV
                                              intro l hl
                                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                                              rcases hl with rfl | rfl
                                              · exact layer_validSafe_construction M _ _ _ _ _ _ hCV
                                              · exact hLV
                                            · rw [dite_eq_right hV]
                                              intro _ hl; cases hl

end ValiditySafety

/-! ## Section 4: Effect coverage (`deployCoverage`, `deployIdeal_coverage`) -/

section Coverage

variable {V : Vocabulary} (M : Model V)

/-- Whether a clause `c` matches effect `op`. -/
private def ClauseMatches {hs : Headers V} {r : Role} {state : V.Ty}
    (c : Clause V hs r state) (op : ROp M) : Prop :=
  c.site.site = (ROp.occurrence M op).site ∧ some c.site.part = ROp.part M op ∧
    c.site.takes = ROp.takes M op ∧ c.site.gives = ROp.gives M op

/-- Every clause `c` produces only `opOk₂` effects whenever it runs on a matching `op`. -/
private def ClauseEmits {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty}
    (opOk₂ : ROp M → Prop) (c : Clause V hs r state) : Prop :=
  ∀ (op : ROp M) (hMatch : ClauseMatches M c op) (s : M.Val state),
    (c.code.denote (roleSem M r fnTable rTable) (ROp.occurrence M op).path
      (Env.positional (aloneIn M r (HList.append
        (cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op))
        (.cons s .nil))))).SafeWith M (fun _ _ => True) opOk₂ (fun _ => True) (fun _ => True)

private theorem clause_answer_covers {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty}
    {opOk₂ : ROp M → Prop} :
    ∀ (cs : List (Clause V hs r state)),
      (∀ c ∈ cs, ClauseEmits M fnTable rTable opOk₂ c) →
      ∀ (op : ROp M) (s : M.Val state),
        (opOk₂ op ∨ ∃ c ∈ cs, ClauseMatches M c op) →
        (Clause.answer M fnTable rTable cs op s).SafeWith M (fun _ _ => True) opOk₂
          (fun _ => True) (fun _ => True)
  | [], _, op, _, hCov => by
      rcases hCov with h2 | ⟨_, hc, _⟩
      · exact ⟨h2, fun _ _ => trivial⟩
      · cases hc
  | c :: cs, hEm, op, s, hCov => by
      unfold Clause.answer
      split
      · rename_i hMatch
        rw [Process.safeWith_map, Process.safeWith_mapHalt]
        exact hEm c List.mem_cons_self op hMatch s
      · rename_i hNoMatch
        apply clause_answer_covers fnTable rTable cs (fun c' hc' => hEm c' (List.mem_cons_of_mem _ hc')) op s
        rcases hCov with h2 | ⟨c', hc', hm'⟩
        · exact .inl h2
        · rcases List.mem_cons.mp hc' with rfl | hmem
          · exact absurd hm' hNoMatch
          · exact .inr ⟨c', hmem, hm'⟩

/-- Lightweight handler coverage invariant (unrestricted replies and halts): every `opOk₁` effect
is transformed into `opOk₂` effects. -/
private def Handler.Covers {σ : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (opOk₁ opOk₂ : ROp M → Prop) : Prop :=
  ∀ op s, opOk₁ op →
    (h.clause op s).SafeWith M (fun _ _ => True) opOk₂ (fun _ => True) (fun _ => True)

private theorem handler_answer_covers {τ X E : Type} {h : Handler (RSig M) (RSig M) Stop τ}
    {opOk₁ opOk₂ : ROp M → Prop} (hCov : Handler.Covers M h opOk₁ opOk₂) :
    ∀ {p : Process (RSig M) (Stop × E) X} (upper : E) (t : τ),
      p.SafeWith M (fun _ _ => True) opOk₁ (fun _ => True) (fun _ => True) →
      (h.answer p upper t).SafeWith M (fun _ _ => True) opOk₂ (fun _ => True) (fun _ => True)
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call op k, upper, t, ⟨ho, hk⟩ => by
      simp only [Handler.answer]
      rw [Process.safeWith_bind, Process.safeWith_mapHalt]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun out _ => handler_answer_covers hCov upper out.2 (hk out.1 trivial))
        (fun _ _ => trivial) (hCov op t ho)

private theorem handler_covers_over {σ τ : Type}
    {inner : Handler (RSig M) (RSig M) Stop σ} {outer : Handler (RSig M) (RSig M) Stop τ}
    {opOk₁ opOk₂ opOk₃ : ROp M → Prop}
    (hIn : Handler.Covers M inner opOk₁ opOk₂) (hOut : Handler.Covers M outer opOk₂ opOk₃) :
    Handler.Covers M (inner.over outer) opOk₁ opOk₃ := by
  intro op st ho
  simp only [Handler.over]
  rw [Process.safeWith_bind, Process.safeWith_mapHalt]
  exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (handler_answer_covers M hOut st.1 st.2 (hIn op st.1 ho))

private theorem attempts_covers {σ A : Type} {opOk : ROp M → Prop}
    (retriable : Stop → Bool) (exhausted : Stop)
    (again : Nat → σ → σ → Except Stop σ)
    (body : Nat → σ → Process (RSig M) ((Bool × Stop) × σ) (A × σ))
    (hbody : ∀ i s, (body i s).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True))
    (entry : σ) :
    ∀ (n i : Nat) (s : σ),
      (attempts retriable exhausted again body entry n i s).SafeWith M (fun _ _ => True) opOk
        (fun _ => True) (fun _ => True)
  | 0, _, _ => trivial
  | n + 1, i, s => by
      simp only [attempts]
      rw [Process.safeWith_recover]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun _ _ => trivial) (fun stop _ => ?_) (hbody i s)
      split
      · cases n with
        | zero => trivial
        | succ m =>
            cases again (i + 1) entry stop.2 with
            | error _ => trivial
            | ok next => exact attempts_covers retriable exhausted again body hbody entry (m + 1) (i + 1) next
      · trivial

private theorem handler_covers_run_and_inside {σ A : Type}
    {h : Handler (RSig M) (RSig M) Stop σ} {opOk₁ opOk₂ : ROp M → Prop}
    (hCov : Handler.Covers M h opOk₁ opOk₂) (retry : Option (Nat × Site))
    (hopMark : ∀ frame law at_ ins payload τ,
      opOk₂ (.own (.coin law) [] at_ ins payload τ) →
      opOk₂ (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ)) :
    ∀ (p : Process (RSig M) Stop A),
      p.SafeWith M (fun _ _ => True) opOk₁ (fun _ => True) (fun _ => True) →
      (∀ s, (h.run (retryOf M retry) p s).SafeWith M (fun _ _ => True) opOk₂
        (fun _ => True) (fun _ => True)) ∧
      (∀ i s, (h.inside (retryOf M retry) i p s).SafeWith M (fun _ _ => True) opOk₂
        (fun _ => True) (fun _ => True))
  | .done _, _ => ⟨fun _ => trivial, fun _ _ => trivial⟩
  | .halt _, _ => ⟨fun _ => trivial, fun _ _ => trivial⟩
  | .call op k, ⟨ho, hk⟩ => by
      have ih := fun reply => handler_covers_run_and_inside hCov retry hopMark (k reply) (hk reply trivial)
      constructor
      · intro s
        simp only [Handler.run]
        cases (retryOf M retry).begins op with
        | none =>
            rw [Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun out _ => (ih out.1).1 out.2) (fun _ _ => trivial) (hCov op s ho)
        | some pair =>
            exact attempts_covers M _ pair.1 h.again
              (fun i s' => h.inside (retryOf M retry) i (k (pair.2 i)) s')
              (fun i s' => (ih (pair.2 i)).2 i s') s _ 0 s
      · intro i s
        simp only [Handler.inside]
        cases (retryOf M retry).ends op with
        | some reply =>
            rw [Process.safeWith_mapHalt]
            exact (ih reply).1 s
        | none =>
            rw [Process.safeWith_bind, Process.safeWith_mapHalt]
            have hcl : ((retryOf M retry).mark i (h.clause op s)).SafeWith M (fun _ _ => True) opOk₂
                (fun _ => True) (fun _ => True) := by
              cases retry with
              | none => exact hCov op s ho
              | some rpair =>
                  exact Process.safeWith_markOwn M (.attempt rpair.2.key i)
                    (fun _ _ _ _ _ _ _ => trivial) (hopMark _) (hCov op s ho)
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun out _ => (ih out.1).2 i out.2) (fun _ _ => trivial) hcl

private theorem stack_handler_covers_nil {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    {r : Role} {ins : List (LTy V)} (opOk : ROp M → Prop) :
    Handler.Covers M (Stack.handler M fnTable rTable ([] : List (Layer V hs r ins))) opOk opOk :=
  fun _ _ ho => ⟨ho, fun _ _ => trivial⟩

private theorem stack_handler_covers_cons {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    {r : Role} {ins : List (LTy V)}
    {l : Layer V hs r ins} {rest : List (Layer V hs r ins)}
    {opOk₁ opOk₂ opOk₃ : ROp M → Prop}
    (hl : Handler.Covers M (Layer.handler M fnTable rTable l) opOk₁ opOk₂)
    (hrest : Handler.Covers M (Stack.handler M fnTable rTable rest) opOk₂ opOk₃) :
    Handler.Covers M (Stack.handler M fnTable rTable (l :: rest)) opOk₁ opOk₃ := by
  have hboth := handler_covers_over M hl hrest
  intro op st ho
  cases st with
  | cons mine below =>
      change (((((Layer.handler M fnTable rTable l).over
        (Stack.handler M fnTable rTable rest)).clause op (mine, below)).mapHalt
          fun stop => (stop.1, HList.cons stop.2.1 stop.2.2)).map
          fun out => (out.1, HList.cons out.2.1 out.2.2)).SafeWith M
          (fun _ _ => True) opOk₃ (fun _ => True) (fun _ => True)
      rw [Process.safeWith_map, Process.safeWith_mapHalt]
      exact hboth op (mine, below) ho

private theorem liftLocal_safeWith_any {H A : Type} {opOk : ROp M → Prop}
    (f : Stop → H) (p : Local A) :
    (liftLocal (S := RSig M) f p).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True) := by
  cases p with
  | done _ => trivial
  | halt _ => trivial
  | call op _ => nomatch op

private theorem runStack_closedEffects (a : Admitted V) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (retry : Option (Nat × Site))
    (r : Role) (layers : List (Layer V a.program.headers r hdr.ins))
    (hCov : Handler.Covers M
      (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) layers)
      (ROp.MatchesShape M r (hdr.shape.events [] id)) (ROp.IsClosed M))
    (ins : HList (RV M r) hdr.ins) (taken : HList M.Val (Stack.Takes layers)) :
    Process.ClosedEffects (runStack a M callee retry r layers ins taken) := by
  apply Process.closedEffects_of_safeWith M (P := fun _ => True) (R := fun _ => True)
  unfold runStack
  rw [Process.safeWith_bind]
  refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
    (fun first _ => ?_) (fun _ _ => trivial)
    (stack_start_noEffects M (Defs.fnTable M a.program.defs) (ROp.IsClosed M) layers ins taken)
  rw [Process.safeWith_bind, Process.safeWith_mapHalt]
  have hRole := roleMeaning_matchesShape M a.program callee r [] ins
  have hRun := (handler_covers_run_and_inside M hCov retry
    (fun _ _ _ _ _ _ _ => trivial) _ hRole).1 first
  refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
    (fun out _ => ?_) (fun _ _ => trivial) hRun
  rw [Process.safeWith_map]
  exact stack_finish_noEffects M (Defs.fnTable M a.program.defs) (ROp.IsClosed M) layers out.2

/-- Effects permitted to reach prover's layout layer. -/
private def LayoutInputP (prover verifier : Role) (events : List (ShapeEvent V)) (op : ROp M) : Prop :=
  ROp.IsClosed M op ∨
  (∃ e ∈ events, match op with
    | .give kind getters at_ τ _ =>
        e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind prover getters ∧ verifier ∈ getters
    | _ => False) ∨
  (∃ (idx : Nat) (e : ShapeEvent V), events[idx]? = some e ∧
    match op with
    | .give .message getters at_ τ _ =>
        getters = [verifier] ∧ at_.site = ⟨e.site.through, drawToldKey events idx⟩ ∧
        e.τ = τ ∧ ∃ law hearers, e.cls = .given (.coin law) verifier hearers ∧ prover ∈ hearers
    | _ => False)

/-- Effects permitted to reach verifier's layout layer. -/
private def LayoutInputV (prover verifier : Role) (events : List (ShapeEvent V)) (op : ROp M) : Prop :=
  ROp.IsClosed M op ∨
  (∃ e ∈ events, match op with
    | .get kind giver at_ τ =>
        giver = prover ∧ e.site = at_.site ∧ e.τ = τ ∧
        ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters
    | _ => False) ∨
  (∃ (idx : Nat) (e : ShapeEvent V), events[idx]? = some e ∧
    match op with
    | .give .message getters at_ τ _ =>
        getters = [prover] ∧ at_.site = ⟨e.site.through, drawToldKey events idx⟩ ∧
        e.τ = τ ∧ ∃ law hearers, e.cls = .given (.coin law) verifier hearers ∧ prover ∈ hearers
    | _ => False)

private theorem site_from_match {occ : Occurrence} {s : Site} (h : s = occ.site) :
    (⟨occ.path, s.key⟩ : Occurrence).site = s := by
  have h1 : s.through = Frame.applications occ.path := by
    have := congrArg Site.through h; exact this
  have h2 : s.key = occ.key := by
    have := congrArg Site.key h; exact this
  cases s with
  | mk through key =>
      dsimp only [Occurrence.site] at h1 ⊢
      rw [← h1]

private theorem site_told_from_match {occ : Occurrence} {s : Site} {k : Key} (h : s = occ.site) :
    (⟨occ.path, k⟩ : Occurrence).site = ⟨s.through, k⟩ := by
  have h1 : s.through = Frame.applications occ.path := congrArg Site.through h
  dsimp only [Occurrence.site]
  rw [← h1]

private theorem layoutClause_emits_any_drop {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty} {opOk : ROp M → Prop}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role) :
    ClauseEmits M fnTable rTable opOk
      (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters) := by
  intro op hMatch s
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args with
  | cons x xn =>
      cases xn
      show ((layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters).code.denote
        (roleSem M r fnTable rTable) (ROp.occurrence M op).path
        (Env.positional (aloneIn M r (.cons x (.cons s .nil))))).SafeWith
          M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
      rw [layoutDropClause_denote]; trivial

private theorem layoutClause_emits_any_pWrite {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty} {opOk : ROp M → Prop}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (wRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    ClauseEmits M fnTable rTable opOk (layoutPWriteClause prover site kind getters wRef) := by
  intro op hMatch buf
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args with
  | cons msg mn =>
      cases mn
      show ((layoutPWriteClause prover site kind getters wRef).code.denote
        (roleSem M prover fnTable rTable) (ROp.occurrence M op).path
        (Env.positional (aloneIn M prover (.cons msg (.cons buf .nil))))).SafeWith
          M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
      rw [layoutPWriteClause_denote]
      dsimp only [roleSem, layoutPWriteClause, Clause.site, List.cons_append, List.nil_append]
      rw [Process.safeWith_map]
      exact liftLocal_safeWith_any M id _

private theorem layoutClause_emits_any_vRead {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty} {opOk : ROp M → Prop}
    (hfree : Ty.isLinear V unitTy = false) (verifier prover : Role) (site : Site) (kind : FlowKind)
    (rRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat]) :
    ClauseEmits M fnTable rTable opOk (layoutVReadClause hfree verifier prover site kind rRef) := by
  intro op hMatch st
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args
  rcases st with ⟨buf, off, ⟨⟩⟩
  show ((layoutVReadClause hfree verifier prover site kind rRef).code.denote
    (roleSem M verifier fnTable rTable) (ROp.occurrence M op).path
    (Env.positional (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))).SafeWith
      M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
  rw [layoutVReadClause_denote]
  dsimp only [roleSem, layoutVReadClause, Clause.site, List.cons_append, List.nil_append]
  rw [Process.safeWith_map]
  exact liftLocal_safeWith_any M id _

private theorem layoutClause_emits_any_vCarry {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty} {opOk : ROp M → Prop}
    (hfree : Ty.isLinear V unitTy = false) (verifier prover : Role) (toldSite : Site)
    (guardKey : Key) (rRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    ClauseEmits M fnTable rTable opOk
      (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef) := by
  intro op hMatch st
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args with
  | cons der dn =>
      cases dn
      rcases st with ⟨buf, off, ⟨⟩⟩
      show ((layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).code.denote
        (roleSem M verifier fnTable rTable) (ROp.occurrence M op).path
        (Env.positional (aloneIn M verifier (.cons der (.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))))).SafeWith
          M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
      rw [layoutVCarryClause_denote]
      dsimp only [roleSem, layoutVCarryClause, Clause.site, List.cons_append, List.nil_append]
      rw [Process.safeWith_bind]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun res _ => ?_) (fun _ _ => trivial)
        (liftLocal_safeWith_any M id _)
      cases res with
      | cons c r1 =>
          cases r1 with
          | cons n r2 =>
              cases r2
              change ((liftLocal id (eqRef.eval M fnTable (.cons der (.cons c .nil)))).bind
                fun eqRes => bif eqRes.single then .done (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (n, ())) .nil))
                  else .halt (.declared .reject ⟨(ROp.occurrence M op).path, guardKey⟩)).SafeWith
                    M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
              rw [Process.safeWith_bind]
              refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun eqRes _ => ?_)
                (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
              cases eqRes.single <;> trivial

private theorem proverSampleClause_emits_any {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {τ : V.Ty} {opOk : ROp M → Prop}
    (prover : Role) (site : Site) (law : V.LawKey)
    (sRef : TypedFnRef V hs.fns [.nat, .nat] [τ]) :
    ClauseEmits M fnTable rTable opOk (proverSampleClause prover site law sRef) := by
  intro op hMatch att
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args
  show ((proverSampleClause prover site law sRef).code.denote
    (roleSem M prover fnTable rTable) (ROp.occurrence M op).path
    (Env.positional (aloneIn M prover (.cons att .nil)))).SafeWith
      M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
  rw [proverSampleClause_denote]
  dsimp only [roleSem, proverSampleClause, Clause.site, List.cons_append, List.nil_append]
  rw [Process.safeWith_map]
  exact liftLocal_safeWith_any M id _

private theorem compactReadSlotClause_emits_any {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty} {opOk : ROp M → Prop}
    (htfree : Tys.anyLinear V stateTys = false) (verifier prover : Role) (site : Site)
    (kind : FlowKind) (pos : Member stateTys.toList τ) :
    ClauseEmits M fnTable rTable opOk
      (compactReadSlotClause (hs := hs) htfree verifier prover site kind pos) := by
  intro op hMatch st
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args
  show ((compactReadSlotClause (hs := hs) htfree verifier prover site kind pos).code.denote
    (roleSem M verifier fnTable rTable) (ROp.occurrence M op).path
    (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)))).SafeWith
      M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
  rw [compactReadSlotClause_denote]; trivial

private theorem compactCompareClause_emits_any {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty} {opOk : ROp M → Prop}
    (htfree : Tys.anyLinear V stateTys = false) (verifier prover : Role) (toldSite : Site)
    (guardKey : Key) (pos : Member stateTys.toList τ) (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    ClauseEmits M fnTable rTable opOk
      (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef) := by
  intro op hMatch st
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args with
  | cons der dn =>
      cases dn
      show ((compactCompareClause htfree verifier prover toldSite guardKey pos eqRef).code.denote
        (roleSem M verifier fnTable rTable) (ROp.occurrence M op).path
        (Env.positional (aloneIn M verifier (.cons der (.cons (a := Ty.tuple stateTys) st .nil))))).SafeWith
          M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
      rw [compactCompareClause_denote]
      dsimp only [roleSem, compactCompareClause, Clause.site, List.cons_append, List.nil_append]
      rw [Process.safeWith_bind]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun eqRes _ => ?_)
        (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
      cases eqRes.single <;> trivial

private theorem compactRecoverClause_emits_any {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty} {opOk : ROp M → Prop}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recRef : SafeFnRef V hs.fns stateTys.toList [τ]) :
    ClauseEmits M fnTable rTable opOk
      (compactRecoverClause verifier prover site kind recRef) := by
  intro op hMatch st
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args
  show ((compactRecoverClause verifier prover site kind recRef).code.denote
    (roleSem M verifier fnTable rTable) (ROp.occurrence M op).path
    (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)))).SafeWith
      M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
  rw [compactRecoverClause_denote]
  dsimp only [roleSem, compactRecoverClause, Clause.site, List.cons_append, List.nil_append]
  rw [Process.safeWith_map]
  exact liftLocal_safeWith_any M id _

private theorem buildConstructionClauses_go_covers {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ k e, es[k]? = some e → events[idx + k]? = some e) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)}
        {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absorbRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      (∀ c ∈ cP, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (LayoutInputP M prover verifier events) c) ∧
      (∀ c ∈ cV, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (LayoutInputV M prover verifier events) c) ∧
      (∀ c ∈ cS, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (ROp.MatchesShape M prover events) c) ∧
      (∀ op, ROp.MatchesShape M prover es op →
        LayoutInputP M prover verifier events op ∨ ∃ c ∈ cP, ClauseMatches M c op) ∧
      (∀ op, ROp.MatchesShape M verifier es op →
        LayoutInputV M prover verifier events op ∨ ∃ c ∈ cV, ClauseMatches M c op)
  | _, [], _, _, _, _, h => by
      cases h
      refine ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ hc => nomatch hc), ?_, ?_⟩
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl (.inl trivial)
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl (.inl trivial)
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
  | idx, e :: rest, hSuf, cP, cV, cS, h => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k e', rest[k]? = some e' → events[(idx + 1) + k]? = some e' := by
        intro k e' hk
        have := hSuf (k + 1) e' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by
        simpa using hSuf 0 e rfl
      have hMem : e ∈ events := List.mem_of_getElem? hIdx
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absorbRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihEmP, ihEmV, ihEmS, ihCovP, ihCovV⟩ :=
            buildConstructionClauses_go_covers hNe (idx + 1) rest hSufRest hRec
          have liftRestP : ∀ op, (∃ e' ∈ rest, ROp.MatchesShapeEvent M prover e' op) →
              LayoutInputP M prover verifier events op ∨ ∃ c ∈ triple.1, ClauseMatches M c op := by
            intro op ho
            apply ihCovP op
            cases op with
            | «begin» | settle => trivial
            | give | get | own | hear => exact ho
          have liftRestV : ∀ op, (∃ e' ∈ rest, ROp.MatchesShapeEvent M verifier e' op) →
              LayoutInputV M prover verifier events op ∨ ∃ c ∈ triple.2.1, ClauseMatches M c op := by
            intro op ho
            apply ihCovV op
            cases op with
            | «begin» | settle => trivial
            | give | get | own | hear => exact ho
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPVFlow
                cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    refine ⟨?_, ?_, ihEmS, ?_, ?_⟩
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · intro op hMatch st
                        generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
                        cases args with
                        | cons msg mn =>
                            cases mn
                            show ((proverAbsorbClause prover e.site kind getters (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef absorbRef).code.denote
                              (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                              (ROp.occurrence M op).path
                              (Env.positional (aloneIn M prover (.cons msg (.cons st .nil))))).SafeWith
                                M (fun _ _ => True) (LayoutInputP M prover verifier events) (fun _ => True) (fun _ => True)
                            rw [proverAbsorbClause_denote]
                            dsimp only [roleSem, proverAbsorbClause, Clause.site, List.cons_append, List.nil_append]
                            rw [Process.safeWith_bind]
                            refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => ?_)
                              (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
                            rw [Process.safeWith_bind]
                            refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => ?_)
                              (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
                            refine ⟨.inr (.inl ⟨e, hMem, ?_⟩), fun _ _ => trivial⟩
                            exact ⟨(site_from_match hMatch.1).symm, rfl, hPVFlow.1 ▸ hCls, hPVFlow.2⟩
                      · exact ihEmP c hm
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · intro op hMatch st
                        generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
                        cases args
                        show ((verifierAbsorbClause verifier prover e.site kind (msgLabel e.site)
                          (msgLabel_bytes e.site) encRef absorbRef).code.denote
                          (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                          (ROp.occurrence M op).path
                          (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith
                            M (fun _ _ => True) (LayoutInputV M prover verifier events) (fun _ => True) (fun _ => True)
                        rw [verifierAbsorbClause_denote]
                        refine ⟨.inr (.inl ⟨e, hMem, ?_⟩), fun _ _ => ?_⟩
                        · exact ⟨rfl, (site_from_match hMatch.1).symm, rfl, getters, hPVFlow.2, hPVFlow.1 ▸ hCls⟩
                        · rw [Process.safeWith_bind]
                          refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => ?_)
                            (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
                          rw [Process.safeWith_map]
                          exact liftLocal_safeWith_any M id _
                      · exact ihEmV c hm
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl (.inl trivial)
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            exact .inr ⟨_, List.mem_cons_self, hSite, rfl, by cases hTy; rfl, rfl⟩
                          · rcases liftRestP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            exact absurd hPVFlow.1 hNeG
                          · rcases liftRestP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · rcases liftRestP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · rcases liftRestP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl (.inl trivial)
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; exact absurd hPVFlow.1.symm hNe
                          · rcases liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            exact .inr ⟨_, List.mem_cons_self, hSite, by dsimp only [verifierAbsorbClause, ROp.part]; rw [hPVFlow.1],
                              rfl, by cases hTy; rfl⟩
                          · rcases liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · rcases liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · rcases liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
              · split at h
                · rename_i hOut
                  cases h
                  refine ⟨ihEmP, ihEmV, ihEmS, ?_, ?_⟩
                  · intro op ho
                    cases op with
                    | «begin» | settle => exact .inl (.inl trivial)
                    | give k' gs' at_ τ' x' =>
                        obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
                        · exact liftRestP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                    | get k' g' at_ τ' =>
                        obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls; exact absurd hrIn hOut.2.2.1
                        · exact liftRestP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                    | own gk hs' at_ ins' pl' τ' =>
                        obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · exact liftRestP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                    | hear gk ow' at_ τ' =>
                        obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · exact liftRestP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                  · intro op ho
                    cases op with
                    | «begin» | settle => exact .inl (.inl trivial)
                    | give k' gs' at_ τ' x' =>
                        obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.2.1
                        · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                    | get k' g' at_ τ' =>
                        obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls; exact absurd hrIn hOut.2.2.2
                        · exact liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                    | own gk hs' at_ ins' pl' τ' =>
                        obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · exact liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                    | hear gk ow' at_ τ' =>
                        obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · exact liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · rename_i hOutEq
                          cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                rcases sig with ⟨sIns, sOut⟩
                                dsimp only at hIns
                                subst hIns
                                refine ⟨?_, ?_, ihEmS, ?_, ?_⟩
                                · intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hm
                                  · intro op hMatch st
                                    generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm)
                                      (ROp.payload M op) = args
                                    cases args
                                    show ((deriveClause prover verifier e.site (.hear (.coin law) verifier) []
                                      (drawToldKey events idx) (drawLabel e.site) (drawLabel_bytes e.site) derRef).code.denote
                                      (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                                      (ROp.occurrence M op).path
                                      (Env.positional (aloneIn M prover (.cons st .nil)))).SafeWith
                                        M (fun _ _ => True) (LayoutInputP M prover verifier events) (fun _ => True) (fun _ => True)
                                    rw [deriveClause_denote_nil]
                                    dsimp only [roleSem, deriveClause, Clause.site, List.cons_append, List.nil_append]
                                    rw [Process.safeWith_bind]
                                    refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                                      (fun res _ => ?_) (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
                                    cases res with
                                    | cons coin r1 =>
                                        cases r1 with
                                        | cons nst r2 =>
                                            cases r2
                                            refine ⟨.inr (.inr ⟨idx, e, hIdx, rfl,
                                              site_told_from_match hMatch.1, rfl, law, hearers,
                                              hCoin.1 ▸ hCls, hCoin.2⟩), fun _ _ => trivial⟩
                                  · exact ihEmP c hm
                                · intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hm
                                  · intro op hMatch st
                                    generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm)
                                      (ROp.payload M op) = args
                                    cases args
                                    show ((deriveClause verifier prover e.site (.own (.coin law) hearers) []
                                      (drawToldKey events idx) (drawLabel e.site) (drawLabel_bytes e.site) derRef).code.denote
                                      (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                                      (ROp.occurrence M op).path
                                      (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith
                                        M (fun _ _ => True) (LayoutInputV M prover verifier events) (fun _ => True) (fun _ => True)
                                    rw [deriveClause_denote_nil]
                                    dsimp only [roleSem, deriveClause, Clause.site, List.cons_append, List.nil_append]
                                    rw [Process.safeWith_bind]
                                    refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                                      (fun res _ => ?_) (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
                                    cases res with
                                    | cons coin r1 =>
                                        cases r1 with
                                        | cons nst r2 =>
                                            cases r2
                                            refine ⟨.inr (.inr ⟨idx, e, hIdx, rfl,
                                              site_told_from_match hMatch.1, rfl, law, hearers,
                                              hCoin.1 ▸ hCls, hCoin.2⟩), fun _ _ => trivial⟩
                                  · exact ihEmV c hm
                                · intro op ho
                                  cases op with
                                  | «begin» | settle => exact .inl (.inl trivial)
                                  | give k' gs' at_ τ' x' =>
                                      obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls
                                      · rcases liftRestP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                  | get k' g' at_ τ' =>
                                      obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls
                                      · rcases liftRestP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                  | own gk hs' at_ ins' pl' τ' =>
                                      obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls; exact absurd hCoin.1 hNe
                                      · rcases liftRestP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                  | hear gk ow' at_ τ' =>
                                      obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls
                                        exact .inr ⟨_, List.mem_cons_self, hSite,
                                          by dsimp only [deriveClause, ROp.part]; rw [hCoin.1], rfl, by cases hTy; rfl⟩
                                      · rcases liftRestP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                · intro op ho
                                  cases op with
                                  | «begin» | settle => exact .inl (.inl trivial)
                                  | give k' gs' at_ τ' x' =>
                                      obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls
                                      · rcases liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                  | get k' g' at_ τ' =>
                                      obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls
                                      · rcases liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                  | own gk hs' at_ ins' pl' τ' =>
                                      obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls
                                        have hInsEq : ins' = [] := by
                                          obtain ⟨s, hsLaw, hsIns, _⟩ := hTyped
                                          rw [hLaw] at hsLaw; cases hsLaw
                                          rw [← hsIns]
                                        exact .inr ⟨_, List.mem_cons_self, hSite, rfl,
                                          by cases hInsEq; rfl, by cases hTy; rfl⟩
                                      · rcases liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                  | hear gk ow' at_ τ' =>
                                      obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                                      rcases List.mem_cons.mp he' with rfl | hmem
                                      · rw [hCls] at hECls; cases hECls; exact absurd hCoin.1 hNeO
                                      · rcases liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                                        · exact .inl hL
                                        · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                              · cases h
                        · cases h
                  · split at h
                    · rename_i hNil
                      have hStepP : ∀ op, ROp.MatchesShape M prover (e :: rest) op →
                          LayoutInputP M prover verifier events op ∨ ∃ c ∈ triple.1, ClauseMatches M c op := by
                        intro op ho
                        cases op with
                        | «begin» | settle => exact .inl (.inl trivial)
                        | give k' gs' at_ τ' x' =>
                            obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls
                            · exact liftRestP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                        | get k' g' at_ τ' =>
                            obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls
                            · exact liftRestP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                        | own gk hs' at_ ins' pl' τ' =>
                            obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl (.inl trivial)
                            · exact liftRestP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                        | hear gk ow' at_ τ' =>
                            obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
                            · exact liftRestP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                      have hStepV : ∀ op, ROp.MatchesShape M verifier (e :: rest) op →
                          LayoutInputV M prover verifier events op ∨ ∃ c ∈ triple.2.1, ClauseMatches M c op := by
                        intro op ho
                        cases op with
                        | «begin» | settle => exact .inl (.inl trivial)
                        | give k' gs' at_ τ' x' =>
                            obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls
                            · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                        | get k' g' at_ τ' =>
                            obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls
                            · exact liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                        | own gk hs' at_ ins' pl' τ' =>
                            obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl (.inl trivial)
                            · exact liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                        | hear gk ow' at_ τ' =>
                            obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
                            · exact liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                      split at h
                      · cases samplesKey with
                        | none => cases h; exact ⟨ihEmP, ihEmV, ihEmS, hStepP, hStepV⟩
                        | some sKey =>
                            dsimp only at h
                            cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                            | none => rw [hS] at h; cases h
                            | some sRef =>
                                rw [hS] at h; cases h
                                refine ⟨ihEmP, ihEmV, fun c hc => ?_, hStepP, hStepV⟩
                                rcases List.mem_cons.mp hc with rfl | hm
                                · apply proverSampleClause_emits_any M
                                · exact ihEmS c hm
                      · cases h; exact ⟨ihEmP, ihEmV, ihEmS, hStepP, hStepV⟩
                    · cases h
              | request svc =>
                  dsimp only at h
                  split at h
                  · rename_i hReq
                    cases h
                    refine ⟨ihEmP, ihEmV, ihEmS, ?_, ?_⟩
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl (.inl trivial)
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftRestP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftRestP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; exact .inl (.inl trivial)
                          · exact liftRestP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            rcases hReq.1 with hEqO | hNotIn
                            · exact absurd hEqO hNeO
                            · exact absurd hrIn hNotIn
                          · exact liftRestP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl (.inl trivial)
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; exact .inl (.inl trivial)
                          · exact liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            rcases hReq.2 with hEqO | hNotIn
                            · exact absurd hEqO hNeO
                            · exact absurd hrIn hNotIn
                          · exact liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                  · cases h

private theorem buildIdealVerifierClauses_go_covers {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {serviceKey : Key} {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ k e, es[k]? = some e → events[idx + k]? = some e) →
      ∀ {cV : List (Clause V a.program.headers verifier stateTy)},
      buildIdealVerifierClauses.go a suite stateTy unitTy absorbRef serviceKey prover verifier
        declKey events idx es = .ok cV →
      (∀ c ∈ cV, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (LayoutInputV M prover verifier events) c) ∧
      (∀ op, ROp.MatchesShape M verifier es op →
        LayoutInputV M prover verifier events op ∨ ∃ c ∈ cV, ClauseMatches M c op)
  | _, [], _, _, h => by
      cases h
      refine ⟨(fun _ hc => nomatch hc), fun op ho => ?_⟩
      cases op with
      | «begin» | settle => exact .inl (.inl trivial)
      | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
  | idx, e :: rest, hSuf, cV, h => by
      unfold buildIdealVerifierClauses.go at h
      have hSufRest : ∀ k e', rest[k]? = some e' → events[(idx + 1) + k]? = some e' := by
        intro k e' hk
        have := hSuf (k + 1) e' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 e rfl
      have hMem : e ∈ events := List.mem_of_getElem? hIdx
      cases hRec : buildIdealVerifierClauses.go a suite stateTy unitTy absorbRef serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihEmV, ihCovV⟩ := buildIdealVerifierClauses_go_covers hNe (idx + 1) rest hSufRest hRec
          have liftRestV : ∀ op, (∃ e' ∈ rest, ROp.MatchesShapeEvent M verifier e' op) →
              LayoutInputV M prover verifier events op ∨ ∃ c ∈ vRest, ClauseMatches M c op := by
            intro op ho
            apply ihCovV op
            cases op with
            | «begin» | settle => trivial
            | give | get | own | hear => exact ho
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPVFlow
                cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    refine ⟨?_, ?_⟩
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · intro op hMatch st
                        generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm)
                          (ROp.payload M op) = args
                        cases args
                        show ((verifierAbsorbClause verifier prover e.site kind (msgLabel e.site)
                          (msgLabel_bytes e.site) encRef absorbRef).code.denote
                          (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                          (ROp.occurrence M op).path
                          (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith
                            M (fun _ _ => True) (LayoutInputV M prover verifier events) (fun _ => True) (fun _ => True)
                        rw [verifierAbsorbClause_denote]
                        dsimp only [roleSem, verifierAbsorbClause, Clause.site, List.cons_append, List.nil_append]
                        refine ⟨.inr (.inl ⟨e, hMem, rfl, (site_from_match hMatch.1).symm, rfl,
                          getters, hPVFlow.2, hPVFlow.1 ▸ hCls⟩), fun _ _ => ?_⟩
                        rw [Process.safeWith_bind]
                        refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => ?_)
                          (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
                        rw [Process.safeWith_map]
                        exact liftLocal_safeWith_any M id _
                      · exact ihEmV c hm
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl (.inl trivial)
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; exact absurd hPVFlow.1.symm hNe
                          · rcases liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            exact .inr ⟨_, List.mem_cons_self, hSite, by dsimp only [verifierAbsorbClause, ROp.part]; rw [hPVFlow.1],
                              rfl, by cases hTy; rfl⟩
                          · rcases liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · rcases liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · rcases liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                            · exact .inl hL
                            · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
              · split at h
                · rename_i hOut
                  cases h
                  refine ⟨ihEmV, fun op ho => ?_⟩
                  cases op with
                  | «begin» | settle => exact .inl (.inl trivial)
                  | give k' gs' at_ τ' x' =>
                      obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.2.1
                      · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                  | get k' g' at_ τ' =>
                      obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; exact absurd hrIn hOut.2.2.2
                      · exact liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                  | own gk hs' at_ ins' pl' τ' =>
                      obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · exact liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                  | hear gk ow' at_ τ' =>
                      obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · exact liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hIns : sig.ins with
                          | cons _ _ => rw [hIns] at h; cases h
                          | nil =>
                              rw [hIns] at h; dsimp only at h
                              cases hEnc : findSuiteEncode a suite unitTy e.τ with
                              | none => rw [hEnc] at h; cases h
                              | some encRef =>
                                  rw [hEnc] at h; cases h
                                  refine ⟨?_, ?_⟩
                                  · intro c hc
                                    rcases List.mem_cons.mp hc with rfl | hm
                                    · intro op hMatch st
                                      generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm)
                                        (ROp.payload M op) = args
                                      cases args
                                      show ((idealDeriveClause verifier prover e.site (.own (.coin law) hearers) []
                                        serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                        (drawLabel e.site) (drawLabel_bytes e.site) encRef absorbRef).code.denote
                                        (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                                        (ROp.occurrence M op).path
                                        (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith
                                          M (fun _ _ => True) (LayoutInputV M prover verifier events) (fun _ => True) (fun _ => True)
                                      rw [idealDeriveClause_denote_nil]
                                      dsimp only [roleSem, idealDeriveClause, Clause.site, List.cons_append, List.nil_append]
                                      refine ⟨.inl trivial, fun _ _ => ?_⟩
                                      refine ⟨.inr (.inr ⟨idx, e, hIdx, rfl,
                                        site_told_from_match hMatch.1, rfl, law, hearers,
                                        hCoin.1 ▸ hCls, hCoin.2⟩), fun _ _ => ?_⟩
                                      rw [Process.safeWith_bind]
                                      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                                        (fun _ _ => ?_) (fun _ _ => trivial) (liftLocal_safeWith_any M id _)
                                      rw [Process.safeWith_map]
                                      exact liftLocal_safeWith_any M id _
                                    · exact ihEmV c hm
                                  · intro op ho
                                    cases op with
                                    | «begin» | settle => exact .inl (.inl trivial)
                                    | give k' gs' at_ τ' x' =>
                                        obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                                        rcases List.mem_cons.mp he' with rfl | hmem
                                        · rw [hCls] at hECls; cases hECls
                                        · rcases liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩ with hL | ⟨c, hc, hm⟩
                                          · exact .inl hL
                                          · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                    | get k' g' at_ τ' =>
                                        obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                                        rcases List.mem_cons.mp he' with rfl | hmem
                                        · rw [hCls] at hECls; cases hECls
                                        · rcases liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                                          · exact .inl hL
                                          · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                    | own gk hs' at_ ins' pl' τ' =>
                                        obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                                        rcases List.mem_cons.mp he' with rfl | hmem
                                        · rw [hCls] at hECls; cases hECls
                                          have hInsEq : ins' = [] := by
                                            obtain ⟨s, hsLaw, hsIns, _⟩ := hTyped
                                            rw [hLaw] at hsLaw; cases hsLaw
                                            rw [← hsIns, hIns]
                                          exact .inr ⟨_, List.mem_cons_self, hSite, rfl,
                                            by cases hInsEq; rfl, by cases hTy; rfl⟩
                                        · rcases liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩ with hL | ⟨c, hc, hm⟩
                                          · exact .inl hL
                                          · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                                    | hear gk ow' at_ τ' =>
                                        obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                                        rcases List.mem_cons.mp he' with rfl | hmem
                                        · rw [hCls] at hECls; cases hECls; exact absurd hCoin.1 hNeO
                                        · rcases liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩ with hL | ⟨c, hc, hm⟩
                                          · exact .inl hL
                                          · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hm⟩
                        · cases h
                  · split at h
                    · rename_i hNil
                      cases h
                      refine ⟨ihEmV, fun op ho => ?_⟩
                      cases op with
                      | «begin» | settle => exact .inl (.inl trivial)
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl (.inl trivial)
                          · exact liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
                          · exact liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · rename_i hReq
                    cases h
                    refine ⟨ihEmV, fun op ho => ?_⟩
                    cases op with
                    | «begin» | settle => exact .inl (.inl trivial)
                    | give k' gs' at_ τ' x' =>
                        obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                    | get k' g' at_ τ' =>
                        obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · exact liftRestV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                    | own gk hs' at_ ins' pl' τ' =>
                        obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls; exact .inl (.inl trivial)
                        · exact liftRestV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                    | hear gk ow' at_ τ' =>
                        obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                          rcases hReq.2 with hEqO | hNotIn
                          · exact absurd hEqO hNeO
                          · exact absurd hrIn hNotIn
                        · exact liftRestV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                  · cases h

private theorem checkAuthoredEvents_covers {a : Admitted V} {prover verifier : Role}
    (hNe : prover ≠ verifier) {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (es : List (ShapeEvent V)), (∀ e ∈ es, e ∈ events) →
      {cS : List (Clause V a.program.headers prover .nat)} →
      checkAuthoredEvents a prover verifier samplesKey declKey es = .ok cS →
      (∀ c ∈ cS, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (ROp.MatchesShape M prover events) c) ∧
      (∀ op, ROp.MatchesShape M prover es op → LayoutInputP M prover verifier events op) ∧
      (∀ op, ROp.MatchesShape M verifier es op → LayoutInputV M prover verifier events op)
  | [], _, _, h => by
      cases h
      refine ⟨(fun _ hc => nomatch hc), ?_, ?_⟩
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl trivial
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl trivial
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
  | e :: rest, hSub, cS, h => by
      unfold checkAuthoredEvents at h
      have hSubRest : ∀ e' ∈ rest, e' ∈ events := fun e' he' => hSub e' (List.mem_cons_of_mem _ he')
      have hMem : e ∈ events := hSub e List.mem_cons_self
      cases hRec : checkAuthoredEvents a prover verifier samplesKey declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihS, ihP, ihV⟩ := checkAuthoredEvents_covers hNe rest hSubRest hRec
          have liftP : ∀ op, (∃ e' ∈ rest, ROp.MatchesShapeEvent M prover e' op) →
              LayoutInputP M prover verifier events op := fun op ho => by
            apply ihP op
            cases op with
            | «begin» | settle => trivial
            | give | get | own | hear => exact ho
          have liftV : ∀ op, (∃ e' ∈ rest, ROp.MatchesShapeEvent M verifier e' op) →
              LayoutInputV M prover verifier events op := fun op ho => by
            apply ihV op
            cases op with
            | «begin» | settle => trivial
            | give | get | own | hear => exact ho
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hFl
                cases h
                refine ⟨ihS, ?_, ?_⟩
                · intro op ho
                  cases op with
                  | «begin» | settle => exact .inl trivial
                  | give k' gs' at_ τ' x' =>
                      obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                        rcases hFl with ⟨_, hVin⟩ | ⟨hNotP, _, _, _⟩
                        · exact .inr (.inl ⟨e', hMem, hSite, hTy, hCls, hVin⟩)
                        · exact absurd rfl hNotP
                      · exact liftP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                  | get k' g' at_ τ' =>
                      obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                        rcases hFl with ⟨hEqP, _⟩ | ⟨_, _, hNotIn, _⟩
                        · exact absurd hEqP hNeG
                        · exact absurd hrIn hNotIn
                      · exact liftP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                  | own gk hs' at_ ins' pl' τ' =>
                      obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · exact liftP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                  | hear gk ow' at_ τ' =>
                      obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · exact liftP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                · intro op ho
                  cases op with
                  | «begin» | settle => exact .inl trivial
                  | give k' gs' at_ τ' x' =>
                      obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                        rcases hFl with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
                        · exact absurd hEqP.symm hNe
                        · exact absurd rfl hNotV
                      · exact liftV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                  | get k' g' at_ τ' =>
                      obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                        rcases hFl with ⟨hEqP, hVin⟩ | ⟨_, _, _, hNotIn⟩
                        · exact .inr (.inl ⟨e', hMem, hEqP, hSite, hTy, getters, hVin, hEqP ▸ hCls⟩)
                        · exact absurd hrIn hNotIn
                      · exact liftV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                  | own gk hs' at_ ins' pl' τ' =>
                      obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · exact liftV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                  | hear gk ow' at_ τ' =>
                      obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · exact liftV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
              · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hNil
                    have hStepP : ∀ op, ROp.MatchesShape M prover (e :: rest) op →
                        LayoutInputP M prover verifier events op := by
                      intro op ho
                      cases op with
                      | «begin» | settle => exact .inl trivial
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl trivial
                          · exact liftP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
                          · exact liftP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                    have hStepV : ∀ op, ROp.MatchesShape M verifier (e :: rest) op →
                        LayoutInputV M prover verifier events op := by
                      intro op ho
                      cases op with
                      | «begin» | settle => exact .inl trivial
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl trivial
                          · exact liftV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
                          · exact liftV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                    split at h
                    · cases samplesKey with
                      | none => cases h; exact ⟨ihS, hStepP, hStepV⟩
                      | some sKey =>
                          dsimp only at h
                          cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                          | none => rw [hS] at h; cases h
                          | some sRef =>
                              rw [hS] at h; cases h
                              refine ⟨fun c hc => ?_, hStepP, hStepV⟩
                              rcases List.mem_cons.mp hc with rfl | hm
                              · apply proverSampleClause_emits_any M
                              · exact ihS c hm
                    · cases h; exact ⟨ihS, hStepP, hStepV⟩
                  · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · rename_i hReq
                    cases h
                    refine ⟨ihS, ?_, ?_⟩
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl trivial
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftP (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; exact .inl trivial
                          · exact liftP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            rcases hReq.1 with hEqO | hNotIn
                            · exact absurd hEqO hNeO
                            · exact absurd hrIn hNotIn
                          · exact liftP (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl trivial
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                          · exact liftV (.get k' g' at_ τ') ⟨e', hmem, hNeG, hSite, hTy, gs', hrIn, hECls⟩
                      | own gk hs' at_ ins' pl' τ' =>
                          obtain ⟨e', he', hSite, hTy, hECls, hTyped⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; exact .inl trivial
                          · exact liftV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            rcases hReq.2 with hEqO | hNotIn
                            · exact absurd hEqO hNeO
                            · exact absurd hrIn hNotIn
                          · exact liftV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                  · cases h

private theorem buildStreamingLayoutClauses_go_covers {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      (∀ c ∈ pCs, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (ROp.IsClosed M) c) ∧
      (∀ c ∈ vCs, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (ROp.IsClosed M) c) ∧
      (∀ e ∈ es, ∀ kind getters (at_ : Occurrence) τ x,
        e.site = at_.site → e.τ = τ → e.cls = .flow kind prover getters → verifier ∈ getters →
        ∃ c ∈ pCs, ClauseMatches M c (.give kind getters at_ τ x)) ∧
      (∀ e ∈ es, ∀ kind getters (at_ : Occurrence) τ,
        e.site = at_.site → e.τ = τ → e.cls = .flow kind prover getters → verifier ∈ getters →
        ∃ c ∈ vCs, ClauseMatches M c (.get kind prover at_ τ)) ∧
      (∀ (k : Nat) (e : ShapeEvent V), es[k]? = some e →
        ∀ law hearers (at_ : Occurrence) τ x,
        e.cls = .given (.coin law) verifier hearers → prover ∈ hearers → e.τ = τ →
        at_.site = ⟨e.site.through, drawToldKey events (idx + k)⟩ →
        (∃ c ∈ pCs, ClauseMatches M c (.give .message [verifier] at_ τ x)) ∧
        (∃ c ∈ vCs, ClauseMatches M c (.give .message [prover] at_ τ x)))
  | _, [], _, _, h => by
      cases h
      exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ _ hk => by simp at hk)⟩
  | idx, e :: rest, pCs, vCs, h => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihEmP, ihEmV, ihFP, ihFV, ihTold⟩ :=
            buildStreamingLayoutClauses_go_covers (idx + 1) rest hRec
          have ihToldShift : ∀ k e', rest[k]? = some e' →
              ∀ law hearers (at_ : Occurrence) τ x,
              e'.cls = .given (.coin law) verifier hearers → prover ∈ hearers → e'.τ = τ →
              at_.site = ⟨e'.site.through, drawToldKey events (idx + (k + 1))⟩ →
              (∃ c ∈ pair.1, ClauseMatches M c (.give .message [verifier] at_ τ x)) ∧
              (∃ c ∈ pair.2, ClauseMatches M c (.give .message [prover] at_ τ x)) := by
            intro k e' hk law hearers at_ τ x hC hIn hT hS
            exact ihTold k e' hk law hearers at_ τ x hC hIn hT
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hS)
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · cases h
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · intro c hc
                    rcases List.mem_cons.mp hc with rfl | hm
                    · apply layoutClause_emits_any_pWrite M
                    · exact ihEmP c hm
                  · intro c hc
                    rcases List.mem_cons.mp hc with rfl | hm
                    · apply layoutClause_emits_any_vRead M
                    · exact ihEmV c hm
                  · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                    rcases List.mem_cons.mp he' with rfl | hm
                    · rw [hCls] at hECls; cases hECls
                      exact ⟨_, List.mem_cons_self, hSite, rfl, by cases hTy; rfl, rfl⟩
                    · obtain ⟨c, hc, hcm⟩ := ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                      exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                  · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                    rcases List.mem_cons.mp he' with rfl | hm
                    · rw [hCls] at hECls; cases hECls
                      exact ⟨_, List.mem_cons_self, hSite, rfl, rfl, by cases hTy; rfl⟩
                    · obtain ⟨c, hc, hcm⟩ := ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                      exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                  · intro k e' hk law hearers at_ τ' x' hECls hIn hTy hS
                    cases k with
                    | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                    | succ k' =>
                        obtain ⟨⟨cP, hcP, hmP⟩, ⟨cV, hcV, hmV⟩⟩ :=
                          ihToldShift k' e' hk law hearers at_ τ' x' hECls hIn hTy hS
                        exact ⟨⟨cP, List.mem_cons_of_mem _ hcP, hmP⟩,
                               ⟨cV, List.mem_cons_of_mem _ hcV, hmV⟩⟩
              · rename_i hNotPV
                cases h
                refine ⟨ihEmP, ihEmV, ?_, ?_, ?_⟩
                · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                  rcases List.mem_cons.mp he' with rfl | hm
                  · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                  · exact ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                  rcases List.mem_cons.mp he' with rfl | hm
                  · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                  · exact ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                · intro k e' hk law hearers at_ τ' x' hECls hIn hTy hS
                  cases k with
                  | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                  | succ k' => exact ihToldShift k' e' hk law hearers at_ τ' x' hECls hIn hTy hS
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨?_, ?_, ?_, ?_, ?_⟩
                        · intro c hc
                          rcases List.mem_cons.mp hc with rfl | hm
                          · apply layoutClause_emits_any_pWrite M
                          · exact ihEmP c hm
                        · intro c hc
                          rcases List.mem_cons.mp hc with rfl | hm
                          · apply layoutClause_emits_any_vCarry M
                          · exact ihEmV c hm
                        · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                          rcases List.mem_cons.mp he' with rfl | hm
                          · rw [hCls] at hECls; cases hECls
                          · obtain ⟨c, hc, hcm⟩ := ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                        · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                          rcases List.mem_cons.mp he' with rfl | hm
                          · rw [hCls] at hECls; cases hECls
                          · obtain ⟨c, hc, hcm⟩ := ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                        · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                          cases k with
                          | zero =>
                              simp at hk; subst hk
                              exact ⟨⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                                      by cases hTy; rfl, rfl⟩,
                                     ⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                                      by cases hTy; rfl, rfl⟩⟩
                          | succ k' =>
                              obtain ⟨⟨cP, hcP, hmP⟩, ⟨cV, hcV, hmV⟩⟩ :=
                                ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                              exact ⟨⟨cP, List.mem_cons_of_mem _ hcP, hmP⟩,
                                     ⟨cV, List.mem_cons_of_mem _ hcV, hmV⟩⟩
                    · cases h
                      refine ⟨?_, ?_, ?_, ?_, ?_⟩
                      · intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutClause_emits_any_drop M
                        · exact ihEmP c hm
                      · intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutClause_emits_any_drop M
                        · exact ihEmV c hm
                      · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                        rcases List.mem_cons.mp he' with rfl | hm
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨c, hc, hcm⟩ := ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                          exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                      · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                        rcases List.mem_cons.mp he' with rfl | hm
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨c, hc, hcm⟩ := ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                          exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                      · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                        cases k with
                        | zero =>
                            simp at hk; subst hk
                            exact ⟨⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                                    by cases hTy; rfl, rfl⟩,
                                   ⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                                    by cases hTy; rfl, rfl⟩⟩
                        | succ k' =>
                            obtain ⟨⟨cP, hcP, hmP⟩, ⟨cV, hcV, hmV⟩⟩ :=
                              ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                            exact ⟨⟨cP, List.mem_cons_of_mem _ hcP, hmP⟩,
                                   ⟨cV, List.mem_cons_of_mem _ hcV, hmV⟩⟩
                  · rename_i hNotCoin
                    cases h
                    refine ⟨ihEmP, ihEmV, ?_, ?_, ?_⟩
                    · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                      rcases List.mem_cons.mp he' with rfl | hm
                      · rw [hCls] at hECls; cases hECls
                      · exact ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                    · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                      rcases List.mem_cons.mp he' with rfl | hm
                      · rw [hCls] at hECls; cases hECls
                      · exact ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                    · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                      cases k with
                      | zero =>
                          simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                          exact absurd ⟨rfl, hIn⟩ hNotCoin
                      | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
              | request _ =>
                  cases h
                  refine ⟨ihEmP, ihEmV, ?_, ?_, ?_⟩
                  · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                    rcases List.mem_cons.mp he' with rfl | hm
                    · rw [hCls] at hECls; cases hECls
                    · exact ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                  · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                    rcases List.mem_cons.mp he' with rfl | hm
                    · rw [hCls] at hECls; cases hECls
                    · exact ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                  · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                    cases k with
                    | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                    | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS

private theorem collectCompactWire_covers {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {ws : List (WireSpec V a.program.headers.fns unitTy)}
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))},
      collectCompactWire a layout unitTy prover verifier declKey events idx es = .ok (ws, pCs) →
      (∀ c ∈ pCs, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (ROp.IsClosed M) c) ∧
      (∀ e ∈ es, ∀ kind getters (at_ : Occurrence) τ x,
        e.site = at_.site → e.τ = τ → e.cls = .flow kind prover getters → verifier ∈ getters →
        ∃ c ∈ pCs, ClauseMatches M c (.give kind getters at_ τ x)) ∧
      (∀ (k : Nat) (e : ShapeEvent V), es[k]? = some e →
        ∀ law hearers (at_ : Occurrence) τ x,
        e.cls = .given (.coin law) verifier hearers → prover ∈ hearers → e.τ = τ →
        at_.site = ⟨e.site.through, drawToldKey events (idx + k)⟩ →
        ∃ c ∈ pCs, ClauseMatches M c (.give .message [verifier] at_ τ x))
  | _, [], _, _, h => by
      cases h
      exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ _ hk => by simp at hk)⟩
  | idx, e :: rest, ws, pCs, h => by
      unfold collectCompactWire at h
      cases hRec : collectCompactWire a layout unitTy prover verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihEmP, ihFP, ihTold⟩ := collectCompactWire_covers (idx + 1) rest hRec
          have ihToldShift : ∀ k e', rest[k]? = some e' →
              ∀ law hearers (at_ : Occurrence) τ x,
              e'.cls = .given (.coin law) verifier hearers → prover ∈ hearers → e'.τ = τ →
              at_.site = ⟨e'.site.through, drawToldKey events (idx + (k + 1))⟩ →
              ∃ c ∈ pair.2, ClauseMatches M c (.give .message [verifier] at_ τ x) := by
            intro k e' hk law hearers at_ τ x hC hIn hT hS
            exact ihTold k e' hk law hearers at_ τ x hC hIn hT
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hS)
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some _ =>
                    rw [hLk] at h; cases h
                    refine ⟨?_, ?_, ?_⟩
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · apply layoutClause_emits_any_drop M
                      · exact ihEmP c hm
                    · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                      rcases List.mem_cons.mp he' with rfl | hm
                      · rw [hCls] at hECls; cases hECls
                        exact ⟨_, List.mem_cons_self, hSite, rfl, by cases hTy; rfl, rfl⟩
                      · obtain ⟨c, hc, hcm⟩ := ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                        exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                    · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                      cases k with
                      | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                      | succ k' =>
                          obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                          exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                | none =>
                    rw [hLk] at h; dsimp only at h
                    cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      refine ⟨?_, ?_, ?_⟩
                      · intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutClause_emits_any_pWrite M
                        · exact ihEmP c hm
                      · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                        rcases List.mem_cons.mp he' with rfl | hm
                        · rw [hCls] at hECls; cases hECls
                          exact ⟨_, List.mem_cons_self, hSite, rfl, by cases hTy; rfl, rfl⟩
                        · obtain ⟨c, hc, hcm⟩ := ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                          exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                      · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                        cases k with
                        | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                        | succ k' =>
                            obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
              · rename_i hNotPV
                cases h
                refine ⟨ihEmP, ?_, ?_⟩
                · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                  rcases List.mem_cons.mp he' with rfl | hm
                  · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                  · exact ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                  cases k with
                  | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                  | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                        simp only [hW, hR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨?_, ?_, ?_⟩
                        · intro c hc
                          rcases List.mem_cons.mp hc with rfl | hm
                          · apply layoutClause_emits_any_pWrite M
                          · exact ihEmP c hm
                        · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                          rcases List.mem_cons.mp he' with rfl | hm
                          · rw [hCls] at hECls; cases hECls
                          · obtain ⟨c, hc, hcm⟩ := ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                        · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                          cases k with
                          | zero =>
                              simp at hk; subst hk
                              exact ⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                                by cases hTy; rfl, rfl⟩
                          | succ k' =>
                              obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                              exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                    · cases h
                      refine ⟨?_, ?_, ?_⟩
                      · intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutClause_emits_any_drop M
                        · exact ihEmP c hm
                      · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                        rcases List.mem_cons.mp he' with rfl | hm
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨c, hc, hcm⟩ := ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                          exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                      · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                        cases k with
                        | zero =>
                            simp at hk; subst hk
                            exact ⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                              by cases hTy; rfl, rfl⟩
                        | succ k' =>
                            obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                  · rename_i hNotCoin
                    cases h
                    refine ⟨ihEmP, ?_, ?_⟩
                    · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                      rcases List.mem_cons.mp he' with rfl | hm
                      · rw [hCls] at hECls; cases hECls
                      · exact ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                    · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                      cases k with
                      | zero =>
                          simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                          exact absurd ⟨rfl, hIn⟩ hNotCoin
                      | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
              | request _ =>
                  cases h
                  refine ⟨ihEmP, ?_, ?_⟩
                  · intro e' he' k' gs' at_ τ' x' hSite hTy hECls hVin
                    rcases List.mem_cons.mp he' with rfl | hm
                    · rw [hCls] at hECls; cases hECls
                    · exact ihFP e' hm k' gs' at_ τ' x' hSite hTy hECls hVin
                  · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                    cases k with
                    | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                    | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS

private theorem buildCompactVClauses_covers {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {stmtTys : List V.Ty} {wireSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {vCs : List (Clause V a.program.headers verifier
        (.tuple (tysOfList (stmtTys ++ wireSpecs.map (·.ty)))))},
      buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs
        htfree idx es = .ok vCs →
      (∀ c ∈ vCs, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (ROp.IsClosed M) c) ∧
      (∀ e ∈ es, ∀ kind getters (at_ : Occurrence) τ,
        e.site = at_.site → e.τ = τ → e.cls = .flow kind prover getters → verifier ∈ getters →
        ∃ c ∈ vCs, ClauseMatches M c (.get kind prover at_ τ)) ∧
      (∀ (k : Nat) (e : ShapeEvent V), es[k]? = some e →
        ∀ law hearers (at_ : Occurrence) τ x,
        e.cls = .given (.coin law) verifier hearers → prover ∈ hearers → e.τ = τ →
        at_.site = ⟨e.site.through, drawToldKey events (idx + k)⟩ →
        ∃ c ∈ vCs, ClauseMatches M c (.give .message [prover] at_ τ x))
  | _, [], _, h => by
      cases h
      exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ _ hk => by simp at hk)⟩
  | idx, e :: rest, vCs, h => by
      unfold buildCompactVClauses at h
      cases hRec : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys
          wireSpecs htfree (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihEmV, ihFV, ihTold⟩ := buildCompactVClauses_covers (idx + 1) rest hRec
          have ihToldShift : ∀ k e', rest[k]? = some e' →
              ∀ law hearers (at_ : Occurrence) τ x,
              e'.cls = .given (.coin law) verifier hearers → prover ∈ hearers → e'.τ = τ →
              at_.site = ⟨e'.site.through, drawToldKey events (idx + (k + 1))⟩ →
              ∃ c ∈ vRest, ClauseMatches M c (.give .message [prover] at_ τ x) := by
            intro k e' hk law hearers at_ τ x hC hIn hT hS
            exact ihTold k e' hk law hearers at_ τ x hC hIn hT
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hS)
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; dsimp only at h
                    cases hRecFn : findSafeFnRef a recKey
                        (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                    | none => rw [hRecFn] at h; cases h
                    | some recRef =>
                        rw [hRecFn] at h; cases h
                        refine ⟨?_, ?_, ?_⟩
                        · intro c hc
                          rcases List.mem_cons.mp hc with rfl | hm
                          · apply compactRecoverClause_emits_any M
                          · exact ihEmV c hm
                        · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                          rcases List.mem_cons.mp he' with rfl | hm
                          · rw [hCls] at hECls; cases hECls
                            exact ⟨_, List.mem_cons_self, hSite, rfl, rfl, by cases hTy; rfl⟩
                          · obtain ⟨c, hc, hcm⟩ := ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                        · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                          cases k with
                          | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                          | succ k' =>
                              obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                              exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                | none =>
                    rw [hLk] at h; dsimp only at h
                    cases hWM : findWireMember e.site e.τ wireSpecs with
                    | none => rw [hWM] at h; cases h
                    | some mWire =>
                        rw [hWM] at h; cases h
                        refine ⟨?_, ?_, ?_⟩
                        · intro c hc
                          rcases List.mem_cons.mp hc with rfl | hm
                          · apply compactReadSlotClause_emits_any M
                          · exact ihEmV c hm
                        · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                          rcases List.mem_cons.mp he' with rfl | hm
                          · rw [hCls] at hECls; cases hECls
                            exact ⟨_, List.mem_cons_self, hSite, rfl, rfl, by cases hTy; rfl⟩
                          · obtain ⟨c, hc, hcm⟩ := ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                        · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                          cases k with
                          | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                          | succ k' =>
                              obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                              exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
              · rename_i hNotPV
                cases h
                refine ⟨ihEmV, ?_, ?_⟩
                · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                  rcases List.mem_cons.mp he' with rfl | hm
                  · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                  · exact ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                  cases k with
                  | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                  | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hWM : findWireMember ⟨e.site.through, drawToldKey events idx⟩ e.τ wireSpecs <;>
                      cases hEq : findLayoutEqual a layout.module e.τ <;>
                        simp only [hWM, hEq] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨?_, ?_, ?_⟩
                        · intro c hc
                          rcases List.mem_cons.mp hc with rfl | hm
                          · apply compactCompareClause_emits_any M
                          · exact ihEmV c hm
                        · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                          rcases List.mem_cons.mp he' with rfl | hm
                          · rw [hCls] at hECls; cases hECls
                          · obtain ⟨c, hc, hcm⟩ := ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                        · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                          cases k with
                          | zero =>
                              simp at hk; subst hk
                              exact ⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                                by cases hTy; rfl, rfl⟩
                          | succ k' =>
                              obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                              exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                    · cases h
                      refine ⟨?_, ?_, ?_⟩
                      · intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply layoutClause_emits_any_drop M
                        · exact ihEmV c hm
                      · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                        rcases List.mem_cons.mp he' with rfl | hm
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨c, hc, hcm⟩ := ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                          exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                      · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                        cases k with
                        | zero =>
                            simp at hk; subst hk
                            exact ⟨_, List.mem_cons_self, by rw [Nat.add_zero] at hS; exact hS.symm, rfl,
                              by cases hTy; rfl, rfl⟩
                        | succ k' =>
                            obtain ⟨c, hc, hcm⟩ := ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                            exact ⟨c, List.mem_cons_of_mem _ hc, hcm⟩
                  · rename_i hNotCoin
                    cases h
                    refine ⟨ihEmV, ?_, ?_⟩
                    · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                      rcases List.mem_cons.mp he' with rfl | hm
                      · rw [hCls] at hECls; cases hECls
                      · exact ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                    · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                      cases k with
                      | zero =>
                          simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                          exact absurd ⟨rfl, hIn⟩ hNotCoin
                      | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS
              | request _ =>
                  cases h
                  refine ⟨ihEmV, ?_, ?_⟩
                  · intro e' he' k' gs' at_ τ' hSite hTy hECls hVin
                    rcases List.mem_cons.mp he' with rfl | hm
                    · rw [hCls] at hECls; cases hECls
                    · exact ihFV e' hm k' gs' at_ τ' hSite hTy hECls hVin
                  · intro k e' hk law' hs' at_ τ' x' hECls hIn hTy hS
                    cases k with
                    | zero => simp at hk; subst hk; rw [hCls] at hECls; cases hECls
                    | succ k' => exact ihToldShift k' e' hk law' hs' at_ τ' x' hECls hIn hTy hS

private theorem buildLayoutLayers_covers {a : Admitted V} {entry : ProtocolHeader V}
    {layout : Layout} {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins}
    (h : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    Handler.Covers M
      (Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) layP)
      (LayoutInputP M prover verifier events) (ROp.IsClosed M) ∧
    Handler.Covers M
      (Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) layV)
      (LayoutInputV M prover verifier events) (ROp.IsClosed M) := by
  unfold buildLayoutLayers at h
  cases hUnit : findLayoutUnit a layout.module with
  | none => rw [hUnit] at h; cases h
  | some uPair =>
      rw [hUnit] at h; dsimp only at h
      split at h
      · cases hStr : buildStreamingLayoutClauses a layout uPair.1 uPair.2.down prover verifier
            declKey events with
        | error _ => rw [hStr] at h; cases h
        | ok cs =>
            rw [hStr] at h; cases h
            obtain ⟨hEmP, hEmV, hFP, hFV, hTold⟩ :=
              buildStreamingLayoutClauses_go_covers M 0 events hStr
            constructor
            · intro op s ho
              apply clause_answer_covers M _ _ _ hEmP op s
              rcases ho with hCl | ⟨e, he, hFl⟩ | ⟨idx, e, hIdx, hTd⟩
              · exact .inl hCl
              · cases op with
                | give k gs at_ τ x =>
                    exact .inr (hFP e he k gs at_ τ x hFl.1 hFl.2.1 hFl.2.2.1 hFl.2.2.2)
                | get | own | hear | «begin» | settle => exact False.elim hFl
              · cases op with
                | give k gs at_ τ x =>
                    cases k with
                    | message =>
                        obtain ⟨hGs, hSite, hTy, law, hearers, hCls, hIn⟩ := hTd
                        subst hGs
                        exact .inr (hTold idx e hIdx law hearers at_ τ x hCls hIn hTy
                          (by simpa using hSite)).1
                    | rows | opening => exact False.elim hTd
                | get | own | hear | «begin» | settle => exact False.elim hTd
            · intro op s ho
              apply clause_answer_covers M _ _ _ hEmV op s
              rcases ho with hCl | ⟨e, he, hFl⟩ | ⟨idx, e, hIdx, hTd⟩
              · exact .inl hCl
              · cases op with
                | get k g at_ τ =>
                    obtain ⟨hG, hSite, hTy, gs, hVin, hCls⟩ := hFl
                    subst hG
                    exact .inr (hFV e he k gs at_ τ hSite hTy hCls hVin)
                | give | own | hear | «begin» | settle => exact False.elim hFl
              · cases op with
                | give k gs at_ τ x =>
                    cases k with
                    | message =>
                        obtain ⟨hGs, hSite, hTy, law, hearers, hCls, hIn⟩ := hTd
                        subst hGs
                        exact .inr (hTold idx e hIdx law hearers at_ τ x hCls hIn hTy
                          (by simpa using hSite)).2
                    | rows | opening => exact False.elim hTd
                | get | own | hear | «begin» | settle => exact False.elim hTd
      · unfold buildCompactLayoutLayers at h
        cases hCW : collectCompactWire a layout uPair.1 prover verifier declKey events 0 events with
        | error _ => rw [hCW] at h; cases h
        | ok cw =>
            rw [hCW] at h; dsimp only [bind, Except.bind] at h
            split at h
            · cases hVC : buildCompactVClauses a layout uPair.1 prover verifier declKey events _ cw.1
                  _ 0 events with
              | error _ => rw [hVC] at h; cases h
              | ok vcs =>
                  rw [hVC] at h; cases h
                  obtain ⟨hEmP, hFP, hToldP⟩ := collectCompactWire_covers M 0 events hCW
                  obtain ⟨hEmV, hFV, hToldV⟩ := buildCompactVClauses_covers M 0 events hVC
                  constructor
                  · intro op s ho
                    apply clause_answer_covers M _ _ _ hEmP op s
                    rcases ho with hCl | ⟨e, he, hFl⟩ | ⟨idx, e, hIdx, hTd⟩
                    · exact .inl hCl
                    · cases op with
                      | give k gs at_ τ x =>
                          exact .inr (hFP e he k gs at_ τ x hFl.1 hFl.2.1 hFl.2.2.1 hFl.2.2.2)
                      | get | own | hear | «begin» | settle => exact False.elim hFl
                    · cases op with
                      | give k gs at_ τ x =>
                          cases k with
                          | message =>
                              obtain ⟨hGs, hSite, hTy, law, hearers, hCls, hIn⟩ := hTd
                              subst hGs
                              exact .inr (hToldP idx e hIdx law hearers at_ τ x hCls hIn hTy
                                (by simpa using hSite))
                          | rows | opening => exact False.elim hTd
                      | get | own | hear | «begin» | settle => exact False.elim hTd
                  · intro op s ho
                    apply clause_answer_covers M _ _ _ hEmV op s
                    rcases ho with hCl | ⟨e, he, hFl⟩ | ⟨idx, e, hIdx, hTd⟩
                    · exact .inl hCl
                    · cases op with
                      | get k g at_ τ =>
                          obtain ⟨hG, hSite, hTy, gs, hVin, hCls⟩ := hFl
                          subst hG
                          exact .inr (hFV e he k gs at_ τ hSite hTy hCls hVin)
                      | give | own | hear | «begin» | settle => exact False.elim hFl
                    · cases op with
                      | give k gs at_ τ x =>
                          cases k with
                          | message =>
                              obtain ⟨hGs, hSite, hTy, law, hearers, hCls, hIn⟩ := hTd
                              subst hGs
                              exact .inr (hToldV idx e hIdx law hearers at_ τ x hCls hIn hTy
                                (by simpa using hSite))
                          | rows | opening => exact False.elim hTd
                      | get | own | hear | «begin» | settle => exact False.elim hTd
            · cases h

private theorem stack_covers_cast {a : Admitted V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V a.program.headers r₂ hdr₂.ins))
    (h : Handler.Covers M
      (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) layers)
      (ROp.MatchesShape M r₂ (hdr₂.shape.events [] id)) (ROp.IsClosed M)) :
    Handler.Covers M
      (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) (hr ▸ hHdr ▸ layers))
      (ROp.MatchesShape M r₁ (hdr₁.shape.events [] id)) (ROp.IsClosed M) :=
  cast_layer_stack_elim hHdr hr layers
    (fun hdr r ls => Handler.Covers M
      (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) ls)
      (ROp.MatchesShape M r (hdr.shape.events [] id)) (ROp.IsClosed M)) h

/-- Every non-interactive deployment covers all non-closed effects on both prover and verifier. -/
theorem deploy_coverage (enc : VocabEncoder V) {a : Admitted V} {declaration : Declaration}
    {d : Deployed V} (hDep : deploy enc a declaration = .ok d)
    (hNonInt : declaration.interactive = false) : d.Covered := by
  intro M prover verifier hRoles r hRole ins taken _ _
  rw [deployed_run_eq_runStack]
  apply runStack_closedEffects M d.admitted d.callee d.retry r (d.stack r) _ ins taken
  unfold deploy at hDep
  split at hDep
  · cases hDep
  · rename_i foundPair hFound
    dsimp only at hDep
    split at hDep
    · cases hDep
    · cases hCon : declaration.construction with
      | interactive => simp [Declaration.interactive, hCon] at hNonInt
      | authored =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · rename_i hNe
                cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples declaration.key
                    (foundPair.1.shape.events [] id) with
                | error _ => rw [hAuth] at hDep; cases hDep
                | ok sClauses =>
                    rw [hAuth] at hDep; dsimp only [bind, Except.bind] at hDep
                    cases hLO : declaration.layout with
                    | none => rw [hLO] at hDep; cases hDep
                    | some layout =>
                        rw [hLO] at hDep; dsimp only at hDep
                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                            declaration.key (foundPair.1.shape.events [] id) with
                        | error _ => rw [hLay] at hDep; cases hDep
                        | ok lays =>
                            rw [hLay] at hDep; cases hDep
                            have hRolesEq : proverAndVerifier foundPair.1 declaration = some (prover, verifier) := by
                              simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                            rw [hPV] at hRolesEq; cases hRolesEq
                            obtain ⟨hEmS, hAuthP, hAuthV⟩ :=
                              checkAuthoredEvents_covers M hNe _ (fun _ h => h) hAuth
                            obtain ⟨hLayP, hLayV⟩ := buildLayoutLayers_covers M hLay
                            have hLayP' : Handler.Covers M (Layer.handler M (Defs.fnTable M a.program.defs)
                                (Defs.rTable M a.program.defs) lays.1)
                                (ROp.MatchesShape M prover (foundPair.1.shape.events [] id)) (ROp.IsClosed M) :=
                              fun op s ho => hLayP op s (hAuthP op ho)
                            have hLayV' : Handler.Covers M (Layer.handler M (Defs.fnTable M a.program.defs)
                                (Defs.rTable M a.program.defs) lays.2)
                                (ROp.MatchesShape M verifier (foundPair.1.shape.events [] id)) (ROp.IsClosed M) :=
                              fun op s ho => hLayV op s (hAuthV op ho)
                            rcases hRole with rfl | rfl
                            · dsimp only
                              rw [dite_eq_left rfl]
                              apply stack_covers_cast M (by simp [hFound]) rfl
                              cases declaration.samples with
                              | none =>
                                  exact stack_handler_covers_cons M _ _ hLayP'
                                    (stack_handler_covers_nil M _ _ _)
                              | some _ =>
                                  have hSamp : Handler.Covers M
                                      (Layer.handler M (Defs.fnTable M a.program.defs)
                                        (Defs.rTable M a.program.defs)
                                        ({ line := .samples, state := .nat, takes := [], gives := [],
                                           clauses := sClauses, again := attemptNumAgain,
                                           start := samplesStart, finish := emptyFinish .nat } :
                                          Layer V a.program.headers r foundPair.1.ins))
                                      (ROp.MatchesShape M r (foundPair.1.shape.events [] id))
                                      (ROp.MatchesShape M r (foundPair.1.shape.events [] id)) :=
                                    fun op s ho => clause_answer_covers M _ _ _ hEmS op s (.inl ho)
                                  exact stack_handler_covers_cons M _ _ hSamp
                                    (stack_handler_covers_cons M _ _ hLayP'
                                      (stack_handler_covers_nil M _ _ _))
                            · dsimp only
                              rw [dite_eq_right (Ne.symm hNe), dite_eq_left rfl]
                              apply stack_covers_cast M (by simp [hFound]) rfl
                              exact stack_handler_covers_cons M _ _ hLayV'
                                (stack_handler_covers_nil M _ _ _)
      | derived suite sessionTag =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · rename_i hNe
                cases hLO : declaration.layout with
                | none => rw [hLO] at hDep; cases hDep
                | some layout =>
                    rw [hLO] at hDep; dsimp only at hDep
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at hDep; cases hDep
                    | some stPair =>
                        rw [hSt] at hDep; dsimp only at hDep
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at hDep; cases hDep
                        | some absPair =>
                            rw [hAb] at hDep; dsimp only at hDep
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at hDep; cases hDep
                            | ok sess =>
                                rw [hSess] at hDep; dsimp only [bind, Except.bind] at hDep
                                cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1 pv.2
                                    (.inl rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSP] at hDep; cases hDep
                                | ok stmtP =>
                                    rw [hSP] at hDep; dsimp only [bind, Except.bind] at hDep
                                    cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                        (.inr rfl) foundPair.1.ins declaration.key with
                                    | error _ => rw [hSV] at hDep; cases hDep
                                    | ok stmtV =>
                                        rw [hSV] at hDep; dsimp only [bind, Except.bind] at hDep
                                        cases hCC : buildConstructionClauses a suite stPair.1 absPair.1
                                            absPair.2 pv.1 pv.2 declaration.samples declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hCC] at hDep; cases hDep
                                        | ok cc =>
                                            rw [hCC] at hDep; dsimp only [bind, Except.bind] at hDep
                                            cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                                declaration.key (foundPair.1.shape.events [] id) with
                                            | error _ => rw [hLay] at hDep; cases hDep
                                            | ok lays =>
                                                rw [hLay] at hDep; cases hDep
                                                have hRolesEq : proverAndVerifier foundPair.1 declaration =
                                                    some (prover, verifier) := by
                                                  simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                                                rw [hPV] at hRolesEq; cases hRolesEq
                                                obtain ⟨hEmP, hEmV, hEmS, hCovP, hCovV⟩ :=
                                                  buildConstructionClauses_go_covers M hNe 0 _
                                                    (fun k e hk => by simpa using hk) hCC
                                                obtain ⟨hLayP, hLayV⟩ := buildLayoutLayers_covers M hLay
                                                rcases hRole with rfl | rfl
                                                · dsimp only
                                                  rw [dite_eq_left rfl]
                                                  apply stack_covers_cast M (by simp [hFound]) rfl
                                                  have hConP : Handler.Covers M
                                                      (Layer.handler M (Defs.fnTable M a.program.defs)
                                                        (Defs.rTable M a.program.defs)
                                                        ({ line := .construction, state := stPair.1,
                                                           takes := [], gives := [], clauses := cc.1,
                                                           again := restoreAgain stPair.1,
                                                           start := constructionStart sess.1 sess.2 stPair.2
                                                             absPair.2 stmtP,
                                                           finish := emptyFinish stPair.1 } :
                                                          Layer V a.program.headers r foundPair.1.ins))
                                                      (ROp.MatchesShape M r (foundPair.1.shape.events [] id))
                                                      (LayoutInputP M r verifier (foundPair.1.shape.events [] id)) :=
                                                    fun op s ho => clause_answer_covers M _ _ _ hEmP op s (hCovP op ho)
                                                  cases declaration.samples with
                                                  | none =>
                                                      exact stack_handler_covers_cons M _ _ hConP
                                                        (stack_handler_covers_cons M _ _ hLayP
                                                          (stack_handler_covers_nil M _ _ _))
                                                  | some _ =>
                                                      have hSamp : Handler.Covers M
                                                          (Layer.handler M (Defs.fnTable M a.program.defs)
                                                            (Defs.rTable M a.program.defs)
                                                            ({ line := .samples, state := .nat, takes := [], gives := [],
                                                               clauses := cc.2.2, again := attemptNumAgain,
                                                               start := samplesStart, finish := emptyFinish .nat } :
                                                              Layer V a.program.headers r foundPair.1.ins))
                                                          (ROp.MatchesShape M r (foundPair.1.shape.events [] id))
                                                          (ROp.MatchesShape M r (foundPair.1.shape.events [] id)) :=
                                                        fun op s ho => clause_answer_covers M _ _ _ hEmS op s (.inl ho)
                                                      exact stack_handler_covers_cons M _ _ hSamp
                                                        (stack_handler_covers_cons M _ _ hConP
                                                          (stack_handler_covers_cons M _ _ hLayP
                                                            (stack_handler_covers_nil M _ _ _)))
                                                · dsimp only
                                                  rw [dite_eq_right (Ne.symm hNe), dite_eq_left rfl]
                                                  apply stack_covers_cast M (by simp [hFound]) rfl
                                                  have hConV : Handler.Covers M
                                                      (Layer.handler M (Defs.fnTable M a.program.defs)
                                                        (Defs.rTable M a.program.defs)
                                                        ({ line := .construction, state := stPair.1,
                                                           takes := [], gives := [], clauses := cc.2.1,
                                                           again := restoreAgain stPair.1,
                                                           start := constructionStart sess.1 sess.2 stPair.2
                                                             absPair.2 stmtV,
                                                           finish := emptyFinish stPair.1 } :
                                                          Layer V a.program.headers r foundPair.1.ins))
                                                      (ROp.MatchesShape M r (foundPair.1.shape.events [] id))
                                                      (LayoutInputV M prover r (foundPair.1.shape.events [] id)) :=
                                                    fun op s ho => clause_answer_covers M _ _ _ hEmV op s (hCovV op ho)
                                                  exact stack_handler_covers_cons M _ _ hConV
                                                    (stack_handler_covers_cons M _ _ hLayV
                                                      (stack_handler_covers_nil M _ _ _))

theorem statements_deployCoverage (enc : VocabEncoder V) (c : Functions V)
    (hdep : c.deploy = deploy enc) : Statements.deployCoverage c := by
  intro _ _ _ _ _ decl d hD hni; rw [hdep] at hD; exact deploy_coverage enc hD hni

/-- An ideal-RO deployment's verifier asks the world only closed effects (its own private coins,
service requests — including `serviceKey` — and local attempt marks). -/
theorem deployIdeal_verifier_covered (enc : VocabEncoder V) (serviceKey : Key)
    {a : Admitted V} {declaration : Declaration} {d : Deployed V}
    (hDep : deployIdeal enc serviceKey a declaration = .ok d)
    (M : Model V) (prover verifier : Role) (hRoles : d.roles = some (prover, verifier))
    (ins : HList (RV M verifier) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack verifier))) :
    Process.ClosedEffects (d.run M verifier ins taken) := by
  rw [deployed_run_eq_runStack]
  apply runStack_closedEffects M d.admitted d.callee d.retry verifier (d.stack verifier) _ ins taken
  unfold deployIdeal at hDep
  split at hDep
  · cases hDep
  · rename_i foundPair hFound
    dsimp only at hDep
    split at hDep
    · cases hDep
    · cases hCon : declaration.construction with
      | interactive => rw [hCon] at hDep; cases hDep
      | authored => rw [hCon] at hDep; cases hDep
      | derived suite sessionTag =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · rename_i hNe
                cases hLO : declaration.layout with
                | none => rw [hLO] at hDep; cases hDep
                | some layout =>
                    rw [hLO] at hDep; dsimp only at hDep
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at hDep; cases hDep
                    | some stPair =>
                        rw [hSt] at hDep; dsimp only at hDep
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at hDep; cases hDep
                        | some absPair =>
                            rw [hAb] at hDep; dsimp only at hDep
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at hDep; cases hDep
                            | ok sess =>
                                rw [hSess] at hDep; dsimp only [bind, Except.bind] at hDep
                                cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                    (.inr rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSV] at hDep; cases hDep
                                | ok stmtV =>
                                    rw [hSV] at hDep; dsimp only [bind, Except.bind] at hDep
                                    cases hIV : buildIdealVerifierClauses a suite stPair.1 absPair.1
                                        absPair.2 serviceKey pv.1 pv.2 declaration.key
                                        (foundPair.1.shape.events [] id) with
                                    | error _ => rw [hIV] at hDep; cases hDep
                                    | ok idealVClauses =>
                                        rw [hIV] at hDep; dsimp only [bind, Except.bind] at hDep
                                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                            declaration.key (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hLay] at hDep; cases hDep
                                        | ok lays =>
                                            rw [hLay] at hDep; cases hDep
                                            have hRolesEq : proverAndVerifier foundPair.1 declaration =
                                                some (prover, verifier) := by
                                              simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                                            rw [hPV] at hRolesEq; cases hRolesEq
                                            obtain ⟨hEmV, hCovV⟩ := buildIdealVerifierClauses_go_covers
                                              M hNe 0 _ (fun k e hk => by simpa using hk) hIV
                                            obtain ⟨_, hLayV⟩ := buildLayoutLayers_covers M hLay
                                            dsimp only
                                            rw [dite_eq_left rfl]
                                            apply stack_covers_cast M (by simp [hFound]) rfl
                                            have hConV : Handler.Covers M
                                                (Layer.handler M (Defs.fnTable M a.program.defs)
                                                  (Defs.rTable M a.program.defs)
                                                  ({ line := .construction, state := stPair.1,
                                                     takes := [], gives := [], clauses := idealVClauses,
                                                     again := restoreAgain stPair.1,
                                                     start := constructionStart sess.1 sess.2 stPair.2
                                                       absPair.2 stmtV,
                                                     finish := emptyFinish stPair.1 } :
                                                    Layer V a.program.headers verifier foundPair.1.ins))
                                                (ROp.MatchesShape M verifier (foundPair.1.shape.events [] id))
                                                (LayoutInputV M prover verifier (foundPair.1.shape.events [] id)) :=
                                              fun op s ho => clause_answer_covers M _ _ _ hEmV op s (hCovV op ho)
                                            exact stack_handler_covers_cons M _ _ hConV
                                              (stack_handler_covers_cons M _ _ hLayV
                                                (stack_handler_covers_nil M _ _ _))

end Coverage

/-! ## Section 5: Completeness (`deploy_complete`) -/

section Completeness

variable {V : Vocabulary} (M : Model V)

/-! ### `Alone`, `patchSource`, and `Stack.handler` stepping lemmas -/

private theorem alone_bind {source : Source M} {r : Role} {H A B : Type}
    {p : Process (RSig M) H A} {f : A → Process (RSig M) H B}
    {a : A} {rec₁ rec₂ : List (Happened M)} {e : Ending B H}
    (hp : Alone M source r p rec₁ (.returned a))
    (hf : Alone M source r (f a) rec₂ e) :
    Alone M source r (p.bind f) (rec₁ ++ rec₂) e := by
  generalize hEnd : Ending.returned a = end₁ at hp
  induction hp with
  | done => cases hEnd; exact hf
  | halt => cases hEnd
  | waits => cases hEnd
  | give _ ih => exact .give (ih hEnd)
  | own hsrc _ ih => exact .own hsrc (ih hEnd)
  | hear hsrc _ ih => exact .hear hsrc (ih hEnd)
  | begin _ ih => exact .begin (ih hEnd)
  | settle _ ih => exact .settle (ih hEnd)

private theorem alone_map {source : Source M} {r : Role} {H A B : Type}
    {p : Process (RSig M) H A} {f : A → B} {a : A} {rec : List (Happened M)}
    (hp : Alone M source r p rec (.returned a)) :
    Alone M source r (p.map f) rec (.returned (f a)) := by
  rw [Process.map_eq_bind, ← List.append_nil rec]
  exact alone_bind M hp .done

private theorem alone_mapHalt {source : Source M} {r : Role} {H H' A : Type}
    {p : Process (RSig M) H A} {g : H → H'} {a : A} {rec : List (Happened M)}
    (hp : Alone M source r p rec (.returned a)) :
    Alone M source r (p.mapHalt g) rec (.returned a) := by
  generalize hEnd : Ending.returned a = end₁ at hp
  induction hp with
  | done => cases hEnd; exact .done
  | halt => cases hEnd
  | waits => cases hEnd
  | give _ ih => exact .give (ih hEnd)
  | own hsrc _ ih => exact .own hsrc (ih hEnd)
  | hear hsrc _ ih => exact .hear hsrc (ih hEnd)
  | begin _ ih => exact .begin (ih hEnd)
  | settle _ ih => exact .settle (ih hEnd)

/-- Patch a `Source` at a single `(occurrence, type)` pair. -/
private def patchSource (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) : Source M :=
  fun at_ τ =>
    if h : at_ = target ∧ τ = τ₀ then some (cast (congrArg M.Val h.2.symm) v₀)
    else source at_ τ

private theorem patchSource_self (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) :
    patchSource M source target τ₀ v₀ target τ₀ = some v₀ := by
  unfold patchSource
  rw [dite_eq_left ⟨rfl, rfl⟩]
  rfl

private theorem patchSource_ne (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) {at_ : Occurrence} (hne : at_ ≠ target) (τ : V.Ty) :
    patchSource M source target τ₀ v₀ at_ τ = source at_ τ := by
  unfold patchSource
  rw [dite_eq_right (fun h => hne h.1)]

private theorem lawful_of_agree {A : Type} {P : Occurrence → Prop} {s₁ s₂ : Source M}
    (hAgree : ∀ at_ τ, P at_ → s₁ at_ τ = s₂ at_ τ) :
    ∀ {p : Protocol M A}, Protocol.OccsIn M P p → Lawful M s₁ p → Lawful M s₂ p
  | .done _, _, _ => trivial
  | .halt _, _, _ => trivial
  | .call (.flow ..) k, ⟨_, hk⟩, hL => lawful_of_agree hAgree (p := k ()) (hk ()) hL
  | .call (.given _ _ _ at_ _ _ τ) k, ⟨ho, hk⟩, hL => by
      intro v hv
      rw [← hAgree at_ τ ho] at hv
      have ⟨hA, hL'⟩ := hL v hv
      exact ⟨hA, lawful_of_agree hAgree (p := k v) (hk v) hL'⟩

private theorem grun_of_agree {A : Type} {P : Occurrence → Prop} {s₁ s₂ : Source M}
    (hAgree : ∀ at_ τ, P at_ → s₁ at_ τ = s₂ at_ τ)
    {p : Protocol M A} {evs : List (Event M)} {e : GEnd A}
    (hOcc : Protocol.OccsIn M P p) (hRun : GRun M s₁ p evs e) : GRun M s₂ p evs e := by
  induction hRun with
  | done => exact .done
  | halt => exact .halt
  | flow _ ih => exact .flow (ih (hOcc.2 ()))
  | given hsrc _ ih =>
      exact .given (by
        dsimp only [Protocol.OccsIn, GOp.occurrence] at hOcc
        rw [← hAgree _ _ hOcc.1]; exact hsrc) (ih (hOcc.2 _))

private theorem stack1_clause_done {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (lay : Layer V hs r ins) (op : ROp M) (s s' : M.Val lay.state) (reply : (RSig M).Reply op)
    (hLay : Clause.answer M fnTable rTable lay.clauses op s = .done (reply, s')) :
    (Stack.handler M fnTable rTable [lay]).clause op (.cons s .nil) =
      .done (reply, .cons s' .nil) := by
  change ((((Layer.handler M fnTable rTable lay).over
      (Stack.handler M fnTable rTable [])).clause op (s, .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = .done (reply, .cons s' .nil)
  dsimp only [Layer.handler, Handler.over]
  rw [hLay]; rfl

private theorem stack1_clause_pass {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (lay : Layer V hs r ins) (op : ROp M) (s : M.Val lay.state)
    (hLay : Clause.answer M fnTable rTable lay.clauses op s = .call op fun reply => .done (reply, s)) :
    (Stack.handler M fnTable rTable [lay]).clause op (.cons s .nil) =
      .call op fun reply => .done (reply, .cons s .nil) := by
  change ((((Layer.handler M fnTable rTable lay).over
      (Stack.handler M fnTable rTable [])).clause op (s, .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = .call op fun reply => .done (reply, .cons s .nil)
  dsimp only [Layer.handler, Handler.over]
  rw [hLay]; rfl

private theorem stack2_clause_step {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (con lay : Layer V hs r ins) (op op₂ : ROp M)
    (st st' : M.Val con.state) (laySt laySt' : M.Val lay.state)
    (r₂ : (RSig M).Reply op₂) (reply : (RSig M).Reply op)
    (k₂ : (RSig M).Reply op₂ → Process (RSig M) (Stop × M.Val con.state) ((RSig M).Reply op × M.Val con.state))
    (hCon : Clause.answer M fnTable rTable con.clauses op st = .call op₂ k₂)
    (hLay : Clause.answer M fnTable rTable lay.clauses op₂ laySt = .done (r₂, laySt'))
    (hK : k₂ r₂ = .done (reply, st')) :
    (Stack.handler M fnTable rTable [con, lay]).clause op (.cons st (.cons laySt .nil)) =
      .done (reply, .cons st' (.cons laySt' .nil)) := by
  change ((((Layer.handler M fnTable rTable con).over
      (Stack.handler M fnTable rTable [lay])).clause op (st, .cons laySt .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = .done (reply, .cons st' (.cons laySt' .nil))
  dsimp only [Layer.handler, Handler.over]
  rw [hCon]
  dsimp only [Handler.answer]
  rw [stack1_clause_done M fnTable rTable lay op₂ laySt laySt' r₂ hLay]
  dsimp only [Process.mapHalt, Process.bind]
  rw [hK]; rfl

private theorem stack2_clause_pass {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (con lay : Layer V hs r ins) (op : ROp M) (st : M.Val con.state) (laySt : M.Val lay.state)
    (hCon : Clause.answer M fnTable rTable con.clauses op st = .call op fun reply => .done (reply, st))
    (hLay : Clause.answer M fnTable rTable lay.clauses op laySt = .call op fun reply => .done (reply, laySt)) :
    (Stack.handler M fnTable rTable [con, lay]).clause op (.cons st (.cons laySt .nil)) =
      .call op fun reply => .done (reply, .cons st (.cons laySt .nil)) := by
  change ((((Layer.handler M fnTable rTable con).over
      (Stack.handler M fnTable rTable [lay])).clause op (st, .cons laySt .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) =
      .call op fun reply => .done (reply, .cons st (.cons laySt .nil))
  dsimp only [Layer.handler, Handler.over]
  rw [hCon]
  dsimp only [Handler.answer]
  rw [stack1_clause_pass M fnTable rTable lay op laySt hLay]
  rfl

/-! ### Exact `Clause.answer` behavior lemmas for streaming `deploy` -/

private theorem clause_answer_unmatched_all {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty}
    (op : ROp M) (s : M.Val state) :
    ∀ (cs : List (Clause V hs r state)),
      (∀ c ∈ cs, ¬ ClauseMatches M c op) →
      Clause.answer M fnTable rTable cs op s = .call op fun reply => .done (reply, s)
  | [], _ => rfl
  | c :: cs, hNo => by
      unfold Clause.answer
      have hne := hNo c List.mem_cons_self
      unfold ClauseMatches at hne
      rw [dite_eq_right hne]
      exact clause_answer_unmatched_all fnTable rTable op s cs (fun c' hc' => hNo c' (List.mem_cons_of_mem _ hc'))

/-- Exact `Clause.answer` result of `proverAbsorbClause` on a matching `.give`. -/
private theorem proverAbsorbClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (msg : M.Val τ) (st : M.Val stateTy)
    (enc : List (M.Val unitTy)) (st' : M.Val stateTy)
    (hEnc : encRef.eval M fnTable (.cons msg .nil) = .done (.cons enc .nil))
    (hAbs : absRef.eval M fnTable (.cons st (.cons label (.cons enc .nil))) = .done (.cons st' .nil))
    (cs : List (Clause V hs prover stateTy)) :
    Clause.answer M fnTable rTable
        (proverAbsorbClause prover site kind getters label hlabel encRef absRef :: cs)
        (.give kind getters at_ τ msg) st =
      .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ => .done ((), st') := by
  unfold Clause.answer
  have hM : (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.site =
      (ROp.occurrence M (.give kind getters at_ τ msg)).site ∧
      some (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.part =
      ROp.part M (.give kind getters at_ τ msg) ∧
      (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.takes =
      ROp.takes M (.give kind getters at_ τ msg) ∧
      (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.gives =
      ROp.gives M (.give kind getters at_ τ msg) := ⟨hSite, rfl, rfl, rfl⟩
  rw [dite_eq_left hM]
  change (((proverAbsorbClause prover site kind getters label hlabel encRef absRef).code.denote
    (roleSem M prover fnTable rTable) at_.path
    (Env.positional (aloneIn M prover (.cons msg (.cons st .nil))))).mapHalt _).map _ = _
  have hStep : ((liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
      (liftLocal (S := RSig M) id (absRef.eval M fnTable (.cons st (.cons label (.cons enc.single .nil))))).bind fun nextSt =>
        .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ =>
          .done (aloneIn M prover nextSt)) =
      .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ =>
        .done (aloneIn M prover (.cons st' .nil)) := by
    rw [hEnc, liftLocal_done]
    change ((liftLocal (S := RSig M) id
      (absRef.eval M fnTable (.cons st (.cons label (.cons enc .nil))))).bind fun nextSt =>
        .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ =>
          .done (aloneIn M prover nextSt)) = _
    rw [hAbs, liftLocal_done]
    rfl
  rw [proverAbsorbClause_denote, hStep]
  dsimp only [Process.map, Process.mapHalt, proverAbsorbClause, Clause.site, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]

/-- Exact `Clause.answer` result of `verifierAbsorbClause` on a matching `.get`. -/
private theorem verifierAbsorbClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (st : M.Val stateTy)
    (cs : List (Clause V hs verifier stateTy)) :
    Clause.answer M fnTable rTable
        (verifierAbsorbClause verifier prover site kind label hlabel encRef absRef :: cs)
        (.get kind prover at_ τ) st =
      .call (.get kind prover ⟨at_.path, site.key⟩ τ) fun msg =>
        (((liftLocal id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
          (liftLocal id (absRef.eval M fnTable (.cons st (.cons label (.cons enc.single .nil))))).map
            fun nextSt => aloneIn M verifier (.cons msg nextSt)).mapHalt fun why => (why, st)).map fun out =>
          let values := HList.split [τ] (aloneOut M verifier out)
          (values.1.single, values.2.single) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((verifierAbsorbClause verifier prover site kind label hlabel encRef absRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt _).map _ = _
  rw [verifierAbsorbClause_denote]
  dsimp only [Process.mapHalt, Process.map, verifierAbsorbClause, Clause.site, ROp.reply]
  congr 1; funext msg; congr 1; funext out
  cases hsp : HList.split [τ] (aloneOut M verifier out) with
  | mk v1 v2 =>
      cases v1 with | cons a an => cases an; rfl

/-- Exact `Clause.answer` result of `deriveClause` (`drawIns = []`) on a matching `.hear`/`.own`. -/
private theorem deriveClause_answer_hear {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (prover verifier : Role) (site : Site) (law : V.LawKey)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (derRef : TypedFnRef V hs.fns [stateTy, bytesTy] [τ, stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (st : M.Val stateTy)
    (coin : M.Val τ) (st' : M.Val stateTy)
    (hDer : derRef.eval M fnTable (.cons st (.cons label .nil)) = .done (.cons coin (.cons st' .nil)))
    (cs : List (Clause V hs prover stateTy)) :
    Clause.answer M fnTable rTable
        (deriveClause prover verifier site (.hear (.coin law) verifier) [] toldKey label hlabel derRef :: cs)
        (.hear (.coin law) verifier at_ τ) st =
      .call (.give .message [verifier] ⟨at_.path, toldKey⟩ τ coin) fun _ => .done (coin, st') := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((deriveClause prover verifier site (.hear (.coin law) verifier) [] toldKey label hlabel
    derRef).code.denote (roleSem M prover fnTable rTable) at_.path
    (Env.positional (aloneIn M prover (.cons st .nil)))).mapHalt _).map _ = _
  rw [deriveClause_denote_nil, hDer, liftLocal_done]
  dsimp only [Process.bind, deriveClause, Clause.site, List.cons_append, List.nil_append]
  simp only [Process.map, Process.mapHalt, aloneOut_aloneIn, HList.split, HList.single, ROp.reply]
  rfl

private theorem deriveClause_answer_own {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (law : V.LawKey) (hearers : List Role)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (derRef : TypedFnRef V hs.fns [stateTy, bytesTy] [τ, stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (st : M.Val stateTy)
    (coin : M.Val τ) (st' : M.Val stateTy)
    (hDer : derRef.eval M fnTable (.cons st (.cons label .nil)) = .done (.cons coin (.cons st' .nil)))
    (cs : List (Clause V hs verifier stateTy)) :
    Clause.answer M fnTable rTable
        (deriveClause verifier prover site (.own (.coin law) hearers) [] toldKey label hlabel derRef :: cs)
        (.own (.coin law) hearers at_ [] .nil τ) st =
      .call (.give .message [prover] ⟨at_.path, toldKey⟩ τ coin) fun _ => .done (coin, st') := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((deriveClause verifier prover site (.own (.coin law) hearers) [] toldKey label hlabel
    derRef).code.denote (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt _).map _ = _
  rw [deriveClause_denote_nil, hDer, liftLocal_done]
  dsimp only [Process.bind, deriveClause, Clause.site, List.cons_append, List.nil_append]
  simp only [Process.map, Process.mapHalt, aloneOut_aloneIn, HList.split, HList.single, ROp.reply]
  rfl

private theorem layoutPWriteClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (wRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (at_ : Occurrence) (hSite : site = at_.site) (msg : M.Val τ) (buf chunk : List (M.Val unitTy))
    (hW : wRef.eval M fnTable (.cons msg .nil) = .done (.cons chunk .nil))
    (cs : List (Clause V hs prover (.seq unitTy none))) :
    Clause.answer M fnTable rTable
        (layoutPWriteClause prover site kind getters wRef :: cs)
        (.give kind getters at_ τ msg) buf =
      .done ((), buf ++ chunk) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((layoutPWriteClause prover site kind getters wRef).code.denote
    (roleSem M prover fnTable rTable) at_.path
    (Env.positional (aloneIn M prover (.cons msg (.cons buf .nil))))).mapHalt _).map _ = _
  rw [layoutPWriteClause_denote, hW, liftLocal_done]
  dsimp only [Process.map, Process.mapHalt, HList.single, layoutPWriteClause, Clause.site, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, ROp.reply]

private theorem layoutDropClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (at_ : Occurrence) (hSite : site = at_.site) (msg : M.Val τ) (s : M.Val stateTy)
    (cs : List (Clause V hs r stateTy)) :
    Clause.answer M fnTable rTable
        (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters :: cs)
        (.give kind getters at_ τ msg) s =
      .done ((), s) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((layoutDropClause r site kind getters).code.denote
    (roleSem M r fnTable rTable) at_.path
    (Env.positional (aloneIn M r (.cons msg (.cons s .nil))))).mapHalt _).map _ = _
  rw [layoutDropClause_denote]
  dsimp only [Process.map, Process.mapHalt, layoutDropClause, Clause.site]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]

private theorem layoutVReadClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (rRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (at_ : Occurrence) (hSite : site = at_.site) (buf : List (M.Val unitTy)) (off nextOff : Nat)
    (v : M.Val τ)
    (hR : rRef.eval M fnTable (.cons buf (.cons off .nil)) = .done (.cons v (.cons nextOff .nil)))
    (cs : List (Clause V hs verifier (streamStateTy unitTy))) :
    Clause.answer M fnTable rTable
        (layoutVReadClause hfree verifier prover site kind rRef :: cs)
        (.get kind prover at_ τ) (buf, (off, ())) =
      .done (v, (buf, (nextOff, ()))) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((layoutVReadClause hfree verifier prover site kind rRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons (buf, (off, ())) .nil)))).mapHalt _).map _ = _
  rw [layoutVReadClause_denote, hR, liftLocal_done]
  dsimp only [Process.map, Process.mapHalt, layoutVReadClause, Clause.site,
    List.cons_append, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]
  rfl

private theorem layoutVCarryClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (rRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (at_ : Occurrence) (hSite : toldSite = at_.site)
    (coin : M.Val τ) (buf : List (M.Val unitTy)) (off nextOff : Nat)
    (hR : rRef.eval M fnTable (.cons buf (.cons off .nil)) = .done (.cons coin (.cons nextOff .nil)))
    (hEq : eqRef.eval M fnTable (.cons coin (.cons coin .nil)) = .done (.cons true .nil))
    (cs : List (Clause V hs verifier (streamStateTy unitTy))) :
    Clause.answer M fnTable rTable
        (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef :: cs)
        (.give .message [prover] at_ τ coin) (buf, (off, ())) =
      .done ((), (buf, (nextOff, ()))) := by
  unfold Clause.answer
  have hM : (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.site =
      (ROp.occurrence M (.give .message [prover] at_ τ coin)).site ∧
      some (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.part =
      ROp.part M (.give .message [prover] at_ τ coin) ∧
      (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.takes =
      ROp.takes M (.give .message [prover] at_ τ coin) ∧
      (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.gives =
      ROp.gives M (.give .message [prover] at_ τ coin) := ⟨hSite, rfl, rfl, rfl⟩
  rw [dite_eq_left hM]
  change (((layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons coin (.cons (buf, (off, ())) .nil))))).mapHalt _).map _ = _
  rw [layoutVCarryClause_denote, hR, liftLocal_done]
  change ((((liftLocal (S := RSig M) id (eqRef.eval M fnTable (.cons coin (.cons coin .nil)))).bind fun eqRes =>
      bif eqRes.single then .done (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))
      else .halt (.declared .reject ⟨at_.path, guardKey⟩)).mapHalt
        (fun why => (why, (buf, (off, ()))))).map
      (fun out =>
        let values := HList.split (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.gives (aloneOut M verifier out)
        (ROp.reply M (.give .message [prover] at_ τ coin) (cast (congrArg (HList M.Val) hM.2.2.2) values.1), values.2.single))) = _
  rw [hEq, liftLocal_done]
  change ((Process.done (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).mapHalt _).map _ = _
  dsimp only [Process.map, Process.mapHalt, layoutVCarryClause, Clause.site, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]

/-! ### Builder behavior lookups for `buildConstructionClauses` and `buildStreamingLayoutClauses` -/

private theorem construction_clauses_answer_prover_flow {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty)
        (msg : M.Val τ) (st : M.Val stateTy),
        M.Valid τ msg → M.Valid stateTy st →
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind prover getters) →
        ∃ (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none])
          (enc : List (M.Val unitTy)) (st' : M.Val stateTy),
          findSuiteEncode a suite unitTy τ = some encRef ∧
          encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil) = .done (.cons enc .nil) ∧
          absRef.eval M (Defs.fnTable M a.program.defs)
            (.cons st (.cons (msgLabel at_.site) (.cons enc .nil))) = .done (.cons st' .nil) ∧
          M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cP (.give kind getters at_ τ msg) st =
            .call (.give kind getters ⟨at_.path, at_.site.key⟩ τ msg) fun _ => .done ((), st')
  | _, [], _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, cP, cV, cS, h, kind, getters, at_, τ, msg, st, hMsgV, hStV, ⟨e', he', hSite, hTy, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_prover_flow (idx + 1) rest hRec
            kind getters at_ τ msg st hMsgV hStV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    by_cases hMatch :
                        (proverAbsorbClause prover e.site kind₀ getters₀ (msgLabel e.site)
                          (msgLabel_bytes e.site) encRef absRef).site.site = at_.site ∧
                        some (proverAbsorbClause prover e.site kind₀ getters₀ (msgLabel e.site)
                          (msgLabel_bytes e.site) encRef absRef).site.part = some (.give kind getters) ∧
                        [e.τ] = [τ] ∧ ([] : List V.Ty) = []
                    · have hSiteEq : e.site = at_.site := hMatch.1
                      have hPartEq : Part.give kind₀ getters₀ = .give kind getters := Option.some.inj hMatch.2.1
                      cases hPartEq
                      have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.1 |>.1
                      subst hTyEq
                      obtain ⟨encH, hEncD, hEncV⟩ := encRef.eval_done M a (.cons msg .nil) ⟨hMsgV, trivial⟩
                      cases encH with
                      | cons enc en =>
                          cases en
                          have hLblV : M.Valid bytesTy (msgLabel e.site) :=
                            ⟨msgLabel_bytes e.site, (fun _ h => nomatch h)⟩
                          obtain ⟨stH, hAbsD, hAbsV⟩ := absRef.eval_done M a
                            (.cons st (.cons (msgLabel e.site) (.cons enc .nil)))
                            ⟨hStV, hLblV, hEncV.1, trivial⟩
                          cases stH with
                          | cons st' sn =>
                              cases sn
                              refine ⟨encRef, enc, st', hEnc, hEncD, hSiteEq ▸ hAbsD, hAbsV.1, ?_⟩
                              rw [← hSiteEq]
                              exact proverAbsorbClause_answer M _ _ prover e.site kind getters
                                (msgLabel e.site) (msgLabel_bytes e.site) encRef absRef
                                at_ hSiteEq msg st enc st' hEncD hAbsD triple.1
                    · rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                        exact absurd ⟨hSite, rfl, by cases hTy; rfl, rfl⟩ hMatch
                      · obtain ⟨encR, enc, st', hE, hED, hAD, hSV, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                        refine ⟨encR, enc, st', hE, hED, hAD, hSV, ?_⟩
                        unfold Clause.answer
                        exact (dite_eq_right hMatch).trans hAns
              · split at h
                · rename_i hOut
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
                  · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                rcases List.mem_cons.mp he' with rfl | hmem
                                · rw [hCls] at hECls; cases hECls
                                · obtain ⟨encR, enc, st', hE, hED, hAD, hSV, hAns⟩ :=
                                    ih ⟨e', hmem, hSite, hTy, hECls⟩
                                  refine ⟨encR, enc, st', hE, hED, hAD, hSV, ?_⟩
                                  unfold Clause.answer
                                  rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                  exact hAns
                              · cases h
                        · cases h
                  · split at h
                    · rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                        · cases h; exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                  · cases h

private theorem construction_clauses_answer_verifier_flow {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧
          ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]),
          findSuiteEncode a suite unitTy τ = some encRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.get kind prover at_ τ) st =
            .call (.get kind prover ⟨at_.path, at_.site.key⟩ τ) fun msg =>
              (((liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil))).bind fun enc =>
                (liftLocal id (absRef.eval M (Defs.fnTable M a.program.defs)
                  (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).map
                  fun nextSt => aloneIn M verifier (.cons msg nextSt)).mapHalt fun why => (why, st)).map fun out =>
                let values := HList.split [τ] (aloneOut M verifier out)
                (values.1.single, values.2.single)
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, cP, cV, cS, h, kind, at_, τ, st, ⟨e', he', hSite, hTy, gs', hVin, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_verifier_flow (idx + 1) rest hRec
            kind at_ τ st hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    by_cases hMatch :
                        (verifierAbsorbClause verifier prover e.site kind₀ (msgLabel e.site)
                          (msgLabel_bytes e.site) encRef absRef).site.site = at_.site ∧
                        some (verifierAbsorbClause verifier prover e.site kind₀ (msgLabel e.site)
                          (msgLabel_bytes e.site) encRef absRef).site.part = some (.get kind prover) ∧
                        ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                    · have hSiteEq : e.site = at_.site := hMatch.1
                      have hPartEq : Part.get kind₀ prover = .get kind prover := Option.some.inj hMatch.2.1
                      cases hPartEq
                      have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                      subst hTyEq
                      refine ⟨encRef, hEnc, ?_⟩
                      rw [← hSiteEq]
                      exact verifierAbsorbClause_answer M _ _ verifier prover e.site kind
                        (msgLabel e.site) (msgLabel_bytes e.site) encRef absRef at_ hSiteEq st triple.2.1
                    · rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                        exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                      · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        refine ⟨encR, hE, ?_⟩
                        unfold Clause.answer
                        exact (dite_eq_right hMatch).trans hAns
              · split at h
                · rename_i hOut
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
                  · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                rcases List.mem_cons.mp he' with rfl | hmem
                                · rw [hCls] at hECls; cases hECls
                                · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                                  refine ⟨encR, hE, ?_⟩
                                  unfold Clause.answer
                                  rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                  exact hAns
                              · cases h
                        · cases h
                  · split at h
                    · rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        · cases h; exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                  · cases h

private theorem construction_clauses_answer_prover_coin {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ k e, es[k]? = some e → events[idx + k]? = some e) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)}
        {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (law : V.LawKey) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        M.Valid stateTy st →
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧
          ∃ hearers, prover ∈ hearers ∧ e.cls = .given (.coin law) verifier hearers) →
        ∃ (idxP : Nat) (eP : ShapeEvent V)
          (derRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy] [τ, stateTy])
          (coin : M.Val τ) (st' : M.Val stateTy),
          events[idxP]? = some eP ∧ eP.site = at_.site ∧ eP.τ = τ ∧
          (∃ hearersP, prover ∈ hearersP ∧ eP.cls = .given (.coin law) verifier hearersP) ∧
          findSuiteDerive a suite stateTy [] τ = some derRef ∧
          derRef.eval M (Defs.fnTable M a.program.defs) (.cons st (.cons (drawLabel at_.site) .nil)) =
            .done (.cons coin (.cons st' .nil)) ∧
          M.Valid τ coin ∧ M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cP (.hear (.coin law) verifier at_ τ) st =
            .call (.give .message [verifier] ⟨at_.path, drawToldKey events idxP⟩ τ coin)
              fun _ => .done (coin, st')
  | _, [], _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, hSuf, cP, cV, cS, h, law, at_, τ, st, hStV, ⟨e', he', hSite, hTy, hs', hPin, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k e'', rest[k]? = some e'' → events[(idx + 1) + k]? = some e'' := by
        intro k e'' hk
        have := hSuf (k + 1) e'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 e rfl
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_prover_coin (idx + 1) rest hSufRest hRec
            law at_ τ st hStV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some _ =>
                    rw [hEnc] at h; cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · obtain ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, hAns⟩ :=
                        ih ⟨e', hmem, hSite, hTy, hs', hPin, hECls⟩
                      refine ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
                      unfold Clause.answer
                      rw [dite_eq_right (fun hm => by cases hm.2.1)]
                      exact hAns
              · split at h
                · cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, hs', hPin, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law₀ =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law₀ with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                let derRefP : TypedFnRef V a.program.headers.fns [stateTy, bytesTy]
                                    [e.τ, stateTy] := hIns ▸ derRef
                                have hDerP : findSuiteDerive a suite stateTy [] e.τ = some derRefP := by
                                  cases sig with
                                  | mk sIns sOut =>
                                      dsimp only [derRefP] at hIns ⊢
                                      subst hIns; exact hDer
                                by_cases hMatch :
                                    e.site = at_.site ∧
                                    some (Part.hear (.coin law₀) verifier) = some (.hear (.coin law) verifier) ∧
                                    ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                                · have hSiteEq : e.site = at_.site := hMatch.1
                                  have hLawEq : law₀ = law := by
                                    have hp := Option.some.inj hMatch.2.1
                                    cases hp; rfl
                                  have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                                  subst hLawEq; subst hTyEq
                                  have hLblV : M.Valid bytesTy (drawLabel e.site) :=
                                    ⟨drawLabel_bytes e.site, (fun _ h => nomatch h)⟩
                                  obtain ⟨resH, hDerD, hResV⟩ := derRefP.eval_done M a
                                    (.cons st (.cons (drawLabel e.site) .nil)) ⟨hStV, hLblV, trivial⟩
                                  cases resH with
                                  | cons coin r1 =>
                                      cases r1 with
                                      | cons st' r2 =>
                                          cases r2
                                          refine ⟨idx, e, derRefP, coin, st', hIdx, hSiteEq, rfl,
                                            ⟨hearers, hCoin.2, hCoin.1 ▸ hCls⟩, hDerP,
                                            hSiteEq ▸ hDerD, hResV.1, hResV.2.1, ?_⟩
                                          exact deriveClause_answer_hear M _ _ prover verifier e.site law₀
                                            (drawToldKey events idx) (drawLabel e.site)
                                            (drawLabel_bytes e.site) derRefP at_ hSiteEq st coin st'
                                            hDerD triple.1
                                · rcases List.mem_cons.mp he' with rfl | hmem
                                  · rw [hCls] at hECls; cases hECls
                                    exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                                  · obtain ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, hAns⟩ :=
                                      ih ⟨e', hmem, hSite, hTy, hs', hPin, hECls⟩
                                    refine ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
                                    unfold Clause.answer
                                    exact (dite_eq_right hMatch).trans hAns
                              · cases h
                        · cases h
                  · split at h
                    · rename_i hNil
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; subst hNil; cases hPin
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨e', hmem, hSite, hTy, hs', hPin, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨e', hmem, hSite, hTy, hs', hPin, hECls⟩
                        · cases h; exact ih ⟨e', hmem, hSite, hTy, hs', hPin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hs', hPin, hECls⟩
                  · cases h

private theorem construction_clauses_answer_verifier_coin {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ k e, es[k]? = some e → events[idx + k]? = some e) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)}
        {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        M.Valid stateTy st →
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧ prover ∈ hearers ∧
          e.cls = .given (.coin law) verifier hearers) →
        ∃ (idxV : Nat) (eV : ShapeEvent V)
          (derRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy] [τ, stateTy])
          (coin : M.Val τ) (st' : M.Val stateTy),
          events[idxV]? = some eV ∧ eV.site = at_.site ∧ eV.τ = τ ∧
          eV.cls = .given (.coin law) verifier hearers ∧
          V.law law = some ⟨[], τ⟩ ∧
          findSuiteDerive a suite stateTy [] τ = some derRef ∧
          derRef.eval M (Defs.fnTable M a.program.defs) (.cons st (.cons (drawLabel at_.site) .nil)) =
            .done (.cons coin (.cons st' .nil)) ∧
          M.Valid τ coin ∧ M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.own (.coin law) hearers at_ [] .nil τ) st =
            .call (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
              fun _ => .done (coin, st')
  | _, [], _, _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, hSuf, cP, cV, cS, h, law, hearers, at_, τ, st, hStV, ⟨e', he', hSite, hTy, hPin, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k e'', rest[k]? = some e'' → events[(idx + 1) + k]? = some e'' := by
        intro k e'' hk
        have := hSuf (k + 1) e'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 e rfl
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_verifier_coin (idx + 1) rest hSufRest hRec
            law hearers at_ τ st hStV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some _ =>
                    rw [hEnc] at h; cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · obtain ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, hAns⟩ :=
                        ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                      refine ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
                      unfold Clause.answer
                      rw [dite_eq_right (fun hm => by cases hm.2.1)]
                      exact hAns
              · split at h
                · cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                · cases h
          | given gkind owner hearers₀ =>
              rw [hCls] at h
              cases gkind with
              | coin law₀ =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law₀ with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · rename_i hOutEq
                          cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                have hSigEq : sig = ⟨[], e.τ⟩ := by
                                    cases sig with
                                    | mk ins out =>
                                        dsimp only at hIns hOutEq
                                        subst hIns; subst hOutEq; rfl
                                subst hSigEq
                                by_cases hMatch :
                                    e.site = at_.site ∧
                                    some (Part.own (.coin law₀) hearers₀) = some (.own (.coin law) hearers) ∧
                                    ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                                · have hSiteEq : e.site = at_.site := hMatch.1
                                  have hPartEq : Part.own (.coin law₀) hearers₀ = .own (.coin law) hearers :=
                                    Option.some.inj hMatch.2.1
                                  cases hPartEq
                                  have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                                  subst hTyEq
                                  have hLblV : M.Valid bytesTy (drawLabel e.site) :=
                                    ⟨drawLabel_bytes e.site, (fun _ h => nomatch h)⟩
                                  obtain ⟨resH, hDerD, hResV⟩ := derRef.eval_done M a
                                    (.cons st (.cons (drawLabel e.site) .nil)) ⟨hStV, hLblV, trivial⟩
                                  cases resH with
                                  | cons coin r1 =>
                                      cases r1 with
                                      | cons st' r2 =>
                                          cases r2
                                          refine ⟨idx, e, derRef, coin, st', hIdx, hSiteEq, rfl,
                                            hCoin.1 ▸ hCls, hLaw, hDer, hSiteEq ▸ hDerD,
                                            hResV.1, hResV.2.1, ?_⟩
                                          exact deriveClause_answer_own M _ _ verifier prover e.site law
                                            hearers (drawToldKey events idx) (drawLabel e.site)
                                            (drawLabel_bytes e.site) derRef at_ hSiteEq st coin st'
                                            hDerD triple.2.1
                                · rcases List.mem_cons.mp he' with rfl | hmem
                                  · rw [hCls] at hECls; cases hECls
                                    exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                                  · obtain ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, hAns⟩ :=
                                      ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                                    refine ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
                                    unfold Clause.answer
                                    exact (dite_eq_right hMatch).trans hAns
                              · cases h
                        · cases h
                  · split at h
                    · rename_i hNil
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; subst hNil; cases hPin
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                        · cases h; exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                  · cases h

/-- No clause in `cP` or `cV` matches a closed effect (`.own (.coin _) []`, `.own (.request _)`,
`.begin`, `.settle`). -/
private theorem construction_clauses_unmatched_closed {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ op, ROp.IsClosed M op →
        (∀ c ∈ cP, ¬ ClauseMatches M c op) ∧ (∀ c ∈ cV, ¬ ClauseMatches M c op)
  | _, [], _, _, _, h, _, _ => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, cP, cV, cS, h, op, hCl => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := construction_clauses_unmatched_closed (idx + 1) rest hRec op hCl
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some _ =>
                    rw [hEnc] at h; cases h
                    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                    · rcases List.mem_cons.mp hc with rfl | hm
                      · intro hm; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, proverAbsorbClause] at hCl hm
                      · exact ihP c hm
                    · rcases List.mem_cons.mp hc with rfl | hm
                      · intro hm; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, verifierAbsorbClause] at hCl hm
                      · exact ihV c hm
              · split at h
                · cases h; exact ⟨ihP, ihV⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some _ =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hm; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, deriveClause] at hCl hm
                                  · exact ihP c hm
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hm
                                    cases op with
                                    | own gk hs' _ _ _ _ =>
                                        cases gk with
                                        | coin _ =>
                                            cases hs' with
                                            | nil =>
                                                have hp := Option.some.inj hm.2.1
                                                cases hp
                                                exact nomatch hCoin.2
                                            | cons _ _ => exact False.elim hCl
                                        | request _ =>
                                            have hp := Option.some.inj hm.2.1; cases hp
                                    | give | get | hear | «begin» | settle =>
                                        simp [ROp.IsClosed, ROp.part, ClauseMatches, deriveClause] at hCl hm
                                  · exact ihV c hm
                              · cases h
                        · cases h
                  · split at h
                    · split at h
                      · cases samplesKey with
                        | none => cases h; exact ⟨ihP, ihV⟩
                        | some sKey =>
                            dsimp only at h
                            cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                            | none => rw [hS] at h; cases h
                            | some _ => rw [hS] at h; cases h; exact ⟨ihP, ihV⟩
                      · cases h; exact ⟨ihP, ihV⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV⟩
                  · cases h

private theorem streaming_layout_unmatched_closed {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ op, ROp.IsClosed M op →
        (∀ c ∈ pCs, ¬ ClauseMatches M c op) ∧ (∀ c ∈ vCs, ¬ ClauseMatches M c op)
  | _, [], _, _, h, _, _ => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, pCs, vCs, h, op, hCl => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := streaming_layout_unmatched_closed (idx + 1) rest hRec op hCl
          have hNotGive : ∀ k gs, some (Part.give k gs) ≠ ROp.part M op := by
            intro k gs hm; cases op <;> simp [ROp.IsClosed, ROp.part] at hCl hm
          have hNotGet : ∀ k g, some (Part.get k g) ≠ ROp.part M op := by
            intro k g hm; cases op <;> simp [ROp.IsClosed, ROp.part] at hCl hm
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · cases h
                  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · exact fun hM => hNotGive _ _ hM.2.1
                    · exact ihP c hm
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · exact fun hM => hNotGet _ _ hM.2.1
                    · exact ihV c hm
              · cases h; exact ⟨ihP, ihV⟩
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact fun hM => hNotGive _ _ hM.2.1
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact fun hM => hNotGive _ _ hM.2.1
                          · exact ihV c hm
                    · cases h
                      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact fun hM => hNotGive _ _ hM.2.1
                        · exact ihP c hm
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact fun hM => hNotGive _ _ hM.2.1
                        · exact ihV c hm
                  · cases h; exact ⟨ihP, ihV⟩
              | request _ => cases h; exact ⟨ihP, ihV⟩

private theorem streaming_layout_answer_prover_flow {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ e ∈ es, e ∈ events) →
      ∀ {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
        {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty)
        (msg : M.Val τ) (buf : List (M.Val unitTy)),
        M.Valid τ msg →
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧ verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (wRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none])
          (chunk : List (M.Val unitTy)),
          findLayoutWrite a layout.module unitTy τ = some wRef ∧
          wRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil) = .done (.cons chunk .nil) ∧
          (∀ u ∈ chunk, M.Valid unitTy u) ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            pCs (.give kind getters at_ τ msg) buf = .done ((), buf ++ chunk)
  | _, [], _, _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, hSub, pCs, vCs, h, kind, getters, at_, τ, msg, buf, hMsgV,
      ⟨e', he', hSite, hTy, hVin, hECls⟩ => by
      unfold buildStreamingLayoutClauses.go at h
      have hSubRest : ∀ e'' ∈ rest, e'' ∈ events := fun e'' he'' => hSub e'' (List.mem_cons_of_mem _ he'')
      have hAtInEvents : at_.site.key ∈ events.map (·.site.key) := by
        have hMemE' : e' ∈ events := hSub e' he'
        rw [← hSite]
        exact List.mem_map.mpr ⟨e', hMemE', rfl⟩
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => streaming_layout_answer_prover_flow (idx + 1) rest hSubRest hRec
            kind getters at_ τ msg buf hMsgV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · rename_i wRef rRef
                  cases h
                  by_cases hMatch :
                      e.site = at_.site ∧
                      some (Part.give (V := V) kind₀ getters₀) = some (.give kind getters) ∧
                      [e.τ] = [τ] ∧ ([] : List V.Ty) = []
                  · have hSiteEq : e.site = at_.site := hMatch.1
                    have hPartEq : Part.give kind₀ getters₀ = .give kind getters := Option.some.inj hMatch.2.1
                    cases hPartEq
                    have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.1 |>.1
                    subst hTyEq
                    obtain ⟨chH, hWD, hChV⟩ := wRef.eval_done M a (.cons msg .nil) ⟨hMsgV, trivial⟩
                    cases chH with
                    | cons chunk cn =>
                        cases cn
                        refine ⟨wRef, chunk, hW, hWD, hChV.1.1, ?_⟩
                        exact layoutPWriteClause_answer M _ _ prover e.site kind getters wRef
                          at_ hSiteEq msg buf chunk hWD pair.1
                  · rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                      exact absurd ⟨hSite, rfl, by cases hTy; rfl, rfl⟩ hMatch
                    · obtain ⟨wR, ch, h1, h2, h3, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
                      refine ⟨wR, ch, h1, h2, h3, ?_⟩
                      unfold Clause.answer
                      exact (dite_eq_right hMatch).trans hAns
              · rename_i hNotPV
                cases h
                rcases List.mem_cons.mp he' with rfl | hmem
                · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                · exact ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              have hNoTold : ¬ (⟨e.site.through, drawToldKey events idx⟩ : Site) = at_.site := by
                intro heq
                have hk : drawToldKey events idx = at_.site.key := congrArg Site.key heq
                exact drawToldKey_fresh events idx (hk ▸ hAtInEvents)
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨wR, ch, h1, h2, h3, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
                          refine ⟨wR, ch, h1, h2, h3, ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => hNoTold hm.1)]
                          exact hAns
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨wR, ch, h1, h2, h3, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
                        refine ⟨wR, ch, h1, h2, h3, ?_⟩
                        unfold Clause.answer
                        rw [dite_eq_right (fun hm => hNoTold hm.1)]
                        exact hAns
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩

private theorem streaming_layout_answer_verifier_flow {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty)
        (buf : List (M.Val unitTy)) (off : Nat),
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧
          ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]),
          findLayoutRead a layout.module unitTy τ = some rRef ∧
          (∀ v nextOff,
            rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) =
              .done (.cons v (.cons nextOff .nil)) →
            Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              vCs (.get kind prover at_ τ) (buf, (off, ())) = .done (v, (buf, (nextOff, ()))))
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, pCs, vCs, h, kind, at_, τ, buf, off,
      ⟨e', he', hSite, hTy, gs', hVin, hECls⟩ => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => streaming_layout_answer_verifier_flow (idx + 1) rest hRec
            kind at_ τ buf off hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · rename_i wRef rRef
                  cases h
                  by_cases hMatch :
                      e.site = at_.site ∧
                      some (Part.get (V := V) kind₀ prover) = some (.get kind prover) ∧
                      ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                  · have hSiteEq : e.site = at_.site := hMatch.1
                    have hPartEq : Part.get kind₀ prover = .get kind prover := Option.some.inj hMatch.2.1
                    cases hPartEq
                    have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                    subst hTyEq
                    refine ⟨rRef, hR, fun v nextOff hRD => ?_⟩
                    exact layoutVReadClause_answer M _ _ hfree verifier prover e.site kind rRef
                      at_ hSiteEq buf off nextOff v hRD pair.2
                  · rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                      exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                    · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                      refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                      unfold Clause.answer
                      exact (dite_eq_right hMatch).trans (hAns v nextOff hRD)
              · rename_i hNotPV
                cases h
                rcases List.mem_cons.mp he' with rfl | hmem
                · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                          refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns v nextOff hRD
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                        unfold Clause.answer
                        rw [dite_eq_right (fun hm => by cases hm.2.1)]
                        exact hAns v nextOff hRD
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩

private theorem streaming_layout_answer_told {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ e ∈ es, e ∈ events) →
      ∀ {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
        {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (k : Nat) (e₀ : ShapeEvent V), es[k]? = some e₀ →
        ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (coin : M.Val e₀.τ),
          e₀.cls = .given (.coin law) verifier hearers → prover ∈ hearers →
          at_.site = ⟨e₀.site.through, drawToldKey events (idx + k)⟩ →
          M.Valid e₀.τ coin →
          if e₀.site ∈ layout.carry then
            ∃ (wRef : TypedFnRef V a.program.headers.fns [e₀.τ] [.seq unitTy none])
              (rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [e₀.τ, .nat])
              (eqRef : TypedFnRef V a.program.headers.fns [e₀.τ, e₀.τ] [.bool])
              (chunk : List (M.Val unitTy)),
              findLayoutWrite a layout.module unitTy e₀.τ = some wRef ∧
              findLayoutRead a layout.module unitTy e₀.τ = some rRef ∧
              findLayoutEqual a layout.module e₀.τ = some eqRef ∧
              wRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil) = .done (.cons chunk .nil) ∧
              (∀ u ∈ chunk, M.Valid unitTy u) ∧
              (∀ buf, Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                pCs (.give .message [verifier] at_ e₀.τ coin) buf = .done ((), buf ++ chunk)) ∧
              (∀ buf off nextOff,
                rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) =
                  .done (.cons coin (.cons nextOff .nil)) →
                eqRef.eval M (Defs.fnTable M a.program.defs) (.cons coin (.cons coin .nil)) =
                  .done (.cons true .nil) →
                Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                  vCs (.give .message [prover] at_ e₀.τ coin) (buf, (off, ())) =
                  .done ((), (buf, (nextOff, ()))))
          else
            (∀ buf, Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              pCs (.give .message [verifier] at_ e₀.τ coin) buf = .done ((), buf)) ∧
            (∀ buf off, Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              vCs (.give .message [prover] at_ e₀.τ coin) (buf, (off, ())) = .done ((), (buf, (off, ()))))
  | _, [], _, _, _, _, _, _, hk, _, _, _, _, _, _, _, _ => by simp at hk
  | idx, e :: rest, hSub, pCs, vCs, h, k, e₀, hk, law, hearers, at_, coin, hE₀Cls, hPin, hAtSite, hCoinV => by
      unfold buildStreamingLayoutClauses.go at h
      have hSubRest : ∀ e'' ∈ rest, e'' ∈ events := fun e'' he'' => hSub e'' (List.mem_cons_of_mem _ he'')
      have hMemE : e ∈ events := hSub e List.mem_cons_self
      have hFlowNoMatch : e.site ≠ at_.site := by
        intro heq
        have hkEq : e.site.key = drawToldKey events (idx + k) := by
          have := congrArg Site.key heq; rw [hAtSite] at this; exact this
        exact drawToldKey_fresh events (idx + k) (hkEq ▸ List.mem_map.mpr ⟨e, hMemE, rfl⟩)
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          cases k with
          | zero =>
              simp at hk; subst hk
              rw [hE₀Cls] at h; dsimp only at h
              rw [ite_eq_left ⟨rfl, hPin⟩] at h
              have hSiteEq : ⟨e.site.through, drawToldKey events idx⟩ = at_.site := by
                simpa using hAtSite.symm
              by_cases hCar : e.site ∈ layout.carry
              · rw [ite_eq_left hCar] at h
                cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                cases hE : findLayoutEqual a layout.module e.τ <;>
                  simp only [hW, hR, hE] at h
                · cases h
                · cases h
                · cases h
                · cases h
                · cases h
                · cases h
                · cases h
                · rename_i wRef rRef eqRef
                  cases h
                  rw [ite_eq_left hCar]
                  obtain ⟨chH, hWD, hChV⟩ := wRef.eval_done M a (.cons coin .nil) ⟨hCoinV, trivial⟩
                  cases chH with
                  | cons chunk cn =>
                      cases cn
                      refine ⟨wRef, rRef, eqRef, chunk, rfl, rfl, rfl, hWD, hChV.1.1, fun buf => ?_,
                        fun buf off nextOff hRD hEqD => ?_⟩
                      · exact layoutPWriteClause_answer M _ _ prover _ .message [verifier] wRef
                          at_ hSiteEq coin buf chunk hWD pair.1
                      · exact layoutVCarryClause_answer M _ _ hfree verifier prover _ _ rRef eqRef
                          at_ hSiteEq coin buf off nextOff hRD hEqD pair.2
              · rw [ite_eq_right hCar] at h; cases h
                rw [ite_eq_right hCar]
                exact ⟨fun buf => layoutDropClause_answer M _ _ prover _ .message [verifier] at_ hSiteEq coin buf pair.1,
                       fun buf off => layoutDropClause_answer M _ _ verifier _ .message [prover] at_ hSiteEq coin (buf, (off, ())) pair.2⟩
          | succ k' =>
              have hShiftSite : at_.site = ⟨e₀.site.through, drawToldKey events ((idx + 1) + k')⟩ := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAtSite
              have hToldNoMatch : (⟨e.site.through, drawToldKey events idx⟩ : Site) ≠ at_.site := by
                intro heq
                have hkEq : (drawToldKey events idx).number = (drawToldKey events (idx + (k' + 1))).number := by
                  have := congrArg (fun s : Site => s.key.number) heq
                  rw [hAtSite] at this; exact this
                simp only [drawToldKey] at hkEq; omega
              have ih := streaming_layout_answer_told (idx + 1) rest hSubRest hRec k' e₀ hk
                law hearers at_ coin hE₀Cls hPin hShiftSite hCoinV
              cases hCls : e.cls with
              | flow _ _ _ =>
                  rw [hCls] at h; dsimp only at h
                  split at h
                  · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      by_cases hCar : e₀.site ∈ layout.carry
                      · rw [ite_eq_left hCar] at ih ⊢
                        obtain ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, hAnsP, hAnsV⟩ := ih
                        refine ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, fun buf => ?_, fun buf off nO hRD hEqD => ?_⟩
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact hAnsP buf
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact hAnsV buf off nO hRD hEqD
                      · rw [ite_eq_right hCar] at ih ⊢
                        refine ⟨fun buf => ?_, fun buf off => ?_⟩
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact ih.1 buf
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact ih.2 buf off
                  · cases h; exact ih
              | given gkind _ _ =>
                  rw [hCls] at h
                  cases gkind with
                  | coin _ =>
                      dsimp only at h
                      split at h
                      · split at h
                        · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                          cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                          cases hE : findLayoutEqual a layout.module e.τ <;>
                            simp only [hW, hR, hE] at h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                            by_cases hCar : e₀.site ∈ layout.carry
                            · rw [ite_eq_left hCar] at ih ⊢
                              obtain ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, hAnsP, hAnsV⟩ := ih
                              refine ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, fun buf => ?_, fun buf off nO hRD hEqD => ?_⟩
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsP buf
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsV buf off nO hRD hEqD
                            · rw [ite_eq_right hCar] at ih ⊢
                              refine ⟨fun buf => ?_, fun buf off => ?_⟩
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.1 buf
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.2 buf off
                        · cases h
                          by_cases hCar : e₀.site ∈ layout.carry
                          · rw [ite_eq_left hCar] at ih ⊢
                            obtain ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, hAnsP, hAnsV⟩ := ih
                            refine ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, fun buf => ?_, fun buf off nO hRD hEqD => ?_⟩
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsP buf
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsV buf off nO hRD hEqD
                          · rw [ite_eq_right hCar] at ih ⊢
                            refine ⟨fun buf => ?_, fun buf off => ?_⟩
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.1 buf
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.2 buf off
                      · cases h; exact ih
                  | request _ => cases h; exact ih

/-! ### Applying `SuiteLawful` and `LayoutLawful` to `TypedFnRef` / `SafeFnRef` -/

private theorem suiteLawful_allows {d : Deployed V} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawful M)
    {stateTy τ : V.Ty} {derRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy] [τ, stateTy]}
    (hFind : findSuiteDerive d.admitted suite stateTy [] τ = some derRef)
    {e : ShapeEvent V} (hE : e ∈ d.entry.shape.events [] id)
    {law : V.LawKey} {owner h0 : Role} {hs : List Role}
    (hCls : e.cls = .given (.coin law) owner (h0 :: hs)) (hTy : e.τ = τ)
    (hLaw : V.law law = some ⟨[], τ⟩)
    {st st' : M.Val stateTy} {label : List Nat} {coin : M.Val τ}
    (hStV : M.Valid stateTy st) (hLbl : ∀ b, b ∈ label → b < 256)
    (hEval : derRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons st (.cons label .nil)) =
      .done (.cons coin (.cons st' .nil))) :
    Allows M (.coin law) [] .nil τ coin := by
  subst hTy
  unfold Deployed.SuiteLawful at hSuite
  rw [hCon] at hSuite
  obtain ⟨defKey, hInSuite, hProgFind⟩ := findSuiteDerive_some hFind
  have hFnEq : Defs.fnTable M d.admitted.program.defs derRef.hdr derRef.member
      (cast (congrArg (HList M.Val) derRef.insEq.symm) (.cons st (.cons label .nil))) =
      .done (cast (congrArg (HList M.Val) derRef.outsEq.symm) (.cons coin (.cons st' .nil))) := by
    have hEq := derRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons st (.cons label .nil))
    rw [hEval] at hEq
    rcases derRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut
    cases hIn; cases hOut
    exact hEq.symm
  exact hSuite defKey hInSuite derRef.hdr derRef.member hProgFind stateTy [] e law owner h0 hs
    hE hCls hLaw derRef.insEq derRef.outsEq st label .nil coin st' hStV hLbl trivial hFnEq

private theorem layoutLawful_roundTrip {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    {unitTy τ : V.Ty}
    {wRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
    {rRef : SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
    (hW : findLayoutWrite d.admitted layout.module unitTy τ = some wRef)
    (hR : findLayoutRead d.admitted layout.module unitTy τ = some rRef)
    {v : M.Val τ} {chunk pre post : List (M.Val unitTy)}
    (hV : M.Valid τ v) (hPre : ∀ u ∈ pre, M.Valid unitTy u) (hPost : ∀ u ∈ post, M.Valid unitTy u)
    (hWrite : wRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil) =
      .done (.cons chunk .nil)) :
    rRef.eval M (Defs.fnTable M d.admitted.program.defs)
      (.cons (pre ++ chunk ++ post) (.cons pre.length .nil)) =
      .done (.cons v (.cons (pre.length + chunk.length) .nil)) := by
  unfold Deployed.LayoutLawful at hLayLaw
  rw [hLayOpt] at hLayLaw
  obtain ⟨wKey, hInW, hFindW⟩ := findLayoutWrite_some hW
  obtain ⟨rKey, hInR, hFindR⟩ := findLayoutRead_some hR
  have hWF : Defs.fnTable M d.admitted.program.defs wRef.hdr wRef.member
      (cast (congrArg (HList M.Val) wRef.insEq.symm) (.cons v .nil)) =
      .done (cast (congrArg (HList M.Val) wRef.outsEq.symm) (.cons chunk .nil)) := by
    have hEq := wRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil)
    rw [hWrite] at hEq
    rcases wRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut
    cases hIn; cases hOut
    exact hEq.symm
  have hRF := hLayLaw.1 wKey rKey hInW hInR wRef.hdr rRef.hdr wRef.member rRef.member
    hFindW hFindR unitTy τ wRef.insEq wRef.outsEq rRef.insEq rRef.outsEq v chunk pre post
    hV hPre hPost hWF
  have hEqR := rRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs)
    (.cons (pre ++ chunk ++ post) (.cons pre.length .nil))
  rw [hEqR, hRF]
  rcases rRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _⟩
  dsimp only at hIn hOut
  cases hIn; cases hOut
  rfl

private theorem layoutLawful_equal_refl {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    {τ : V.Ty} {eqRef : TypedFnRef V d.admitted.program.headers.fns [τ, τ] [.bool]}
    (hE : findLayoutEqual d.admitted layout.module τ = some eqRef)
    {v : M.Val τ} (hV : M.Valid τ v) :
    eqRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v (.cons v .nil)) =
      .done (.cons true .nil) := by
  unfold Deployed.LayoutLawful at hLayLaw
  rw [hLayOpt] at hLayLaw
  obtain ⟨eqKey, hInE, hFindE⟩ := findLayoutEqual_some hE
  have hEF := hLayLaw.2 eqKey hInE eqRef.hdr eqRef.member hFindE τ eqRef.insEq eqRef.outsEq v hV
  have hEqE := eqRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons v (.cons v .nil))
  rw [hEqE, hEF]
  rcases eqRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
  dsimp only at hIn hOut
  cases hIn; cases hOut
  rfl

/-! ### Mark-peeling helpers for `Proj.begins` and `Proj.settles` -/

private def isRoleMark {A : Type} : Program M A → Prop
  | .call (.begin _) _ => True
  | .call (.settle _) _ => True
  | _ => False

private theorem proj_peel_begin {A B : Type} {r : Role} {post : A → B → Prop} :
    ∀ {p : Protocol M A} {at_ : Occurrence} {k : Nat → Program M B},
      Proj M r post p (.call (.begin at_) k) → Proj M r post p (k 0)
  | _, _, _, .begins h => h
  | _, _, _, .stopsElsewhere h => .stopsElsewhere h
  | _, _, _, .passed h1 h2 h => .passed h1 h2 (proj_peel_begin h)
  | _, _, _, .unheard h1 h2 h => .unheard h1 h2 (fun v => proj_peel_begin (h v))

private theorem proj_peel_settle {A B : Type} {r : Role} {post : A → B → Prop} :
    ∀ {p : Protocol M A} {at_ : Occurrence} {k : Unit → Program M B},
      Proj M r post p (.call (.settle at_) k) → Proj M r post p (k ())
  | _, _, _, .settles h => h
  | _, _, _, .stopsElsewhere h => .stopsElsewhere h
  | _, _, _, .passed h1 h2 h => .passed h1 h2 (proj_peel_settle h)
  | _, _, _, .unheard h1 h2 h => .unheard h1 h2 (fun v => proj_peel_settle (h v))

private theorem peelMarks_alone {A B σ : Type} {r : Role}
    {h : Handler (RSig M) (RSig M) Stop σ}
    (hMarkPass : ∀ (op : ROp M) (s : σ), (op = .begin (ROp.occurrence M op) ∨ op = .settle (ROp.occurrence M op)) →
      h.clause op s = .call op fun reply => .done (reply, s))
    {post : A → B → Prop} {p : Protocol M A} {events : List (ShapeEvent V)}
    (Q : Program M B → Prop)
    (hBase : ∀ q, ¬ isRoleMark M q → Proj M r post p q →
      q.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      q.SafeWith M (fun _ _ => True) (ROp.MatchesShape M r events) (fun _ => True) (fun _ => True) →
      Q q)
    (hStepBegin : ∀ at_ k, Q (k 0) → Q (.call (.begin at_) k))
    (hStepSettle : ∀ at_ k, Q (k ()) → Q (.call (.settle at_) k)) :
    ∀ {q : Program M B}, Proj M r post p q →
      q.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      q.SafeWith M (fun _ _ => True) (ROp.MatchesShape M r events) (fun _ => True) (fun _ => True) →
      Q q
  | .call (.begin at_) k, hProj, hSafe, hShape =>
      hStepBegin at_ k
        (peelMarks_alone hMarkPass Q hBase hStepBegin hStepSettle (proj_peel_begin M hProj)
          (hSafe.2 0 trivial) (hShape.2 0 trivial))
  | .call (.settle at_) k, hProj, hSafe, hShape =>
      hStepSettle at_ k
        (peelMarks_alone hMarkPass Q hBase hStepBegin hStepSettle (proj_peel_settle M hProj)
          (hSafe.2 () trivial) (hShape.2 () trivial))
  | .done _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .halt _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.give ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.get ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.own ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.hear ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape

private theorem stack_run_begin {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (at_ : Occurrence) (k : Nat → Program M B) (s : σ)
    (hPass : h.clause (.begin at_) s = .call (.begin at_) fun n => .done (n, s)) :
    h.run (retryOf M none) (.call (.begin at_) k) s =
      .call (.begin at_) fun n => h.run (retryOf M none) (k n) s := by
  change (h.clause (.begin at_) s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

private theorem stack_run_settle {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (at_ : Occurrence) (k : Unit → Program M B) (s : σ)
    (hPass : h.clause (.settle at_) s = .call (.settle at_) fun u => .done (u, s)) :
    h.run (retryOf M none) (.call (.settle at_) k) s =
      .call (.settle at_) fun u => h.run (retryOf M none) (k u) s := by
  change (h.clause (.settle at_) s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

private theorem stack_run_own {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (gkind : GivenKind V) (hearers : List Role) (at_ : Occurrence)
    (gIns : List V.Ty) (payload : HList M.Val gIns) (τ : V.Ty)
    (k : M.Val τ → Program M B) (s : σ)
    (hPass : h.clause (.own gkind hearers at_ gIns payload τ) s =
      .call (.own gkind hearers at_ gIns payload τ) fun w => .done (w, s)) :
    h.run (retryOf M none) (.call (.own gkind hearers at_ gIns payload τ) k) s =
      .call (.own gkind hearers at_ gIns payload τ) fun w => h.run (retryOf M none) (k w) s := by
  change (h.clause (.own gkind hearers at_ gIns payload τ) s).bind
    (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

private theorem stack_run_clause_done {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (op : ROp M) (k : (RSig M).Reply op → Program M B) (s s' : σ) (reply : (RSig M).Reply op)
    (hStep : h.clause op s = .done (reply, s')) :
    h.run (retryOf M none) (.call op k) s = h.run (retryOf M none) (k reply) s' := by
  change (h.clause op s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hStep]
  rfl

private theorem layer_cast_state {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (l : Layer V hs r hdr₂.ins) : (h ▸ l).state = l.state := by
  subst h; rfl

private theorem layer_cast_clauses {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (l : Layer V hs r hdr₂.ins) :
    (layer_cast_state h l) ▸ (h ▸ l).clauses = l.clauses := by
  subst h; rfl

private theorem ins_cast_valid {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
    (ins : HList (LVal M) hdr₁.ins) (hv : ins.All (fun a v => M.Valid a.ty v)) :
    (cast (congrArg (fun hdr => HList (LVal M) hdr.ins) h) ins).All (fun a v => M.Valid a.ty v) := by
  subst h; exact hv

private theorem insRV_cast_valid {r : Role} {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
    (ins : HList (RV M r) hdr₁.ins) (hv : ins.All (RV.Valid M r)) :
    (cast (congrArg (fun hdr => HList (RV M r) hdr.ins) h) ins).All (RV.Valid M r) := by
  subst h; exact hv

private theorem alone_cast_stack1 {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (hE : hdr₁ = hdr₂) (l : Layer V a.program.headers r hdr₂.ins)
    {st : V.Ty} (hSt : l.state = st) {B : Type} {source : Source M} {p : Program M B}
    {rec : List (Happened M)} {out : B} {s0 s1 : M.Val st}
    (hAl : Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [hE ▸ l]).run
        (retryOf M none) p (.cons ((layer_cast_state hE l).trans hSt ▸ s0) .nil))
      rec (.returned (out, .cons ((layer_cast_state hE l).trans hSt ▸ s1) .nil))) :
    Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) (hE ▸ [l])).run
        (retryOf M none) p (cast (by subst hE; subst hSt; rfl) (HList.cons s0 HList.nil)))
      rec (.returned (out, cast (by subst hE; subst hSt; rfl) (HList.cons s1 HList.nil))) := by
  subst hE; subst hSt; exact hAl

private theorem alone_cast_stack2 {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (hE : hdr₁ = hdr₂) (c l : Layer V a.program.headers r hdr₂.ins)
    {stC stL : V.Ty} (hStC : c.state = stC) (hStL : l.state = stL)
    {B : Type} {source : Source M} {p : Program M B}
    {rec : List (Happened M)} {out : B} {c0 c1 : M.Val stC} {l0 l1 : M.Val stL}
    (hAl : Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [hE ▸ c, hE ▸ l]).run
        (retryOf M none) p (.cons ((layer_cast_state hE c).trans hStC ▸ c0)
          (.cons ((layer_cast_state hE l).trans hStL ▸ l0) .nil)))
      rec (.returned (out, .cons ((layer_cast_state hE c).trans hStC ▸ c1)
        (.cons ((layer_cast_state hE l).trans hStL ▸ l1) .nil)))) :
    Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) (hE ▸ [c, l])).run
        (retryOf M none) p (cast (by subst hE; subst hStC; subst hStL; rfl) (HList.cons c0 (HList.cons l0 HList.nil))))
      rec (.returned (out, cast (by subst hE; subst hStC; subst hStL; rfl) (HList.cons c1 (HList.cons l1 HList.nil)))) := by
  subst hE; subst hStC; subst hStL; exact hAl

private theorem stack_start_one {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} (l : Layer V hs r ins)
    (inputs : HList (RV M r) ins) (taken : HList M.Val (Stack.Takes [l])) :
    Stack.start M fnTable [l] inputs taken =
      (liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
        (Env.positional ((HList.split l.takes taken).1.append (heldValues M r inputs))))).bind
        fun first => .done (.cons first.single .nil) := rfl

private theorem stack_start_two {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} (l₁ l₂ : Layer V hs r ins)
    (inputs : HList (RV M r) ins) (taken : HList M.Val (Stack.Takes [l₁, l₂])) :
    Stack.start M fnTable [l₁, l₂] inputs taken =
      (liftLocal id (l₁.start.denote (localSem M hs.fns fnTable) []
        (Env.positional ((HList.split l₁.takes taken).1.append (heldValues M r inputs))))).bind
        fun f₁ =>
          ((liftLocal id (l₂.start.denote (localSem M hs.fns fnTable) []
            (Env.positional ((HList.split l₂.takes (HList.split l₁.takes taken).2).1.append
              (heldValues M r inputs))))).bind fun f₂ => .done (.cons f₂.single .nil)).map
            fun others => .cons f₁.single others := rfl

private theorem stack_finish_one {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} (l : Layer V hs r ins) (s : M.Val l.state) :
    Stack.finish M fnTable [l] (.cons s .nil) =
      (liftLocal id (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil)))).bind
        fun mine => .done (mine.append .nil) := rfl

private theorem stack_finish_two {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} (l₁ l₂ : Layer V hs r ins)
    (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state) :
    Stack.finish M fnTable [l₁, l₂] (.cons s₁ (.cons s₂ .nil)) =
      (liftLocal id (l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)))).bind
        fun m₁ =>
          ((liftLocal id (l₂.finish.denote (localSem M hs.fns fnTable) []
            (Env.positional (.cons s₂ .nil)))).bind fun m₂ => .done (m₂.append .nil)).map
            fun others => m₁.append others := rfl

private theorem alone_deployed_run_congr {a : Admitted V} {d : Deployed V} (hA : d.admitted = a)
    (hRet : d.retry = none) {r : Role} {s : List (Layer V a.program.headers r d.entry.ins)}
    (hSt : hA ▸ d.stack r = s)
    {source : Source M} {ins : HList (RV M r) d.entry.ins}
    {t₁ : HList M.Val (Stack.Takes (d.stack r))} {t₂ : HList M.Val (Stack.Takes s)}
    (hT : HEq t₁ t₂)
    {rec : List (Happened M)} {out : HList (RV M r) d.entry.outs}
    {g₁ : HList M.Val (Stack.Gives (d.stack r))} {g₂ : HList M.Val (Stack.Gives s)}
    (hG : HEq g₁ g₂)
    (hRun : Alone M source r (runStack a M (hA ▸ d.callee) none r s ins t₂) rec (.returned (out, g₂))) :
    Alone M source r (d.run M r ins t₁) rec (.returned (out, g₁)) := by
  cases d; dsimp only at hA; subst hA
  dsimp only [Deployed.run, runStack, Deployed.callee, Deployed.entry] at hSt hRun ⊢
  subst hSt; rw [hRet]; cases eq_of_heq hT; cases eq_of_heq hG; exact hRun

private theorem ideal_deployed_run_congr {a : Admitted V} {d : Deployed V} (hA : d.admitted = a)
    (hRet : d.retry = none) {r : Role} {s : List (Layer V a.program.headers r d.entry.ins)}
    (hSt : hA ▸ d.stack r = s)
    {ins : HList (RV M r) d.entry.ins}
    {t₁ : HList M.Val (Stack.Takes (d.stack r))} {t₂ : HList M.Val (Stack.Takes s)}
    (hT : HEq t₁ t₂)
    {hG₁ : Stack.Gives (d.stack r) = []} {hG₂ : Stack.Gives s = []}
    (serviceKey : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ)) :
    (Process.answerService serviceKey oracle (d.run M r ins t₁)).map
      (fun out => (out.1, cast (congrArg (HList M.Val) hG₁) out.2)) =
    (Process.answerService serviceKey oracle (runStack a M (hA ▸ d.callee) none r s ins t₂)).map
      (fun out => (out.1, cast (congrArg (HList M.Val) hG₂) out.2)) := by
  cases d; dsimp only at hA; subst hA
  dsimp only [Deployed.run, runStack, Deployed.callee, Deployed.entry] at hSt ⊢
  subst hSt; rw [hRet]; cases eq_of_heq hT; rfl

/-! ### Coupled prover-verifier-protocol simulation for streaming `.derived` and `.authored` -/

private theorem mem_heardCoins_of_event {s : Shape V} {e : ShapeEvent V}
    (hE : e ∈ s.events [] id) {law : V.LawKey} {owner h0 : Role} {hs : List Role}
    (hCls : e.cls = .given (.coin law) owner (h0 :: hs)) :
    e.site ∈ s.heardCoins := by
  unfold Shape.heardCoins
  exact List.mem_filterMap.mpr ⟨e, hE, by simp [hCls]⟩

private theorem simulate_derived {d : Deployed V} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    {layout : Layout} {stateTy suiteUnitTy unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {conP : Layer V d.admitted.program.headers prover d.entry.ins}
    {conV : Layer V d.admitted.program.headers verifier d.entry.ins}
    {layP : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawful M) (hLayLaw : d.LayoutLawful M)
    (hConPState : conP.state = stateTy) (hConVState : conV.state = stateTy)
    (hLayPState : layP.state = .seq unitTy none) (hLayVState : layV.state = streamStateTy unitTy)
    {cS : List (Clause V d.admitted.program.headers prover .nat)}
    (hCC : buildConstructionClauses.go d.admitted suite stateTy suiteUnitTy absRef prover verifier
      none declKey (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hConPState ▸ conP.clauses, hConVState ▸ conV.clauses, cS))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLayPState ▸ layP.clauses, hLayVState ▸ layV.clauses)) :
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (pP : Program M BP) (pV : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
      Proj M prover postP p pP → Proj M verifier postV p pV →
      pP.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      pV.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      pP.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      pV.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      Protocol.MatchesShape M (d.entry.shape.events [] id) p →
      Protocol.UniqueOccs M p →
      LawfulPrivate M source p →
      Fed M source p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source₁ at_ τ = source at_ τ) →
        ∀ e, GExec M source₁ p e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy) (suffix : List (M.Val unitTy))
        (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
            (Defs.rTable M d.admitted.program.defs) [conP, layP]).run (retryOf M none) pP
              (.cons (hConPState.symm ▸ st) (.cons (hLayPState.symm ▸ buf) .nil)))
          recP (.returned (outP, .cons (hConPState.symm ▸ finalSt) (.cons (hLayPState.symm ▸ (buf ++ suffix)) .nil))) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
              (Defs.rTable M d.admitted.program.defs) [conV, layV]).run (retryOf M none) pV
                (.cons (hConVState.symm ▸ st) (.cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
            recV (.returned (outV, .cons (hConVState.symm ▸ finalSt)
              (.cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
        GExec M source' p (.returned a) := by
  -- Eliminate the four state-type equality casts cleanly by destructuring the 4 layers.
  cases conP with
  | mk cPLine cPSt cPTakes cPGives cPClauses cPAgain cPStart cPFin =>
      cases conV with
      | mk cVLine cVSt cVTakes cVGives cVClauses cVAgain cVStart cVFin =>
          cases layP with
          | mk lPLine lPSt lPTakes lPGives lPClauses lPAgain lPStart lPFin =>
              cases layV with
              | mk lVLine lVSt lVTakes lVGives lVClauses lVAgain lVStart lVFin =>
                  dsimp only at hConPState hConVState hLayPState hLayVState
                  subst cPSt; subst cVSt; subst lPSt; subst lVSt
                  dsimp only at hCC hSL
                  let conP' : Layer V d.admitted.program.headers prover d.entry.ins :=
                    ⟨cPLine, stateTy, cPTakes, cPGives, cPClauses, cPAgain, cPStart, cPFin⟩
                  let conV' : Layer V d.admitted.program.headers verifier d.entry.ins :=
                    ⟨cVLine, stateTy, cVTakes, cVGives, cVClauses, cVAgain, cVStart, cVFin⟩
                  let layP' : Layer V d.admitted.program.headers prover d.entry.ins :=
                    ⟨lPLine, .seq unitTy none, lPTakes, lPGives, lPClauses, lPAgain, lPStart, lPFin⟩
                  let layV' : Layer V d.admitted.program.headers verifier d.entry.ins :=
                    ⟨lVLine, streamStateTy unitTy, lVTakes, lVGives, lVClauses, lVAgain, lVStart, lVFin⟩
                  let fnTable := Defs.fnTable M d.admitted.program.defs
                  let rTable := Defs.rTable M d.admitted.program.defs
                  let events := d.entry.shape.events [] id
                  have hConUnm := fun op hCl =>
                    construction_clauses_unmatched_closed M 0 events hCC op hCl
                  have hLayUnm := fun op hCl =>
                    streaming_layout_unmatched_closed M 0 events hSL op hCl
                  have hPassP : ∀ op (st : M.Val stateTy) (buf : List (M.Val unitTy)),
                      ROp.IsClosed M op →
                      (Stack.handler M fnTable rTable [conP', layP']).clause op (.cons st (.cons buf .nil)) =
                        .call op fun reply => .done (reply, .cons st (.cons buf .nil)) := fun op st buf hCl =>
                    stack2_clause_pass M fnTable rTable conP' layP' op st buf
                      (clause_answer_unmatched_all M fnTable rTable op st cPClauses (hConUnm op hCl).1)
                      (clause_answer_unmatched_all M fnTable rTable op buf lPClauses (hLayUnm op hCl).1)
                  have hPassV : ∀ op (st : M.Val stateTy) (lst : M.Val (streamStateTy unitTy)),
                      ROp.IsClosed M op →
                      (Stack.handler M fnTable rTable [conV', layV']).clause op (.cons st (.cons lst .nil)) =
                        .call op fun reply => .done (reply, .cons st (.cons lst .nil)) := fun op st lst hCl =>
                    stack2_clause_pass M fnTable rTable conV' layV' op st lst
                      (clause_answer_unmatched_all M fnTable rTable op st cVClauses (hConUnm op hCl).2)
                      (clause_answer_unmatched_all M fnTable rTable op lst lVClauses (hLayUnm op hCl).2)
                  -- Helper: check what `buildConstructionClauses.go` ensures about any event in `events`
                  have hEventDisc : ∀ e ∈ events,
                      (match e.cls with
                       | .flow _ giver getters =>
                           (giver = prover ∧ verifier ∈ getters) ∨
                           (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                       | .given (.coin law) owner hearers =>
                           (owner = verifier ∧ prover ∈ hearers ∧
                             ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
                           hearers = []
                       | .given (.request _) owner hearers =>
                           (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers)) := by
                    have hGo : ∀ (idx : Nat) (es : List (ShapeEvent V)) {cP' cV' cS'},
                        buildConstructionClauses.go d.admitted suite stateTy suiteUnitTy absRef
                          prover verifier none declKey events idx es = .ok (cP', cV', cS') →
                        ∀ e ∈ es, match e.cls with
                          | .flow _ giver getters =>
                              (giver = prover ∧ verifier ∈ getters) ∨
                              (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                          | .given (.coin law) owner hearers =>
                              (owner = verifier ∧ prover ∈ hearers ∧
                                ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
                              hearers = []
                          | .given (.request _) owner hearers =>
                              (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
                      intro idx es
                      induction es generalizing idx with
                      | nil => intro _ _ _ _ _ he; cases he
                      | cons e rest ih =>
                          intro cP' cV' cS' hGo' e' he'
                          unfold buildConstructionClauses.go at hGo'
                          cases hRec : buildConstructionClauses.go d.admitted suite stateTy suiteUnitTy
                              absRef prover verifier none declKey events (idx + 1) rest with
                          | error _ => rw [hRec] at hGo'; cases hGo'
                          | ok tr =>
                              rw [hRec] at hGo'; dsimp only [bind, Except.bind] at hGo'
                              rcases List.mem_cons.mp he' with rfl | hmem
                              · cases hCls : e'.cls with
                                | flow _ giver getters =>
                                    rw [hCls] at hGo'; dsimp only at hGo'
                                    split at hGo'
                                    · exact .inl ‹_›
                                    · split at hGo'
                                      · exact .inr ‹_›
                                      · cases hGo'
                                | given gkind owner hearers =>
                                    rw [hCls] at hGo'
                                    cases gkind with
                                    | coin law =>
                                        dsimp only at hGo'
                                        split at hGo'
                                        · rename_i hC
                                          cases hLaw : V.law law with
                                          | none => rw [hLaw] at hGo'; cases hGo'
                                          | some sig =>
                                              rw [hLaw] at hGo'; dsimp only at hGo'
                                              split at hGo'
                                              · rename_i hOut
                                                cases hDer : findSuiteDerive d.admitted suite stateTy sig.ins e'.τ with
                                                | none => rw [hDer] at hGo'; cases hGo'
                                                | some _ =>
                                                    rw [hDer] at hGo'; dsimp only at hGo'
                                                    split at hGo'
                                                    · rename_i hIns; exact .inl ⟨hC.1, hC.2, sig, hLaw, hOut, hIns⟩
                                                    · cases hGo'
                                              · cases hGo'
                                        · split at hGo'
                                          · exact .inr ‹_›
                                          · cases hGo'
                                    | request _ =>
                                        dsimp only at hGo'
                                        split at hGo'
                                        · rename_i hReq; exact hReq
                                        · cases hGo'
                              · exact ih (idx + 1) hRec e' hmem
                    exact hGo 0 events hCC
                  intro A BP BV p
                  let SimGoal := fun (p0 : Protocol M A) (postP : A → BP → Prop) (postV : A → BV → Prop)
                      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M)
                      (qP : Program M BP) (qV : Program M BV) =>
                    ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy) (suffix : List (M.Val unitTy))
                      (recP : List (Happened M)) (source' : Source M),
                      (∀ u ∈ suffix, M.Valid unitTy u) ∧
                      Alone M source prover
                        ((Stack.handler M fnTable rTable [conP', layP']).run (retryOf M none) qP
                            (.cons st (.cons buf .nil)))
                        recP (.returned (outP, .cons finalSt (.cons (buf ++ suffix) .nil))) ∧
                      (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                        ∃ recV, Alone M source verifier
                          ((Stack.handler M fnTable rTable [conV', layV']).run (retryOf M none) qV
                              (.cons st (.cons (buf ++ suffix ++ post, (buf.length, ())) .nil)))
                          recV (.returned (outV, .cons finalSt
                            (.cons (buf ++ suffix ++ post, (buf.length + suffix.length, ())) .nil)))) ∧
                      postP a outP ∧ postV a outV ∧
                      Lawful M source' p0 ∧
                      (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
                      GExec M source' p0 (.returned a)
                  induction p with
                  | done a =>
                      intro postP postV pP pV st buf source hStV hBufV hProjP hProjV hSafeP hSafeV hShapeP hShapeV _ _ _ _ _
                      refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conP', layP'])
                        (fun op s hM => by
                          cases s with | cons st' s1 => cases s1 with | cons buf' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ _ trivial)
                        (fun qP => SimGoal (.done a) postP postV st buf source qP pV)
                        (fun qP hNotMP hPP hSP hShP => ?_)
                        (fun at_ kP h => by
                          obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a', outP, outV, fSt, suf, .began prover at_ :: recP, src', h1,
                            by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .begin h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        (fun at_ kP h => by
                          obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a', outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1,
                            by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .settle h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        hProjP hSafeP hShapeP
                      cases hPP with
                      | done hPostP =>
                          refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conV', layV'])
                            (fun op s hM => by
                              cases s with | cons st' s1 => cases s1 with | cons lst' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ _ trivial)
                            (fun qV => SimGoal (.done a) postP postV st buf source (.done _) qV)
                            (fun qV hNotMV hPV hSV hShV => ?_)
                            (fun at_ kV h => by
                              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2,
                                fun post hPost =>
                                  let ⟨recV, hAlV⟩ := h3 post hPost
                                  ⟨.began verifier at_ :: recV,
                                    by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hAlV⟩,
                                h4, h5, h6, h7, h8⟩)
                            (fun at_ kV h => by
                              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2,
                                fun post hPost =>
                                  let ⟨recV, hAlV⟩ := h3 post hPost
                                  ⟨.settled verifier at_ :: recV,
                                    by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hAlV⟩,
                                h4, h5, h6, h7, h8⟩)
                            hProjV hSafeV hShapeV
                          cases hPV with
                          | done hPostV =>
                              exact ⟨a, _, _, st, [], [], source, (fun _ h => nomatch h),
                                by simpa [Handler.run] using Alone.done,
                                fun post _ => ⟨[], by simpa [Handler.run] using Alone.done⟩,
                                hPostP, hPostV, trivial, fun _ _ _ => rfl, ⟨[], .done⟩⟩
                          | begins _ => exact False.elim (hNotMV trivial)
                          | settles _ => exact False.elim (hNotMV trivial)
                      | begins _ => exact False.elim (hNotMP trivial)
                      | settles _ => exact False.elim (hNotMP trivial)
                  | halt payload =>
                      intro _ _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ _ hNoHalt
                      obtain ⟨a, hContra⟩ := hNoHalt source trivial (fun _ _ _ => rfl)
                        (.stopped payload.1 payload.2) ⟨[], .halt⟩
                      cases hContra
                  | call op k ih =>
                      intro postP postV pP pV st buf source hStV hBufV hProjP hProjV hSafeP hSafeV
                        hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt
                      -- Peel leading `.begin` / `.settle` marks from prover and verifier
                      refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conP', layP'])
                        (fun op s hM => by
                          cases s with | cons st' s1 => cases s1 with | cons buf' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ _ trivial)
                        (fun qP => SimGoal (.call op k) postP postV st buf source qP pV)
                        (fun qP hNotMP hPP hSP hShP => ?_)
                        (fun at_ kP h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, .began prover at_ :: recP, src', h1,
                            by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .begin h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        (fun at_ kP h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1,
                            by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .settle h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        hProjP hSafeP hShapeP
                      refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conV', layV'])
                        (fun op s hM => by
                          cases s with | cons st' s1 => cases s1 with | cons lst' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ _ trivial)
                        (fun qV => SimGoal (.call op k) postP postV st buf source qP qV)
                        (fun qV hNotMV hPV hSV hShV => ?_)
                        (fun at_ kV h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2,
                            fun post hPost =>
                              let ⟨recV, hAlV⟩ := h3 post hPost
                              ⟨.began verifier at_ :: recV,
                                by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hAlV⟩,
                            h4, h5, h6, h7, h8⟩)
                        (fun at_ kV h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2,
                            fun post hPost =>
                              let ⟨recV, hAlV⟩ := h3 post hPost
                              ⟨.settled verifier at_ :: recV,
                                by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hAlV⟩,
                            h4, h5, h6, h7, h8⟩)
                        hProjV hSafeV hShapeV
                      cases op with
                      | flow kind giver getters at_ τ x =>
                          have hNoHalt' : ∀ source₁, Lawful M source₁ (k ()) →
                              (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                              ∀ e, GExec M source₁ (k ()) e → ∃ a, e = .returned a := by
                            intro source₁ hL₁ hAg e ⟨evs, hRun⟩
                            exact hNoHalt source₁ hL₁ hAg e ⟨_, .flow hRun⟩
                          cases hPP with
                          | begins _ => exact False.elim (hNotMP trivial)
                          | settles _ => exact False.elim (hNotMP trivial)
                          | gave hNotIn hPP' =>
                              -- `giver = prover`
                              obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
                              have hDisc := hEventDisc eP hEP
                              rw [hClsP] at hDisc
                              have hVin : verifier ∈ getters := by
                                rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
                                · exact hV
                                · exact absurd rfl hNotP
                              have hMsgV : M.Valid τ x := hSP.1
                              cases hPV with
                              | begins _ => exact False.elim (hNotMV trivial)
                              | settles _ => exact False.elim (hNotMV trivial)
                              | gave _ _ => exact absurd rfl hNe
                              | passed _ hVOut _ => exact absurd hVin hVOut
                              | got _ _ hPV' =>
                                  obtain ⟨encP, enc, st', hEncFindP, hEncD, hAbsD, hSt'V, hConPAns⟩ :=
                                    construction_clauses_answer_prover_flow M 0 events hCC
                                      kind getters at_ τ x st hMsgV hStV ⟨eP, hEP, hSiteP, hTyP, hClsP⟩
                                  obtain ⟨encV, hEncFindV, hConVAns⟩ :=
                                    construction_clauses_answer_verifier_flow M 0 events hCC
                                      kind at_ τ st ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                  have hEncEq : encP = encV := Option.some.inj (hEncFindP.symm.trans hEncFindV)
                                  subst hEncEq
                                  have hAtOcc : (⟨at_.path, at_.site.key⟩ : Occurrence).site = at_.site := rfl
                                  obtain ⟨wRef, chunk, hWFind, hWD, hChV, hLayPAns⟩ :=
                                    streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                                      kind getters ⟨at_.path, at_.site.key⟩ τ x buf hMsgV
                                      ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                                  obtain ⟨rRef, hRFind, _⟩ :=
                                    streaming_layout_answer_verifier_flow M 0 events hSL
                                      kind ⟨at_.path, at_.site.key⟩ τ buf buf.length
                                      ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                  have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                                    intro u hu
                                    rcases List.mem_append.mp hu with h1 | h2
                                    · exact hBufV u h1
                                    · exact hChV u h2
                                  obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV,
                                    hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                    ih () _ _ st' (buf ++ chunk) source hSt'V hBufChV hPP' hPV'
                                      (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                                      (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                  have hStepP : (Stack.handler M fnTable rTable [conP', layP']).clause
                                      (.give kind getters at_ τ x) (.cons st (.cons buf .nil)) =
                                      .done ((), .cons st' (.cons (buf ++ chunk) .nil)) :=
                                    stack2_clause_step M fnTable rTable conP' layP' _ _ st st' buf (buf ++ chunk)
                                      () () _ hConPAns hLayPAns rfl
                                  refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src', ?_, ?_, ?_,
                                    hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
                                  · intro u hu
                                    rcases List.mem_append.mp hu with h1 | h2
                                    · exact hChV u h1
                                    · exact hSufV u h2
                                  · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                    simpa [List.append_assoc] using hAlP
                                  · intro post hPost
                                    have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                                      intro u hu
                                      rcases List.mem_append.mp hu with h1 | h2
                                      · exact hSufV u h1
                                      · exact hPost u h2
                                    have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind
                                      hMsgV hBufV hSufPostV hWD
                                    have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                                      simp [List.append_assoc]
                                    obtain ⟨rRef', hRFind', hLayVAns'⟩ :=
                                      streaming_layout_answer_verifier_flow M 0 events hSL
                                        kind ⟨at_.path, at_.site.key⟩ τ
                                        (buf ++ chunk ++ (suf' ++ post)) buf.length
                                        ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                    have hREq : rRef = rRef' := Option.some.inj (hRFind.symm.trans hRFind')
                                    subst hREq
                                    have hLayVDone := hLayVAns' x (buf.length + chunk.length) hRD
                                    have hKV :
                                        ((((liftLocal (S := RSig M) id (encP.eval M fnTable (.cons x .nil))).bind fun enc0 =>
                                          (liftLocal (S := RSig M) id (absRef.eval M fnTable
                                            (.cons st (.cons (msgLabel at_.site) (.cons enc0.single .nil))))).map
                                            fun nextSt => aloneIn M verifier (.cons x nextSt)).mapHalt
                                              fun why => (why, st)).map fun out =>
                                          let values := HList.split [τ] (aloneOut M verifier out)
                                          (values.1.single, values.2.single)) =
                                        .done (x, st') := by
                                      rw [hEncD]
                                      simp only [liftLocal_done, Process.bind, HList.single]
                                      rw [hAbsD]
                                      simp only [liftLocal_done, Process.map, Process.mapHalt,
                                        aloneOut_aloneIn, HList.split]
                                    have hStepV : (Stack.handler M fnTable rTable [conV', layV']).clause
                                        (.get kind prover at_ τ)
                                        (.cons st (.cons (buf ++ chunk ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                        .done (x, .cons st' (.cons (buf ++ chunk ++ (suf' ++ post),
                                          (buf.length + chunk.length, ())) .nil)) :=
                                      stack2_clause_step M fnTable rTable conV' layV' _ _ st st'
                                        (buf ++ chunk ++ (suf' ++ post), (buf.length, ()))
                                        (buf ++ chunk ++ (suf' ++ post), (buf.length + chunk.length, ()))
                                        x x _ hConVAns hLayVDone hKV
                                    obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                    refine ⟨recV, ?_⟩
                                    rw [hBufEq]
                                    rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                    have hLenEq : buf.length + (chunk ++ suf').length =
                                        (buf ++ chunk).length + suf'.length := by
                                      simp [List.length_append, Nat.add_assoc]
                                    have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                                      simp [List.append_assoc]
                                    rw [hLenEq, hBufEq2, ← List.length_append]
                                    exact hAlV'
                          | got hGNeP hPIn _ =>
                              obtain ⟨eP, hEP, _, _, _, gs', hPin', hClsP⟩ := hShP.1
                              have hDisc := hEventDisc eP hEP
                              rw [hClsP] at hDisc
                              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
                              · exact absurd hEqP hGNeP
                              · exact absurd hPin' hNotP
                          | passed hGNeP hPOut hPP' =>
                              cases hPV with
                              | begins _ => exact False.elim (hNotMV trivial)
                              | settles _ => exact False.elim (hNotMV trivial)
                              | gave _ _ =>
                                  obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
                                  have hDisc := hEventDisc eV hEV
                                  rw [hClsV] at hDisc
                                  rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
                                  · exact absurd hEqP.symm hNe
                                  · exact absurd rfl hNotV
                              | got _ hVin _ =>
                                  obtain ⟨eV, hEV, _, _, _, gs', hVin', hClsV⟩ := hShV.1
                                  have hDisc := hEventDisc eV hEV
                                  rw [hClsV] at hDisc
                                  rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
                                  · exact absurd hEqP hGNeP
                                  · exact absurd hVin' hNotV
                              | passed _ _ hPV' =>
                                  obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                                    ih () _ _ st buf source hStV hBufV hPP' hPV' hSP hSV hShP hShV
                                      (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                  exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
                      | given gkind owner hearers at_ gIns payload τ =>
                          -- Case split on whether this is a verifier-owned heard coin (`owner = verifier ∧ prover ∈ hearers`)
                          -- vs a private/service event answered by `source`.
                          have hCoinDec : Decidable (∃ law, gkind = .coin law) :=
                            match gkind with
                            | .coin law => isTrue ⟨law, rfl⟩
                            | .request _ => isFalse fun ⟨_, h⟩ => nomatch h
                          have hHeardDec : Decidable ((∃ law, gkind = .coin law) ∧ owner = verifier ∧ prover ∈ hearers) :=
                            @instDecidableAnd _ _ hCoinDec (@instDecidableAnd _ _ inferInstance inferInstance)
                          cases hHeardDec with
                          | isTrue hHeardCoin =>
                            obtain ⟨⟨law, rfl⟩, hOwV, hPin⟩ := hHeardCoin
                            subst owner
                            have hNonEmpty : ∃ h0 hs, hearers = h0 :: hs := by
                              cases hearers with
                              | nil => cases hPin
                              | cons h0 hs => exact ⟨h0, hs, rfl⟩
                            obtain ⟨h0, hs, hHCons⟩ := hNonEmpty
                            cases hPP with
                            | begins _ => exact False.elim (hNotMP trivial)
                            | settles _ => exact False.elim (hNotMP trivial)
                            | owned _ => exact absurd rfl hNe
                            | unheard _ hOut _ => exact absurd hPin hOut
                            | heard _ _ hPP' =>
                                cases hPV with
                                | begins _ => exact False.elim (hNotMV trivial)
                                | settles _ => exact False.elim (hNotMV trivial)
                                | heard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | unheard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | owned hPV' =>
                                    obtain ⟨eV, hEV, hSiteV, hTyV, hClsV, hTypedV⟩ := hShV.1
                                    have hDisc := hEventDisc eV hEV
                                    rw [hClsV] at hDisc
                                    have hGInsNil : gIns = [] := by
                                      rcases hDisc with ⟨_, _, sig, hLaw, _, hSigIns⟩ | hNil
                                      · obtain ⟨s, hsLaw, hsIns, _⟩ := hTypedV
                                        rw [hLaw] at hsLaw; cases hsLaw
                                        rw [← hsIns, hSigIns]
                                      · subst hNil; cases hPin
                                    subst hGInsNil
                                    cases payload
                                    obtain ⟨idxP, ⟨ePSite, ePCls, ePτ⟩, derP, coinP, stP', hIdxP, hSiteP, hTyP,
                                      ⟨hsP, hPinP, hClsP⟩, hDerFindP, hDerDP, hCoinPV, hStP'V, hConPAns⟩ :=
                                      construction_clauses_answer_prover_coin M 0 events
                                        (fun k e hk => by simpa using hk) hCC law at_ τ st hStV
                                        ⟨eV, hEV, hSiteV, hTyV, hearers, hPin, hClsV⟩
                                    obtain ⟨idxV, ⟨eV'Site, eV'Cls, eV'τ⟩, derV, coinV, stV', hIdxV, hSiteV', hTyV',
                                      hClsV', hLawV', hDerFindV, hDerDV, hCoinVV, hStV'V, hConVAns⟩ :=
                                      construction_clauses_answer_verifier_coin M 0 events
                                        (fun k e hk => by simpa using hk) hCC law hearers at_ τ st hStV
                                        ⟨eV, hEV, hSiteV, hTyV, hPin, hClsV⟩
                                    dsimp only at hSiteP hTyP hClsP hSiteV' hTyV' hClsV'
                                    subst ePτ; subst eV'τ
                                    have hDerEq : derP = derV := Option.some.inj (hDerFindP.symm.trans hDerFindV)
                                    subst hDerEq
                                    have hEvalEq : Process.done (HList.cons coinP (HList.cons stP' HList.nil)) =
                                        .done (.cons coinV (.cons stV' .nil)) := hDerDP.symm.trans hDerDV
                                    cases hEvalEq
                                    -- `coinP = coinV`, `stP' = stV'`!
                                    have hAllowsCoin : Allows M (.coin law) [] .nil τ coinP :=
                                      suiteLawful_allows M hConDecl hSuiteLaw hDerFindV
                                        (List.mem_of_getElem? hIdxV) (hHCons ▸ hClsV') rfl hLawV'
                                        hStV (drawLabel_bytes at_.site) hDerDV
                                    have hAtHeard : at_.site ∈ d.entry.shape.heardCoins := by
                                      rw [← hSiteV']
                                      exact mem_heardCoins_of_event (List.mem_of_getElem? hIdxV) (hHCons ▸ hClsV')
                                    have hLP' : LawfulPrivate M source (k coinP) := by
                                      subst hHCons; exact hLP coinP hAllowsCoin
                                    have hFed' : Fed M source (k coinP) := by
                                      subst hHCons; exact hFed coinP hAllowsCoin
                                    have hOccK : Protocol.OccsIn M (· ≠ at_) (k coinP) := (hUniq coinP).1
                                    have hNoHalt' : ∀ source₁, Lawful M source₁ (k coinP) →
                                        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                          source₁ at' τ' = source at' τ') →
                                        ∀ e, GExec M source₁ (k coinP) e → ∃ a, e = .returned a := by
                                      intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
                                      let source₂ := patchSource M source₁ at_ τ coinP
                                      have hAgree12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = source₂ at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M source₁ at_ τ coinP hne τ').symm
                                      have hL₂ : Lawful M source₂ (.call (.given (.coin law) verifier hearers at_ [] .nil τ) k) := by
                                        intro v hv
                                        dsimp only [source₂] at hv
                                        rw [patchSource_self] at hv; cases hv
                                        exact ⟨hAllowsCoin, lawful_of_agree M hAgree12 hOccK hL₁⟩
                                      have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                          source₂ at' τ' = source at' τ' := by
                                        intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                        dsimp only [source₂]
                                        rw [patchSource_ne M source₁ at_ τ coinP hne τ']
                                        exact hAg₁ at' τ' hNotIn
                                      have hRun₂ : GRun M source₂
                                          (.call (.given (.coin law) verifier hearers at_ [] .nil τ) k) _ e :=
                                        .given (patchSource_self M source₁ at_ τ coinP)
                                          (grun_of_agree M hAgree12 hOccK hRun₁)
                                      exact hNoHalt source₂ hL₂ hAg₂ e ⟨_, hRun₂⟩
                                    -- Now handle layout carry vs drop cleanly!
                                    have hToldSiteP : (⟨at_.path, drawToldKey events idxP⟩ : Occurrence).site =
                                        ⟨ePSite.through, drawToldKey events (0 + idxP)⟩ := by
                                      simpa using site_told_from_match hSiteP (k := drawToldKey events idxP)
                                    have hToldSiteV : (⟨at_.path, drawToldKey events idxV⟩ : Occurrence).site =
                                        ⟨eV'Site.through, drawToldKey events (0 + idxV)⟩ := by
                                      simpa using site_told_from_match hSiteV' (k := drawToldKey events idxV)
                                    have hCarryP := streaming_layout_answer_told M 0 events (fun _ h => h) hSL
                                      idxP ⟨ePSite, ePCls, τ⟩ hIdxP law hsP ⟨at_.path, drawToldKey events idxP⟩
                                      coinP hClsP hPinP hToldSiteP hCoinPV
                                    have hCarryV := streaming_layout_answer_told M 0 events (fun _ h => h) hSL
                                      idxV ⟨eV'Site, eV'Cls, τ⟩ hIdxV law hearers ⟨at_.path, drawToldKey events idxV⟩
                                      coinP hClsV' hPin hToldSiteV hCoinPV
                                    by_cases hCar : at_.site ∈ layout.carry
                                    · have hCarP : ePSite ∈ layout.carry := hSiteP.symm ▸ hCar
                                      have hCarV : eV'Site ∈ layout.carry := hSiteV'.symm ▸ hCar
                                      rw [ite_eq_left hCarP] at hCarryP
                                      rw [ite_eq_left hCarV] at hCarryV
                                      obtain ⟨wRef, _, _, chunk, hWFind, _, _, hWD, hChV, hLayPAns, _⟩ := hCarryP
                                      obtain ⟨wRefV, rRef, eqRef, chunkV, hWFindV, hRFind, hEqFind, _, _, _, hLayVAns⟩ := hCarryV
                                      have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                                        intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hBufV u h1
                                        · exact hChV u h2
                                      obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih coinP _ _ stP' (buf ++ chunk) source hStP'V hBufChV
                                          (hPP' coinP) (hPV' coinP)
                                          (hSP.2 coinP hCoinPV) (hSV.2 coinP hCoinPV)
                                          (hShP.2 coinP trivial) (hShV.2 coinP trivial)
                                          (hPShape.2 coinP) (hUniq coinP).2 hLP' hFed' hNoHalt'
                                      let src'' := patchSource M src' at_ τ coinP
                                      have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M src' at_ τ coinP hne τ').symm
                                      have hStepP : (Stack.handler M fnTable rTable [conP', layP']).clause
                                          (.hear (.coin law) verifier at_ τ) (.cons st (.cons buf .nil)) =
                                          .done (coinP, .cons stP' (.cons (buf ++ chunk) .nil)) :=
                                        stack2_clause_step M fnTable rTable conP' layP' _ _ st stP' buf (buf ++ chunk)
                                          () coinP _ hConPAns (hLayPAns buf) rfl
                                      refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src'', ?_, ?_, ?_,
                                        hPostP, hPostV, ?_, ?_, ?_⟩
                                      · intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hChV u h1
                                        · exact hSufV u h2
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        simpa [List.append_assoc] using hAlP
                                      · intro post hPost
                                        have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                                          intro u hu
                                          rcases List.mem_append.mp hu with h1 | h2
                                          · exact hSufV u h1
                                          · exact hPost u h2
                                        have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind
                                          hCoinPV hBufV hSufPostV hWD
                                        have hEqD := layoutLawful_equal_refl M hLayDecl hLayLaw hEqFind hCoinPV
                                        have hLayVDone := hLayVAns (buf ++ chunk ++ (suf' ++ post))
                                          buf.length (buf.length + chunk.length) hRD hEqD
                                        have hStepV : (Stack.handler M fnTable rTable [conV', layV']).clause
                                            (.own (.coin law) hearers at_ [] .nil τ)
                                            (.cons st (.cons (buf ++ chunk ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                            .done (coinP, .cons stP' (.cons (buf ++ chunk ++ (suf' ++ post),
                                              (buf.length + chunk.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV' layV' _ _ st stP'
                                            (buf ++ chunk ++ (suf' ++ post), (buf.length, ()))
                                            (buf ++ chunk ++ (suf' ++ post), (buf.length + chunk.length, ()))
                                            () coinP _ hConVAns hLayVDone rfl
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨recV, ?_⟩
                                        have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                                          simp [List.append_assoc]
                                        rw [hBufEq]
                                        rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                        have hLenEq : buf.length + (chunk ++ suf').length =
                                            (buf ++ chunk).length + suf'.length := by
                                          simp [List.length_append, Nat.add_assoc]
                                        have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                                          simp [List.append_assoc]
                                        rw [hLenEq, hBufEq2, ← List.length_append]
                                        exact hAlV'
                                      · intro v hv
                                        dsimp only [src''] at hv
                                        rw [patchSource_self] at hv; cases hv
                                        exact ⟨hAllowsCoin, lawful_of_agree M hAgPatch hOccK hLSrc'⟩
                                      · intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                        dsimp only [src'']
                                        rw [patchSource_ne M src' at_ τ coinP hne τ']
                                        exact hAgSrc' at' τ' hNotIn
                                      · exact ⟨_, .given (patchSource_self M src' at_ τ coinP)
                                          (grun_of_agree M hAgPatch hOccK hRun')⟩
                                    · have hCarP : ePSite ∉ layout.carry := hSiteP.symm ▸ hCar
                                      have hCarV : eV'Site ∉ layout.carry := hSiteV'.symm ▸ hCar
                                      rw [ite_eq_right hCarP] at hCarryP
                                      rw [ite_eq_right hCarV] at hCarryV
                                      obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih coinP _ _ stP' buf source hStP'V hBufV
                                          (hPP' coinP) (hPV' coinP)
                                          (hSP.2 coinP hCoinPV) (hSV.2 coinP hCoinPV)
                                          (hShP.2 coinP trivial) (hShV.2 coinP trivial)
                                          (hPShape.2 coinP) (hUniq coinP).2 hLP' hFed' hNoHalt'
                                      let src'' := patchSource M src' at_ τ coinP
                                      have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M src' at_ τ coinP hne τ').symm
                                      have hStepP : (Stack.handler M fnTable rTable [conP', layP']).clause
                                          (.hear (.coin law) verifier at_ τ) (.cons st (.cons buf .nil)) =
                                          .done (coinP, .cons stP' (.cons buf .nil)) :=
                                        stack2_clause_step M fnTable rTable conP' layP' _ _ st stP' buf buf
                                          () coinP _ hConPAns (hCarryP.1 buf) rfl
                                      refine ⟨a, outP, outV, fSt, suf', recP, src'', hSufV, ?_, ?_,
                                        hPostP, hPostV, ?_, ?_, ?_⟩
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        exact hAlP
                                      · intro post hPost
                                        have hStepV : (Stack.handler M fnTable rTable [conV', layV']).clause
                                            (.own (.coin law) hearers at_ [] .nil τ)
                                            (.cons st (.cons (buf ++ suf' ++ post, (buf.length, ())) .nil)) =
                                            .done (coinP, .cons stP' (.cons (buf ++ suf' ++ post, (buf.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV' layV' _ _ st stP'
                                            (buf ++ suf' ++ post, (buf.length, ()))
                                            (buf ++ suf' ++ post, (buf.length, ()))
                                            () coinP _ hConVAns (hCarryV.2 (buf ++ suf' ++ post) buf.length) rfl
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨recV, ?_⟩
                                        rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                        exact hAlV'
                                      · intro v hv
                                        dsimp only [src''] at hv
                                        rw [patchSource_self] at hv; cases hv
                                        exact ⟨hAllowsCoin, lawful_of_agree M hAgPatch hOccK hLSrc'⟩
                                      · intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                        dsimp only [src'']
                                        rw [patchSource_ne M src' at_ τ coinP hne τ']
                                        exact hAgSrc' at' τ' hNotIn
                                      · exact ⟨_, .given (patchSource_self M src' at_ τ coinP)
                                          (grun_of_agree M hAgPatch hOccK hRun')⟩
                          | isFalse hHeardCoin =>
                            -- Non-heard-coin `.given`: private coin (`hearers = []`) or `.request _`
                            obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
                            have hDisc := hEventDisc eG hEG
                            rw [hClsG] at hDisc
                            have hNotHeardCoin : (∃ law, gkind = .coin law ∧ hearers = []) ∨
                                (∃ svc, gkind = .request svc ∧
                                  (owner = prover ∨ prover ∉ hearers) ∧
                                  (owner = verifier ∨ verifier ∉ hearers)) := by
                              cases gkind with
                              | coin law =>
                                  rcases hDisc with ⟨hO, hP, _⟩ | hNil
                                  · exact absurd ⟨⟨law, rfl⟩, hO, hP⟩ hHeardCoin
                                  · exact .inl ⟨law, rfl, hNil⟩
                              | request svc =>
                                  exact .inr ⟨svc, rfl, hDisc⟩
                            have hSrcFed : ∃ v, source at_ τ = some v ∧ Fed M source (k v) := by
                              rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
                              · exact hFed
                              · exact hFed
                            obtain ⟨v, hSrc, hFed'⟩ := hSrcFed
                            have hLPv : Allows M gkind gIns payload τ v ∧ LawfulPrivate M source (k v) := by
                              rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
                              · exact hLP v hSrc
                              · exact hLP v hSrc
                            obtain ⟨hAllows, hLP'⟩ := hLPv
                            have hValV : M.Valid τ v := allows_valid M hAllows
                            have hIsClOwn : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ) := by
                              rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩ <;> trivial
                            have hOccK : Protocol.OccsIn M (· ≠ at_) (k v) := (hUniq v).1
                            have hNoHalt' : ∀ source₁, Lawful M source₁ (k v) →
                                (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                  source₁ at' τ' = source at' τ') →
                                ∀ e, GExec M source₁ (k v) e → ∃ a, e = .returned a := by
                              intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
                              let source₂ := patchSource M source₁ at_ τ v
                              have hAgree12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = source₂ at' τ' :=
                                fun at' τ' hne => (patchSource_ne M source₁ at_ τ v hne τ').symm
                              have hL₂ : Lawful M source₂ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
                                intro w hw
                                dsimp only [source₂] at hw
                                rw [patchSource_self] at hw; cases hw
                                exact ⟨hAllows, lawful_of_agree M hAgree12 hOccK hL₁⟩
                              have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                  source₂ at' τ' = source at' τ' := by
                                intro at' τ' hNotIn
                                unfold source₂ patchSource
                                split
                                · rename_i heq
                                  cases heq.1; cases heq.2; exact hSrc.symm
                                · exact hAg₁ at' τ' hNotIn
                              exact hNoHalt source₂ hL₂ hAg₂ e
                                ⟨_, .given (patchSource_self M source₁ at_ τ v)
                                  (grun_of_agree M hAgree12 hOccK hRun₁)⟩
                            have hWrapSrc : ∀ (src' : Source M) {evs' a},
                                Lawful M src' (k v) →
                                (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src' at' τ' = source at' τ') →
                                GRun M src' (k v) evs' (.returned a) →
                                ∃ src'', Lawful M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) ∧
                                  (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src'' at' τ' = source at' τ') ∧
                                  GExec M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) (.returned a) := by
                              intro src' evs' a hL' hAg' hRun'
                              let src'' := patchSource M src' at_ τ v
                              have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                              refine ⟨src'', ?_, ?_, ?_⟩
                              · intro w hw
                                dsimp only [src''] at hw
                                rw [patchSource_self] at hw; cases hw
                                exact ⟨hAllows, lawful_of_agree M hAgP hOccK hL'⟩
                              · intro at' τ' hNotIn
                                unfold src'' patchSource
                                split
                                · rename_i heq; cases heq.1; cases heq.2; exact hSrc.symm
                                · exact hAg' at' τ' hNotIn
                              · exact ⟨_, .given (patchSource_self M src' at_ τ v)
                                  (grun_of_agree M hAgP hOccK hRun')⟩
                            cases hPP with
                            | begins _ => exact False.elim (hNotMP trivial)
                            | settles _ => exact False.elim (hNotMP trivial)
                            | heard hONeP hPin _ =>
                                rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, hPReq, _⟩
                                · cases hPin
                                · rcases hPReq with hEqO | hNotIn
                                  · exact absurd hEqO hONeP
                                  · exact absurd hPin hNotIn
                            | owned hPP' =>
                                -- `owner = prover`
                                cases hPV with
                                | begins _ => exact False.elim (hNotMV trivial)
                                | settles _ => exact False.elim (hNotMV trivial)
                                | owned _ => exact absurd rfl hNe
                                | heard _ hVin _ =>
                                    rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                                    · cases hVin
                                    · rcases hVReq with hEqO | hNotIn
                                      · exact absurd hEqO hNe
                                      · exact absurd hVin hNotIn
                                | unheard _ _ hPV' =>
                                    obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                      ih v _ _ st buf source hStV hBufV (hPP' v) (hPV' v)
                                        (hSP.2 v hValV) hSV (hShP.2 v trivial) hShV
                                        (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                    obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                    refine ⟨a, outP, outV, fSt, suf,
                                      .owned prover gkind at_ τ v :: recP, src'', hSufV, ?_, hAlV,
                                      hPostP, hPostV, hL'', hAg'', hGEx''⟩
                                    rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassP _ _ _ hIsClOwn)]
                                    exact .own hSrc hAlP
                            | unheard hONeP _ hPP' =>
                                cases hPV with
                                | begins _ => exact False.elim (hNotMV trivial)
                                | settles _ => exact False.elim (hNotMV trivial)
                                | heard hONeV hVin _ =>
                                    rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                                    · cases hVin
                                    · rcases hVReq with hEqO | hNotIn
                                      · exact absurd hEqO hONeV
                                      · exact absurd hVin hNotIn
                                | owned hPV' =>
                                    -- `owner = verifier`
                                    obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                      ih v _ _ st buf source hStV hBufV (hPP' v) (hPV' v)
                                        hSP (hSV.2 v hValV) hShP (hShV.2 v trivial)
                                        (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                    obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                    refine ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, ?_,
                                      hPostP, hPostV, hL'', hAg'', hGEx''⟩
                                    intro post hPost
                                    obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                    refine ⟨.owned verifier gkind at_ τ v :: recV, ?_⟩
                                    rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassV _ _ _ hIsClOwn)]
                                    exact .own hSrc hAlV'
                                | unheard _ _ hPV' =>
                                    obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                      ih v _ _ st buf source hStV hBufV (hPP' v) (hPV' v)
                                        hSP hSV hShP hShV
                                        (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                    obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                    exact ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hL'', hAg'', hGEx''⟩

private theorem simulate_authored {d : Deployed V} {layout : Layout} {unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {layP : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hLayDecl : d.declaration.layout = some layout)
    (hLayLaw : d.LayoutLawful M)
    (hLayPState : layP.state = .seq unitTy none) (hLayVState : layV.state = streamStateTy unitTy)
    {cS : List (Clause V d.admitted.program.headers prover .nat)}
    (hAuth : checkAuthoredEvents d.admitted prover verifier none declKey
      (d.entry.shape.events [] id) = .ok cS)
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLayPState ▸ layP.clauses, hLayVState ▸ layV.clauses)) :
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (pP : Program M BP) (pV : Program M BV)
      (buf : List (M.Val unitTy)) (source : Source M),
      (∀ u ∈ buf, M.Valid unitTy u) →
      Proj M prover postP p pP → Proj M verifier postV p pV →
      pP.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      pV.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      pP.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      pV.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      Protocol.MatchesShape M (d.entry.shape.events [] id) p →
      Protocol.UniqueOccs M p →
      LawfulPrivate M source p →
      Fed M source p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source₁ at_ τ = source at_ τ) →
        ∀ e, GExec M source₁ p e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (suffix : List (M.Val unitTy))
        (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
            (Defs.rTable M d.admitted.program.defs) [layP]).run (retryOf M none) pP
              (.cons (hLayPState.symm ▸ buf) .nil))
          recP (.returned (outP, .cons (hLayPState.symm ▸ (buf ++ suffix)) .nil)) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
              (Defs.rTable M d.admitted.program.defs) [layV]).run (retryOf M none) pV
                (.cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil))
            recV (.returned (outV,
              .cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
        GExec M source' p (.returned a) := by
  cases layP with
  | mk lPLine lPSt lPTakes lPGives lPClauses lPAgain lPStart lPFin =>
      cases layV with
      | mk lVLine lVSt lVTakes lVGives lVClauses lVAgain lVStart lVFin =>
          dsimp only at hLayPState hLayVState
          subst lPSt; subst lVSt
          dsimp only at hSL
          let layP' : Layer V d.admitted.program.headers prover d.entry.ins :=
            ⟨lPLine, .seq unitTy none, lPTakes, lPGives, lPClauses, lPAgain, lPStart, lPFin⟩
          let layV' : Layer V d.admitted.program.headers verifier d.entry.ins :=
            ⟨lVLine, streamStateTy unitTy, lVTakes, lVGives, lVClauses, lVAgain, lVStart, lVFin⟩
          let fnTable := Defs.fnTable M d.admitted.program.defs
          let rTable := Defs.rTable M d.admitted.program.defs
          let events := d.entry.shape.events [] id
          have hLayUnm := fun op hCl => streaming_layout_unmatched_closed M 0 events hSL op hCl
          have hPassP : ∀ op (buf : List (M.Val unitTy)), ROp.IsClosed M op →
              (Stack.handler M fnTable rTable [layP']).clause op (.cons buf .nil) =
                .call op fun reply => .done (reply, .cons buf .nil) := fun op buf hCl =>
            stack1_clause_pass M fnTable rTable layP' op buf
              (clause_answer_unmatched_all M fnTable rTable op buf lPClauses (hLayUnm op hCl).1)
          have hPassV : ∀ op (lst : M.Val (streamStateTy unitTy)), ROp.IsClosed M op →
              (Stack.handler M fnTable rTable [layV']).clause op (.cons lst .nil) =
                .call op fun reply => .done (reply, .cons lst .nil) := fun op lst hCl =>
            stack1_clause_pass M fnTable rTable layV' op lst
              (clause_answer_unmatched_all M fnTable rTable op lst lVClauses (hLayUnm op hCl).2)
          have hEventDisc : ∀ e ∈ events,
              match e.cls with
              | .flow _ giver getters =>
                  (giver = prover ∧ verifier ∈ getters) ∨
                  (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
              | .given (.coin _) _ hearers => hearers = []
              | .given (.request _) owner hearers =>
                  (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
            have hGo : ∀ (es : List (ShapeEvent V)) {cS'},
                checkAuthoredEvents d.admitted prover verifier none declKey es = .ok cS' →
                ∀ e ∈ es, match e.cls with
                  | .flow _ giver getters =>
                      (giver = prover ∧ verifier ∈ getters) ∨
                      (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                  | .given (.coin _) _ hearers => hearers = []
                  | .given (.request _) owner hearers =>
                      (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
              intro es
              induction es with
              | nil => intro _ _ _ he; cases he
              | cons e rest ih =>
                  intro cS' hGo' e' he'
                  unfold checkAuthoredEvents at hGo'
                  cases hRec : checkAuthoredEvents d.admitted prover verifier none declKey rest with
                  | error _ => rw [hRec] at hGo'; cases hGo'
                  | ok sRest =>
                      rw [hRec] at hGo'; dsimp only [bind, Except.bind] at hGo'
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · cases hCls : e'.cls with
                        | flow _ giver getters =>
                            rw [hCls] at hGo'; dsimp only at hGo'
                            split at hGo'
                            · rename_i hCond; exact hCond
                            · cases hGo'
                        | given gkind owner hearers =>
                            rw [hCls] at hGo'
                            cases gkind with
                            | coin _ =>
                                dsimp only at hGo'
                                split at hGo'
                                · rename_i hNil; exact hNil
                                · cases hGo'
                            | request _ =>
                                dsimp only at hGo'
                                split at hGo'
                                · rename_i hReq; exact hReq
                                · cases hGo'
                      · exact ih hRec e' hmem
            exact hGo events hAuth
          intro A BP BV p
          let SimGoal := fun (p0 : Protocol M A) (postP : A → BP → Prop) (postV : A → BV → Prop)
              (buf : List (M.Val unitTy)) (source : Source M)
              (qP : Program M BP) (qV : Program M BV) =>
            ∃ (a : A) (outP : BP) (outV : BV) (suffix : List (M.Val unitTy))
              (recP : List (Happened M)) (source' : Source M),
              (∀ u ∈ suffix, M.Valid unitTy u) ∧
              Alone M source prover
                ((Stack.handler M fnTable rTable [layP']).run (retryOf M none) qP (.cons buf .nil))
                recP (.returned (outP, .cons (buf ++ suffix) .nil)) ∧
              (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                ∃ recV, Alone M source verifier
                  ((Stack.handler M fnTable rTable [layV']).run (retryOf M none) qV
                      (.cons (buf ++ suffix ++ post, (buf.length, ())) .nil))
                  recV (.returned (outV, .cons (buf ++ suffix ++ post, (buf.length + suffix.length, ())) .nil))) ∧
              postP a outP ∧ postV a outV ∧
              Lawful M source' p0 ∧
              (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
              GExec M source' p0 (.returned a)
          induction p with
          | done a =>
              intro postP postV pP pV buf source hBufV hProjP hProjV hSafeP hSafeV hShapeP hShapeV _ _ _ _ _
              refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layP'])
                (fun op s hM => by
                  cases s with | cons b bn => cases bn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ trivial)
                (fun qP => SimGoal (.done a) postP postV buf source qP pV)
                (fun qP hNotMP hPP hSP hShP => ?_)
                (fun at_ kP h => by
                  obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a', outP, outV, suf, .began prover at_ :: recP, src', h1,
                    by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ trivial)]; exact .begin h2,
                    h3, h4, h5, h6, h7, h8⟩)
                (fun at_ kP h => by
                  obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a', outP, outV, suf, .settled prover at_ :: recP, src', h1,
                    by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ trivial)]; exact .settle h2,
                    h3, h4, h5, h6, h7, h8⟩)
                hProjP hSafeP hShapeP
              cases hPP with
              | done hPostP =>
                  refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layV'])
                    (fun op s hM => by
                      cases s with | cons l ln => cases ln; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ trivial)
                    (fun qV => SimGoal (.done a) postP postV buf source (.done _) qV)
                    (fun qV hNotMV hPV hSV hShV => ?_)
                    (fun at_ kV h => by
                      obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                      exact ⟨a', outP, outV, suf, recP, src', h1, h2,
                        fun post hPost =>
                          let ⟨recV, hAlV⟩ := h3 post hPost
                          ⟨.began verifier at_ :: recV,
                            by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ trivial)]; exact .begin hAlV⟩,
                        h4, h5, h6, h7, h8⟩)
                    (fun at_ kV h => by
                      obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                      exact ⟨a', outP, outV, suf, recP, src', h1, h2,
                        fun post hPost =>
                          let ⟨recV, hAlV⟩ := h3 post hPost
                          ⟨.settled verifier at_ :: recV,
                            by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ trivial)]; exact .settle hAlV⟩,
                        h4, h5, h6, h7, h8⟩)
                    hProjV hSafeV hShapeV
                  cases hPV with
                  | done hPostV =>
                      exact ⟨a, _, _, [], [], source, (fun _ h => nomatch h),
                        by simpa [Handler.run] using Alone.done,
                        fun post _ => ⟨[], by simpa [Handler.run] using Alone.done⟩,
                        hPostP, hPostV, trivial, fun _ _ _ => rfl, ⟨[], .done⟩⟩
                  | begins _ => exact False.elim (hNotMV trivial)
                  | settles _ => exact False.elim (hNotMV trivial)
              | begins _ => exact False.elim (hNotMP trivial)
              | settles _ => exact False.elim (hNotMP trivial)
          | halt payload =>
              intro _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ hNoHalt
              obtain ⟨a, hContra⟩ := hNoHalt source trivial (fun _ _ _ => rfl)
                (.stopped payload.1 payload.2) ⟨[], .halt⟩
              cases hContra
          | call op k ih =>
              intro postP postV pP pV buf source hBufV hProjP hProjV hSafeP hSafeV
                hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt
              refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layP'])
                (fun op s hM => by
                  cases s with | cons b bn => cases bn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ trivial)
                (fun qP => SimGoal (.call op k) postP postV buf source qP pV)
                (fun qP hNotMP hPP hSP hShP => ?_)
                (fun at_ kP h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, .began prover at_ :: recP, src', h1,
                    by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ trivial)]; exact .begin h2,
                    h3, h4, h5, h6, h7, h8⟩)
                (fun at_ kP h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, .settled prover at_ :: recP, src', h1,
                    by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ trivial)]; exact .settle h2,
                    h3, h4, h5, h6, h7, h8⟩)
                hProjP hSafeP hShapeP
              refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layV'])
                (fun op s hM => by
                  cases s with | cons l ln => cases ln; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ trivial)
                (fun qV => SimGoal (.call op k) postP postV buf source qP qV)
                (fun qV hNotMV hPV hSV hShV => ?_)
                (fun at_ kV h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, recP, src', h1, h2,
                    fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.began verifier at_ :: recV,
                        by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ trivial)]; exact .begin hAlV⟩,
                    h4, h5, h6, h7, h8⟩)
                (fun at_ kV h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, recP, src', h1, h2,
                    fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.settled verifier at_ :: recV,
                        by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ trivial)]; exact .settle hAlV⟩,
                    h4, h5, h6, h7, h8⟩)
                hProjV hSafeV hShapeV
              cases op with
              | flow kind giver getters at_ τ x =>
                  have hNoHalt' : ∀ source₁, Lawful M source₁ (k ()) →
                      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                      ∀ e, GExec M source₁ (k ()) e → ∃ a, e = .returned a := fun source₁ hL₁ hAg e ⟨evs, hRun⟩ =>
                    hNoHalt source₁ hL₁ hAg e ⟨_, .flow hRun⟩
                  cases hPP with
                  | begins _ => exact False.elim (hNotMP trivial)
                  | settles _ => exact False.elim (hNotMP trivial)
                  | gave _ hPP' =>
                      obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
                      have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
                      have hVin : verifier ∈ getters := by
                        rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
                        · exact hV
                        · exact absurd rfl hNotP
                      have hMsgV : M.Valid τ x := hSP.1
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | gave _ _ => exact absurd rfl hNe
                      | passed _ hVOut _ => exact absurd hVin hVOut
                      | got _ _ hPV' =>
                          obtain ⟨wRef, chunk, hWFind, hWD, hChV, hLayPAns⟩ :=
                            streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                              kind getters at_ τ x buf hMsgV ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                          have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                            intro u hu; rcases List.mem_append.mp hu with h1 | h2
                            · exact hBufV u h1
                            · exact hChV u h2
                          obtain ⟨a, outP, outV, suf', recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih () _ _ (buf ++ chunk) source hBufChV hPP' hPV'
                              (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                              (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                          have hStepP := stack1_clause_done M fnTable rTable layP'
                            (.give kind getters at_ τ x) buf (buf ++ chunk) () hLayPAns
                          refine ⟨a, outP, outV, chunk ++ suf', recP, src', ?_, ?_, ?_,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
                          · intro u hu; rcases List.mem_append.mp hu with h1 | h2
                            · exact hChV u h1
                            · exact hSufV u h2
                          · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                            simpa [List.append_assoc] using hAlP
                          · intro post hPost
                            have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                              intro u hu; rcases List.mem_append.mp hu with h1 | h2
                              · exact hSufV u h1
                              · exact hPost u h2
                            obtain ⟨rRef, hRFind, hLayVAns⟩ :=
                              streaming_layout_answer_verifier_flow M 0 events hSL
                                kind at_ τ (buf ++ chunk ++ (suf' ++ post)) buf.length
                                ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                            have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind
                              hMsgV hBufV hSufPostV hWD
                            have hStepV := stack1_clause_done M fnTable rTable layV'
                              (.get kind prover at_ τ)
                              (buf ++ chunk ++ (suf' ++ post), (buf.length, ()))
                              (buf ++ chunk ++ (suf' ++ post), (buf.length + chunk.length, ()))
                              x (hLayVAns x (buf.length + chunk.length) hRD)
                            obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                            refine ⟨recV, ?_⟩
                            have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                              simp [List.append_assoc]
                            rw [hBufEq]
                            rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                            have hLenEq : buf.length + (chunk ++ suf').length =
                                (buf ++ chunk).length + suf'.length := by
                              simp [List.length_append, Nat.add_assoc]
                            have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                              simp [List.append_assoc]
                            rw [hLenEq, hBufEq2, ← List.length_append]
                            exact hAlV'
                  | got hGNeP hPIn _ =>
                      obtain ⟨eP, hEP, _, _, _, gs', hPin', hClsP⟩ := hShP.1
                      have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
                      rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
                      · exact absurd hEqP hGNeP
                      · exact absurd hPin' hNotP
                  | passed hGNeP _ hPP' =>
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | gave _ _ =>
                          obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
                          have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
                          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
                          · exact absurd hEqP.symm hNe
                          · exact absurd rfl hNotV
                      | got _ _ _ =>
                          obtain ⟨eV, hEV, _, _, _, gs', hVin', hClsV⟩ := hShV.1
                          have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
                          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
                          · exact absurd hEqP hGNeP
                          · exact absurd hVin' hNotV
                      | passed _ _ hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                            ih () _ _ buf source hBufV hPP' hPV' hSP hSV hShP hShV
                              (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                          exact ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
              | given gkind owner hearers at_ gIns payload τ =>
                  obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
                  have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
                  have hNotHeardCoin : (∃ law, gkind = .coin law ∧ hearers = []) ∨
                      (∃ svc, gkind = .request svc ∧
                        (owner = prover ∨ prover ∉ hearers) ∧
                        (owner = verifier ∨ verifier ∉ hearers)) := by
                    cases gkind with
                    | coin law => exact .inl ⟨law, rfl, hDisc⟩
                    | request svc => exact .inr ⟨svc, rfl, hDisc⟩
                  have hSrcFed : ∃ v, source at_ τ = some v ∧ Fed M source (k v) := by
                    rcases hNotHeardCoin with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩ <;> exact hFed
                  obtain ⟨v, hSrc, hFed'⟩ := hSrcFed
                  have hLPv : Allows M gkind gIns payload τ v ∧ LawfulPrivate M source (k v) := by
                    rcases hNotHeardCoin with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩ <;> exact hLP v hSrc
                  obtain ⟨hAllows, hLP'⟩ := hLPv
                  have hValV : M.Valid τ v := allows_valid M hAllows
                  have hIsClOwn : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ) := by
                    rcases hNotHeardCoin with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩ <;> trivial
                  have hOccK : Protocol.OccsIn M (· ≠ at_) (k v) := (hUniq v).1
                  have hNoHalt' : ∀ source₁, Lawful M source₁ (k v) →
                      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                      ∀ e, GExec M source₁ (k v) e → ∃ a, e = .returned a := by
                    intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
                    let source₂ := patchSource M source₁ at_ τ v
                    have hAgree12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = source₂ at' τ' :=
                      fun at' τ' hne => (patchSource_ne M source₁ at_ τ v hne τ').symm
                    have hL₂ : Lawful M source₂ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
                      intro w hw; dsimp only [source₂] at hw; rw [patchSource_self] at hw; cases hw
                      exact ⟨hAllows, lawful_of_agree M hAgree12 hOccK hL₁⟩
                    have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                        source₂ at' τ' = source at' τ' := by
                      intro at' τ' hNotIn
                      unfold source₂ patchSource; split
                      · rename_i heq; cases heq.1; cases heq.2; exact hSrc.symm
                      · exact hAg₁ at' τ' hNotIn
                    exact hNoHalt source₂ hL₂ hAg₂ e
                      ⟨_, .given (patchSource_self M source₁ at_ τ v)
                        (grun_of_agree M hAgree12 hOccK hRun₁)⟩
                  have hWrapSrc : ∀ (src' : Source M) {evs' a},
                      Lawful M src' (k v) →
                      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src' at' τ' = source at' τ') →
                      GRun M src' (k v) evs' (.returned a) →
                      ∃ src'', Lawful M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) ∧
                        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src'' at' τ' = source at' τ') ∧
                        GExec M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) (.returned a) := by
                    intro src' evs' a hL' hAg' hRun'
                    let src'' := patchSource M src' at_ τ v
                    have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                      fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                    refine ⟨src'', ?_, ?_, ?_⟩
                    · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                      exact ⟨hAllows, lawful_of_agree M hAgP hOccK hL'⟩
                    · intro at' τ' hNotIn
                      unfold src'' patchSource; split
                      · rename_i heq; cases heq.1; cases heq.2; exact hSrc.symm
                      · exact hAg' at' τ' hNotIn
                    · exact ⟨_, .given (patchSource_self M src' at_ τ v)
                        (grun_of_agree M hAgP hOccK hRun')⟩
                  cases hPP with
                  | begins _ => exact False.elim (hNotMP trivial)
                  | settles _ => exact False.elim (hNotMP trivial)
                  | heard hONeP hPin _ =>
                      rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, hPReq, _⟩
                      · cases hPin
                      · rcases hPReq with hEqO | hNotIn
                        · exact absurd hEqO hONeP
                        · exact absurd hPin hNotIn
                  | owned hPP' =>
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | owned _ => exact absurd rfl hNe
                      | heard _ hVin _ =>
                          rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                          · cases hVin
                          · rcases hVReq with hEqO | hNotIn
                            · exact absurd hEqO hNe
                            · exact absurd hVin hNotIn
                      | unheard _ _ hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih v _ _ buf source hBufV (hPP' v) (hPV' v)
                              (hSP.2 v hValV) hSV (hShP.2 v trivial) hShV
                              (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                          obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                          refine ⟨a, outP, outV, suf, .owned prover gkind at_ τ v :: recP, src'',
                            hSufV, ?_, hAlV, hPostP, hPostV, hL'', hAg'', hGEx''⟩
                          rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassP _ _ hIsClOwn)]
                          exact .own hSrc hAlP
                  | unheard hONeP _ hPP' =>
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | heard hONeV hVin _ =>
                          rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                          · cases hVin
                          · rcases hVReq with hEqO | hNotIn
                            · exact absurd hEqO hONeV
                            · exact absurd hVin hNotIn
                      | owned hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih v _ _ buf source hBufV (hPP' v) (hPV' v)
                              hSP (hSV.2 v hValV) hShP (hShV.2 v trivial)
                              (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                          obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                          refine ⟨a, outP, outV, suf, recP, src'', hSufV, hAlP, ?_,
                            hPostP, hPostV, hL'', hAg'', hGEx''⟩
                          intro post hPost
                          obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                          refine ⟨.owned verifier gkind at_ τ v :: recV, ?_⟩
                          rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassV _ _ hIsClOwn)]
                          exact .own hSrc hAlV'
                      | unheard _ _ hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih v _ _ buf source hBufV (hPP' v) (hPV' v)
                              hSP hSV hShP hShV
                              (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                          obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                          exact ⟨a, outP, outV, suf, recP, src'', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hL'', hAg'', hGEx''⟩

/-- Top-level streaming completeness (`Statements.complete`) for `deploy`. -/
theorem deploy_complete (enc : VocabEncoder V) {named : NamedProgram V} {assoc : Association}
    {a : Admitted V} (hAdmit : admit named assoc = .ok a)
    {declaration : Declaration} {d : Deployed V} (hDep : deploy enc a declaration = .ok d)
    (hNonInt : declaration.interactive = false) (hNoRetry : declaration.retry = none)
    (hNoSamp : declaration.samples = none)
    (hNoRec : ∀ l, declaration.layout = some l → l.recover = [])
    (prover verifier : Role) (hRoles : d.roles = some (prover, verifier))
    (first : Stack.Takes (d.stack prover) = [])
    (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
    (ins : HList (LVal M) d.entry.ins) (hIns : ins.All (fun a v => M.Valid a.ty v))
    (hSuiteLaw : d.SuiteLawful M) (hLayLaw : d.LayoutLawful M)
    (hNoHalt : ∀ source, Lawful M source (protocolMeaning M d.admitted.program d.callee [] ins) →
      ∀ e, GExec M source (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out)
    (source : Source M)
    (hLP : LawfulPrivate M source (protocolMeaning M d.admitted.program d.callee [] ins))
    (hFed : Fed M source (protocolMeaning M d.admitted.program d.callee [] ins)) :
    ∃ outP gives recordP outV givesV recordV,
      Alone M source prover
        (d.run M prover (hideAll M prover ins) (cast (congrArg (HList M.Val) first.symm) .nil))
        recordP (.returned (outP, gives)) ∧
      Alone M source verifier
        (d.run M verifier (hideAll M verifier ins) (cast (congrArg (HList M.Val) matched) gives))
        recordV (.returned (outV, givesV)) ∧
      ∃ source' out,
        Lawful M source' (protocolMeaning M d.admitted.program d.callee [] ins) ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
        GExec M source' (protocolMeaning M d.admitted.program d.callee [] ins) (.returned out) ∧
        outP = hideAll M prover out.1 ∧ outV = hideAll M verifier out.1 := by
  have hProjP := projection M d.admitted.program d.callee prover [] ins
  have hProjV := projection M d.admitted.program d.callee verifier [] ins
  have hInsP : (hideAll M prover ins).All (RV.Valid M prover) := hideAll_valid M prover ins hIns
  have hInsV : (hideAll M verifier ins).All (RV.Valid M verifier) := hideAll_valid M verifier ins hIns
  have hKeep := deploy_keeps enc a declaration d hDep
  have hSafeP : (roleMeaning M d.admitted.program d.callee prover [] (hideAll M prover ins)).SafeWith
      M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) := by
    have hs := roleMeaning_safeWith_valid M (hKeep.1 ▸ hAdmit) d.callee prover [] (hideAll M prover ins) hInsP
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) hs
  have hSafeV : (roleMeaning M d.admitted.program d.callee verifier [] (hideAll M verifier ins)).SafeWith
      M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) := by
    have hs := roleMeaning_safeWith_valid M (hKeep.1 ▸ hAdmit) d.callee verifier [] (hideAll M verifier ins) hInsV
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) hs
  have hShapeP := roleMeaning_matchesShape M d.admitted.program d.callee prover [] (hideAll M prover ins)
  have hShapeV := roleMeaning_matchesShape M d.admitted.program d.callee verifier [] (hideAll M verifier ins)
  have hPShape := protocolMeaning_matchesShape M d.admitted.program d.callee [] ins
  have hUniq := protocolMeaning_uniqueOccs M d.admitted.program d.callee [] ins
  have hNoHalt' : ∀ source₁, Lawful M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) →
      (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source₁ at_ τ = source at_ τ) →
      ∀ e, GExec M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out := fun s₁ hL₁ _ e hEx => hNoHalt s₁ hL₁ e hEx
  unfold deploy at hDep
  split at hDep
  · cases hDep
  · rename_i foundPair hFound
    dsimp only at hDep
    split at hDep
    · cases hDep
    · cases hCon : declaration.construction with
      | interactive => simp [Declaration.interactive, hCon] at hNonInt
      | authored =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · rename_i hNe
                cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples declaration.key
                    (foundPair.1.shape.events [] id) with
                | error _ => rw [hAuth] at hDep; cases hDep
                | ok sClauses =>
                    rw [hAuth] at hDep; dsimp only [bind, Except.bind] at hDep
                    cases hLO : declaration.layout with
                    | none => rw [hLO] at hDep; cases hDep
                    | some layout =>
                        rw [hLO] at hDep; dsimp only at hDep
                        have hRecNil : layout.recover = [] := hNoRec layout hLO
                        cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                            declaration.key (foundPair.1.shape.events [] id) with
                        | error _ => rw [hLay] at hDep; cases hDep
                        | ok lays =>
                            rw [hLay, hNoSamp] at hDep; dsimp only at hDep; cases hDep
                            have hRolesEq : proverAndVerifier foundPair.1 declaration = some (prover, verifier) := by
                              simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                            rw [hPV] at hRolesEq; cases hRolesEq
                            unfold buildLayoutLayers at hLay
                            cases hUnit : findLayoutUnit a layout.module with
                            | none => rw [hUnit] at hLay; cases hLay
                            | some uPair =>
                                rw [hUnit] at hLay; dsimp only at hLay
                                rw [show layout.recover.isEmpty = true by simp [hRecNil], ite_eq_left rfl] at hLay
                                cases hStr : buildStreamingLayoutClauses a layout uPair.1 uPair.2.down
                                    prover verifier declaration.key (foundPair.1.shape.events [] id) with
                                | error _ => rw [hStr] at hLay; cases hLay
                                | ok cs =>
                                    rw [hStr] at hLay; cases hLay
                                    dsimp only [Deployed.entry, Deployed.retry] at *
                                    have hEntryF : ((a.program.findProtocol declaration.entry).get
                                        (by rw [hFound]; rfl)).1 = foundPair.1 := by simp [hFound]
                                    let layP0 : Layer V a.program.headers prover foundPair.1.ins :=
                                      { line := .layout, state := .seq uPair.1 none, takes := [],
                                        gives := [.seq uPair.1 none], clauses := cs.1,
                                        again := restoreAgain (.seq uPair.1 none),
                                        start := layoutPStart uPair.1,
                                        finish := identityFinish (.seq uPair.1 none) }
                                    let layV0 : Layer V a.program.headers verifier foundPair.1.ins :=
                                      { line := .layout, state := streamStateTy uPair.1,
                                        takes := [.seq uPair.1 none], gives := [], clauses := cs.2,
                                        again := restoreAgain (streamStateTy uPair.1),
                                        start := layoutVStart uPair.1,
                                        finish := layoutVFinish uPair.1 uPair.2.down
                                          (finishGuardKey (foundPair.1.shape.events [] id)) }
                                    let dAuth : Deployed V :=
                                      { admitted := a, declaration := declaration,
                                        found := (by rw [hFound]; rfl),
                                        stack := fun r =>
                                          if hP : r = prover then hP ▸ hEntryF ▸ [layP0]
                                          else if hV : r = verifier then hV ▸ hEntryF ▸ [layV0]
                                          else [] }
                                    -- Build transported streaming layers matching `d.entry`
                                    let layP' : Layer V a.program.headers prover _ := hEntryF ▸ layP0
                                    let layV' : Layer V a.program.headers verifier _ := hEntryF ▸ layV0
                                    have hAuth' : checkAuthoredEvents a prover verifier none declaration.key
                                        ((((a.program.findProtocol declaration.entry).get
                                          (by rw [hFound]; rfl)).1).shape.events [] id) = .ok sClauses := by
                                      rw [hEntryF, ← hNoSamp]; exact hAuth
                                    have hLayPSt : layP'.state = .seq uPair.1 none := layer_cast_state hEntryF layP0
                                    have hLayVSt : layV'.state = streamStateTy uPair.1 := layer_cast_state hEntryF layV0
                                    have hSL' : buildStreamingLayoutClauses.go a layout uPair.1 uPair.2.down
                                        prover verifier declaration.key
                                        ((((a.program.findProtocol declaration.entry).get
                                          (by rw [hFound]; rfl)).1).shape.events [] id) 0
                                        ((((a.program.findProtocol declaration.entry).get
                                          (by rw [hFound]; rfl)).1).shape.events [] id) =
                                        .ok (hLayPSt ▸ layP'.clauses, hLayVSt ▸ layV'.clauses) := by
                                      rw [layer_cast_clauses hEntryF layP0, layer_cast_clauses hEntryF layV0, hEntryF]
                                      exact hStr
                                    obtain ⟨out, outP, outV, suffix, recP, source', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
                                      simulate_authored M hNe (d := dAuth)
                                        hLO hLayLaw hLayPSt hLayVSt hAuth' hSL'
                                        (protocolMeaning M a.program _ [] ins)
                                        (roleMeaning M a.program _ prover [] (hideAll M prover ins))
                                        (roleMeaning M a.program _ verifier [] (hideAll M verifier ins))
                                        [] source (fun _ h => nomatch h) hProjP hProjV hSafeP hSafeV
                                        hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt'
                                    -- Now assemble `d.run` for prover & verifier via `Stack.start` and `Stack.finish`
                                    -- by eliminating `hEntryF` uniformly on both `d.run` expressions.
                                    have hFinish : ∀ (hdr : ProtocolHeader V) (hE : hdr = foundPair.1)
                                        (callee : Member a.program.headers.protocols hdr)
                                        (ins' : HList (LVal M) hdr.ins)
                                        (first' : Stack.Takes (hE ▸ [layP0]) = [])
                                        (matched' : Stack.Gives (hE ▸ [layP0]) =
                                          Stack.Takes (hE ▸ [layV0]))
                                        (outP' : HList (RV M prover) hdr.outs)
                                        (outV' : HList (RV M verifier) hdr.outs)
                                        (recP' : List (Happened M)) (recV' : List (Happened M)),
                                        Alone M source prover
                                          ((Stack.handler M (Defs.fnTable M a.program.defs)
                                            (Defs.rTable M a.program.defs)
                                            (hE ▸ [layP0])).run
                                              (retryOf M none)
                                              (roleMeaning M a.program callee prover [] (hideAll M prover ins'))
                                              (cast (by subst hE; rfl) (HList.cons ([] : List (M.Val uPair.1)) HList.nil)))
                                          recP' (.returned (outP', cast (by subst hE; rfl) (HList.cons suffix HList.nil))) →
                                        Alone M source verifier
                                          ((Stack.handler M (Defs.fnTable M a.program.defs)
                                            (Defs.rTable M a.program.defs)
                                            (hE ▸ [layV0])).run
                                              (retryOf M none)
                                              (roleMeaning M a.program callee verifier [] (hideAll M verifier ins'))
                                              (cast (by subst hE; rfl) (HList.cons (suffix, ((0 : Nat), ())) HList.nil)))
                                          recV' (.returned (outV', cast (by subst hE; rfl) (HList.cons (suffix, (suffix.length, ())) HList.nil))) →
                                        ∃ gives givesV,
                                          Alone M source prover
                                            (runStack a M callee none prover
                                              (hE ▸ [layP0])
                                              (hideAll M prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                                            recP' (.returned (outP', gives)) ∧
                                          Alone M source verifier
                                            (runStack a M callee none verifier
                                              (hE ▸ [layV0])
                                              (hideAll M verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                                            recV' (.returned (outV', givesV)) := by
                                      intro hdr hE callee ins' first' matched' outP' outV' recP' recV' hAP hAV
                                      subst hE
                                      change Alone M source prover
                                        ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layP0]).run
                                          (retryOf M none) (roleMeaning M a.program callee prover [] (hideAll M prover ins'))
                                          (.cons ([] : List (M.Val uPair.1)) .nil))
                                        recP' (.returned (outP', .cons suffix .nil)) at hAP
                                      change Alone M source verifier
                                        ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layV0]).run
                                          (retryOf M none) (roleMeaning M a.program callee verifier [] (hideAll M verifier ins'))
                                          (.cons (suffix, ((0 : Nat), ())) .nil))
                                        recV' (.returned (outV', .cons (suffix, (suffix.length, ())) .nil)) at hAV
                                      refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
                                      · unfold runStack
                                        change Alone M source prover
                                          ((Stack.start M (Defs.fnTable M a.program.defs) [layP0]
                                            (hideAll M prover ins') .nil).bind _) _ _
                                        have hStP : Stack.start M (Defs.fnTable M a.program.defs)
                                            [layP0] (hideAll M prover ins') .nil =
                                            .done (.cons ([] : List (M.Val uPair.1)) .nil) := by
                                          change ((liftLocal id ((layoutPStart uPair.1).denote
                                            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                            (Env.positional (heldValues M prover (hideAll M prover ins'))))).bind fun first =>
                                              (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first.single others) = _
                                          rw [layoutPStart_denote]; rfl
                                        rw [hStP]; dsimp only [Process.bind]
                                        have hAP' := alone_mapHalt M (g := Prod.fst) hAP
                                        rw [← List.append_nil recP']
                                        refine alone_bind M hAP' ?_
                                        have hFinP : Stack.finish M (Defs.fnTable M a.program.defs)
                                            [layP0] (.cons suffix .nil) = .done (.cons suffix .nil) := by
                                          rw [stack_finish_one]; dsimp only [layP0]
                                          rw [identityFinish_denote]; rfl
                                        rw [hFinP]; exact .done
                                      · unfold runStack
                                        change Alone M source verifier
                                          ((Stack.start M (Defs.fnTable M a.program.defs) [layV0]
                                            (hideAll M verifier ins') (.cons suffix .nil)).bind _) _ _
                                        have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                                            [layV0] (hideAll M verifier ins') (.cons suffix .nil) =
                                            .done (.cons (suffix, ((0 : Nat), ())) .nil) := by
                                          change ((liftLocal id ((layoutVStart uPair.1).denote
                                            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                            (Env.positional (.cons suffix (heldValues M verifier (hideAll M verifier ins')))))).bind fun first =>
                                              (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first.single others) = _
                                          rw [layoutVStart_denote]; rfl
                                        rw [hStV]; dsimp only [Process.bind]
                                        have hAV' := alone_mapHalt M (g := Prod.fst) hAV
                                        rw [← List.append_nil recV']
                                        refine alone_bind M hAV' ?_
                                        have hFinV : Stack.finish M (Defs.fnTable M a.program.defs)
                                            [layV0] (.cons (suffix, (suffix.length, ())) .nil) = .done .nil := by
                                          rw [stack_finish_one]; dsimp only [layV0]
                                          rw [layoutVFinish_denote]
                                          simp only [Nat.beq_refl, Bool.cond_true]; rfl
                                        rw [hFinV]; exact .done
                                    obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
                                    simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlV0
                                    have hRunDone := hFinish _ hEntryF _ ins
                                      (by simpa [layP0] using first)
                                      (by simpa [Ne.symm hNe, layP0, layV0] using matched)
                                      outP outV recP recV
                                      (alone_cast_stack1 M hEntryF layP0 rfl hAlP)
                                      (alone_cast_stack1 M hEntryF layV0 rfl hAlV0)
                                    obtain ⟨gives, givesV, hRunP, hRunV⟩ := hRunDone
                                    have hStackPEq : dAuth.stack prover = hEntryF ▸ [layP0] := by
                                      dsimp only [dAuth]; rw [dite_eq_left rfl]
                                    have hStackVEq : dAuth.stack verifier = hEntryF ▸ [layV0] := by
                                      dsimp only [dAuth]; rw [dite_eq_right (Ne.symm hNe), dite_eq_left rfl]
                                    refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
                                      recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
                                      ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
                                    · exact alone_deployed_run_congr M (d := dAuth) rfl hNoRetry hStackPEq
                                        ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
                                    · exact alone_deployed_run_congr M (d := dAuth) rfl hNoRetry hStackVEq
                                        ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
                                        (cast_heq _ _) hRunV
      | derived suite sessionTag =>
          rw [hCon] at hDep; dsimp only at hDep
          cases hPV : proverAndVerifier foundPair.1 declaration with
          | none => rw [hPV] at hDep; cases hDep
          | some pv =>
              rw [hPV] at hDep; dsimp only at hDep
              split at hDep
              · cases hDep
              · rename_i hNe
                cases hLO : declaration.layout with
                | none => rw [hLO] at hDep; cases hDep
                | some layout =>
                    rw [hLO] at hDep; dsimp only at hDep
                    have hRecNil : layout.recover = [] := hNoRec layout hLO
                    cases hSt : findSuiteStart a suite with
                    | none => rw [hSt] at hDep; cases hDep
                    | some stPair =>
                        rw [hSt] at hDep; dsimp only at hDep
                        cases hAb : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAb] at hDep; cases hDep
                        | some absPair =>
                            rw [hAb] at hDep; dsimp only at hDep
                            cases hSess : resolveSessionBytes enc a declaration sessionTag with
                            | error _ => rw [hSess] at hDep; cases hDep
                            | ok sess =>
                                rw [hSess] at hDep; dsimp only [bind, Except.bind] at hDep
                                cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1 pv.2
                                    (.inl rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSP] at hDep; cases hDep
                                | ok stmtP =>
                                    rw [hSP] at hDep; dsimp only [bind, Except.bind] at hDep
                                    cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                                        (.inr rfl) foundPair.1.ins declaration.key with
                                    | error _ => rw [hSV] at hDep; cases hDep
                                    | ok stmtV =>
                                        rw [hSV] at hDep; dsimp only [bind, Except.bind] at hDep
                                        cases hCC : buildConstructionClauses a suite stPair.1 absPair.1
                                            absPair.2 pv.1 pv.2 declaration.samples declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hCC] at hDep; cases hDep
                                        | ok cc =>
                                            rw [hCC] at hDep; dsimp only [bind, Except.bind] at hDep
                                            cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                                declaration.key (foundPair.1.shape.events [] id) with
                                            | error _ => rw [hLay] at hDep; cases hDep
                                            | ok lays =>
                                                rw [hLay, hNoSamp] at hDep; dsimp only at hDep; cases hDep
                                                have hRolesEq : proverAndVerifier foundPair.1 declaration =
                                                    some (prover, verifier) := by
                                                  simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                                                rw [hPV] at hRolesEq; cases hRolesEq
                                                unfold buildLayoutLayers at hLay
                                                cases hUnit : findLayoutUnit a layout.module with
                                                | none => rw [hUnit] at hLay; cases hLay
                                                | some uPair =>
                                                    rw [hUnit] at hLay; dsimp only at hLay
                                                    rw [show layout.recover.isEmpty = true by simp [hRecNil],
                                                      ite_eq_left rfl] at hLay
                                                    cases hStr : buildStreamingLayoutClauses a layout uPair.1
                                                        uPair.2.down prover verifier declaration.key
                                                        (foundPair.1.shape.events [] id) with
                                                    | error _ => rw [hStr] at hLay; cases hLay
                                                    | ok cs =>
                                                        rw [hStr] at hLay; cases hLay
                                                        dsimp only [Deployed.entry, Deployed.retry] at *
                                                        have hEntryF : ((a.program.findProtocol declaration.entry).get
                                                            (by rw [hFound]; rfl)).1 = foundPair.1 := by simp [hFound]
                                                        let conPL : Layer V a.program.headers prover foundPair.1.ins :=
                                                          { line := .construction, state := stPair.1, takes := [],
                                                            gives := [], clauses := cc.1, again := restoreAgain stPair.1,
                                                            start := constructionStart sess.1 sess.2 stPair.2 absPair.2 stmtP,
                                                            finish := emptyFinish stPair.1 }
                                                        let conVL : Layer V a.program.headers verifier foundPair.1.ins :=
                                                          { line := .construction, state := stPair.1, takes := [],
                                                            gives := [], clauses := cc.2.1, again := restoreAgain stPair.1,
                                                            start := constructionStart sess.1 sess.2 stPair.2 absPair.2 stmtV,
                                                            finish := emptyFinish stPair.1 }
                                                        let layPL : Layer V a.program.headers prover foundPair.1.ins :=
                                                          { line := .layout, state := .seq uPair.1 none, takes := [],
                                                            gives := [.seq uPair.1 none], clauses := cs.1,
                                                            again := restoreAgain (.seq uPair.1 none),
                                                            start := layoutPStart uPair.1,
                                                            finish := identityFinish (.seq uPair.1 none) }
                                                        let layVL : Layer V a.program.headers verifier foundPair.1.ins :=
                                                          { line := .layout, state := streamStateTy uPair.1,
                                                            takes := [.seq uPair.1 none], gives := [], clauses := cs.2,
                                                            again := restoreAgain (streamStateTy uPair.1),
                                                            start := layoutVStart uPair.1,
                                                            finish := layoutVFinish uPair.1 uPair.2.down
                                                              (finishGuardKey (foundPair.1.shape.events [] id)) }
                                                        let dDer : Deployed V :=
                                                          { admitted := a, declaration := declaration,
                                                            found := (by rw [hFound]; rfl),
                                                            stack := fun r =>
                                                              if hP : r = prover then hP ▸ hEntryF ▸ [conPL, layPL]
                                                              else if hV : r = verifier then hV ▸ hEntryF ▸ [conVL, layVL]
                                                              else [] }
                                                        -- Compute shared initial transcript state `st0`!
                                                        have hStartEq : ∀ (ins' : HList (LVal M) foundPair.1.ins),
                                                            ins'.All (fun a v => M.Valid a.ty v) →
                                                            ∃ st0,
                                                              conPL.start.denote (localSem M a.program.headers.fns
                                                                (Defs.fnTable M a.program.defs)) []
                                                                (Env.positional (heldValues M prover (hideAll M prover ins'))) =
                                                                .done (.cons st0 .nil) ∧
                                                              conVL.start.denote (localSem M a.program.headers.fns
                                                                (Defs.fnTable M a.program.defs)) []
                                                                (Env.positional (heldValues M verifier (hideAll M verifier ins'))) =
                                                                .done (.cons st0 .nil) ∧
                                                              M.Valid stPair.1 st0 := by
                                                          intro ins' hIns'
                                                          obtain ⟨st0, hDoneP, hSt0V⟩ := constructionStart_done M a
                                                            sess.1 sess.2 stPair.2 absPair.2 stmtP
                                                            (heldValues M prover (hideAll M prover ins'))
                                                            (heldValues_valid M prover _ (hideAll_valid M prover ins' hIns'))
                                                          have hAgree := constructionStart_agree M a suite prover verifier
                                                            foundPair.1.ins declaration.key sess.1 sess.2 stPair.2 absPair.2
                                                            stmtP stmtV hSP hSV ins'
                                                          exact ⟨st0, hDoneP, hAgree.symm.trans hDoneP, hSt0V⟩
                                                        have hInsF := ins_cast_valid M hEntryF ins hIns
                                                        obtain ⟨st0, hSt0P, hSt0V, hSt0Valid⟩ :=
                                                          hStartEq (cast (congrArg (fun hdr => HList (LVal M) hdr.ins) hEntryF) ins) hInsF
                                                        let conP' : Layer V a.program.headers prover _ := hEntryF ▸ conPL
                                                        let conV' : Layer V a.program.headers verifier _ := hEntryF ▸ conVL
                                                        let layP' : Layer V a.program.headers prover _ := hEntryF ▸ layPL
                                                        let layV' : Layer V a.program.headers verifier _ := hEntryF ▸ layVL
                                                        have hCPSt : conP'.state = stPair.1 := layer_cast_state hEntryF conPL
                                                        have hCVSt : conV'.state = stPair.1 := layer_cast_state hEntryF conVL
                                                        have hLPSt : layP'.state = .seq uPair.1 none := layer_cast_state hEntryF layPL
                                                        have hLVSt : layV'.state = streamStateTy uPair.1 := layer_cast_state hEntryF layVL
                                                        have hCC' : buildConstructionClauses.go a suite stPair.1 absPair.1
                                                            absPair.2 prover verifier none declaration.key
                                                            ((((a.program.findProtocol declaration.entry).get
                                                              (by rw [hFound]; rfl)).1).shape.events [] id) 0
                                                            ((((a.program.findProtocol declaration.entry).get
                                                              (by rw [hFound]; rfl)).1).shape.events [] id) =
                                                            .ok (hCPSt ▸ conP'.clauses, hCVSt ▸ conV'.clauses, cc.2.2) := by
                                                          rw [layer_cast_clauses hEntryF conPL, layer_cast_clauses hEntryF conVL, hEntryF, ← hNoSamp]
                                                          exact hCC
                                                        have hSL' : buildStreamingLayoutClauses.go a layout uPair.1
                                                            uPair.2.down prover verifier declaration.key
                                                            ((((a.program.findProtocol declaration.entry).get
                                                              (by rw [hFound]; rfl)).1).shape.events [] id) 0
                                                            ((((a.program.findProtocol declaration.entry).get
                                                              (by rw [hFound]; rfl)).1).shape.events [] id) =
                                                            .ok (hLPSt ▸ layP'.clauses, hLVSt ▸ layV'.clauses) := by
                                                          rw [layer_cast_clauses hEntryF layPL, layer_cast_clauses hEntryF layVL, hEntryF]
                                                          exact hStr
                                                        obtain ⟨out, outP, outV, finalSt, suffix, recP, source',
                                                          hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
                                                          simulate_derived M hNe (d := dDer)
                                                            hCon hLO hSuiteLaw hLayLaw hCPSt hCVSt hLPSt hLVSt hCC' hSL'
                                                            (protocolMeaning M a.program _ [] ins)
                                                            (roleMeaning M a.program _ prover [] (hideAll M prover ins))
                                                            (roleMeaning M a.program _ verifier [] (hideAll M verifier ins))
                                                            st0 [] source hSt0Valid (fun _ h => nomatch h)
                                                            hProjP hProjV hSafeP hSafeV hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt'
                                                        obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
                                                        have hFinish : ∀ (hdr : ProtocolHeader V) (hE : hdr = foundPair.1)
                                                            (callee : Member a.program.headers.protocols hdr)
                                                            (ins' : HList (LVal M) hdr.ins)
                                                            (hStartP' : conPL.start.denote (localSem M a.program.headers.fns
                                                              (Defs.fnTable M a.program.defs)) []
                                                              (Env.positional (heldValues M prover (hideAll M prover (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                                                              .done (.cons st0 .nil))
                                                            (hStartV' : conVL.start.denote (localSem M a.program.headers.fns
                                                              (Defs.fnTable M a.program.defs)) []
                                                              (Env.positional (heldValues M verifier (hideAll M verifier (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                                                              .done (.cons st0 .nil))
                                                            (first' : Stack.Takes (hE ▸ [conPL, layPL]) = [])
                                                            (matched' : Stack.Gives (hE ▸ [conPL, layPL]) =
                                                              Stack.Takes (hE ▸ [conVL, layVL]))
                                                            (outP' : HList (RV M prover) hdr.outs)
                                                            (outV' : HList (RV M verifier) hdr.outs)
                                                            (recP' recV' : List (Happened M)),
                                                            Alone M source prover
                                                              ((Stack.handler M (Defs.fnTable M a.program.defs)
                                                                (Defs.rTable M a.program.defs) (hE ▸ [conPL, layPL])).run
                                                                (retryOf M none)
                                                                (roleMeaning M a.program callee prover [] (hideAll M prover ins'))
                                                                (cast (by subst hE; rfl)
                                                                  (HList.cons st0 (HList.cons ([] : List (M.Val uPair.1)) HList.nil))))
                                                              recP' (.returned (outP', cast (by subst hE; rfl)
                                                                (HList.cons finalSt (HList.cons suffix HList.nil)))) →
                                                            Alone M source verifier
                                                              ((Stack.handler M (Defs.fnTable M a.program.defs)
                                                                (Defs.rTable M a.program.defs) (hE ▸ [conVL, layVL])).run
                                                                (retryOf M none)
                                                                (roleMeaning M a.program callee verifier [] (hideAll M verifier ins'))
                                                                (cast (by subst hE; rfl)
                                                                  (HList.cons st0 (HList.cons (suffix, ((0 : Nat), ())) HList.nil))))
                                                              recV' (.returned (outV', cast (by subst hE; rfl)
                                                                (HList.cons finalSt (HList.cons (suffix, (suffix.length, ())) HList.nil)))) →
                                                            ∃ gives givesV,
                                                              Alone M source prover
                                                                (runStack a M callee none prover (hE ▸ [conPL, layPL])
                                                                  (hideAll M prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                                                                recP' (.returned (outP', gives)) ∧
                                                              Alone M source verifier
                                                                (runStack a M callee none verifier (hE ▸ [conVL, layVL])
                                                                  (hideAll M verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                                                                recV' (.returned (outV', givesV)) := by
                                                          intro hdr hE callee ins' hSP' hSV' first' matched' outP' outV' recP' recV' hAP hAV
                                                          subst hE
                                                          dsimp only at hSP' hSV'
                                                          simp only [cast_eq] at hSP' hSV'
                                                          change Alone M source prover
                                                            ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conPL, layPL]).run
                                                              (retryOf M none) (roleMeaning M a.program callee prover [] (hideAll M prover ins'))
                                                              (.cons st0 (.cons ([] : List (M.Val uPair.1)) .nil)))
                                                            recP' (.returned (outP', .cons finalSt (.cons suffix .nil))) at hAP
                                                          change Alone M source verifier
                                                            ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conVL, layVL]).run
                                                              (retryOf M none) (roleMeaning M a.program callee verifier [] (hideAll M verifier ins'))
                                                              (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)))
                                                            recV' (.returned (outV', .cons finalSt (.cons (suffix, (suffix.length, ())) .nil))) at hAV
                                                          refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
                                                          · unfold runStack
                                                            change Alone M source prover
                                                              ((Stack.start M (Defs.fnTable M a.program.defs) [conPL, layPL]
                                                                (hideAll M prover ins') .nil).bind _) _ _
                                                            have hStP : Stack.start M (Defs.fnTable M a.program.defs)
                                                                [conPL, layPL] (hideAll M prover ins') .nil =
                                                                .done (.cons st0 (.cons ([] : List (M.Val uPair.1)) .nil)) := by
                                                              change ((liftLocal id (conPL.start.denote
                                                                (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                                                (Env.positional (heldValues M prover (hideAll M prover ins'))))).bind fun f₁ =>
                                                                  ((liftLocal id ((layoutPStart uPair.1).denote
                                                                    (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                                                    (Env.positional (heldValues M prover (hideAll M prover ins'))))).bind fun f₂ =>
                                                                      (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                                                                        HList.cons f₁.single others) = _
                                                              rw [hSP', liftLocal_done]
                                                              dsimp only [Process.bind, HList.single]
                                                              rw [layoutPStart_denote]; rfl
                                                            rw [hStP]; dsimp only [Process.bind]
                                                            have hAP' := alone_mapHalt M (g := Prod.fst) hAP
                                                            rw [← List.append_nil recP']
                                                            refine alone_bind M hAP' ?_
                                                            have hFinP : Stack.finish M (Defs.fnTable M a.program.defs)
                                                                [conPL, layPL] (.cons finalSt (.cons suffix .nil)) =
                                                                .done (.cons suffix .nil) := by
                                                              rw [stack_finish_two]; dsimp only [conPL, layPL]
                                                              rw [emptyFinish_denote]
                                                              dsimp only [liftLocal_done, Process.bind]
                                                              rw [identityFinish_denote]; rfl
                                                            rw [hFinP]; exact .done
                                                          · unfold runStack
                                                            change Alone M source verifier
                                                              ((Stack.start M (Defs.fnTable M a.program.defs) [conVL, layVL]
                                                                (hideAll M verifier ins') (.cons suffix .nil)).bind _) _ _
                                                            have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                                                                [conVL, layVL] (hideAll M verifier ins') (.cons suffix .nil) =
                                                                .done (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)) := by
                                                              change ((liftLocal id (conVL.start.denote
                                                                (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                                                (Env.positional (heldValues M verifier (hideAll M verifier ins'))))).bind fun f₁ =>
                                                                  ((liftLocal id ((layoutVStart uPair.1).denote
                                                                    (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                                                    (Env.positional (.cons suffix (heldValues M verifier (hideAll M verifier ins')))))).bind fun f₂ =>
                                                                      (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                                                                        HList.cons f₁.single others) = _
                                                              rw [hSV', liftLocal_done]
                                                              dsimp only [Process.bind, HList.single]
                                                              rw [layoutVStart_denote]; rfl
                                                            rw [hStV]; dsimp only [Process.bind]
                                                            have hAV' := alone_mapHalt M (g := Prod.fst) hAV
                                                            rw [← List.append_nil recV']
                                                            refine alone_bind M hAV' ?_
                                                            have hFinV : Stack.finish M (Defs.fnTable M a.program.defs)
                                                                [conVL, layVL] (.cons finalSt (.cons (suffix, (suffix.length, ())) .nil)) =
                                                                .done .nil := by
                                                              rw [stack_finish_two]; dsimp only [conVL, layVL]
                                                              rw [emptyFinish_denote]
                                                              dsimp only [liftLocal_done, Process.bind]
                                                              rw [layoutVFinish_denote]
                                                              simp only [Nat.beq_refl, Bool.cond_true]; rfl
                                                            rw [hFinV]; exact .done
                                                        simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlV0
                                                        obtain ⟨gives, givesV, hRunP, hRunV⟩ :=
                                                          hFinish _ hEntryF _ ins hSt0P hSt0V
                                                            (by simpa [conPL, layPL] using first)
                                                            (by simpa [Ne.symm hNe, conPL, layPL, conVL, layVL] using matched)
                                                            outP outV recP recV
                                                            (alone_cast_stack2 M hEntryF conPL layPL rfl rfl hAlP)
                                                            (alone_cast_stack2 M hEntryF conVL layVL rfl rfl hAlV0)
                                                        have hStackPEq : dDer.stack prover = hEntryF ▸ [conPL, layPL] := by
                                                          dsimp only [dDer]; rw [dite_eq_left rfl]
                                                        have hStackVEq : dDer.stack verifier = hEntryF ▸ [conVL, layVL] := by
                                                          dsimp only [dDer]; rw [dite_eq_right (Ne.symm hNe), dite_eq_left rfl]
                                                        refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
                                                          recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
                                                          ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
                                                        · exact alone_deployed_run_congr M (d := dDer) rfl hNoRetry hStackPEq
                                                            ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
                                                        · exact alone_deployed_run_congr M (d := dDer) rfl hNoRetry hStackVEq
                                                            ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
                                                            (cast_heq _ _) hRunV

theorem statements_complete (enc : VocabEncoder V) (c : Functions V)
    (hadm : c.admit = admit) (hdep : c.deploy = deploy enc) : Statements.complete c := by
  intro named assoc a hA _ decl d hD hNI hNR hNS hRec p v hR first matched M ins hIns hSL hLL hNH src hLP hFed
  rw [hadm] at hA; rw [hdep] at hD
  exact deploy_complete M enc hA hD hNI hNR hNS hRec p v hR first matched ins hIns hSL hLL hNH src hLP hFed

end Completeness

/-! ## Section 6: Ideal random-oracle linkage (`deployIdeal_link`) -/

section IdealLink

variable {V : Vocabulary} (M : Model V)

private theorem answerService_bind {H A B : Type} (service : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ)) :
    ∀ (p : Process (RSig M) H A) (f : A → Process (RSig M) H B),
      Process.answerService service oracle (p.bind f) =
        (Process.answerService service oracle p).bind fun a => Process.answerService service oracle (f a)
  | .done _, _ => rfl
  | .halt _, _ => rfl
  | .call (.own (.request svc) hearers at_ ins payload τ) k, f => by
      dsimp only [Process.bind]
      by_cases hs : svc = service
      · simp only [Process.answerService, hs, ↓reduceIte]
        cases hO : oracle ins payload τ with
        | some v => exact answerService_bind service oracle (k v) f
        | none =>
            dsimp only [Process.bind]
            congr 1; funext v; exact answerService_bind service oracle (k v) f
      · simp only [Process.answerService, hs, ↓reduceIte]
        dsimp only [Process.bind]
        congr 1; funext v; exact answerService_bind service oracle (k v) f
  | .call (.own (.coin _) _ _ _ _ _) k, f => by
      dsimp only [Process.bind, Process.answerService]
      congr 1; funext v; exact answerService_bind service oracle (k v) f
  | .call (.give ..) k, f => by
      dsimp only [Process.bind, Process.answerService]
      congr 1; funext u; exact answerService_bind service oracle (k u) f
  | .call (.get ..) k, f => by
      dsimp only [Process.bind, Process.answerService]
      congr 1; funext v; exact answerService_bind service oracle (k v) f
  | .call (.hear ..) k, f => by
      dsimp only [Process.bind, Process.answerService]
      congr 1; funext v; exact answerService_bind service oracle (k v) f
  | .call (.begin _) k, f => by
      dsimp only [Process.bind, Process.answerService]
      congr 1; funext n; exact answerService_bind service oracle (k n) f
  | .call (.settle _) k, f => by
      dsimp only [Process.bind, Process.answerService]
      congr 1; funext u; exact answerService_bind service oracle (k u) f

private theorem answerService_map {H A B : Type} (service : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    (g : A → B) (p : Process (RSig M) H A) :
    Process.answerService service oracle (p.map g) =
      (Process.answerService service oracle p).map g := by
  rw [Process.map_eq_bind, Process.map_eq_bind, answerService_bind]
  rfl

private theorem answerService_mapHalt {H H' A : Type} (service : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    (g : H → H') : ∀ (p : Process (RSig M) H A),
    Process.answerService service oracle (p.mapHalt g) =
      (Process.answerService service oracle p).mapHalt g
  | .done _ => rfl
  | .halt _ => rfl
  | .call (.own (.request svc) hearers at_ ins payload τ) k => by
      dsimp only [Process.mapHalt]
      by_cases hs : svc = service
      · simp only [Process.answerService, hs, ↓reduceIte]
        cases hO : oracle ins payload τ with
        | some v => exact answerService_mapHalt service oracle g (k v)
        | none =>
            dsimp only [Process.mapHalt]
            congr 1; funext v; exact answerService_mapHalt service oracle g (k v)
      · simp only [Process.answerService, hs, ↓reduceIte]
        dsimp only [Process.mapHalt]
        congr 1; funext v; exact answerService_mapHalt service oracle g (k v)
  | .call (.own (.coin _) _ _ _ _ _) k => by
      dsimp only [Process.mapHalt, Process.answerService]
      congr 1; funext v; exact answerService_mapHalt service oracle g (k v)
  | .call (.give ..) k => by
      dsimp only [Process.mapHalt, Process.answerService]
      congr 1; funext u; exact answerService_mapHalt service oracle g (k u)
  | .call (.get ..) k => by
      dsimp only [Process.mapHalt, Process.answerService]
      congr 1; funext v; exact answerService_mapHalt service oracle g (k v)
  | .call (.hear ..) k => by
      dsimp only [Process.mapHalt, Process.answerService]
      congr 1; funext v; exact answerService_mapHalt service oracle g (k v)
  | .call (.begin _) k => by
      dsimp only [Process.mapHalt, Process.answerService]
      congr 1; funext n; exact answerService_mapHalt service oracle g (k n)
  | .call (.settle _) k => by
      dsimp only [Process.mapHalt, Process.answerService]
      congr 1; funext u; exact answerService_mapHalt service oracle g (k u)

private theorem answerService_liftLocal {H A : Type} (service : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    (f : Stop → H) : ∀ (p : Local A),
    Process.answerService service oracle (liftLocal (S := RSig M) f p) = liftLocal f p
  | .done _ => rfl
  | .halt _ => rfl
  | .call op _ => nomatch op

/-- Direct ideal-RO verifier state machine (completely independent of `Layer`/`Stack`/`Handler`/
`Clause`), parameterized directly by a total random oracle `ro` on `(state, drawLabel, ty)` for a
non-carry streaming verifier. -/
def evalIdealVerifierLoop {A : Type} (a : Admitted V) (suite : ModuleRef) (layout : Layout)
    {stateTy suiteUnitTy unitTy : V.Ty}
    (absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy])
    (serviceKey : Key) (prover : Role) (finishGuard : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    (ro : M.Val stateTy → List Nat → (τ : V.Ty) → M.Val τ) :
    Program M A → M.Val stateTy → List (M.Val unitTy) → Nat →
    Process (RSig M) Stop (A × HList M.Val [])
  | .done outV, _, buf, off =>
      bif Nat.beq off buf.length then .done (outV, .nil)
      else .halt (.declared .reject ⟨[], finishGuard⟩)
  | .halt why, _, _, _ => .halt why
  | .call op k, st, buf, off =>
      match op with
      | .get knd giver at_ τ =>
          if giver = prover then
            match findLayoutRead a layout.module unitTy τ, findSuiteEncode a suite suiteUnitTy τ with
            | some rRef, some encRef =>
                (liftLocal id (rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)))).bind
                  fun res => match res with
                  | .cons msg (.cons nextOff .nil) =>
                      (liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil))).bind
                        fun enc =>
                          (liftLocal id (absRef.eval M (Defs.fnTable M a.program.defs)
                            (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).bind
                            fun nextSt =>
                              evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
                                oracle ro (k msg) nextSt.single buf nextOff
            | _, _ => .call (.get knd giver at_ τ) fun v =>
                evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
                  oracle ro (k v) st buf off
          else
            .call (.get knd giver at_ τ) fun v =>
              evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
                oracle ro (k v) st buf off
      | .own (.coin law) (h0 :: hs) at_ [] .nil τ =>
          match findSuiteEncode a suite suiteUnitTy τ with
          | some encRef =>
              let coin := ro st (drawLabel at_.site) τ
              (liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil))).bind
                fun enc =>
                  (liftLocal id (absRef.eval M (Defs.fnTable M a.program.defs)
                    (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil))))).bind
                    fun nextSt =>
                      evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
                        oracle ro (k coin) nextSt.single buf off
          | none => .call (.own (.coin law) (h0 :: hs) at_ [] .nil τ) fun v =>
              evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
                oracle ro (k v) st buf off
      | .own (.request svc) hearers at_ ins payload τ =>
          if svc = serviceKey then
            match oracle ins payload τ with
            | some v =>
                evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
                  oracle ro (k v) st buf off
            | none => .call (.own (.request svc) hearers at_ ins payload τ) fun v =>
                evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
                  oracle ro (k v) st buf off
          else .call (.own (.request svc) hearers at_ ins payload τ) fun v =>
            evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
              oracle ro (k v) st buf off
      | op' => .call op' fun v =>
          evalIdealVerifierLoop a suite layout absRef serviceKey prover finishGuard
            oracle ro (k v) st buf off

private theorem ideal_clauses_answer_flow {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildIdealVerifierClauses.go a suite stateTy unitTy absRef serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧
          ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]),
          findSuiteEncode a suite unitTy τ = some encRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.get kind prover at_ τ) st =
            .call (.get kind prover ⟨at_.path, at_.site.key⟩ τ) fun msg =>
              (((liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil))).bind fun enc =>
                (liftLocal id (absRef.eval M (Defs.fnTable M a.program.defs)
                  (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).map
                  fun nextSt => aloneIn M verifier (.cons msg nextSt)).mapHalt fun why => (why, st)).map fun out =>
                let values := HList.split [τ] (aloneOut M verifier out)
                (values.1.single, values.2.single)
  | _, [], _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, cV, h, kind, at_, τ, st, ⟨e', he', hSite, hTy, gs', hVin, hECls⟩ => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite stateTy unitTy absRef serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => ideal_clauses_answer_flow (idx + 1) rest hRec kind at_ τ st hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some encRef =>
                    rw [hEnc] at h; cases h
                    by_cases hMatch :
                        e.site = at_.site ∧
                        some (Part.get (V := V) kind₀ prover) = some (.get kind prover) ∧
                        ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                    · have hSiteEq : e.site = at_.site := hMatch.1
                      have hPartEq : Part.get kind₀ prover = .get kind prover := Option.some.inj hMatch.2.1
                      cases hPartEq
                      have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                      subst hTyEq
                      refine ⟨encRef, hEnc, ?_⟩
                      rw [← hSiteEq]
                      exact verifierAbsorbClause_answer M _ _ verifier prover e.site kind
                        (msgLabel e.site) (msgLabel_bytes e.site) encRef absRef at_ hSiteEq st vRest
                    · rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                        exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                      · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        refine ⟨encR, hE, ?_⟩
                        unfold Clause.answer
                        exact (dite_eq_right hMatch).trans hAns
              · split at h
                · rename_i hOut; cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
                  · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                · cases h
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hIns : sig.ins with
                          | cons _ _ => rw [hIns] at h; cases h
                          | nil =>
                              rw [hIns] at h; dsimp only at h
                              cases hEnc : findSuiteEncode a suite unitTy e.τ with
                              | none => rw [hEnc] at h; cases h
                              | some _ =>
                                  rw [hEnc] at h; cases h
                                  rcases List.mem_cons.mp he' with rfl | hmem
                                  · rw [hCls] at hECls; cases hECls
                                  · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                                    refine ⟨encR, hE, ?_⟩
                                    unfold Clause.answer
                                    rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                    exact hAns
                        · cases h
                  · split at h
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                  · cases h

private theorem ideal_clauses_answer_coin {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ k e, es[k]? = some e → events[idx + k]? = some e) →
      ∀ {cV : List (Clause V a.program.headers verifier stateTy)},
      buildIdealVerifierClauses.go a suite stateTy unitTy absRef serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧ prover ∈ hearers ∧
          e.cls = .given (.coin law) verifier hearers) →
        ∃ (idxV : Nat) (eV : ShapeEvent V)
          (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]),
          events[idxV]? = some eV ∧ eV.site = at_.site ∧ eV.τ = τ ∧
          eV.cls = .given (.coin law) verifier hearers ∧
          findSuiteEncode a suite unitTy τ = some encRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.own (.coin law) hearers at_ [] .nil τ) st =
            .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ) fun coin =>
              .call (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin) fun _ =>
                (((liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil))).bind fun enc =>
                  (liftLocal id (absRef.eval M (Defs.fnTable M a.program.defs)
                    (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil))))).map
                    fun nextSt => aloneIn M verifier (.cons coin nextSt)).mapHalt
                      fun why => (why, st)).map fun out =>
                  let values := HList.split [τ] (aloneOut M verifier out)
                  (values.1.single, values.2.single)
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, hSuf, cV, h, law, hearers, at_, τ, st, ⟨e', he', hSite, hTy, hPin, hECls⟩ => by
      unfold buildIdealVerifierClauses.go at h
      have hSufRest : ∀ k e'', rest[k]? = some e'' → events[(idx + 1) + k]? = some e'' := by
        intro k e'' hk; have := hSuf (k + 1) e'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 e rfl
      cases hRec : buildIdealVerifierClauses.go a suite stateTy unitTy absRef serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => ideal_clauses_answer_coin (idx + 1) rest hSufRest hRec
            law hearers at_ τ st hIn
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some _ =>
                    rw [hEnc] at h; cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · obtain ⟨idxV, eV, encR, h1, h2, h3, h4, h5, hAns⟩ :=
                        ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                      refine ⟨idxV, eV, encR, h1, h2, h3, h4, h5, ?_⟩
                      unfold Clause.answer; rw [dite_eq_right (fun hm => by cases hm.2.1)]; exact hAns
              · split at h
                · cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                · cases h
          | given gkind owner hearers₀ =>
              rw [hCls] at h
              cases gkind with
              | coin law₀ =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law₀ with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hIns : sig.ins with
                          | cons _ _ => rw [hIns] at h; cases h
                          | nil =>
                              rw [hIns] at h; dsimp only at h
                              cases hEnc : findSuiteEncode a suite unitTy e.τ with
                              | none => rw [hEnc] at h; cases h
                              | some encRef =>
                                  rw [hEnc] at h; cases h
                                  by_cases hMatch :
                                      e.site = at_.site ∧
                                      some (Part.own (.coin law₀) hearers₀) = some (.own (.coin law) hearers) ∧
                                      ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                                  · have hSiteEq : e.site = at_.site := hMatch.1
                                    have hPartEq : Part.own (.coin law₀) hearers₀ = .own (.coin law) hearers :=
                                      Option.some.inj hMatch.2.1
                                    cases hPartEq
                                    have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                                    cases e with
                                    | mk eSite eCls eτ =>
                                        dsimp only at hIdx hCls hEnc hSiteEq hTyEq hMatch hCoin
                                        subst eτ; subst eSite
                                        refine ⟨idx, ⟨at_.site, eCls, τ⟩, encRef, hIdx, rfl, rfl, hCoin.1 ▸ hCls, hEnc, ?_⟩
                                        unfold Clause.answer
                                        have hM : (idealDeriveClause verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef absRef).site.site =
                                            (ROp.occurrence M (.own (.coin law) hearers at_ [] .nil τ)).site ∧
                                            some (idealDeriveClause verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef absRef).site.part =
                                            ROp.part M (.own (.coin law) hearers at_ [] .nil τ) ∧
                                            (idealDeriveClause verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef absRef).site.takes =
                                            ROp.takes M (.own (.coin law) hearers at_ [] .nil τ) ∧
                                            (idealDeriveClause verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef absRef).site.gives =
                                            ROp.gives M (.own (.coin law) hearers at_ [] .nil τ) := ⟨rfl, rfl, rfl, rfl⟩
                                        rw [dite_eq_left hM]
                                        change (((idealDeriveClause verifier prover at_.site (.own (.coin law) hearers)
                                          [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                          (drawLabel at_.site) (drawLabel_bytes at_.site) encRef absRef).code.denote
                                          (roleSem M verifier _ _) at_.path
                                          (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt _).map _ = _
                                        rw [idealDeriveClause_denote_nil]
                                        dsimp only [Process.mapHalt, Process.map, idealDeriveClause, Clause.site]
                                        congr 1; funext coin; congr 1; funext _; congr 1; funext out
                                        cases hsp : HList.split [τ] (aloneOut M verifier out) with
                                        | mk v1 v2 => cases v1 with | cons a an => cases an; rfl
                                  · rcases List.mem_cons.mp he' with rfl | hmem
                                    · rw [hCls] at hECls; cases hECls
                                      exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                                    · obtain ⟨idxV, eV, encR, h1, h2, h3, h4, h5, hAns⟩ :=
                                        ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                                      refine ⟨idxV, eV, encR, h1, h2, h3, h4, h5, ?_⟩
                                      unfold Clause.answer
                                      exact (dite_eq_right hMatch).trans hAns
                        · cases h
                  · split at h
                    · rename_i hNil
                      cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; subst hNil; cases hPin
                      · exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hPin, hECls⟩
                  · cases h

private theorem ideal_clauses_unmatched_closed {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildIdealVerifierClauses.go a suite stateTy unitTy absRef serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ op, ROp.IsClosed M op → ∀ c ∈ cV, ¬ ClauseMatches M c op
  | _, [], _, h, _, _ => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, cV, h, op, hCl => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite stateTy unitTy absRef serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := ideal_clauses_unmatched_closed (idx + 1) rest hRec op hCl
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hEnc : findSuiteEncode a suite unitTy e.τ with
                | none => rw [hEnc] at h; cases h
                | some _ =>
                    rw [hEnc] at h; cases h
                    intro c hc
                    rcases List.mem_cons.mp hc with rfl | hm
                    · intro hM; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, verifierAbsorbClause] at hCl hM
                    · exact ih c hm
              · split at h
                · cases h; exact ih
                · cases h
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hIns : sig.ins with
                          | cons _ _ => rw [hIns] at h; cases h
                          | nil =>
                              rw [hIns] at h; dsimp only at h
                              cases hEnc : findSuiteEncode a suite unitTy e.τ with
                              | none => rw [hEnc] at h; cases h
                              | some _ =>
                                  rw [hEnc] at h; cases h
                                  intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hM
                                    cases op with
                                    | own gk hs' _ _ _ _ =>
                                        cases gk with
                                        | coin _ =>
                                            cases hs' with
                                            | nil =>
                                                have hp := Option.some.inj hM.2.1; cases hp
                                                exact nomatch hCoin.2
                                            | cons _ _ => exact False.elim hCl
                                        | request _ =>
                                            have hp := Option.some.inj hM.2.1; cases hp
                                    | give | get | hear | «begin» | settle =>
                                        simp [ROp.IsClosed, ROp.part, ClauseMatches, idealDeriveClause] at hCl hM
                                  · exact ih c hm
                        · cases h
                  · split at h
                    · cases h; exact ih
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ih
                  · cases h

private theorem streaming_layout_answer_verifier_flow_full {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty) (buf : List (M.Val unitTy)) (off : Nat),
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧
          ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]),
          findLayoutRead a layout.module unitTy τ = some rRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            vCs (.get kind prover at_ τ) (buf, (off, ())) =
            ((liftLocal id (rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)))).map
              fun res => match res with
                | .cons v (.cons nextOff .nil) => (v, (buf, (nextOff, ())))).mapHalt
              fun why => (why, (buf, (off, ())))
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, pCs, vCs, h, kind, at_, τ, buf, off,
      ⟨e', he', hSite, hTy, gs', hVin, hECls⟩ => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => streaming_layout_answer_verifier_flow_full (idx + 1) rest hRec
            kind at_ τ buf off hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · rename_i wRef rRef
                  cases h
                  by_cases hMatch :
                      e.site = at_.site ∧
                      some (Part.get (V := V) kind₀ prover) = some (.get kind prover) ∧
                      ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                  · have hSiteEq : e.site = at_.site := hMatch.1
                    have hPartEq : Part.get kind₀ prover = .get kind prover := Option.some.inj hMatch.2.1
                    cases hPartEq
                    have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                    subst hTyEq
                    refine ⟨rRef, hR, ?_⟩
                    unfold Clause.answer
                    have hM : (layoutVReadClause hfree verifier prover e.site kind rRef).site.site =
                        (ROp.occurrence M (.get kind prover at_ e.τ)).site ∧
                        some (layoutVReadClause hfree verifier prover e.site kind rRef).site.part =
                        ROp.part M (.get kind prover at_ e.τ) ∧
                        (layoutVReadClause hfree verifier prover e.site kind rRef).site.takes =
                        ROp.takes M (.get kind prover at_ e.τ) ∧
                        (layoutVReadClause hfree verifier prover e.site kind rRef).site.gives =
                        ROp.gives M (.get kind prover at_ e.τ) := ⟨hSiteEq, rfl, rfl, rfl⟩
                    rw [dite_eq_left hM]
                    change (((layoutVReadClause hfree verifier prover e.site kind rRef).code.denote
                      (roleSem M verifier _ _) at_.path
                      (Env.positional (aloneIn M verifier (.cons (buf, (off, ())) .nil)))).mapHalt _).map _ = _
                    rw [layoutVReadClause_denote]
                    cases rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) with
                    | done res =>
                        cases res with
                        | cons v r1 =>
                            cases r1 with
                            | cons nO r2 =>
                                cases r2
                                rw [liftLocal_done]
                                dsimp only [Process.map, Process.mapHalt, layoutVReadClause,
                                  Clause.site, List.cons_append, List.nil_append]
                                simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]
                                rfl
                    | halt why => rfl
                    | call op _ => cases op
                  · rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                      exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                    · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                      refine ⟨rR, h1, ?_⟩
                      unfold Clause.answer
                      exact (dite_eq_right hMatch).trans hAns
              · rename_i hNotPV; cases h
                rcases List.mem_cons.mp he' with rfl | hmem
                · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                          refine ⟨rR, h1, ?_⟩
                          unfold Clause.answer; rw [dite_eq_right (fun hm => by cases hm.2.1)]; exact hAns
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        refine ⟨rR, h1, ?_⟩
                        unfold Clause.answer; rw [dite_eq_right (fun hm => by cases hm.2.1)]; exact hAns
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩

private theorem streaming_layout_answer_told_drop {a : Admitted V} {layout : Layout}
    (hNoCarry : layout.carry = [])
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ e ∈ es, e ∈ events) →
      ∀ {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
        {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (k : Nat) (e₀ : ShapeEvent V), es[k]? = some e₀ →
        ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (coin : M.Val e₀.τ),
          e₀.cls = .given (.coin law) verifier hearers → prover ∈ hearers →
          at_.site = ⟨e₀.site.through, drawToldKey events (idx + k)⟩ →
          ∀ buf off, Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            vCs (.give .message [prover] at_ e₀.τ coin) (buf, (off, ())) =
            .done ((), (buf, (off, ())))
  | _, [], _, _, _, _, _, _, hk, _, _, _, _, _, _, _, _, _ => by simp at hk
  | idx, e :: rest, hSub, pCs, vCs, h, k, e₀, hk, law, hearers, at_, coin, hE₀Cls, hPin, hAtSite, buf, off => by
      unfold buildStreamingLayoutClauses.go at h
      have hSubRest : ∀ e'' ∈ rest, e'' ∈ events := fun e'' he'' => hSub e'' (List.mem_cons_of_mem _ he'')
      have hMemE : e ∈ events := hSub e List.mem_cons_self
      have hFlowNoMatch : e.site ≠ at_.site := by
        intro heq
        have hkEq : e.site.key = drawToldKey events (idx + k) := by
          have := congrArg Site.key heq; rw [hAtSite] at this; exact this
        exact drawToldKey_fresh events (idx + k) (hkEq ▸ List.mem_map.mpr ⟨e, hMemE, rfl⟩)
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          cases k with
          | zero =>
              simp at hk; subst hk
              rw [hE₀Cls] at h; dsimp only at h
              rw [ite_eq_left ⟨rfl, hPin⟩, ite_eq_right (by simp [hNoCarry])] at h; cases h
              have hSiteEq : ⟨e.site.through, drawToldKey events idx⟩ = at_.site := by
                simpa using hAtSite.symm
              exact layoutDropClause_answer M _ _ verifier _ .message [prover] at_ hSiteEq coin (buf, (off, ())) pair.2
          | succ k' =>
              have hShiftSite : at_.site = ⟨e₀.site.through, drawToldKey events ((idx + 1) + k')⟩ := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAtSite
              have hToldNoMatch : (⟨e.site.through, drawToldKey events idx⟩ : Site) ≠ at_.site := by
                intro heq
                have hkEq : (drawToldKey events idx).number = (drawToldKey events (idx + (k' + 1))).number := by
                  have := congrArg (fun s : Site => s.key.number) heq; rw [hAtSite] at this; exact this
                simp only [drawToldKey] at hkEq; omega
              have ih := streaming_layout_answer_told_drop hNoCarry (idx + 1) rest hSubRest hRec k' e₀ hk
                law hearers at_ coin hE₀Cls hPin hShiftSite buf off
              cases hCls : e.cls with
              | flow _ _ _ =>
                  rw [hCls] at h; dsimp only at h
                  split at h
                  · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact ih
                  · cases h; exact ih
              | given gkind _ _ =>
                  rw [hCls] at h
                  cases gkind with
                  | coin _ =>
                      dsimp only at h
                      split at h
                      · rw [ite_eq_right (by simp [hNoCarry])] at h; cases h
                        unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih
                      · cases h; exact ih
                  | request _ => cases h; exact ih

private theorem ideal_verifier_loop_eq {a : Admitted V} {suite : ModuleRef} {layout : Layout}
    (hNoCarry : layout.carry = []) {stateTy suiteUnitTy unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {serviceKey : Key} {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {events : List (ShapeEvent V)} {entryIns : List (LTy V)}
    (idealConV layV : Layer V a.program.headers verifier entryIns)
    (hConSt : idealConV.state = stateTy) (hLaySt : layV.state = streamStateTy unitTy)
    (hConGives : idealConV.gives = []) (hLayGives : layV.gives = [])
    (hConFin : idealConV.finish = hConGives.symm ▸ hConSt.symm ▸ emptyFinish stateTy)
    (hLayFin : layV.finish = hLayGives.symm ▸ hLaySt.symm ▸ layoutVFinish unitTy hfree (finishGuardKey events))
    (hIV : buildIdealVerifierClauses.go a suite stateTy suiteUnitTy absRef serviceKey prover verifier
      declKey events 0 events = .ok (hConSt ▸ idealConV.clauses))
    (hSL : ∃ pCs, buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
      events 0 events = .ok (pCs, hLaySt ▸ layV.clauses))
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    (ro : M.Val stateTy → List Nat → (τ : V.Ty) → M.Val τ)
    (hOracleRo : ∀ st lbl τ,
      oracle [idealQueryTy stateTy] (.cons (st, (lbl, ())) .nil) τ = some (ro st lbl τ)) :
    ∀ {A : Type} (p : Program M A) (st : M.Val stateTy) (buf : List (M.Val unitTy)) (off : Nat),
      p.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier events) (fun _ => True) (fun _ => True) →
      Process.answerService serviceKey oracle
        ((((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
          [idealConV, layV]).run (retryOf M none) p
            (.cons (hConSt.symm ▸ st) (.cons (hLaySt.symm ▸ (buf, (off, ())))
              (.nil : HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns))))))).mapHalt Prod.fst).bind
          fun out => (Stack.finish M (Defs.fnTable M a.program.defs) [idealConV, layV] out.2).map
            fun gives => (out.1, cast (by simp [Stack.Gives, hConGives, hLayGives]) gives)) =
        evalIdealVerifierLoop M a suite layout absRef serviceKey prover (finishGuardKey events)
          oracle ro p st buf off := by
  cases idealConV with
  | mk cLine cSt cTakes cGives cClauses cAgain cStart cFin =>
      cases layV with
      | mk lLine lSt lTakes lGives lClauses lAgain lStart lFin =>
          dsimp only at hConSt hLaySt hConGives hLayGives
          subst cSt; subst lSt; subst cGives; subst lGives
          dsimp only at hConFin hLayFin hIV hSL
          subst cFin; subst lFin
          obtain ⟨pCs, hSL'⟩ := hSL
          let fnTable := Defs.fnTable M a.program.defs
          let rTable := Defs.rTable M a.program.defs
          have hIdealDisc : ∀ e ∈ events,
              match e.cls with
              | .flow _ giver getters =>
                  (giver = prover ∧ verifier ∈ getters) ∨
                  (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
              | .given (.coin law) owner hearers =>
                  (owner = verifier ∧ prover ∈ hearers ∧
                    ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
                  hearers = []
              | .given (.request _) owner hearers =>
                  (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
            have hGo : ∀ (idx : Nat) (es : List (ShapeEvent V)) {cV'},
                buildIdealVerifierClauses.go a suite stateTy suiteUnitTy absRef serviceKey
                  prover verifier declKey events idx es = .ok cV' →
                ∀ e ∈ es, match e.cls with
                  | .flow _ giver getters =>
                      (giver = prover ∧ verifier ∈ getters) ∨
                      (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                  | .given (.coin law) owner hearers =>
                      (owner = verifier ∧ prover ∈ hearers ∧
                        ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
                      hearers = []
                  | .given (.request _) owner hearers =>
                      (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
              intro idx es
              induction es generalizing idx with
              | nil => intro _ _ _ he; cases he
              | cons e rest ih =>
                  intro cV' hGo' e' he'
                  unfold buildIdealVerifierClauses.go at hGo'
                  cases hRec : buildIdealVerifierClauses.go a suite stateTy suiteUnitTy absRef
                      serviceKey prover verifier declKey events (idx + 1) rest with
                  | error _ => rw [hRec] at hGo'; cases hGo'
                  | ok vRest =>
                      rw [hRec] at hGo'; dsimp only [bind, Except.bind] at hGo'
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · cases hCls : e'.cls with
                        | flow _ giver getters =>
                            rw [hCls] at hGo'; dsimp only at hGo'
                            split at hGo'
                            · exact .inl ‹_›
                            · split at hGo'
                              · exact .inr ‹_›
                              · cases hGo'
                        | given gkind owner hearers =>
                            rw [hCls] at hGo'
                            cases gkind with
                            | coin law =>
                                dsimp only at hGo'
                                split at hGo'
                                · rename_i hC
                                  cases hLaw : V.law law with
                                  | none => rw [hLaw] at hGo'; cases hGo'
                                  | some sig =>
                                      rw [hLaw] at hGo'; dsimp only at hGo'
                                      split at hGo'
                                      · rename_i hOut
                                        cases hIns : sig.ins with
                                        | nil => exact .inl ⟨hC.1, hC.2, sig, hLaw, hOut, hIns⟩
                                        | cons _ _ => rw [hIns] at hGo'; cases hGo'
                                      · cases hGo'
                                · split at hGo'
                                  · exact .inr ‹_›
                                  · cases hGo'
                            | request _ =>
                                dsimp only at hGo'
                                split at hGo'
                                · rename_i hReq; exact hReq
                                · cases hGo'
                      · exact ih (idx + 1) hRec e' hmem
            exact hGo 0 events hIV
          let idealConV' : Layer V a.program.headers verifier entryIns :=
            ⟨cLine, stateTy, cTakes, [], cClauses, cAgain, cStart, emptyFinish stateTy⟩
          let layV' : Layer V a.program.headers verifier entryIns :=
            ⟨lLine, streamStateTy unitTy, lTakes, [], lClauses, lAgain, lStart,
              layoutVFinish unitTy hfree (finishGuardKey events)⟩
          have hPassV : ∀ op (st : M.Val stateTy) (lst : M.Val (streamStateTy unitTy)),
              ROp.IsClosed M op →
              (Stack.handler M fnTable rTable [idealConV', layV']).clause op
                  (.cons st (.cons lst (.nil : HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns)))))) =
                .call op fun reply =>
                  .done (reply, .cons st (.cons lst (.nil : HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns)))))) := fun op st lst hCl =>
            stack2_clause_pass M fnTable rTable idealConV' layV' op st lst
              (clause_answer_unmatched_all M fnTable rTable op st cClauses
                (ideal_clauses_unmatched_closed M 0 events hIV op hCl))
              (clause_answer_unmatched_all M fnTable rTable op lst lClauses
                (streaming_layout_unmatched_closed M 0 events hSL' op hCl).2)
          intro A p
          induction p with
          | done outV =>
              intro st buf off _
              have hFin : Stack.finish M (Defs.fnTable M a.program.defs) [idealConV', layV']
                  (.cons st (.cons (buf, (off, ())) .nil)) =
                  bif Nat.beq off buf.length then .done .nil
                  else .halt (.declared .reject ⟨[], finishGuardKey events⟩) := by
                rw [stack_finish_two]; dsimp only [idealConV', layV']
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [layoutVFinish_denote]
                cases Nat.beq off buf.length <;> rfl
              dsimp only [Handler.run, Process.mapHalt, Process.bind, evalIdealVerifierLoop]
              rw [hFin]
              cases Nat.beq off buf.length <;> rfl
          | halt why =>
              intro _ _ _ _; rfl
          | call op k ih =>
              intro st buf off ⟨hOpSh, hKSh⟩
              cases op with
              | give kind getters at_ τ x =>
                  obtain ⟨e, he, _, _, hCls⟩ := hOpSh
                  have hD := hIdealDisc e he; rw [hCls] at hD
                  rcases hD with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
                  · exact absurd hEqP.symm hNe
                  · exact absurd rfl hNotV
              | hear gkind owner at_ τ =>
                  obtain ⟨e, he, hONeV, _, _, hs', hVin, hCls⟩ := hOpSh
                  have hD := hIdealDisc e he; rw [hCls] at hD
                  cases gkind with
                  | coin _ =>
                      rcases hD with ⟨hEqO, _, _⟩ | hNil
                      · exact absurd hEqO hONeV
                      · subst hNil; cases hVin
                  | request _ =>
                      rcases hD.2 with hEqO | hNotIn
                      · exact absurd hEqO hONeV
                      · exact absurd hVin hNotIn
              | get kind giver at_ τ =>
                  obtain ⟨e, he, hGNeV, hSite, hTy, gs', hVin, hCls⟩ := hOpSh
                  have hD := hIdealDisc e he; rw [hCls] at hD
                  have hGivP : giver = prover := by
                    rcases hD with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
                    · exact hEqP
                    · exact absurd hVin hNotV
                  subst hGivP
                  obtain ⟨encRef, hEncFind, hConAns⟩ :=
                    ideal_clauses_answer_flow M 0 events hIV kind at_ τ st ⟨e, he, hSite, hTy, gs', hVin, hCls⟩
                  obtain ⟨rRef, hRFind, hLayAns⟩ :=
                    streaming_layout_answer_verifier_flow_full M 0 events hSL' kind ⟨at_.path, at_.site.key⟩ τ buf off
                      ⟨e, he, hSite, hTy, gs', hVin, hCls⟩
                  conv =>
                    rhs
                    rw [evalIdealVerifierLoop]
                    dsimp only
                    rw [ite_eq_left rfl, hRFind, hEncFind]
                  dsimp only [Handler.run]
                  change Process.answerService serviceKey oracle
                    (((((Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                      (.cons st (.cons (buf, (off, ())) .nil))).bind _).mapHalt _).bind _) = _
                  -- Expand `Stack.handler [idealConV', layV'].clause` using `hConAns` and `hLayAns`
                  have hClauseEq : (Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                      (.cons st (.cons (buf, (off, ())) .nil)) =
                      (liftLocal (fun why => (why, .cons st (.cons (buf, (off, ())) .nil)))
                        (rRef.eval M fnTable (.cons buf (.cons off .nil)))).bind fun res =>
                        match res with
                        | .cons msg (.cons nextOff .nil) =>
                            (liftLocal (fun why => (why, .cons st (.cons (buf, (nextOff, ())) .nil)))
                              (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
                                (liftLocal (fun why => (why, .cons st (.cons (buf, (nextOff, ())) .nil)))
                                  (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).map
                                  fun nextSt => (msg, .cons nextSt.single (.cons (buf, (nextOff, ())) .nil)) := by
                    change ((((Layer.handler M fnTable rTable idealConV').over
                        (Stack.handler M fnTable rTable [layV'])).clause (.get kind giver at_ τ)
                        (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                    dsimp only [Layer.handler, Handler.over, idealConV']
                    rw [hConAns]
                    dsimp only [Handler.answer]
                    have hLayStep : (Stack.handler M fnTable rTable [layV']).clause
                        (.get kind giver ⟨at_.path, at_.site.key⟩ τ) (.cons (buf, (off, ())) .nil) =
                        ((Clause.answer M fnTable rTable lClauses
                          (.get kind giver ⟨at_.path, at_.site.key⟩ τ) (buf, (off, ()))).mapHalt
                          fun stop => (stop.1, .cons stop.2 .nil)).map fun out => (out.1, .cons out.2 .nil) := by
                      change ((((Layer.handler M fnTable rTable layV').over
                          (Stack.handler M fnTable rTable [])).clause
                          (.get kind giver ⟨at_.path, at_.site.key⟩ τ)
                          ((buf, (off, ())), .nil)).mapHalt _).map _ = _
                      dsimp only [Layer.handler, Handler.over, layV']
                      have hAns0 : ∀ (p0 : Process (RSig M) (Stop × M.Val (streamStateTy unitTy))
                          (M.Val τ × M.Val (streamStateTy unitTy))),
                          Process.map (fun (out : M.Val τ × M.Val (streamStateTy unitTy) × HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns)))) =>
                              (out.1, HList.cons out.2.1 out.2.2))
                            (Process.mapHalt (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
                              ((Process.mapHalt (fun stop => (stop.1, stop.2.1, stop.2.2))
                                ((Stack.handler M fnTable rTable []).answer p0 (buf, (off, ())) .nil)).bind
                                  fun out => .done (out.1.1, out.1.2, out.2))) =
                          (p0.mapHalt fun stop => (stop.1, HList.cons stop.2 .nil)).map
                            fun out => (out.1, HList.cons out.2 .nil) := by
                        intro p0
                        induction p0 with
                        | done _ => rfl
                        | halt _ => rfl
                        | call op k ih =>
                            dsimp only [Handler.answer, Stack.handler, Process.map, Process.mapHalt, Process.bind]
                            congr 1; funext x; exact ih x
                      exact hAns0 _
                    rw [hLayStep, hLayAns]
                    cases rRef.eval M fnTable (.cons buf (.cons off .nil)) with
                    | halt why => rfl
                    | call op _ => cases op
                    | done res =>
                        cases res with
                        | cons msg r1 =>
                            cases r1 with
                            | cons nextOff r2 =>
                                cases r2
                                change Process.map
                                  (fun (out : M.Val τ × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                    (out.1, HList.cons out.2.1 out.2.2))
                                  (Process.mapHalt
                                    (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                      (stop.1, HList.cons stop.2.1 stop.2.2))
                                    ((Process.mapHalt
                                      (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                        (stop.1, stop.2.1, stop.2.2))
                                      ((Stack.handler M fnTable rTable [layV']).answer
                                        (Process.map
                                          (fun out =>
                                            ((HList.split [τ] (aloneOut M verifier out)).1.single,
                                              (HList.split [τ] (aloneOut M verifier out)).2.single))
                                          (Process.mapHalt (fun why => (why, st))
                                            ((liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
                                              Process.map (fun nextSt => aloneIn M verifier (.cons msg nextSt))
                                                (liftLocal (S := RSig M) id
                                                  (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))))))
                                        st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).bind
                                      fun out => Process.done (out.1.1, out.1.2, out.2))) =
                                  (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                    (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
                                    Process.map (fun nextSt => (msg, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                      (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                        (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil)))))
                                cases encRef.eval M fnTable (.cons msg .nil) with
                                | halt why => rfl
                                | call op _ => cases op
                                | done enc =>
                                    cases enc with
                                    | cons encV en =>
                                        cases en
                                        change Process.map
                                          (fun (out : M.Val τ × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                            (out.1, HList.cons out.2.1 out.2.2))
                                          (Process.mapHalt
                                            (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                              (stop.1, HList.cons stop.2.1 stop.2.2))
                                            ((Process.mapHalt
                                              (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                                (stop.1, stop.2.1, stop.2.2))
                                              ((Stack.handler M fnTable rTable [layV']).answer
                                                (Process.map
                                                  (fun out =>
                                                    ((HList.split [τ] (aloneOut M verifier out)).1.single,
                                                      (HList.split [τ] (aloneOut M verifier out)).2.single))
                                                  (Process.mapHalt (fun why => (why, st))
                                                    (Process.map (fun nextSt => aloneIn M verifier (.cons msg nextSt))
                                                      (liftLocal (S := RSig M) id
                                                        (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encV .nil))))))))
                                                st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).bind
                                              fun out => Process.done (out.1.1, out.1.2, out.2))) =
                                          Process.map (fun nextSt => (msg, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                            (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                              (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encV .nil)))))
                                        cases absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encV .nil))) with
                                        | halt why => rfl
                                        | call op _ => cases op
                                        | done nSt =>
                                            cases nSt with
                                            | cons st' sn =>
                                                cases sn
                                                change Process.done
                                                  ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier (.cons msg (.cons st' .nil))))).1.single,
                                                    HList.cons ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier (.cons msg (.cons st' .nil))))).2.single)
                                                      (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)) =
                                                  Process.done (msg, HList.cons st' (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))
                                                rw [aloneOut_aloneIn]; rfl
                  rw [hClauseEq]
                  change Process.answerService serviceKey oracle
                    ((Process.mapHalt Prod.fst
                      (((liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                        (rRef.eval M fnTable (.cons buf (.cons off .nil)))).bind _).bind _)).bind _) =
                    (liftLocal id (rRef.eval M fnTable (.cons buf (.cons off .nil)))).bind _
                  cases rRef.eval M fnTable (.cons buf (.cons off .nil)) with
                  | halt why => rfl
                  | call op _ => cases op
                  | done res =>
                      cases res with
                      | cons msg r1 =>
                          cases r1 with
                          | cons nextOff r2 =>
                              cases r2
                              change Process.answerService serviceKey oracle
                                ((Process.mapHalt Prod.fst
                                  (((liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                    (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
                                      (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                        (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).map
                                        fun nextSt => (msg, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).bind _)).bind _) =
                                (liftLocal id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
                                  (liftLocal id (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).bind
                                    fun nextSt => evalIdealVerifierLoop M a suite layout absRef serviceKey giver
                                      (finishGuardKey events) oracle ro (k msg) nextSt.single buf nextOff
                              cases encRef.eval M fnTable (.cons msg .nil) with
                              | halt why => rfl
                              | call op _ => cases op
                              | done enc =>
                                  cases enc with
                                  | cons encV en =>
                                      cases en
                                      change Process.answerService serviceKey oracle
                                        ((Process.mapHalt Prod.fst
                                          ((((liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                            (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encV .nil))))).map
                                            fun nextSt => (msg, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).bind _))).bind _) =
                                        (liftLocal id (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encV .nil))))).bind
                                          fun nextSt => evalIdealVerifierLoop M a suite layout absRef serviceKey giver
                                            (finishGuardKey events) oracle ro (k msg) nextSt.single buf nextOff
                                      cases absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encV .nil))) with
                                      | halt why => rfl
                                      | call op _ => cases op
                                      | done nSt =>
                                          cases nSt with
                                          | cons st' sn =>
                                              cases sn
                                              exact ih msg st' buf nextOff (hKSh msg trivial)
              | own gkind hearers at_ gIns payload τ =>
                  cases gkind with
                  | coin law =>
                      cases hearers with
                      | nil =>
                          -- Private coin of verifier: passes straight through
                          have hP := hPassV (.own (.coin law) [] at_ gIns payload τ) st (buf, (off, ())) trivial
                          dsimp only [evalIdealVerifierLoop, Handler.run]
                          change Process.answerService serviceKey oracle
                            (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _) = _
                          rw [hP]
                          dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                          congr 1; funext v
                          exact ih v st buf off (hKSh v trivial)
                      | cons h0 hs =>
                          obtain ⟨e, he, hSite, hTy, hCls, hTyped⟩ := hOpSh
                          have hD := hIdealDisc e he; rw [hCls] at hD
                          rcases hD with ⟨_, hPin, sig, hLaw, _, hSigIns⟩ | hNil
                          · have hGInsNil : gIns = [] := by
                              obtain ⟨s, hsLaw, hsIns, _⟩ := hTyped
                              rw [hLaw] at hsLaw
                              cases Option.some.inj hsLaw
                              exact hsIns.symm.trans hSigIns
                            subst hGInsNil
                            cases payload
                            obtain ⟨idxV, eV, encRef, hIdxV, hSiteV, hTyV, hClsV, hEncFind, hConAns⟩ :=
                              ideal_clauses_answer_coin M 0 events (fun k e hk => by simpa using hk) hIV
                                law (h0 :: hs) at_ τ st ⟨e, he, hSite, hTy, hPin, hCls⟩
                            have hToldSite : (⟨at_.path, drawToldKey events idxV⟩ : Occurrence).site =
                                ⟨eV.site.through, drawToldKey events (0 + idxV)⟩ := by
                              simpa using site_told_from_match hSiteV (k := drawToldKey events idxV)
                            have hLayDrop : ∀ coin : M.Val τ,
                                Clause.answer M fnTable rTable lClauses
                                  (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
                                  (buf, (off, ())) = .done ((), (buf, (off, ()))) := fun coin => by
                              have hd := streaming_layout_answer_told_drop M hNoCarry 0 events (fun _ h => h) hSL'
                                idxV eV hIdxV law (h0 :: hs) ⟨at_.path, drawToldKey events idxV⟩
                                (hTyV.symm ▸ coin) hClsV hPin hToldSite buf off
                              subst hTyV; exact hd
                            have hReqUnm : Clause.answer M fnTable rTable lClauses
                                (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                  [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                (buf, (off, ())) =
                                .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                  [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                  fun reply => .done (reply, (buf, (off, ()))) :=
                              clause_answer_unmatched_all M fnTable rTable
                                (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                  [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                (buf, (off, ())) lClauses
                                (streaming_layout_unmatched_closed M 0 events hSL'
                                  (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                    [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ) trivial).2
                            conv =>
                              rhs
                              rw [evalIdealVerifierLoop]
                              dsimp only
                              rw [hEncFind]
                            dsimp only [Handler.run]
                            change Process.answerService serviceKey oracle
                              (((((Stack.handler M fnTable rTable [idealConV', layV']).clause _ _).bind _).mapHalt _).bind _) = _
                            have hClauseEq : (Stack.handler M fnTable rTable [idealConV', layV']).clause
                                (.own (.coin law) (h0 :: hs) at_ [] .nil τ)
                                (.cons st (.cons (buf, (off, ())) .nil)) =
                                .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                    [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ) fun coin =>
                                  (liftLocal (fun why => (why, .cons st (.cons (buf, (off, ())) .nil)))
                                    (encRef.eval M fnTable (.cons coin .nil))).bind fun enc =>
                                      (liftLocal (fun why => (why, .cons st (.cons (buf, (off, ())) .nil)))
                                        (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil))))).map
                                        fun nextSt => (coin, .cons nextSt.single (.cons (buf, (off, ())) .nil)) := by
                              change ((((Layer.handler M fnTable rTable idealConV').over
                                  (Stack.handler M fnTable rTable [layV'])).clause
                                  (.own (.coin law) (h0 :: hs) at_ [] .nil τ)
                                  (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                              dsimp only [Layer.handler, Handler.over, idealConV']
                              rw [hConAns]
                              dsimp only [Handler.answer]
                              have hReqLay : (Stack.handler M fnTable rTable [layV']).clause
                                  (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                    [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                  (.cons (buf, (off, ())) .nil) =
                                  .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                    [idealQueryTy stateTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                    fun reply => .done (reply, .cons (buf, (off, ())) .nil) :=
                                stack1_clause_pass M fnTable rTable layV' _ (buf, (off, ())) hReqUnm
                              rw [hReqLay]
                              dsimp only [Process.map, Process.mapHalt, Process.bind]
                              congr 1; funext coin
                              have hDropLay : (Stack.handler M fnTable rTable [layV']).clause
                                  (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
                                  (.cons (buf, (off, ())) .nil) =
                                  .done ((), .cons (buf, (off, ())) .nil) := by
                                change ((((Layer.handler M fnTable rTable layV').over
                                    (Stack.handler M fnTable rTable [])).clause
                                    (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
                                    ((buf, (off, ())), .nil)).mapHalt _).map _ = _
                                dsimp only [Layer.handler, Handler.over, layV']
                                rw [hLayDrop coin]; rfl
                              change Process.map
                                (fun (out : M.Val τ × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                  (out.1, HList.cons out.2.1 out.2.2))
                                (Process.mapHalt
                                  (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                    (stop.1, HList.cons stop.2.1 stop.2.2))
                                  ((Process.mapHalt
                                    (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                      (stop.1, stop.2.1, stop.2.2))
                                    ((Process.mapHalt
                                      (fun (stop : Stop × HList M.Val (Stack.States [layV'])) =>
                                        (stop.1, st, stop.2))
                                      ((Stack.handler M fnTable rTable [layV']).clause
                                        (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
                                        (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind
                                      fun out =>
                                        (Stack.handler M fnTable rTable [layV']).answer
                                          (Process.map
                                            (fun out =>
                                              ((HList.split [τ] (aloneOut M verifier out)).1.single,
                                                (HList.split [τ] (aloneOut M verifier out)).2.single))
                                            (Process.mapHalt (fun why => (why, st))
                                              ((liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons coin .nil))).bind fun enc =>
                                                Process.map (fun nextSt => aloneIn M verifier (.cons coin nextSt))
                                                  (liftLocal (S := RSig M) id
                                                    (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil))))))))
                                          st out.2)).bind
                                    fun out => Process.done (out.1.1, out.1.2, out.2))) = _
                              rw [hDropLay]
                              change Process.map
                                (fun (out : M.Val τ × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                  (out.1, HList.cons out.2.1 out.2.2))
                                (Process.mapHalt
                                  (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                    (stop.1, HList.cons stop.2.1 stop.2.2))
                                  ((Process.mapHalt
                                    (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                      (stop.1, stop.2.1, stop.2.2))
                                    ((Stack.handler M fnTable rTable [layV']).answer
                                      (Process.map
                                        (fun out =>
                                          ((HList.split [τ] (aloneOut M verifier out)).1.single,
                                            (HList.split [τ] (aloneOut M verifier out)).2.single))
                                        (Process.mapHalt (fun why => (why, st))
                                          ((liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons coin .nil))).bind fun enc =>
                                            Process.map (fun nextSt => aloneIn M verifier (.cons coin nextSt))
                                              (liftLocal (S := RSig M) id
                                                (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil))))))))
                                      st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind
                                    fun out => Process.done (out.1.1, out.1.2, out.2))) =
                                (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                  (encRef.eval M fnTable (.cons coin .nil))).bind fun enc =>
                                  Process.map (fun nextSt => (coin, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                    (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                      (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil)))))
                              cases encRef.eval M fnTable (.cons coin .nil) with
                              | halt why => rfl
                              | call op _ => cases op
                              | done enc =>
                                  cases enc with
                                  | cons encV en =>
                                      cases en
                                      change Process.map
                                        (fun (out : M.Val τ × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                          (out.1, HList.cons out.2.1 out.2.2))
                                        (Process.mapHalt
                                          (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                            (stop.1, HList.cons stop.2.1 stop.2.2))
                                          ((Process.mapHalt
                                            (fun (stop : Stop × M.Val stateTy × HList M.Val (Stack.States [layV'])) =>
                                              (stop.1, stop.2.1, stop.2.2))
                                            ((Stack.handler M fnTable rTable [layV']).answer
                                              (Process.map
                                                (fun out =>
                                                  ((HList.split [τ] (aloneOut M verifier out)).1.single,
                                                    (HList.split [τ] (aloneOut M verifier out)).2.single))
                                                (Process.mapHalt (fun why => (why, st))
                                                  (Process.map (fun nextSt => aloneIn M verifier (.cons coin nextSt))
                                                    (liftLocal (S := RSig M) id
                                                      (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons encV .nil))))))))
                                              st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind
                                            fun out => Process.done (out.1.1, out.1.2, out.2))) =
                                        Process.map (fun nextSt => (coin, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                          (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                            (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons encV .nil)))))
                                      cases absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons encV .nil))) with
                                      | halt why => rfl
                                      | call op _ => cases op
                                      | done nSt =>
                                          cases nSt with
                                          | cons st' sn =>
                                              cases sn
                                              change Process.done
                                                ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier (.cons coin (.cons st' .nil))))).1.single,
                                                  HList.cons ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier (.cons coin (.cons st' .nil))))).2.single)
                                                    (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)) =
                                                Process.done (coin, HList.cons st' (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))
                                              rw [aloneOut_aloneIn]; rfl
                            rw [hClauseEq]
                            dsimp only [Process.bind, Process.mapHalt]
                            unfold Process.answerService
                            rw [ite_eq_left rfl, hOracleRo st (drawLabel at_.site) τ]
                            let coin := ro st (drawLabel at_.site) τ
                            change Process.answerService serviceKey oracle
                              ((Process.mapHalt Prod.fst
                                (((liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                  (encRef.eval M fnTable (.cons coin .nil))).bind fun enc =>
                                    (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                      (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil))))).map
                                      fun nextSt => (coin, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind _)).bind _) =
                              (liftLocal id (encRef.eval M fnTable (.cons coin .nil))).bind fun enc =>
                                (liftLocal id (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons enc.single .nil))))).bind
                                  fun nextSt => evalIdealVerifierLoop M a suite layout absRef serviceKey prover
                                    (finishGuardKey events) oracle ro (k coin) nextSt.single buf off
                            cases encRef.eval M fnTable (.cons coin .nil) with
                            | halt why => rfl
                            | call op _ => cases op
                            | done enc =>
                                cases enc with
                                | cons encV en =>
                                    cases en
                                    change Process.answerService serviceKey oracle
                                      ((Process.mapHalt Prod.fst
                                        ((((liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                          (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons encV .nil))))).map
                                          fun nextSt => (coin, HList.cons nextSt.single (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind _))).bind _) =
                                      (liftLocal id (absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons encV .nil))))).bind
                                        fun nextSt => evalIdealVerifierLoop M a suite layout absRef serviceKey prover
                                          (finishGuardKey events) oracle ro (k coin) nextSt.single buf off
                                    cases absRef.eval M fnTable (.cons st (.cons (drawLabel at_.site) (.cons encV .nil))) with
                                    | halt why => rfl
                                    | call op _ => cases op
                                    | done nSt =>
                                        cases nSt with
                                        | cons st' sn =>
                                            cases sn
                                            exact ih coin st' buf off (hKSh coin trivial)
                          · cases hNil
                  | request svc =>
                      have hP := hPassV (.own (.request svc) hearers at_ gIns payload τ) st (buf, (off, ())) trivial
                      dsimp only [evalIdealVerifierLoop, Handler.run]
                      change Process.answerService serviceKey oracle
                        (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _) = _
                      rw [hP]
                      dsimp only [Process.bind, Process.mapHalt]
                      unfold Process.answerService
                      by_cases hs : svc = serviceKey
                      · rw [ite_eq_left hs]
                        conv =>
                          rhs
                          rw [evalIdealVerifierLoop]
                          dsimp only
                          rw [ite_eq_left hs]
                        cases oracle gIns payload τ with
                        | some v => dsimp only; exact ih v st buf off (hKSh v trivial)
                        | none => dsimp only; congr 1; funext v; exact ih v st buf off (hKSh v trivial)
                      · rw [ite_eq_right hs]
                        conv =>
                          rhs
                          rw [evalIdealVerifierLoop]
                          dsimp only
                          rw [ite_eq_right hs]
                        congr 1; funext v; exact ih v st buf off (hKSh v trivial)
              | «begin» at_ =>
                  have hP := hPassV (.begin at_) st (buf, (off, ())) trivial
                  dsimp only [evalIdealVerifierLoop, Handler.run]
                  change Process.answerService serviceKey oracle
                    (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _) = _
                  rw [hP]
                  dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                  congr 1; funext n; exact ih n st buf off (hKSh n trivial)
              | settle at_ =>
                  have hP := hPassV (.settle at_) st (buf, (off, ())) trivial
                  dsimp only [evalIdealVerifierLoop, Handler.run]
                  change Process.answerService serviceKey oracle
                    (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _) = _
                  rw [hP]
                  dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                  congr 1; funext u; exact ih u st buf off (hKSh u trivial)

/-- Exact ideal-RO linkage theorem (`SCHEMES-AND-FIAT-SHAMIR.md` §9.2):
for any non-carry streaming `deployIdeal` verifier without retry, answering `.own (.request serviceKey)`
with any oracle extending a total random oracle `ro` yields the direct state-machine interpreter
`evalIdealVerifierLoop` over the bare verifier role program `roleMeaning`, completely eliminating
`Layer`, `Stack`, `Handler`, and `Clause`. -/
theorem deployIdeal_link (enc : VocabEncoder V) (serviceKey : Key)
    {a : Admitted V} {declaration : Declaration} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    {layout : Layout} {dIdeal : Deployed V}
    (hDep : deployIdeal enc serviceKey a declaration = .ok dIdeal)
    (hCon : declaration.construction = .derived suite sessionTag)
    (hLay : declaration.layout = some layout)
    (hNoRetry : declaration.retry = none)
    (hNoCarry : layout.carry = []) (hNoRec : layout.recover = [])
    (prover verifier : Role) (hRoles : dIdeal.roles = some (prover, verifier))
    (ins : HList (RV M verifier) dIdeal.entry.ins) (hIns : ins.All (RV.Valid M verifier)) :
    ∃ (stateTy suiteUnitTy unitTy : V.Ty)
      (startRef : TypedFnRef V a.program.headers.fns [bytesTy] [stateTy])
      (absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy])
      (st0 : M.Val stateTy)
      (hTakes : Stack.Takes (dIdeal.stack verifier) = [.seq unitTy none])
      (hGives : Stack.Gives (dIdeal.stack verifier) = []),
      findSuiteStart a suite = some ⟨stateTy, startRef⟩ ∧
      findSuiteAbsorb a suite stateTy = some ⟨suiteUnitTy, absRef⟩ ∧
      ∀ (proof : List (M.Val unitTy))
        (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
        (ro : M.Val stateTy → List Nat → (τ : V.Ty) → M.Val τ),
        (∀ st lbl τ, oracle [idealQueryTy stateTy] (.cons (st, (lbl, ())) .nil) τ = some (ro st lbl τ)) →
        (Process.answerService serviceKey oracle
          (dIdeal.run M verifier ins (cast (congrArg (HList M.Val) hTakes.symm) (.cons proof .nil)))).map
          (fun out => (out.1, cast (congrArg (HList M.Val) hGives) out.2)) =
          evalIdealVerifierLoop M a suite layout absRef serviceKey prover
            (finishGuardKey (dIdeal.entry.shape.events [] id)) oracle ro
            (roleMeaning M dIdeal.admitted.program dIdeal.callee verifier [] ins) st0 proof 0 := by
  unfold deployIdeal at hDep
  split at hDep
  · cases hDep
  · rename_i foundPair hFound
    dsimp only at hDep
    split at hDep
    · cases hDep
    · rw [hCon] at hDep; dsimp only at hDep
      cases hPV : proverAndVerifier foundPair.1 declaration with
      | none => rw [hPV] at hDep; cases hDep
      | some pv =>
          rw [hPV] at hDep; dsimp only at hDep
          split at hDep
          · cases hDep
          · rename_i hNe
            rw [hLay] at hDep; dsimp only at hDep
            cases hSt : findSuiteStart a suite with
            | none => rw [hSt] at hDep; cases hDep
            | some stPair =>
                rw [hSt] at hDep; dsimp only at hDep
                cases hAb : findSuiteAbsorb a suite stPair.1 with
                | none => rw [hAb] at hDep; cases hDep
                | some absPair =>
                    rw [hAb] at hDep; dsimp only at hDep
                    cases hSess : resolveSessionBytes enc a declaration sessionTag with
                    | error _ => rw [hSess] at hDep; cases hDep
                    | ok sess =>
                        rw [hSess] at hDep; dsimp only [bind, Except.bind] at hDep
                        cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2 pv.1 pv.2
                            (.inr rfl) foundPair.1.ins declaration.key with
                        | error _ => rw [hSV] at hDep; cases hDep
                        | ok stmtV =>
                            rw [hSV] at hDep; dsimp only [bind, Except.bind] at hDep
                            cases hIV : buildIdealVerifierClauses a suite stPair.1 absPair.1
                                absPair.2 serviceKey pv.1 pv.2 declaration.key
                                (foundPair.1.shape.events [] id) with
                            | error _ => rw [hIV] at hDep; cases hDep
                            | ok idealVClauses =>
                                rw [hIV] at hDep; dsimp only [bind, Except.bind] at hDep
                                cases hLayB : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                    declaration.key (foundPair.1.shape.events [] id) with
                                | error _ => rw [hLayB] at hDep; cases hDep
                                | ok lays =>
                                    rw [hLayB] at hDep; cases hDep
                                    have hRolesEq : proverAndVerifier foundPair.1 declaration =
                                        some (prover, verifier) := by
                                      simpa [Deployed.roles, Deployed.entry, hFound] using hRoles
                                    rw [hPV] at hRolesEq; cases hRolesEq
                                    unfold buildLayoutLayers at hLayB
                                    cases hUnit : findLayoutUnit a layout.module with
                                    | none => rw [hUnit] at hLayB; cases hLayB
                                    | some uPair =>
                                        rw [hUnit] at hLayB; dsimp only at hLayB
                                        rw [show layout.recover.isEmpty = true by simp [hNoRec],
                                          ite_eq_left rfl] at hLayB
                                        cases hStr : buildStreamingLayoutClauses a layout uPair.1
                                            uPair.2.down prover verifier declaration.key
                                            (foundPair.1.shape.events [] id) with
                                        | error _ => rw [hStr] at hLayB; cases hLayB
                                        | ok cs =>
                                            rw [hStr] at hLayB; cases hLayB
                                            dsimp only [Deployed.entry, Deployed.retry] at *
                                            have hEntryF : ((a.program.findProtocol declaration.entry).get
                                                (by rw [hFound]; rfl)).1 = foundPair.1 := by simp [hFound]
                                            have hInsF := insRV_cast_valid M hEntryF ins hIns
                                            obtain ⟨st0, hSt0Done, _⟩ := constructionStart_done M a
                                              sess.1 sess.2 stPair.2 absPair.2 stmtV
                                              (heldValues M verifier (cast (congrArg (fun hdr => HList (RV M verifier) hdr.ins) hEntryF) ins))
                                              (heldValues_valid M verifier _ hInsF)
                                            let idealConV0 : Layer V a.program.headers verifier foundPair.1.ins :=
                                              { line := .construction, state := stPair.1,
                                                takes := [], gives := [], clauses := idealVClauses,
                                                again := restoreAgain stPair.1,
                                                start := constructionStart sess.1 sess.2 stPair.2 absPair.2 stmtV,
                                                finish := emptyFinish stPair.1 }
                                            let layV0 : Layer V a.program.headers verifier foundPair.1.ins :=
                                              { line := .layout, state := streamStateTy uPair.1,
                                                takes := [.seq uPair.1 none], gives := [], clauses := cs.2,
                                                again := restoreAgain (streamStateTy uPair.1),
                                                start := layoutVStart uPair.1,
                                                finish := layoutVFinish uPair.1 uPair.2.down
                                                  (finishGuardKey (foundPair.1.shape.events [] id)) }
                                            have hTakes : Stack.Takes (if hV : verifier = verifier then
                                                hV ▸ hEntryF ▸ [idealConV0, layV0] else []) = [.seq uPair.1 none] := by
                                              rw [dite_eq_left rfl, stack_takes_cast_hdr hEntryF]; rfl
                                            have hGives : Stack.Gives (if hV : verifier = verifier then
                                                hV ▸ hEntryF ▸ [idealConV0, layV0] else []) = [] := by
                                              rw [dite_eq_left rfl, stack_gives_cast_hdr hEntryF]; rfl
                                            refine ⟨stPair.1, absPair.1, uPair.1, stPair.2, absPair.2, st0,
                                              hTakes, hGives, rfl, hAb, fun proof oracle ro hOR => ?_⟩
                                            have hBridge : ∀ (hdr : ProtocolHeader V) (hE : hdr = foundPair.1)
                                                (callee : Member a.program.headers.protocols hdr)
                                                (ins' : HList (RV M verifier) hdr.ins)
                                                (hStart' : (constructionStart sess.1 sess.2 stPair.2 absPair.2 stmtV).denote
                                                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                                  (Env.positional (heldValues M verifier (cast (congrArg (fun h => HList (RV M verifier) h.ins) hE) ins'))) = .done (.cons st0 .nil))
                                                (hT' : Stack.Takes (hE ▸ [idealConV0, layV0]) = [.seq uPair.1 none])
                                                (hG' : Stack.Gives (hE ▸ [idealConV0, layV0]) = []),
                                                (Process.answerService serviceKey oracle
                                                  (runStack a M callee none verifier
                                                    (hE ▸ [idealConV0, layV0])
                                                    ins' (cast (congrArg (HList M.Val) hT'.symm) (.cons proof .nil)))).map
                                                  (fun out => (out.1, cast (congrArg (HList M.Val) hG') out.2)) =
                                                  evalIdealVerifierLoop M a suite layout absPair.2 serviceKey prover
                                                    (finishGuardKey (hdr.shape.events [] id)) oracle ro
                                                    (roleMeaning M a.program callee verifier [] ins') st0 proof 0 := by
                                              intro hdr hE callee ins' hStart' hT' hG'
                                              subst hE
                                              dsimp only at hStart'
                                              simp only [cast_eq] at hStart'
                                              unfold runStack
                                              change Process.map (fun (out : HList (RV M verifier) foundPair.1.outs × HList M.Val (Stack.Gives [idealConV0, layV0])) => (out.1, cast (congrArg (HList M.Val) hG') out.2))
                                                (Process.answerService serviceKey oracle
                                                  ((Stack.start M (Defs.fnTable M a.program.defs) [idealConV0, layV0]
                                                    ins' (.cons proof .nil)).bind _)) = _
                                              have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                                                  [idealConV0, layV0]
                                                  ins' (.cons proof .nil) =
                                                  .done (.cons st0 (.cons (proof, ((0 : Nat), ())) .nil)) := by
                                                change ((liftLocal id (idealConV0.start.denote
                                                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                                  (Env.positional (heldValues M verifier ins')))).bind fun f₁ =>
                                                    ((liftLocal id ((layoutVStart uPair.1).denote
                                                      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                                      (Env.positional (.cons proof (heldValues M verifier ins'))))).bind fun f₂ =>
                                                        (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                                                          HList.cons f₁.single others) = _
                                                rw [hStart', liftLocal_done]
                                                dsimp only [Process.bind, HList.single]
                                                rw [layoutVStart_denote]
                                                rfl
                                              rw [hStV]
                                              dsimp only [Process.bind]
                                              rw [← answerService_map]
                                              have hLoop := ideal_verifier_loop_eq M hNoCarry hNe
                                                idealConV0 layV0
                                                rfl rfl rfl rfl rfl rfl hIV ⟨cs.1, hStr⟩ oracle ro hOR
                                                (roleMeaning M a.program callee verifier [] ins') st0 proof 0
                                                (roleMeaning_matchesShape M a.program callee verifier [] ins')
                                              simpa [Process.map_id', Process.map_bind, Process.map_map] using hLoop
                                            let dIdeal : Deployed V :=
                                              { admitted := a, declaration := declaration,
                                                found := (by rw [hFound]; rfl),
                                                stack := fun r =>
                                                  if hV : r = verifier then hV ▸ hEntryF ▸ [idealConV0, layV0]
                                                  else [] }
                                            have hStackVEq : dIdeal.stack verifier = hEntryF ▸ [idealConV0, layV0] := by
                                              dsimp only [dIdeal]; rw [dite_eq_left rfl]
                                            have hT2 : Stack.Takes (hEntryF ▸ [idealConV0, layV0]) = [.seq uPair.1 none] := by
                                              rw [stack_takes_cast_hdr hEntryF]; rfl
                                            have hG2 : Stack.Gives (hEntryF ▸ [idealConV0, layV0]) = [] := by
                                              rw [stack_gives_cast_hdr hEntryF]; rfl
                                            exact (ideal_deployed_run_congr M (d := dIdeal) rfl hNoRetry hStackVEq
                                              ((cast_heq _ _).trans (cast_heq _ _).symm)
                                              (hG₁ := hGives) (hG₂ := hG2) serviceKey oracle).trans
                                              (hBridge _ hEntryF dIdeal.callee ins hSt0Done hT2 hG2)

end IdealLink

end Zkc.Core

