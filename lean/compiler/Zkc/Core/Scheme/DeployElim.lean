module

public import Zkc.Core.Scheme.Deploy
public import Zkc.Core.Scheme.LayerLemmas
public import Zkc.Core.Scheme.RoleLemmas

@[expose] public section

/-!
Elimination lemmas (`deploy_ok_elim`, `deployIdeal_ok_elim`, `buildLayoutLayers_ok_elim`),
shared stack/lookup helpers, and structural theorems (`deploy_keeps`, `deploy_findsRoles`,
`deploy_matches`, `deploy_scoped`, `deployIdeal_scoped`, `deploy_wellNestedRetry`,
`deployIdeal_wellNestedRetry`, `deploy_fresh`, `deployIdeal_fresh`).
-/

namespace Zkc.Core

open LayerBuild

/-! ## Generic lookup, cast, and stack-composition helpers -/

section Helpers

variable {V : Vocabulary}

/-- Eliminate simultaneous `ProtocolHeader` and `Role` equality transports on a layer stack. -/
theorem cast_layer_stack_elim {hs : Headers V}
    {hdr₁ hdr₂ : ProtocolHeader V} (hHdr : hdr₁ = hdr₂)
    {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins))
    (P : ∀ (hdr : ProtocolHeader V) (r : Role), List (Layer V hs r hdr.ins) → Prop)
    (h : P hdr₂ r₂ layers) :
    P hdr₁ r₁ (hr ▸ hHdr ▸ layers) := by
  subst hHdr; subst hr; exact h

/-- Eliminate a `ProtocolHeader` equality transport on a layer stack. -/
theorem cast_hdr_stack_elim {hs : Headers V}
    {hdr₁ hdr₂ : ProtocolHeader V} (hHdr : hdr₁ = hdr₂) {r : Role}
    (layers : List (Layer V hs r hdr₂.ins))
    (P : ∀ (hdr : ProtocolHeader V), List (Layer V hs r hdr.ins) → Prop)
    (h : P hdr₂ layers) :
    P hdr₁ (hHdr ▸ layers) := by
  subst hHdr; exact h

theorem stack_takes_cast {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins)) :
    Stack.Takes (hr ▸ hHdr ▸ layers) = Stack.Takes layers :=
  cast_layer_stack_elim hHdr hr layers (fun _ _ ls => Stack.Takes ls = Stack.Takes layers) rfl

theorem stack_takes_cast_hdr {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r : Role}
    (layers : List (Layer V hs r hdr₂.ins)) :
    Stack.Takes (hHdr ▸ layers) = Stack.Takes layers :=
  cast_layer_stack_elim hHdr rfl layers (fun _ _ ls => Stack.Takes ls = Stack.Takes layers) rfl

theorem stack_gives_cast_hdr {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r : Role}
    (layers : List (Layer V hs r hdr₂.ins)) :
    Stack.Gives (hHdr ▸ layers) = Stack.Gives layers :=
  cast_layer_stack_elim hHdr rfl layers (fun _ _ ls => Stack.Gives ls = Stack.Gives layers) rfl

theorem stack_gives_cast {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins)) :
    Stack.Gives (hr ▸ hHdr ▸ layers) = Stack.Gives layers :=
  cast_layer_stack_elim hHdr hr layers (fun _ _ ls => Stack.Gives ls = Stack.Gives layers) rfl

/-- `findSlotMember` returning `some x` witnesses a member `(slot, defKey) ∈ m.members`. -/
theorem findSlotMember_some {α : Type} {m : ModuleRef} {slot : Key} {pick : Key → Option α}
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
          dsimp only at h
          split at h
          · split at h
            · split at h
              · cases h; rfl
              · cases h
            · cases h
          · cases h

theorem findSuiteEncode_some {a : Admitted V} {suite : ModuleRef} {unitTy τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]}
    (h : findSuiteEncode a suite unitTy τ = some ref) :
    ∃ defKey, (SuiteSlot.encode, defKey) ∈ suite.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

theorem findSuiteDerive_some {a : Admitted V} {suite : ModuleRef} {stateTy : V.Ty}
    {drawIns : List V.Ty} {τ : V.Ty}
    {ref : TypedFnRef V a.program.headers.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]}
    (h : findSuiteDerive a suite stateTy drawIns τ = some ref) :
    ∃ defKey, (SuiteSlot.derive, defKey) ∈ suite.members ∧
      a.program.find defKey = some (.fn ref.member) := by
  obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
  exact ⟨defKey, hIn, findTypedFnRef_some hRef⟩

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

theorem hlist_all_cast {T : Type} {F : T → Type} {P : ∀ t, F t → Prop}
    {as bs : List T} (h : as = bs) {xs : HList F as} (hx : xs.All P) :
    (cast (congrArg (HList F) h) xs).All P := by
  subst h; exact hx

theorem hlist_append_nil {T : Type} {F : T → Type} {bs : List T} (ys : HList F bs) :
    HList.append .nil ys = ys := rfl

theorem hlist_append_cons {T : Type} {F : T → Type} {a : T} {as bs : List T}
    (x : F a) (xs : HList F as) (ys : HList F bs) :
    HList.append (.cons x xs) ys = .cons x (HList.append xs ys) := rfl

theorem hlist_all_append {T : Type} {F : T → Type} {P : ∀ t, F t → Prop} :
    ∀ {as bs : List T} {xs : HList F as} {ys : HList F bs},
      xs.All P → ys.All P → (xs.append ys).All P
  | [], _, .nil, _, _, hy => hy
  | _ :: _, _, .cons _ _, _, hx, hy => ⟨hx.1, hlist_all_append hx.2 hy⟩

theorem hlist_split_all {T : Type} {F : T → Type} {P : ∀ t, F t → Prop} :
    ∀ (as : List T) {bs : List T} (vs : HList F (as ++ bs)),
      vs.All P → (HList.split as vs).1.All P ∧ (HList.split as vs).2.All P
  | [], _, _, hv => ⟨trivial, hv⟩
  | _ :: as, _, .cons _ rest, hv =>
      let ⟨h1, h2⟩ := hlist_split_all as rest hv.2
      ⟨⟨hv.1, h1⟩, h2⟩

theorem allows_valid (M : Model V) {kind : GivenKind V} {ins : List V.Ty}
    {payload : HList M.Val ins} {τ : V.Ty} {v : M.Val τ}
    (h : Allows M kind ins payload τ v) : M.Valid τ v := by
  cases kind with
  | coin _ => exact h.1
  | request _ => exact h

theorem hideAll_valid (M : Model V) (r : Role) :
    ∀ {ins : List (LTy V)} (vs : HList (LVal M) ins),
      vs.All (fun a v => M.Valid a.ty v) → (hideAll M r vs).All (RV.Valid M r)
  | [], .nil, _ => trivial
  | a :: rest, .cons v vs, hv => by
      refine ⟨fun hIn => ?_, hideAll_valid M r vs hv.2⟩
      show M.Valid a.ty (cast _ (hide M r a v))
      have hrv : cast (by simp [RV, hIn]) (hide M r a v) = v := reveal_hide M hIn v
      rw [hrv]
      exact hv.1

theorem valid_seq_append (M : Model V) {unitTy : V.Ty}
    {xs ys : List (M.Val unitTy)}
    (hx : M.Valid (.seq unitTy none) xs) (hy : M.Valid (.seq unitTy none) ys) :
    M.Valid (.seq unitTy none) (xs ++ ys) := by
  refine ⟨fun u hu => ?_, (fun _ h => nomatch h)⟩
  rcases List.mem_append.mp hu with h | h
  · exact hx.1 u h
  · exact hy.1 u h

theorem tys_getAt_valid (M : Model V) :
    ∀ (ts : Tys V.TypeKey) {τ : V.Ty} (pos : Member ts.toList τ) (st : ts.Val M.toCarriers),
      Tys.Valid M.toCarriers ts st → M.Valid τ (Tys.getAt M ts pos st)
  | .nil, _, pos, _, _ => nomatch pos
  | .cons _ _, _, .head, (_, _), hv => hv.1
  | .cons _ rest, _, .tail p, (_, rs), hv => tys_getAt_valid M rest p rs hv.2

theorem tys_toHList_valid (M : Model V) :
    ∀ (ts : Tys V.TypeKey) (st : ts.Val M.toCarriers),
      Tys.Valid M.toCarriers ts st → (Tys.toHList M ts st).All M.Valid
  | .nil, (), _ => trivial
  | .cons _ rest, (_, rs), hv => ⟨hv.1, tys_toHList_valid M rest rs hv.2⟩

/-- Standalone version of `Deployed.run` parameterized directly by `(hdr, callee, retry, layers)`. -/
def runStack (a : Admitted V) (M : Model V) {hdr : ProtocolHeader V}
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

theorem deployed_run_eq_runStack (d : Deployed V) (M : Model V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    d.run M r ins taken = runStack d.admitted M d.callee d.retry r (d.stack r) ins taken :=
  rfl

theorem stack_handler_again_cons (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    {r : Role} {ins : List (LTy V)}
    (l : Layer V hs r ins) (rest : List (Layer V hs r ins)) (i : Nat)
    (e : M.Val l.state) (es : HList M.Val (Stack.States rest))
    (t : M.Val l.state) (ts : HList M.Val (Stack.States rest)) :
    (Stack.handler M fnTable rTable (l :: rest)).again i (.cons e es) (.cons t ts) =
      (((Layer.handler M fnTable rTable l).over (Stack.handler M fnTable rTable rest)).again
        i (e, es) (t, ts)).map fun next => .cons next.1 next.2 := rfl

theorem stack_handler_validSafe_all (M : Model V) {hs : Headers V}
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

theorem stack_start_validSafe (M : Model V) {hs : Headers V}
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

theorem stack_finish_validSafe (M : Model V) {hs : Headers V}
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

theorem local_every_true {A : Type} :
    ∀ (p : Local A), p.Every (fun _ _ => True) (fun _ => True) (fun _ => True)
  | .done _ => trivial
  | .halt _ => trivial
  | .call op _ => nomatch op

/-- `Stack.start` never emits any role effect (it is built purely from `liftLocal`). -/
theorem stack_start_noEffects (M : Model V) {hs : Headers V}
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
theorem stack_finish_noEffects (M : Model V) {hs : Headers V}
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

theorem layer_again_restore_valid (M : Model V) {hs : Headers V}
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

theorem layer_again_attempt_valid (M : Model V) {hs : Headers V}
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

/-! ## Structured elimination lemmas for `buildLayoutLayers`, `deploy`, and `deployIdeal` -/

section Elimination

variable {V : Vocabulary}

/-- Structured witness for a streaming `buildLayoutLayers` result. -/
structure BuildLayoutStreaming (a : Admitted V) (entry : ProtocolHeader V) (layout : Layout)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V)) where
  hSites : checkLayoutSites entry events prover verifier layout = true
  unitTy : V.Ty
  hfree : Ty.isLinear V unitTy = false
  hUnit : findLayoutUnit a layout.module = some ⟨unitTy, ⟨hfree⟩⟩
  hEmpty : layout.recover.isEmpty = true
  pClauses : List (Clause V a.program.headers prover (.seq unitTy none))
  vClauses : List (Clause V a.program.headers verifier (streamStateTy unitTy))
  hStr : buildStreamingLayoutClauses a layout unitTy hfree prover verifier declKey events =
    .ok (pClauses, vClauses)

abbrev BuildLayoutStreaming.layP {a : Admitted V} {entry : ProtocolHeader V} {layout : Layout}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    (w : BuildLayoutStreaming a entry layout prover verifier declKey events) :
    Layer V a.program.headers prover entry.ins :=
  { line := .layout
    state := .seq w.unitTy none
    takes := []
    gives := [.seq w.unitTy none]
    clauses := w.pClauses
    again := restoreAgain (.seq w.unitTy none)
    start := layoutPStart w.unitTy
    finish := identityFinish (.seq w.unitTy none) }

abbrev BuildLayoutStreaming.layV {a : Admitted V} {entry : ProtocolHeader V} {layout : Layout}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    (w : BuildLayoutStreaming a entry layout prover verifier declKey events) :
    Layer V a.program.headers verifier entry.ins :=
  { line := .layout
    state := streamStateTy w.unitTy
    takes := [.seq w.unitTy none]
    gives := []
    clauses := w.vClauses
    again := restoreAgain (streamStateTy w.unitTy)
    start := layoutVStart w.unitTy
    finish := layoutVFinish w.unitTy w.hfree (finishGuardKey events) }

/-- Structured witness for a compact `buildLayoutLayers` result. -/
structure BuildLayoutCompact (a : Admitted V) (entry : ProtocolHeader V) (layout : Layout)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V)) where
  hSites : checkLayoutSites entry events prover verifier layout = true
  unitTy : V.Ty
  hfree : Ty.isLinear V unitTy = false
  hUnit : findLayoutUnit a layout.module = some ⟨unitTy, ⟨hfree⟩⟩
  hNonEmpty : layout.recover.isEmpty = false

/-- Structured witness for a successful `buildLayoutLayers` call. -/
inductive BuildLayoutOk (a : Admitted V) (entry : ProtocolHeader V) (layout : Layout)
    (prover verifier : Role) (declKey : Key) (events : List (ShapeEvent V))
    (layP : Layer V a.program.headers prover entry.ins)
    (layV : Layer V a.program.headers verifier entry.ins) where
  | streaming (w : BuildLayoutStreaming a entry layout prover verifier declKey events)
      (hLayP : layP = w.layP) (hLayV : layV = w.layV)
  | compact (w : BuildLayoutCompact a entry layout prover verifier declKey events)
      (hComp : buildCompactLayoutLayers a entry layout w.unitTy w.hfree prover verifier declKey events =
        .ok (layP, layV))

def buildLayoutLayers_ok_elim {a : Admitted V} {entry : ProtocolHeader V} {layout : Layout}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins}
    (h : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    BuildLayoutOk a entry layout prover verifier declKey events layP layV := by
  unfold buildLayoutLayers at h
  cases hSites : checkLayoutSites entry events prover verifier layout with
  | false => rw [hSites] at h; cases h
  | true =>
      rw [hSites] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hUnit : findLayoutUnit a layout.module with
      | none => rw [hUnit] at h; cases h
      | some uPair =>
          rw [hUnit] at h; dsimp only at h
          cases hEmp : layout.recover.isEmpty with
          | true =>
              rw [hEmp] at h; simp only [↓reduceIte] at h
              cases hStr : buildStreamingLayoutClauses a layout uPair.1 uPair.2.down prover verifier
                  declKey events with
              | error _ => rw [hStr] at h; cases h
              | ok cs =>
                  rw [hStr] at h
                  let w : BuildLayoutStreaming a entry layout prover verifier declKey events :=
                    ⟨hSites, uPair.1, uPair.2.down, hUnit, hEmp, cs.1, cs.2, hStr⟩
                  have hEq : (w.layP, w.layV) = (layP, layV) := Except.ok.inj h
                  exact .streaming w (Prod.mk.inj hEq).1.symm (Prod.mk.inj hEq).2.symm
          | false =>
              rw [hEmp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
              exact .compact ⟨hSites, uPair.1, uPair.2.down, hUnit, hEmp⟩ h

/-- Witness for an interactive `deploy` result. -/
structure DeployInteractive (a : Admitted V) (declaration : Declaration) where
  foundPair : (hdr : ProtocolHeader V) × Member a.program.headers.protocols hdr
  hFound : a.program.findProtocol declaration.entry = some foundPair
  hSupp : checkDeclarationSupported foundPair.1 declaration = true
  hScope : checkScope foundPair.1 declaration = true
  hCon : declaration.construction = .interactive

abbrev DeployInteractive.toDeployed {a : Admitted V} {declaration : Declaration}
    (w : DeployInteractive a declaration) : Deployed V :=
  { admitted := a
    declaration := declaration
    found := by rw [w.hFound]; rfl
    stack := fun _ => [] }

/-- Witness for an authored `deploy` result. -/
structure DeployAuthored (a : Admitted V) (declaration : Declaration) where
  foundPair : (hdr : ProtocolHeader V) × Member a.program.headers.protocols hdr
  hFound : a.program.findProtocol declaration.entry = some foundPair
  hSupp : checkDeclarationSupported foundPair.1 declaration = true
  hScope : checkScope foundPair.1 declaration = true
  hCon : declaration.construction = .authored
  prover : Role
  verifier : Role
  hPV : proverAndVerifier foundPair.1 declaration = some (prover, verifier)
  hNe : prover ≠ verifier
  sClauses : List (Clause V a.program.headers prover .nat)
  hAuth : checkAuthoredEvents a prover verifier declaration.samples declaration.key
    (foundPair.1.shape.events [] id) = .ok sClauses
  layout : Layout
  hLayOpt : declaration.layout = some layout
  layP : Layer V a.program.headers prover foundPair.1.ins
  layV : Layer V a.program.headers verifier foundPair.1.ins
  hLay : buildLayoutLayers a foundPair.1 layout prover verifier declaration.key
    (foundPair.1.shape.events [] id) = .ok (layP, layV)

abbrev DeployAuthored.toDeployed {a : Admitted V} {declaration : Declaration}
    (w : DeployAuthored a declaration) : Deployed V :=
  let hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [w.hFound]; rfl
  let hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = w.foundPair.1 := by
    simp [w.hFound]
  let proverStack : List (Layer V a.program.headers w.prover w.foundPair.1.ins) :=
    match declaration.samples with
    | none => [w.layP]
    | some _ =>
        [{ line := .samples, state := .nat, takes := [], gives := [],
           clauses := w.sClauses, again := attemptNumAgain,
           start := samplesStart, finish := emptyFinish .nat }, w.layP]
  { admitted := a
    declaration := declaration
    found := hIsSome
    stack := fun r =>
      if hP : r = w.prover then hP ▸ hEntryEq ▸ proverStack
      else if hV : r = w.verifier then hV ▸ hEntryEq ▸ [w.layV]
      else [] }

/-- Witness for a derived `deploy` result. -/
structure DeployDerived (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration) where
  foundPair : (hdr : ProtocolHeader V) × Member a.program.headers.protocols hdr
  hFound : a.program.findProtocol declaration.entry = some foundPair
  hSupp : checkDeclarationSupported foundPair.1 declaration = true
  hScope : checkScope foundPair.1 declaration = true
  suite : ModuleRef
  sessionTag : Option (List Nat)
  hCon : declaration.construction = .derived suite sessionTag
  prover : Role
  verifier : Role
  hPV : proverAndVerifier foundPair.1 declaration = some (prover, verifier)
  hNe : prover ≠ verifier
  layout : Layout
  hLayOpt : declaration.layout = some layout
  stateTy : V.Ty
  startRef : TypedFnRef V a.program.headers.fns [bytesTy] [stateTy]
  hStart : findSuiteStart a suite = some ⟨stateTy, startRef⟩
  suiteUnitTy : V.Ty
  absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]
  hAbs : findSuiteAbsorb a suite stateTy = some ⟨suiteUnitTy, absorbRef⟩
  sessBytes : List Nat
  hSessBytes : ∀ b, b ∈ sessBytes → b < 256
  hSess : resolveSessionBytes enc a declaration sessionTag = .ok ⟨sessBytes, hSessBytes⟩
  stmtP : List (StmtAbsorbItem V a.program.headers.fns suiteUnitTy
    (Ctx.positional (held prover foundPair.1.ins)))
  hSP : buildStmtAbsorbItems a suite suiteUnitTy prover prover verifier (.inl rfl)
    foundPair.1.ins declaration.key = .ok stmtP
  stmtV : List (StmtAbsorbItem V a.program.headers.fns suiteUnitTy
    (Ctx.positional (held verifier foundPair.1.ins)))
  hSV : buildStmtAbsorbItems a suite suiteUnitTy verifier prover verifier (.inr rfl)
    foundPair.1.ins declaration.key = .ok stmtV
  cPClauses : List (Clause V a.program.headers prover stateTy)
  cVClauses : List (Clause V a.program.headers verifier stateTy)
  sClauses : List (Clause V a.program.headers prover .nat)
  hCC : buildConstructionClauses a suite stateTy suiteUnitTy absorbRef prover verifier
    declaration.samples declaration.key (foundPair.1.shape.events [] id)
    (foundPair.1.shape.eventsWithAbsorb prover verifier [] id false) =
    .ok (cPClauses, cVClauses, sClauses)
  layP : Layer V a.program.headers prover foundPair.1.ins
  layV : Layer V a.program.headers verifier foundPair.1.ins
  hLay : buildLayoutLayers a foundPair.1 layout prover verifier declaration.key
    (foundPair.1.shape.events [] id) = .ok (layP, layV)

abbrev DeployDerived.toDeployed {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) : Deployed V :=
  let hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [w.hFound]; rfl
  let hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = w.foundPair.1 := by
    simp [w.hFound]
  let conP : Layer V a.program.headers w.prover w.foundPair.1.ins := {
    line := .construction, state := w.stateTy, takes := [], gives := [],
    clauses := w.cPClauses, again := restoreAgain w.stateTy,
    start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP,
    finish := emptyFinish w.stateTy
  }
  let conV : Layer V a.program.headers w.verifier w.foundPair.1.ins := {
    line := .construction, state := w.stateTy, takes := [], gives := [],
    clauses := w.cVClauses, again := restoreAgain w.stateTy,
    start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtV,
    finish := emptyFinish w.stateTy
  }
  let proverStack : List (Layer V a.program.headers w.prover w.foundPair.1.ins) :=
    match declaration.samples with
    | none => [conP, w.layP]
    | some _ =>
        [{ line := .samples, state := .nat, takes := [], gives := [],
           clauses := w.sClauses, again := attemptNumAgain,
           start := samplesStart, finish := emptyFinish .nat }, conP, w.layP]
  { admitted := a
    declaration := declaration
    found := hIsSome
    stack := fun r =>
      if hP : r = w.prover then hP ▸ hEntryEq ▸ proverStack
      else if hV : r = w.verifier then hV ▸ hEntryEq ▸ [conV, w.layV]
      else [] }

/-- Structured witness for a successful `deploy` call, eliminating all nested checks once. -/
inductive DeployOk (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) where
  | interactive (w : DeployInteractive a declaration) (hEq : d = w.toDeployed)
  | authored (w : DeployAuthored a declaration) (hEq : d = w.toDeployed)
  | derived (w : DeployDerived enc a declaration) (hEq : d = w.toDeployed)

/-- Unpack any successful `deploy` result into its exact structured witness (`DeployOk`). -/
def deploy_ok_elim (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) :
    DeployOk enc a declaration d := by
  unfold deploy at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    cases hSupp : checkDeclarationSupported foundPair.1 declaration with
    | false => rw [hSupp] at h; cases h
    | true =>
        rw [hSupp] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hScope : checkScope foundPair.1 declaration with
        | false => rw [hScope] at h; cases h
        | true =>
            rw [hScope] at h
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases hCon : declaration.construction with
            | interactive =>
                rw [hCon] at h
                exact .interactive ⟨foundPair, hFound, hSupp, hScope, hCon⟩ (Except.ok.inj h).symm
            | authored =>
                rw [hCon] at h; dsimp only at h
                cases hPV : proverAndVerifier foundPair.1 declaration with
                | none => rw [hPV] at h; cases h
                | some pv =>
                    rw [hPV] at h; dsimp only at h
                    by_cases hEqPV : pv.1 = pv.2
                    · rw [dite_eq_left hEqPV] at h; cases h
                    · rw [dite_eq_right hEqPV] at h
                      cases hAuth : checkAuthoredEvents a pv.1 pv.2 declaration.samples
                          declaration.key (foundPair.1.shape.events [] id) with
                      | error _ => rw [hAuth] at h; cases h
                      | ok sClauses =>
                          rw [hAuth] at h; dsimp only [bind, Except.bind] at h
                          cases hLayOpt : declaration.layout with
                          | none => rw [hLayOpt] at h; cases h
                          | some layout =>
                              rw [hLayOpt] at h; dsimp only at h
                              cases hLay : buildLayoutLayers a foundPair.1 layout pv.1 pv.2
                                  declaration.key (foundPair.1.shape.events [] id) with
                              | error _ => rw [hLay] at h; cases h
                              | ok lays =>
                                  rw [hLay] at h
                                  exact .authored ⟨foundPair, hFound, hSupp, hScope, hCon, pv.1, pv.2,
                                    hPV, hEqPV, sClauses, hAuth, layout, hLayOpt, lays.1, lays.2, hLay⟩
                                    (Except.ok.inj h).symm
            | derived suite sessionTag =>
                rw [hCon] at h; dsimp only at h
                cases hPV : proverAndVerifier foundPair.1 declaration with
                | none => rw [hPV] at h; cases h
                | some pv =>
                    rw [hPV] at h; dsimp only at h
                    by_cases hEqPV : pv.1 = pv.2
                    · rw [dite_eq_left hEqPV] at h; cases h
                    · rw [dite_eq_right hEqPV] at h
                      cases hLayOpt : declaration.layout with
                      | none => rw [hLayOpt] at h; cases h
                      | some layout =>
                          rw [hLayOpt] at h; dsimp only at h
                          cases hStart : findSuiteStart a suite with
                          | none => rw [hStart] at h; cases h
                          | some stPair =>
                              rw [hStart] at h; dsimp only at h
                              cases hAbs : findSuiteAbsorb a suite stPair.1 with
                              | none => rw [hAbs] at h; cases h
                              | some absPair =>
                                  rw [hAbs] at h; dsimp only at h
                                  cases hSess : resolveSessionBytes enc a declaration sessionTag with
                                  | error _ => rw [hSess] at h; cases h
                                  | ok sess =>
                                      rw [hSess] at h; dsimp only [bind, Except.bind] at h
                                      cases hSP : buildStmtAbsorbItems a suite absPair.1 pv.1 pv.1
                                          pv.2 (.inl rfl) foundPair.1.ins declaration.key with
                                      | error _ => rw [hSP] at h; cases h
                                      | ok stmtP =>
                                          rw [hSP] at h; dsimp only [bind, Except.bind] at h
                                          cases hSV : buildStmtAbsorbItems a suite absPair.1 pv.2
                                              pv.1 pv.2 (.inr rfl) foundPair.1.ins declaration.key with
                                          | error _ => rw [hSV] at h; cases h
                                          | ok stmtV =>
                                              rw [hSV] at h; dsimp only [bind, Except.bind] at h
                                              cases hCC : buildConstructionClauses a suite stPair.1
                                                  absPair.1 absPair.2 pv.1 pv.2 declaration.samples
                                                  declaration.key (foundPair.1.shape.events [] id)
                                                  (foundPair.1.shape.eventsWithAbsorb pv.1 pv.2 [] id false) with
                                              | error _ => rw [hCC] at h; cases h
                                              | ok cc =>
                                                  rw [hCC] at h; dsimp only [bind, Except.bind] at h
                                                  cases hLay : buildLayoutLayers a foundPair.1 layout
                                                      pv.1 pv.2 declaration.key
                                                      (foundPair.1.shape.events [] id) with
                                                  | error _ => rw [hLay] at h; cases h
                                                  | ok lays =>
                                                      rw [hLay] at h
                                                      exact .derived ⟨foundPair, hFound, hSupp, hScope,
                                                        suite, sessionTag, hCon, pv.1, pv.2, hPV, hEqPV,
                                                        layout, hLayOpt, stPair.1, stPair.2, hStart,
                                                        absPair.1, absPair.2, hAbs, sess.1, sess.2, hSess,
                                                        stmtP, hSP, stmtV, hSV, cc.1, cc.2.1, cc.2.2, hCC,
                                                        lays.1, lays.2, hLay⟩ (Except.ok.inj h).symm

/-- Structured witness for a successful `deployIdeal` call (pure collision-free ideal RO path). -/
structure DeployIdealWitness (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) where
  foundPair : (hdr : ProtocolHeader V) × Member a.program.headers.protocols hdr
  hFound : a.program.findProtocol declaration.entry = some foundPair
  hSupp : checkDeclarationSupported foundPair.1 declaration = true
  hScope : checkScope foundPair.1 declaration = true
  suite : ModuleRef
  sessionTag : Option (List Nat)
  hCon : declaration.construction = .derived suite sessionTag
  prover : Role
  verifier : Role
  hPV : proverAndVerifier foundPair.1 declaration = some (prover, verifier)
  hNe : prover ≠ verifier
  layout : Layout
  hLayOpt : declaration.layout = some layout
  suiteUnitTy : V.Ty
  hSuiteFree : Ty.isLinear V suiteUnitTy = false
  hUnit : findSuiteUnit a suite = some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩
  sessBytes : List Nat
  hSessBytes : ∀ b, b ∈ sessBytes → b < 256
  hSess : resolveSessionBytes enc a declaration sessionTag = .ok ⟨sessBytes, hSessBytes⟩
  stmtV : List (StmtAbsorbItem V a.program.headers.fns suiteUnitTy
    (Ctx.positional (held verifier foundPair.1.ins)))
  hSV : buildStmtAbsorbItems a suite suiteUnitTy verifier prover verifier (.inr rfl)
    foundPair.1.ins declaration.key = .ok stmtV
  idealVClauses : List (Clause V a.program.headers verifier (idealPathTy suiteUnitTy))
  hIV : buildIdealVerifierClauses a suite suiteUnitTy hSuiteFree serviceKey prover verifier
    declaration.key (foundPair.1.shape.events [] id)
    (foundPair.1.shape.eventsWithAbsorb prover verifier [] id false) = .ok idealVClauses
  layP : Layer V a.program.headers prover foundPair.1.ins
  layV : Layer V a.program.headers verifier foundPair.1.ins
  hLay : buildLayoutLayers a foundPair.1 layout prover verifier declaration.key
    (foundPair.1.shape.events [] id) = .ok (layP, layV)

abbrev DeployIdealWitness.toDeployed {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) : Deployed V :=
  let hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [w.hFound]; rfl
  let hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = w.foundPair.1 := by
    simp [w.hFound]
  let idealConV : Layer V a.program.headers w.verifier w.foundPair.1.ins := {
    line := .construction, state := idealPathTy w.suiteUnitTy, takes := [], gives := [],
    clauses := w.idealVClauses, again := restoreAgain (idealPathTy w.suiteUnitTy),
    start := idealStart w.hSuiteFree w.sessBytes w.hSessBytes w.stmtV,
    finish := emptyFinish (idealPathTy w.suiteUnitTy)
  }
  { admitted := a
    declaration := declaration
    found := hIsSome
    stack := fun r =>
      if hV : r = w.verifier then hV ▸ hEntryEq ▸ [idealConV, w.layV] else [] }

/-- Packed witness + equality for `deployIdeal ... = .ok d`. -/
structure DeployIdealOk (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V) where
  w : DeployIdealWitness enc serviceKey a declaration
  hEq : d = w.toDeployed

/-- Unpack any successful `deployIdeal` result into its exact structured witness. -/
def deployIdeal_ok_elim (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) :
    DeployIdealOk enc serviceKey a declaration d := by
  unfold deployIdeal at h
  split at h
  · cases h
  · rename_i foundPair hFound
    dsimp only at h
    cases hSupp : checkDeclarationSupported foundPair.1 declaration with
    | false => rw [hSupp] at h; cases h
    | true =>
        rw [hSupp] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hScope : checkScope foundPair.1 declaration with
        | false => rw [hScope] at h; cases h
        | true =>
            rw [hScope] at h
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases hCon : declaration.construction with
            | interactive => rw [hCon] at h; cases h
            | authored => rw [hCon] at h; cases h
            | derived suite sessionTag =>
                rw [hCon] at h; dsimp only at h
                cases hPV : proverAndVerifier foundPair.1 declaration with
                | none => rw [hPV] at h; cases h
                | some pv =>
                    rw [hPV] at h; dsimp only at h
                    by_cases hEqPV : pv.1 = pv.2
                    · rw [dite_eq_left hEqPV] at h; cases h
                    · rw [dite_eq_right hEqPV] at h
                      cases hLayOpt : declaration.layout with
                      | none => rw [hLayOpt] at h; cases h
                      | some layout =>
                          rw [hLayOpt] at h; dsimp only at h
                          cases hUnit : findSuiteUnit a suite with
                          | none => rw [hUnit] at h; cases h
                          | some uPair =>
                              rw [hUnit] at h; dsimp only at h
                              cases hSess : resolveSessionBytes enc a declaration sessionTag with
                              | error _ => rw [hSess] at h; cases h
                              | ok sess =>
                                  rw [hSess] at h; dsimp only [bind, Except.bind] at h
                                  cases hSV : buildStmtAbsorbItems a suite uPair.1 pv.2 pv.1 pv.2
                                      (.inr rfl) foundPair.1.ins declaration.key with
                                  | error _ => rw [hSV] at h; cases h
                                  | ok stmtV =>
                                      rw [hSV] at h; dsimp only [bind, Except.bind] at h
                                      cases hIV : buildIdealVerifierClauses a suite uPair.1
                                          uPair.2.down serviceKey pv.1 pv.2 declaration.key
                                          (foundPair.1.shape.events [] id)
                                          (foundPair.1.shape.eventsWithAbsorb pv.1 pv.2 [] id false) with
                                      | error _ => rw [hIV] at h; cases h
                                      | ok idealVClauses =>
                                          rw [hIV] at h; dsimp only [bind, Except.bind] at h
                                          cases hLay : buildLayoutLayers a foundPair.1 layout pv.1
                                              pv.2 declaration.key (foundPair.1.shape.events [] id) with
                                          | error _ => rw [hLay] at h; cases h
                                          | ok lays =>
                                              rw [hLay] at h
                                              exact ⟨⟨foundPair, hFound, hSupp, hScope, suite, sessionTag,
                                                hCon, pv.1, pv.2, hPV, hEqPV, layout, hLayOpt, uPair.1,
                                                uPair.2.down, hUnit, sess.1, sess.2, hSess, stmtV, hSV,
                                                idealVClauses, hIV, lays.1, lays.2, hLay⟩,
                                                (Except.ok.inj h).symm⟩

end Elimination

/-! ## Structural deployment theorems -/

section StructuralTheorems

variable {V : Vocabulary}

/-- `deploy` preserves `admitted`, `declaration`, and `entry.key`. -/
theorem deploy_keeps (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) :
    d.admitted = a ∧ d.declaration = declaration ∧ d.entry.key = declaration.entry := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq => subst hEq; exact ⟨rfl, rfl, Deployed.entry_key _⟩
  | authored w hEq => subst hEq; exact ⟨rfl, rfl, Deployed.entry_key _⟩
  | derived w hEq => subst hEq; exact ⟨rfl, rfl, Deployed.entry_key _⟩

/-- Every non-interactive deployment resolves `(prover, verifier)`. -/
theorem deploy_findsRoles (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d)
    (hNonInt : declaration.interactive = false) :
    ∃ prover verifier, d.roles = some (prover, verifier) := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w _ => simp [Declaration.interactive, w.hCon] at hNonInt
  | authored w hEq =>
      subst hEq
      exact ⟨w.prover, w.verifier, by unfold Deployed.roles Deployed.entry; simpa [w.hFound] using w.hPV⟩
  | derived w hEq =>
      subst hEq
      exact ⟨w.prover, w.verifier, by unfold Deployed.roles Deployed.entry; simpa [w.hFound] using w.hPV⟩

/-- Every layout layer pair produced by `buildLayoutLayers` takes `[]` on prover and matches
`layP.gives = layV.takes = [.seq unitTy none]`. -/
theorem buildLayoutLayers_io {a : Admitted V} {entry : ProtocolHeader V} {layout : Layout}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins}
    (h : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    ∃ unitTy, layP.takes = [] ∧ layP.gives = [.seq unitTy none] ∧
      layV.takes = [.seq unitTy none] ∧ layV.gives = [] := by
  cases buildLayoutLayers_ok_elim h with
  | streaming w hLayP hLayV => subst hLayP; subst hLayV; exact ⟨w.unitTy, rfl, rfl, rfl, rfl⟩
  | compact w hComp =>
      unfold buildCompactLayoutLayers at hComp
      cases hCW : collectCompactWire a layout w.unitTy prover verifier declKey events 0 events with
      | error _ => rw [hCW] at hComp; cases hComp
      | ok cw =>
          rw [hCW] at hComp; dsimp only [bind, Except.bind] at hComp
          split at hComp
          · cases hVC : buildCompactVClauses a layout w.unitTy prover verifier declKey events _ cw.1
                _ 0 events with
            | error _ => rw [hVC] at hComp; cases hComp
            | ok vcs =>
                rw [hVC] at hComp; cases hComp
                exact ⟨w.unitTy, rfl, rfl, rfl, rfl⟩
          · cases hComp

/-- Prover's stack takes nothing from outside and its output types equal the verifier's input types. -/
theorem deploy_matches (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d)
    (prover verifier : Role) (hRoles : d.roles = some (prover, verifier)) :
    Stack.Takes (d.stack prover) = [] ∧
      Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier) := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq => subst hEq; exact ⟨rfl, rfl⟩
  | authored w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      obtain ⟨unitTy, hPt, hPg, hVt, _⟩ := buildLayoutLayers_io w.hLay
      have hNeSym : w.verifier ≠ w.prover := Ne.symm w.hNe
      dsimp only
      rw [dite_eq_left rfl, dite_eq_right hNeSym, dite_eq_left rfl,
          stack_takes_cast_hdr (by simp [w.hFound]),
          stack_gives_cast_hdr (by simp [w.hFound]),
          stack_takes_cast_hdr (by simp [w.hFound])]
      cases declaration.samples <;> simp [Stack.Takes, Stack.Gives, hPt, hPg, hVt]
  | derived w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      obtain ⟨unitTy, hPt, hPg, hVt, _⟩ := buildLayoutLayers_io w.hLay
      have hNeSym : w.verifier ≠ w.prover := Ne.symm w.hNe
      dsimp only
      rw [dite_eq_left rfl, dite_eq_right hNeSym, dite_eq_left rfl,
          stack_takes_cast_hdr (by simp [w.hFound]),
          stack_gives_cast_hdr (by simp [w.hFound]),
          stack_takes_cast_hdr (by simp [w.hFound])]
      cases declaration.samples <;> simp [Stack.Takes, Stack.Gives, hPt, hPg, hVt]

/-- Every accepted deployment satisfies `Deployed.Scoped`. -/
theorem deploy_scoped (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.Scoped := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq =>
      subst hEq; unfold Deployed.Scoped Deployed.entry
      simpa [w.hFound] using checkScope_sound w.foundPair.1 declaration w.hScope
  | authored w hEq =>
      subst hEq; unfold Deployed.Scoped Deployed.entry
      simpa [w.hFound] using checkScope_sound w.foundPair.1 declaration w.hScope
  | derived w hEq =>
      subst hEq; unfold Deployed.Scoped Deployed.entry
      simpa [w.hFound] using checkScope_sound w.foundPair.1 declaration w.hScope

/-- Every accepted ideal-RO deployment satisfies `Deployed.Scoped`. -/
theorem deployIdeal_scoped (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.Scoped := by
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration d h
  subst hEq; unfold Deployed.Scoped Deployed.entry
  simpa [w.hFound] using checkScope_sound w.foundPair.1 declaration w.hScope

/-- Every accepted deployment satisfies `Deployed.WellNestedRetry` unconditionally. -/
theorem deploy_wellNestedRetry (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.WellNestedRetry := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq =>
      subst hEq
      intro bound site hret
      have hwn := checkScope_wellNested w.foundPair.1 declaration w.hScope
      dsimp only [Deployed.retry] at hret
      rw [hret] at hwn
      simpa [Deployed.entry, w.hFound] using hwn
  | authored w hEq =>
      subst hEq
      intro bound site hret
      have hwn := checkScope_wellNested w.foundPair.1 declaration w.hScope
      dsimp only [Deployed.retry] at hret
      rw [hret] at hwn
      simpa [Deployed.entry, w.hFound] using hwn
  | derived w hEq =>
      subst hEq
      intro bound site hret
      have hwn := checkScope_wellNested w.foundPair.1 declaration w.hScope
      dsimp only [Deployed.retry] at hret
      rw [hret] at hwn
      simpa [Deployed.entry, w.hFound] using hwn

/-- Every accepted ideal-RO deployment satisfies `Deployed.WellNestedRetry` unconditionally. -/
theorem deployIdeal_wellNestedRetry (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.WellNestedRetry := by
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration d h
  subst hEq
  intro bound site hret
  have hwn := checkScope_wellNested w.foundPair.1 declaration w.hScope
  dsimp only [Deployed.retry] at hret
  rw [hret] at hwn
  simpa [Deployed.entry, w.hFound] using hwn

/-! ### Freshness (`Deployed.Fresh`) -/

/-- A single clause satisfies the freshness condition relative to `events`. -/
def ClauseFresh {hs : Headers V} {r : Role} {state : V.Ty}
    (events : List (ShapeEvent V)) (c : Clause V hs r state) : Prop :=
  ∀ key, key ∈ Term.eventKeys (fun o => RoleOp.isEvent o) c.code → key ≠ c.site.site.key →
    key ∉ events.map (·.site.key)

theorem buildConstructionClauses_go_fresh {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
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
  | idx, (e, needAbs) :: rest, cP, cV, cS, h => by
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
              · cases needAbs with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h; exact ⟨ihP, ihV, ihS⟩
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
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

theorem buildIdealVerifierClauses_go_fresh {a : Admitted V} {suite : ModuleRef}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cV : List (Clause V a.program.headers verifier (idealPathTy unitTy))},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ c ∈ cV, ClauseFresh events c
  | _, [], _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, (e, needAbs) :: rest, cV, h => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihV := buildIdealVerifierClauses_go_fresh (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h; exact ihV
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some encRef =>
                        rw [hEnc] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hmem
                        · intro key hk hne
                          rw [idealAbsorbClause_eventKeys] at hk
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

theorem checkAuthoredEvents_fresh {a : Admitted V} {prover verifier : Role}
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

theorem buildStreamingLayoutClauses_go_fresh {a : Admitted V} {layout : Layout}
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

theorem collectCompactWire_fresh {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
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

theorem buildCompactVClauses_fresh {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
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

theorem buildLayoutLayers_fresh {a : Admitted V} {entry : ProtocolHeader V} {layout : Layout}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins}
    (h : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    (∀ c ∈ layP.clauses, ClauseFresh events c) ∧ (∀ c ∈ layV.clauses, ClauseFresh events c) := by
  cases buildLayoutLayers_ok_elim h with
  | streaming w hLayP hLayV =>
      subst hLayP; subst hLayV
      obtain ⟨hP, hV⟩ := buildStreamingLayoutClauses_go_fresh 0 events w.hStr
      exact ⟨(fun c hc key hk _ => by rw [hP c hc] at hk; cases hk),
             (fun c hc key hk _ => by rw [hV c hc] at hk; cases hk)⟩
  | compact w hComp =>
      unfold buildCompactLayoutLayers at hComp
      cases hCW : collectCompactWire a layout w.unitTy prover verifier declKey events 0 events with
      | error _ => rw [hCW] at hComp; cases hComp
      | ok cw =>
          rw [hCW] at hComp; dsimp only [bind, Except.bind] at hComp
          split at hComp
          · cases hVC : buildCompactVClauses a layout w.unitTy prover verifier declKey events _ cw.1
                _ 0 events with
            | error _ => rw [hVC] at hComp; cases hComp
            | ok vcs =>
                rw [hVC] at hComp; cases hComp
                have hP := collectCompactWire_fresh 0 events hCW
                have hV := buildCompactVClauses_fresh 0 events hVC
                exact ⟨(fun c hc key hk _ => by rw [hP c hc] at hk; cases hk),
                       (fun c hc key hk _ => by rw [hV c hc] at hk; cases hk)⟩
          · cases hComp

theorem stack_fresh_cast {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins))
    (h : ∀ l ∈ layers, ∀ c ∈ l.clauses, ClauseFresh (hdr₂.shape.events [] id) c) :
    ∀ l ∈ (hr ▸ hHdr ▸ layers), ∀ c ∈ l.clauses, ClauseFresh (hdr₁.shape.events [] id) c :=
  cast_layer_stack_elim hHdr hr layers
    (fun hdr _ ls => ∀ l ∈ ls, ∀ c ∈ l.clauses, ClauseFresh (hdr.shape.events [] id) c) h

/-- Every accepted deployment satisfies `Deployed.Fresh`. -/
theorem deploy_fresh (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.Fresh := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq =>
      subst hEq
      intro _ _ hl; cases hl
  | authored w hEq =>
      subst hEq
      have hS := checkAuthoredEvents_fresh (events := w.foundPair.1.shape.events [] id) _ w.hAuth
      obtain ⟨hLP, hLV⟩ := buildLayoutLayers_fresh w.hLay
      intro r
      dsimp only [Deployed.entry]
      by_cases hP : r = w.prover
      · rw [dite_eq_left hP]
        apply stack_fresh_cast (by simp [w.hFound]) hP
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
        by_cases hV : r = w.verifier
        · rw [dite_eq_left hV]
          apply stack_fresh_cast (by simp [w.hFound]) hV
          intro l hl
          simp only [List.mem_singleton] at hl; subst hl; exact hLV
        · rw [dite_eq_right hV]
          intro _ hl; cases hl
  | derived w hEq =>
      subst hEq
      obtain ⟨hCP, hCV, hCS⟩ := buildConstructionClauses_go_fresh 0 _ w.hCC
      obtain ⟨hLP, hLV⟩ := buildLayoutLayers_fresh w.hLay
      intro r
      dsimp only [Deployed.entry]
      by_cases hP : r = w.prover
      · rw [dite_eq_left hP]
        apply stack_fresh_cast (by simp [w.hFound]) hP
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
        by_cases hV : r = w.verifier
        · rw [dite_eq_left hV]
          apply stack_fresh_cast (by simp [w.hFound]) hV
          intro l hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact hCV
          · exact hLV
        · rw [dite_eq_right hV]
          intro _ hl; cases hl

/-- Every accepted ideal-RO deployment satisfies `Deployed.Fresh`. -/
theorem deployIdeal_fresh (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.Fresh := by
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration d h
  subst hEq
  have hCV := buildIdealVerifierClauses_go_fresh 0 _ w.hIV
  obtain ⟨_, hLV⟩ := buildLayoutLayers_fresh w.hLay
  intro r
  dsimp only [Deployed.entry]
  by_cases hV : r = w.verifier
  · rw [dite_eq_left hV]
    apply stack_fresh_cast (by simp [w.hFound]) hV
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hCV
    · exact hLV
  · rw [dite_eq_right hV]
    intro _ hl; cases hl

end StructuralTheorems

end Zkc.Core
