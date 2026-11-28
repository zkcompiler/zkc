module

public import Zkc.Core.Scheme.Deploy.Compile
public import Zkc.Core.Scheme.Layer.ClauseLemmas
public import Zkc.Core.Scheme.Proof.ShapeObserve

@[expose] public section

/-!
Elimination witnesses (`deploy_ok_elim`, `deployIdeal_ok_elim`, `buildLayoutLayers_ok_elim`) and
shared lookup, cast, and stack-composition helpers.
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

theorem findLawSlotMember_some {α : Type} {m : ModuleRef} {slot : Key} {lawBytes : List Nat}
    {pick : Key → Option α} {x : α} (h : findLawSlotMember m slot lawBytes pick = some x) :
    ∃ defKey, (slot, lawBytes, defKey) ∈ m.lawMembers ∧ pick defKey = some x := by
  unfold findLawSlotMember at h
  obtain ⟨⟨s, lb, defKey⟩, hIn, hPick⟩ := List.exists_of_findSome?_eq_some h
  by_cases hs : s = slot ∧ lb = lawBytes
  · rcases hs with ⟨rfl, rfl⟩
    simp only [and_self, ↓reduceIte] at hPick
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
  cases hLaw : findLawSlotMember suite SuiteSlot.derive (enc.lawKey law)
      (fun defKey => findTypedFnRef a defKey (stateTy :: bytesTy :: drawIns) [τ, stateTy]) with
  | some ref' =>
      rw [hLaw] at h
      have hEq : ref' = ref := Option.some.inj h
      subst hEq
      obtain ⟨defKey, hIn, hRef⟩ := findLawSlotMember_some hLaw
      exact ⟨defKey, .inl hIn, findTypedFnRef_some hRef⟩
  | none =>
      rw [hLaw] at h
      dsimp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
      obtain ⟨defKey, hIn, hRef⟩ := findSlotMember_some h
      exact ⟨defKey, .inr hIn, findTypedFnRef_some hRef⟩

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
  hCon : declaration.construction = .interactive
  hInt : checkInteractive declaration = true
  hScope : checkInteractiveScope foundPair.1 declaration = true

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
  hCon : declaration.construction = .authored
  hNoSamp : declaration.samples = none
  prover : Role
  verifier : Role
  hPV : proverAndVerifier foundPair.1 declaration = some (prover, verifier)
  hNe : prover ≠ verifier
  hScope : checkNonInteractiveScope foundPair.1 prover declaration = true
  hAuth : checkAuthoredEvents prover verifier declaration.key
    (foundPair.1.shape.events [] id) = .ok ()
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
  { admitted := a
    declaration := declaration
    found := hIsSome
    stack := fun r =>
      if hP : r = w.prover then hP ▸ hEntryEq ▸ [w.layP]
      else if hV : r = w.verifier then hV ▸ hEntryEq ▸ [w.layV]
      else [] }

/-- Witness for a derived `deploy` result. -/
structure DeployDerived (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration) where
  foundPair : (hdr : ProtocolHeader V) × Member a.program.headers.protocols hdr
  hFound : a.program.findProtocol declaration.entry = some foundPair
  hSupp : checkDeclarationSupported foundPair.1 declaration = true
  suite : ModuleRef
  sessionTag : Option (List Nat)
  hCon : declaration.construction = .derived suite sessionTag
  prep : DerivedPrepared enc a declaration foundPair.1 sessionTag
  hPrep : prepareDerivedBody enc a declaration foundPair.1 sessionTag = .ok prep
  stateTy : V.Ty
  startRef : TypedFnRef V a.program.headers.fns [bytesTy] [stateTy]
  hStart : findSuiteStart a suite = some ⟨stateTy, startRef⟩
  suiteUnitTy : V.Ty
  absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]
  hAbs : findSuiteAbsorb a suite stateTy = some ⟨suiteUnitTy, absorbRef⟩
  stmtP : List (StmtAbsorbItem V a.program.headers.fns suiteUnitTy
    (Ctx.positional (held prep.prover foundPair.1.ins)))
  hSP : buildStmtAbsorbItems a suite suiteUnitTy prep.prover prep.prover prep.verifier (.inl rfl)
    foundPair.1.ins declaration.key = .ok stmtP
  stmtV : List (StmtAbsorbItem V a.program.headers.fns suiteUnitTy
    (Ctx.positional (held prep.verifier foundPair.1.ins)))
  hSV : buildStmtAbsorbItems a suite suiteUnitTy prep.verifier prep.prover prep.verifier (.inr rfl)
    foundPair.1.ins declaration.key = .ok stmtV
  cPClauses : List (Clause V a.program.headers prep.prover stateTy)
  cVClauses : List (Clause V a.program.headers prep.verifier stateTy)
  hCC : buildConstructionClauses enc a suite stateTy suiteUnitTy absorbRef prep.prover prep.verifier
    declaration.key (foundPair.1.shape.events [] id)
    (foundPair.1.shape.eventsWithAbsorb prep.prover prep.verifier [] id false) =
    .ok (cPClauses, cVClauses)

abbrev DeployDerived.prover {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) : Role := w.prep.prover
abbrev DeployDerived.verifier {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) : Role := w.prep.verifier
abbrev DeployDerived.hPV {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hPV
abbrev DeployDerived.hNe {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hNe
abbrev DeployDerived.hScope {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hScope
abbrev DeployDerived.layout {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.layout
abbrev DeployDerived.hLayOpt {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hLayOpt
abbrev DeployDerived.sessBytes {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.sessBytes
abbrev DeployDerived.hSessBytes {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hSessBytes
abbrev DeployDerived.hSess {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hSess
abbrev DeployDerived.sampLayer {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.sampLayer
abbrev DeployDerived.hSamp {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hSamp
abbrev DeployDerived.layP {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.layP
abbrev DeployDerived.layV {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.layV
abbrev DeployDerived.hLay {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) := w.prep.hLay

abbrev DeployDerived.toDeployed {enc : VocabEncoder V} {a : Admitted V} {declaration : Declaration}
    (w : DeployDerived enc a declaration) : Deployed V :=
  let hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [w.hFound]; rfl
  let hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = w.foundPair.1 := by
    simp [w.hFound]
  let conP : Layer V a.program.headers w.prep.prover w.foundPair.1.ins := {
    line := .construction, state := w.stateTy, takes := [], gives := [],
    clauses := w.cPClauses, again := restoreAgain w.stateTy,
    start := constructionStart w.prep.sessBytes w.prep.hSessBytes w.startRef w.absorbRef w.stmtP,
    finish := emptyFinish w.stateTy
  }
  let conV : Layer V a.program.headers w.prep.verifier w.foundPair.1.ins := {
    line := .construction, state := w.stateTy, takes := [], gives := [],
    clauses := w.cVClauses, again := restoreAgain w.stateTy,
    start := constructionStart w.prep.sessBytes w.prep.hSessBytes w.startRef w.absorbRef w.stmtV,
    finish := emptyFinish w.stateTy
  }
  let proverStack : List (Layer V a.program.headers w.prep.prover w.foundPair.1.ins) :=
    match w.prep.sampLayer with
    | none => [conP, w.prep.layP]
    | some sampP => [sampP, conP, w.prep.layP]
  { admitted := a
    declaration := declaration
    found := hIsSome
    stack := fun r =>
      if hP : r = w.prep.prover then hP ▸ (congrArg ProtocolHeader.ins hEntryEq) ▸ proverStack
      else if hV : r = w.prep.verifier then hV ▸ (congrArg ProtocolHeader.ins hEntryEq) ▸ [conV, w.prep.layV]
      else [] }

/-- Structured witness for a successful `deploy` call, eliminating all nested checks once. -/
inductive DeployOk (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) where
  | interactive (w : DeployInteractive a declaration) (hEq : d = w.toDeployed)
  | authored (w : DeployAuthored a declaration) (hEq : d = w.toDeployed)
  | derived (w : DeployDerived enc a declaration) (hEq : d = w.toDeployed)

theorem eqRec_hdr_eq_ins {V : Vocabulary} {hs : Headers V} {r : Role}
    {h₁ h₂ : ProtocolHeader V} (h : h₁ = h₂) (ls : List (Layer V hs r h₂.ins)) :
    (h ▸ ls : List (Layer V hs r h₁.ins)) = (congrArg ProtocolHeader.ins h ▸ ls) := by
  subst h; rfl

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
        cases hCon : declaration.construction with
        | interactive =>
            rw [hCon] at h; dsimp only at h
            cases hInt : checkInteractive declaration with
            | false => rw [hInt] at h; cases h
            | true =>
                rw [hInt] at h
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
                cases hScope : checkInteractiveScope foundPair.1 declaration with
                | false => rw [hScope] at h; cases h
                | true =>
                    rw [hScope] at h
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
                    exact .interactive ⟨foundPair, hFound, hSupp, hCon, hInt, hScope⟩ (Except.ok.inj h).symm
        | authored =>
            rw [hCon] at h; dsimp only at h
            cases hSamp : declaration.samples with
            | some _ => rw [hSamp] at h; cases h
            | none =>
                rw [hSamp] at h; simp only [Option.isNone_none, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
                cases hPV : proverAndVerifier foundPair.1 declaration with
                | none => rw [hPV] at h; cases h
                | some pv =>
                    rw [hPV] at h; dsimp only at h
                    by_cases hEqPV : pv.1 = pv.2
                    · rw [dite_eq_left hEqPV] at h; cases h
                    · rw [dite_eq_right hEqPV] at h
                      cases hScope : checkNonInteractiveScope foundPair.1 pv.1 declaration with
                      | false => rw [hScope] at h; cases h
                      | true =>
                          rw [hScope] at h
                          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
                          cases hAuth : checkAuthoredEvents pv.1 pv.2
                              declaration.key (foundPair.1.shape.events [] id) with
                          | error _ => rw [hAuth] at h; cases h
                          | ok u =>
                              cases u
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
                                      exact .authored ⟨foundPair, hFound, hSupp, hCon, hSamp, pv.1, pv.2,
                                        hPV, hEqPV, hScope, hAuth, layout, hLayOpt, lays.1, lays.2, hLay⟩
                                        (Except.ok.inj h).symm
        | derived suite sessionTag =>
            rw [hCon] at h; dsimp only at h
            cases hPrep : prepareDerivedBody enc a declaration foundPair.1 sessionTag with
            | error _ => rw [hPrep] at h; cases h
            | ok prep =>
                rw [hPrep] at h; dsimp only [bind, Except.bind] at h
                cases prep with
                | mk prover verifier hPV hNe hScope layout hLayOpt sessBytes hSessBytes hSess
                    sampLayer hSamp layP layV hLay =>
                    dsimp only at h
                    cases hStart : findSuiteStart a suite with
                    | none => rw [hStart] at h; cases h
                    | some stPair =>
                        rw [hStart] at h; dsimp only at h
                        cases hAbs : findSuiteAbsorb a suite stPair.1 with
                        | none => rw [hAbs] at h; cases h
                        | some absPair =>
                            rw [hAbs] at h; dsimp only at h
                            cases hSP : buildStmtAbsorbItems a suite absPair.1 prover prover
                                verifier (.inl rfl) foundPair.1.ins declaration.key with
                            | error _ => rw [hSP] at h; cases h
                            | ok stmtP =>
                                rw [hSP] at h; dsimp only [bind, Except.bind] at h
                                cases hSV : buildStmtAbsorbItems a suite absPair.1 verifier
                                    prover verifier (.inr rfl) foundPair.1.ins declaration.key with
                                | error _ => rw [hSV] at h; cases h
                                | ok stmtV =>
                                    rw [hSV] at h; dsimp only [bind, Except.bind] at h
                                    cases hCC : buildConstructionClauses enc a suite stPair.1
                                        absPair.1 absPair.2 prover verifier
                                        declaration.key (foundPair.1.shape.events [] id)
                                        (foundPair.1.shape.eventsWithAbsorb prover verifier [] id false) with
                                    | error _ => rw [hCC] at h; cases h
                                    | ok cc =>
                                        rw [hCC] at h
                                        have hEqD : d = (DeployDerived.toDeployed
                                            ⟨foundPair, hFound, hSupp, suite, sessionTag, hCon,
                                              ⟨prover, verifier, hPV, hNe, hScope, layout, hLayOpt,
                                               sessBytes, hSessBytes, hSess, sampLayer, hSamp,
                                               layP, layV, hLay⟩, hPrep,
                                              stPair.1, stPair.2, hStart, absPair.1, absPair.2, hAbs,
                                              stmtP, hSP, stmtV, hSV, cc.1, cc.2, hCC⟩) := by
                                          have he := (Except.ok.inj h).symm
                                          cases he
                                          congr 1
                                          funext r
                                          by_cases hP : r = prover
                                          · subst hP; simp only [↓reduceDIte]
                                            cases sampLayer <;> (refine eqRec_hdr_eq_ins ?_ _; simp [hFound])
                                          · simp only [hP, ↓reduceDIte]
                                            by_cases hV : r = verifier
                                            · subst hV; simp only [↓reduceDIte]
                                              refine eqRec_hdr_eq_ins ?_ _; simp [hFound]
                                            · simp only [hV, ↓reduceDIte]
                                        exact .derived ⟨foundPair, hFound, hSupp, suite, sessionTag, hCon,
                                          ⟨prover, verifier, hPV, hNe, hScope, layout, hLayOpt,
                                           sessBytes, hSessBytes, hSess, sampLayer, hSamp,
                                           layP, layV, hLay⟩, hPrep,
                                          stPair.1, stPair.2, hStart, absPair.1, absPair.2, hAbs,
                                          stmtP, hSP, stmtV, hSV, cc.1, cc.2, hCC⟩ hEqD

/-- Structured witness for a successful `deployIdeal` call (pure collision-free ideal
random-oracle path). -/
structure DeployIdealWitness (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) where
  foundPair : (hdr : ProtocolHeader V) × Member a.program.headers.protocols hdr
  hFound : a.program.findProtocol declaration.entry = some foundPair
  hSupp : checkDeclarationSupported foundPair.1 declaration = true
  suite : ModuleRef
  sessionTag : Option (List Nat)
  hCon : declaration.construction = .derived suite sessionTag
  prep : DerivedPrepared enc a declaration foundPair.1 sessionTag
  hPrep : prepareDerivedBody enc a declaration foundPair.1 sessionTag = .ok prep
  suiteUnitTy : V.Ty
  hSuiteFree : Ty.isLinear V suiteUnitTy = false
  hUnit : findSuiteUnit a suite = some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩
  stmtV : List (StmtAbsorbItem V a.program.headers.fns suiteUnitTy
    (Ctx.positional (held prep.verifier foundPair.1.ins)))
  hSV : buildStmtAbsorbItems a suite suiteUnitTy prep.verifier prep.prover prep.verifier (.inr rfl)
    foundPair.1.ins declaration.key = .ok stmtV
  idealVClauses : List (Clause V a.program.headers prep.verifier (idealPathTy suiteUnitTy))
  hIV : buildIdealVerifierClauses a suite suiteUnitTy hSuiteFree serviceKey prep.prover prep.verifier
    declaration.key (foundPair.1.shape.events [] id)
    (foundPair.1.shape.eventsWithAbsorb prep.prover prep.verifier [] id false) = .ok idealVClauses

abbrev DeployIdealWitness.prover {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.prover
abbrev DeployIdealWitness.verifier {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.verifier
abbrev DeployIdealWitness.hPV {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.hPV
abbrev DeployIdealWitness.hNe {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.hNe
abbrev DeployIdealWitness.hScope {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.hScope
abbrev DeployIdealWitness.layout {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.layout
abbrev DeployIdealWitness.hLayOpt {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.hLayOpt
abbrev DeployIdealWitness.sessBytes {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.sessBytes
abbrev DeployIdealWitness.hSessBytes {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.hSessBytes
abbrev DeployIdealWitness.hSess {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.hSess
abbrev DeployIdealWitness.layP {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.layP
abbrev DeployIdealWitness.layV {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.layV
abbrev DeployIdealWitness.hLay {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) := w.prep.hLay

abbrev DeployIdealWitness.toDeployed {enc : VocabEncoder V} {serviceKey : Key} {a : Admitted V}
    {declaration : Declaration} (w : DeployIdealWitness enc serviceKey a declaration) : Deployed V :=
  let hIsSome : (a.program.findProtocol declaration.entry).isSome := by rw [w.hFound]; rfl
  let hEntryEq : ((a.program.findProtocol declaration.entry).get hIsSome).1 = w.foundPair.1 := by
    simp [w.hFound]
  let idealConV : Layer V a.program.headers w.prep.verifier w.foundPair.1.ins := {
    line := .construction, state := idealPathTy w.suiteUnitTy, takes := [], gives := [],
    clauses := w.idealVClauses, again := restoreAgain (idealPathTy w.suiteUnitTy),
    start := idealStart w.hSuiteFree w.prep.sessBytes w.prep.hSessBytes w.stmtV,
    finish := emptyFinish (idealPathTy w.suiteUnitTy)
  }
  { admitted := a
    declaration := declaration
    found := hIsSome
    stack := fun r =>
      if hV : r = w.prep.verifier then hV ▸ (congrArg ProtocolHeader.ins hEntryEq) ▸ [idealConV, w.prep.layV]
      else [] }

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
        cases hCon : declaration.construction with
        | interactive => rw [hCon] at h; cases h
        | authored => rw [hCon] at h; cases h
        | derived suite sessionTag =>
            rw [hCon] at h; dsimp only at h
            cases hPrep : prepareDerivedBody enc a declaration foundPair.1 sessionTag with
            | error _ => rw [hPrep] at h; cases h
            | ok prep =>
                rw [hPrep] at h; dsimp only [bind, Except.bind] at h
                cases prep with
                | mk prover verifier hPV hNe hScope layout hLayOpt sessBytes hSessBytes hSess
                    sampLayer hSamp layP layV hLay =>
                    dsimp only at h
                    cases hUnit : findSuiteUnit a suite with
                    | none => rw [hUnit] at h; cases h
                    | some uPair =>
                        rw [hUnit] at h; dsimp only at h
                        cases hSV : buildStmtAbsorbItems a suite uPair.1 verifier prover verifier
                            (.inr rfl) foundPair.1.ins declaration.key with
                        | error _ => rw [hSV] at h; cases h
                        | ok stmtV =>
                            rw [hSV] at h; dsimp only [bind, Except.bind] at h
                            cases hIV : buildIdealVerifierClauses a suite uPair.1
                                uPair.2.down serviceKey prover verifier declaration.key
                                (foundPair.1.shape.events [] id)
                                (foundPair.1.shape.eventsWithAbsorb prover verifier [] id false) with
                            | error _ => rw [hIV] at h; cases h
                            | ok idealVClauses =>
                                rw [hIV] at h
                                have hEqD : d = (DeployIdealWitness.toDeployed
                                    ⟨foundPair, hFound, hSupp, suite, sessionTag, hCon,
                                      ⟨prover, verifier, hPV, hNe, hScope, layout, hLayOpt,
                                       sessBytes, hSessBytes, hSess, sampLayer, hSamp,
                                       layP, layV, hLay⟩, hPrep,
                                      uPair.1, uPair.2.down, hUnit, stmtV, hSV,
                                      idealVClauses, hIV⟩) := by
                                  have he := (Except.ok.inj h).symm
                                  cases he
                                  congr 1
                                  funext r
                                  by_cases hV : r = verifier
                                  · subst hV; simp only [↓reduceDIte]
                                    refine eqRec_hdr_eq_ins ?_ _; simp [hFound]
                                  · simp only [hV, ↓reduceDIte]
                                exact ⟨⟨foundPair, hFound, hSupp, suite, sessionTag, hCon,
                                  ⟨prover, verifier, hPV, hNe, hScope, layout, hLayOpt,
                                   sessBytes, hSessBytes, hSess, sampLayer, hSamp,
                                   layP, layV, hLay⟩, hPrep,
                                  uPair.1, uPair.2.down, hUnit, stmtV, hSV,
                                  idealVClauses, hIV⟩, hEqD⟩

end Elimination


end Zkc.Core
