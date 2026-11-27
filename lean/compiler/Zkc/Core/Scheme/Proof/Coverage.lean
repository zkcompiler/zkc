module

public import Zkc.Core.Scheme.Proof.Safety

@[expose] public section

/-!
Effect coverage (`deploy_coverage`, `deployIdeal_verifier_covered`): under a non-interactive
deployment's stack, every online role emits only closed effects (private coins, service requests,
and local attempt marks).
-/

namespace Zkc.Core

open LayerBuild

/-! ## Effect coverage (`deploy_coverage`, `deployIdeal_verifier_covered`) -/

section Coverage

variable {V : Vocabulary} (M : Model V)

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

/-- Lightweight handler coverage invariant: every `opOk₁` effect is transformed into `opOk₂`
effects. -/
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
    (rTable : RTable M hs.protocols) {heldP : List V.Ty} {τ : V.Ty} {opOk : ROp M → Prop}
    (htfree : Tys.anyLinear V (samplesStateTys heldP) = false)
    (prover : Role) (site : Site) (law : V.LawKey)
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (siteBytes : List Nat) (hsite : ∀ b, b ∈ siteBytes → b < 256)
    (sRef : TypedFnRef V hs.fns (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) :
    ClauseEmits M fnTable rTable opOk
      (proverSampleClause htfree prover site law sessionBytes hsess siteBytes hsite sRef) := by
  intro op hMatch st
  generalize hArgs : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = args
  cases args
  rcases st with ⟨att, seq, heldTuple, ⟨⟩⟩
  show ((proverSampleClause htfree prover site law sessionBytes hsess siteBytes hsite sRef).code.denote
    (roleSem M prover fnTable rTable) (ROp.occurrence M op).path
    (Env.positional (aloneIn M prover
      (.cons (a := samplesStateTy heldP) (att, (seq, (heldTuple, ()))) .nil)))).SafeWith
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

private theorem buildSamplesClauses_emits_any {a : Admitted V} {heldP : List V.Ty}
    {htfree : Tys.anyLinear V (samplesStateTys heldP) = false}
    {prover : Role} {sKey : Key}
    {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256}
    {declKey : Key} {opOk : ROp M → Prop} :
    ∀ (es : List (ShapeEvent V))
      {cS : List (Clause V a.program.headers prover (samplesStateTy heldP))},
      buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey es = .ok cS →
      ∀ c ∈ cS, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) opOk c
  | [], _, h => by cases h; exact fun _ hc => nomatch hc
  | e :: rest, cS, h => by
      unfold buildSamplesClauses at h
      cases hRec : buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihS := buildSamplesClauses_emits_any (opOk := opOk) rest hRec
          cases hCls : e.cls with
          | flow _ _ _ => rw [hCls] at h; cases h; exact ihS
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | request _ => cases h; exact ihS
              | coin law =>
                  cases hearers with
                  | cons _ _ => cases h; exact ihS
                  | nil =>
                      dsimp only at h
                      split at h
                      · cases hS : findTypedFnRef a sKey (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [e.τ] with
                        | none => rw [hS] at h; cases h
                        | some sRef =>
                            rw [hS] at h; cases h
                            intro c hc
                            rcases List.mem_cons.mp hc with rfl | hm
                            · apply proverSampleClause_emits_any M
                            · exact ihS c hm
                      · cases h; exact ihS

private theorem buildSamplesLayer_covers {a : Admitted V} {entry : ProtocolHeader V}
    {prover : Role} {samplesKey : Option Key}
    {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256}
    {declKey : Key} {events : List (ShapeEvent V)} {opOk : ROp M → Prop}
    {sampP : Layer V a.program.headers prover entry.ins}
    (h : buildSamplesLayer a entry prover samplesKey sessBytes hSess declKey events = .ok (some sampP)) :
    Handler.Covers M
      (Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) sampP)
      opOk opOk := by
  unfold buildSamplesLayer at h
  cases samplesKey with
  | none => cases h
  | some sKey =>
      dsimp only at h
      cases hF : a.program.find sKey with
      | none => rw [hF] at h; cases h
      | some found =>
          rw [hF] at h
          cases found with
          | protocol _ => cases h
          | fn _ =>
              dsimp only at h
              split at h
              · rename_i htfree
                cases hC : buildSamplesClauses a (held prover entry.ins) htfree prover sKey
                    sessBytes hSess declKey events with
                | error _ => rw [hC] at h; cases h
                | ok cs =>
                    rw [hC] at h; cases h
                    have hEm := buildSamplesClauses_emits_any M (opOk := opOk) events hC
                    exact fun op s ho => clause_answer_covers M _ _ _ hEm op s (.inl ho)
              · cases h

private theorem buildConstructionClauses_go_covers {enc : VocabEncoder V} {a : Admitted V}
    {suite : ModuleRef} {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)),
      (∀ k p, es[k]? = some p → events[idx + k]? = some p.1) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absorbRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      (∀ c ∈ cP, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (LayoutInputP M prover verifier events) c) ∧
      (∀ c ∈ cV, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (LayoutInputV M prover verifier events) c) ∧
      (∀ op, ROp.MatchesShape M prover (es.map Prod.fst) op →
        LayoutInputP M prover verifier events op ∨ ∃ c ∈ cP, ClauseMatches M c op) ∧
      (∀ op, ROp.MatchesShape M verifier (es.map Prod.fst) op →
        LayoutInputV M prover verifier events op ∨ ∃ c ∈ cV, ClauseMatches M c op)
  | _, [], _, _, _, h => by
      cases h
      refine ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), ?_, ?_⟩
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl (.inl trivial)
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl (.inl trivial)
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
  | idx, (e, needAbs) :: rest, hSuf, cP, cV, h => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k p, rest[k]? = some p → events[(idx + 1) + k]? = some p.1 := by
        intro k p hk
        have := hSuf (k + 1) p hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by
        simpa using hSuf 0 (e, needAbs) rfl
      have hMem : e ∈ events := List.mem_of_getElem? hIdx
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absorbRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihEmP, ihEmV, ihCovP, ihCovV⟩ :=
            buildConstructionClauses_go_covers hNe (idx + 1) rest hSufRest hRec
          have liftRestP : ∀ op, (∃ e' ∈ rest.map Prod.fst, ROp.MatchesShapeEvent M prover e' op) →
              LayoutInputP M prover verifier events op ∨ ∃ c ∈ pair.1, ClauseMatches M c op := by
            intro op ho
            apply ihCovP op
            cases op with
            | «begin» | settle => trivial
            | give | get | own | hear => exact ho
          have liftRestV : ∀ op, (∃ e' ∈ rest.map Prod.fst, ROp.MatchesShapeEvent M verifier e' op) →
              LayoutInputV M prover verifier events op ∨ ∃ c ∈ pair.2, ClauseMatches M c op := by
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
                cases needAbs with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h
                    refine ⟨ihEmP, ihEmV, ?_, ?_⟩
                    · intro op ho
                      cases op with
                      | «begin» | settle => exact .inl (.inl trivial)
                      | give k' gs' at_ τ' x' =>
                          obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            exact .inl (.inr (.inl ⟨e', hMem, hSite, hTy, hPVFlow.1 ▸ hCls, hPVFlow.2⟩))
                          · exact liftRestP (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; exact absurd hPVFlow.1 hNeG
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
                          · rw [hCls] at hECls; cases hECls; exact absurd hPVFlow.1.symm hNe
                          · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                      | get k' g' at_ τ' =>
                          obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls
                            exact .inl (.inr (.inl ⟨e', hMem, hPVFlow.1, hSite, hTy, getters, hPVFlow.2, hPVFlow.1 ▸ hCls⟩))
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
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some encRef =>
                        rw [hEnc] at h; cases h
                        refine ⟨?_, ?_, ?_, ?_⟩
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
                              · rw [hCls] at hECls; cases hECls; exact absurd hPVFlow.1 hNeG
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
                  refine ⟨ihEmP, ihEmV, ?_, ?_⟩
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
                          cases hDer : findSuiteDerive enc a suite stateTy law sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                rcases sig with ⟨sIns, sOut⟩
                                dsimp only at hIns
                                subst hIns
                                refine ⟨?_, ?_, ?_, ?_⟩
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
                      cases h
                      refine ⟨ihEmP, ihEmV, ?_, ?_⟩
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
                            · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl (.inl trivial)
                            · exact liftRestP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                        | hear gk ow' at_ τ' =>
                            obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                            rcases List.mem_cons.mp he' with rfl | hmem
                            · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
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
                    refine ⟨ihEmP, ihEmV, ?_, ?_⟩
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
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)),
      (∀ k p, es[k]? = some p → events[idx + k]? = some p.1) →
      ∀ {cV : List (Clause V a.program.headers verifier (idealPathTy unitTy))},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
        declKey events idx es = .ok cV →
      (∀ c ∈ cV, ClauseEmits M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (LayoutInputV M prover verifier events) c) ∧
      (∀ op, ROp.MatchesShape M verifier (es.map Prod.fst) op →
        LayoutInputV M prover verifier events op ∨ ∃ c ∈ cV, ClauseMatches M c op)
  | _, [], _, _, h => by
      cases h
      refine ⟨(fun _ hc => nomatch hc), fun op ho => ?_⟩
      cases op with
      | «begin» | settle => exact .inl (.inl trivial)
      | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
  | idx, (e, needAbs) :: rest, hSuf, cV, h => by
      unfold buildIdealVerifierClauses.go at h
      have hSufRest : ∀ k p, rest[k]? = some p → events[(idx + 1) + k]? = some p.1 := by
        intro k p hk
        have := hSuf (k + 1) p hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 (e, needAbs) rfl
      have hMem : e ∈ events := List.mem_of_getElem? hIdx
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihEmV, ihCovV⟩ := buildIdealVerifierClauses_go_covers hNe (idx + 1) rest hSufRest hRec
          have liftRestV : ∀ op, (∃ e' ∈ rest.map Prod.fst, ROp.MatchesShapeEvent M verifier e' op) →
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
                cases needAbs with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h
                    refine ⟨ihEmV, fun op ho => ?_⟩
                    cases op with
                    | «begin» | settle => exact .inl (.inl trivial)
                    | give k' gs' at_ τ' x' =>
                        obtain ⟨e', he', hSite, hTy, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls; exact absurd hPVFlow.1.symm hNe
                        · exact liftRestV (.give k' gs' at_ τ' x') ⟨e', hmem, hSite, hTy, hECls⟩
                    | get k' g' at_ τ' =>
                        obtain ⟨e', he', hNeG, hSite, hTy, gs', hrIn, hECls⟩ := ho
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                          exact .inl (.inr (.inl ⟨e', hMem, hPVFlow.1, hSite, hTy, getters, hPVFlow.2, hPVFlow.1 ▸ hCls⟩))
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
                | true =>
                    simp only [↓reduceIte] at h
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
                            show ((idealAbsorbClause hfree verifier prover e.site kind (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef).code.denote
                              (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                              (ROp.occurrence M op).path
                              (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith
                                M (fun _ _ => True) (LayoutInputV M prover verifier events) (fun _ => True) (fun _ => True)
                            rw [idealAbsorbClause_denote]
                            refine ⟨.inr (.inl ⟨e, hMem, rfl, (site_from_match hMatch.1).symm, rfl,
                              getters, hPVFlow.2, hPVFlow.1 ▸ hCls⟩), fun _ _ => ?_⟩
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
                                exact .inr ⟨_, List.mem_cons_self, hSite, by dsimp only [idealAbsorbClause, ROp.part]; rw [hPVFlow.1],
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
                                      show ((idealDeriveClause hfree verifier prover e.site (.own (.coin law) hearers) []
                                        serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                        (drawLabel e.site) (drawLabel_bytes e.site) encRef).code.denote
                                        (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                                        (ROp.occurrence M op).path
                                        (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith
                                          M (fun _ _ => True) (LayoutInputV M prover verifier events) (fun _ => True) (fun _ => True)
                                      rw [idealDeriveClause_denote_nil]
                                      refine ⟨.inl trivial, fun _ _ => ?_⟩
                                      refine ⟨.inr (.inr ⟨idx, e, hIdx, rfl,
                                        site_told_from_match hMatch.1, rfl, law, hearers,
                                        hCoin.1 ▸ hCls, hCoin.2⟩), fun _ _ => ?_⟩
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

private theorem checkAuthoredEvents_covers {prover verifier : Role}
    (hNe : prover ≠ verifier) {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (es : List (ShapeEvent V)), (∀ e ∈ es, e ∈ events) →
      checkAuthoredEvents prover verifier declKey es = .ok () →
      (∀ op, ROp.MatchesShape M prover es op → LayoutInputP M prover verifier events op) ∧
      (∀ op, ROp.MatchesShape M verifier es op → LayoutInputV M prover verifier events op)
  | [], _, h => by
      cases h
      refine ⟨?_, ?_⟩
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl trivial
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
      · intro op ho
        cases op with
        | «begin» | settle => exact .inl trivial
        | give | get | own | hear => obtain ⟨_, hc, _⟩ := ho; cases hc
  | e :: rest, hSub, h => by
      unfold checkAuthoredEvents at h
      have hSubRest : ∀ e' ∈ rest, e' ∈ events := fun e' he' => hSub e' (List.mem_cons_of_mem _ he')
      have hMem : e ∈ events := hSub e List.mem_cons_self
      cases hRec : checkAuthoredEvents prover verifier declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok u =>
          cases u
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := checkAuthoredEvents_covers hNe rest hSubRest hRec
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
                refine ⟨?_, ?_⟩
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
                    cases h
                    refine ⟨?_, ?_⟩
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
                          · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl trivial
                          · exact liftP (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
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
                          · rw [hCls] at hECls; cases hECls; subst hNil; exact .inl trivial
                          · exact liftV (.own gk hs' at_ ins' pl' τ') ⟨e', hmem, hSite, hTy, hECls, hTyped⟩
                      | hear gk ow' at_ τ' =>
                          obtain ⟨e', he', hNeO, hSite, hTy, hs', hrIn, hECls⟩ := ho
                          rcases List.mem_cons.mp he' with rfl | hmem
                          · rw [hCls] at hECls; cases hECls; subst hNil; cases hrIn
                          · exact liftV (.hear gk ow' at_ τ') ⟨e', hmem, hNeO, hSite, hTy, hs', hrIn, hECls⟩
                  · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · rename_i hReq
                    cases h
                    refine ⟨?_, ?_⟩
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
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
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
  cases buildLayoutLayers_ok_elim h with
  | streaming w hLayP hLayV =>
      subst hLayP; subst hLayV
      obtain ⟨hEmP, hEmV, hFP, hFV, hTold⟩ := buildStreamingLayoutClauses_go_covers M 0 events w.hStr
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
                  exact .inr (hTold idx e hIdx law hearers at_ τ x hCls hIn hTy (by simpa using hSite)).1
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
                  exact .inr (hTold idx e hIdx law hearers at_ τ x hCls hIn hTy (by simpa using hSite)).2
              | rows | opening => exact False.elim hTd
          | get | own | hear | «begin» | settle => exact False.elim hTd
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
                            exact .inr (hToldP idx e hIdx law hearers at_ τ x hCls hIn hTy (by simpa using hSite))
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
                            exact .inr (hToldV idx e hIdx law hearers at_ τ x hCls hIn hTy (by simpa using hSite))
                        | rows | opening => exact False.elim hTd
                    | get | own | hear | «begin» | settle => exact False.elim hTd
          · cases hComp

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

private theorem stack_covers_cast_ins {a : Admitted V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V a.program.headers r₂ hdr₂.ins))
    (h : Handler.Covers M
      (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) layers)
      (ROp.MatchesShape M r₂ (hdr₂.shape.events [] id)) (ROp.IsClosed M)) :
    Handler.Covers M
      (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (hr ▸ (congrArg ProtocolHeader.ins hHdr) ▸ layers))
      (ROp.MatchesShape M r₁ (hdr₁.shape.events [] id)) (ROp.IsClosed M) := by
  subst hHdr; subst hr; exact h

/-- Every non-interactive deployment covers all non-closed effects on both prover and verifier. -/
theorem deploy_coverage (enc : VocabEncoder V) {a : Admitted V} {declaration : Declaration}
    {d : Deployed V} (hDep : deploy enc a declaration = .ok d)
    (hNonInt : declaration.interactive = false) : d.Covered := by
  intro M prover verifier hRoles r hRole ins taken _ _
  rw [deployed_run_eq_runStack]
  apply runStack_closedEffects M d.admitted d.callee d.retry r (d.stack r) _ ins taken
  cases deploy_ok_elim enc a declaration d hDep with
  | interactive w _ => simp [Declaration.interactive, w.hCon] at hNonInt
  | authored w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      obtain ⟨hAuthP, hAuthV⟩ := checkAuthoredEvents_covers M w.hNe _ (fun _ h => h) w.hAuth
      obtain ⟨hLayP, hLayV⟩ := buildLayoutLayers_covers M w.hLay
      have hLayP' : Handler.Covers M (Layer.handler M (Defs.fnTable M a.program.defs)
          (Defs.rTable M a.program.defs) w.layP)
          (ROp.MatchesShape M w.prover (w.foundPair.1.shape.events [] id)) (ROp.IsClosed M) :=
        fun op s ho => hLayP op s (hAuthP op ho)
      have hLayV' : Handler.Covers M (Layer.handler M (Defs.fnTable M a.program.defs)
          (Defs.rTable M a.program.defs) w.layV)
          (ROp.MatchesShape M w.verifier (w.foundPair.1.shape.events [] id)) (ROp.IsClosed M) :=
        fun op s ho => hLayV op s (hAuthV op ho)
      rcases hRole with rfl | rfl
      · dsimp only; rw [dite_eq_left rfl]
        apply stack_covers_cast M (by simp [w.hFound]) rfl
        exact stack_handler_covers_cons M _ _ hLayP' (stack_handler_covers_nil M _ _ _)
      · dsimp only; rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl]
        apply stack_covers_cast M (by simp [w.hFound]) rfl
        exact stack_handler_covers_cons M _ _ hLayV' (stack_handler_covers_nil M _ _ _)
  | derived w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hFst := eventsWithAbsorb_fst w.prover w.verifier [] id false w.foundPair.1.shape
      obtain ⟨hEmP, hEmV, hCovP, hCovV⟩ := buildConstructionClauses_go_covers M w.hNe 0 _
        (fun k p hk => by rw [Nat.zero_add, ← hFst, List.getElem?_map, hk]; rfl) w.hCC
      rw [hFst] at hCovP hCovV
      obtain ⟨hLayP, hLayV⟩ := buildLayoutLayers_covers M w.hLay
      rcases hRole with rfl | rfl
      · dsimp only; rw [dite_eq_left rfl]
        apply stack_covers_cast_ins M (by simp [w.hFound]) rfl
        have hConP : Handler.Covers M
            (Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              ({ line := .construction, state := w.stateTy, takes := [], gives := [],
                 clauses := w.cPClauses, again := restoreAgain w.stateTy,
                 start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP,
                 finish := emptyFinish w.stateTy } :
                Layer V a.program.headers w.prover w.foundPair.1.ins))
            (ROp.MatchesShape M w.prover (w.foundPair.1.shape.events [] id))
            (LayoutInputP M w.prover w.verifier (w.foundPair.1.shape.events [] id)) :=
          fun op s ho => clause_answer_covers M _ _ _ hEmP op s (hCovP op ho)
        cases hS : w.prep.sampLayer with
        | none =>
            exact stack_handler_covers_cons M _ _ hConP
              (stack_handler_covers_cons M _ _ hLayP (stack_handler_covers_nil M _ _ _))
        | some sampP =>
            have hSamp := buildSamplesLayer_covers M
              (opOk := ROp.MatchesShape M w.prover (w.foundPair.1.shape.events [] id))
              (hS ▸ w.prep.hSamp)
            exact stack_handler_covers_cons M _ _ hSamp
              (stack_handler_covers_cons M _ _ hConP
                (stack_handler_covers_cons M _ _ hLayP (stack_handler_covers_nil M _ _ _)))
      · dsimp only; rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl]
        apply stack_covers_cast_ins M (by simp [w.hFound]) rfl
        have hConV : Handler.Covers M
            (Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              ({ line := .construction, state := w.stateTy, takes := [], gives := [],
                 clauses := w.cVClauses, again := restoreAgain w.stateTy,
                 start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtV,
                 finish := emptyFinish w.stateTy } :
                Layer V a.program.headers w.verifier w.foundPair.1.ins))
            (ROp.MatchesShape M w.verifier (w.foundPair.1.shape.events [] id))
            (LayoutInputV M w.prover w.verifier (w.foundPair.1.shape.events [] id)) :=
          fun op s ho => clause_answer_covers M _ _ _ hEmV op s (hCovV op ho)
        exact stack_handler_covers_cons M _ _ hConV
          (stack_handler_covers_cons M _ _ hLayV (stack_handler_covers_nil M _ _ _))

/-- An ideal random-oracle deployment's verifier asks the world only closed effects (its own
private coins, service requests — including `serviceKey` — and local attempt marks). -/
theorem deployIdeal_verifier_covered (enc : VocabEncoder V) (serviceKey : Key)
    {a : Admitted V} {declaration : Declaration} {d : Deployed V}
    (hDep : deployIdeal enc serviceKey a declaration = .ok d)
    (M : Model V) (prover verifier : Role) (hRoles : d.roles = some (prover, verifier))
    (ins : HList (RV M verifier) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack verifier))) :
    Process.ClosedEffects (d.run M verifier ins taken) := by
  rw [deployed_run_eq_runStack]
  apply runStack_closedEffects M d.admitted d.callee d.retry verifier (d.stack verifier) _ ins taken
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration d hDep
  subst hEq
  have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
    simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
  rw [w.hPV] at hRolesEq; cases hRolesEq
  have hFst := eventsWithAbsorb_fst w.prover w.verifier [] id false w.foundPair.1.shape
  obtain ⟨hEmV, hCovV⟩ := buildIdealVerifierClauses_go_covers M w.hNe 0 _
    (fun k p hk => by rw [Nat.zero_add, ← hFst, List.getElem?_map, hk]; rfl) w.hIV
  rw [hFst] at hCovV
  obtain ⟨_, hLayV⟩ := buildLayoutLayers_covers M w.hLay
  dsimp only; rw [dite_eq_left rfl]
  apply stack_covers_cast_ins M (by simp [w.hFound]) rfl
  have hConV : Handler.Covers M
      (Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        ({ line := .construction, state := idealPathTy w.suiteUnitTy, takes := [], gives := [],
           clauses := w.idealVClauses, again := restoreAgain (idealPathTy w.suiteUnitTy),
           start := idealStart w.hSuiteFree w.sessBytes w.hSessBytes w.stmtV,
           finish := emptyFinish (idealPathTy w.suiteUnitTy) } :
          Layer V a.program.headers w.verifier w.foundPair.1.ins))
      (ROp.MatchesShape M w.verifier (w.foundPair.1.shape.events [] id))
      (LayoutInputV M w.prover w.verifier (w.foundPair.1.shape.events [] id)) :=
    fun op s ho => clause_answer_covers M _ _ _ hEmV op s (hCovV op ho)
  exact stack_handler_covers_cons M _ _ hConV
    (stack_handler_covers_cons M _ _ hLayV (stack_handler_covers_nil M _ _ _))

end Coverage

end Zkc.Core
