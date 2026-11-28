module

public import Zkc.Core.Scheme.Deploy.Elim

@[expose] public section

/-!
Shared clause-matching helpers and validity safety (`deploy_safe`, `deployIdeal_safe`).
-/

namespace Zkc.Core

open LayerBuild

/-! ## Shared clause-matching and occurrence helpers -/

section MatchHelpers

variable {V : Vocabulary} (M : Model V)

/-- Whether a clause `c` matches effect `op`. -/
def ClauseMatches {hs : Headers V} {r : Role} {state : V.Ty}
    (c : Clause V hs r state) (op : ROp M) : Prop :=
  c.site.site = (ROp.occurrence M op).site ∧ some c.site.part = ROp.part M op ∧
    c.site.takes = ROp.takes M op ∧ c.site.gives = ROp.gives M op

theorem site_from_match {occ : Occurrence} {s : Site} (h : s = occ.site) :
    (⟨occ.path, s.key⟩ : Occurrence).site = s := by
  have h1 : s.through = Frame.applications occ.path := congrArg Site.through h
  cases s with
  | mk through key =>
      dsimp only [Occurrence.site] at h1 ⊢
      rw [← h1]

theorem site_told_from_match {occ : Occurrence} {s : Site} {k : Key} (h : s = occ.site) :
    (⟨occ.path, k⟩ : Occurrence).site = ⟨s.through, k⟩ := by
  have h1 : s.through = Frame.applications occ.path := congrArg Site.through h
  dsimp only [Occurrence.site]
  rw [← h1]

end MatchHelpers

/-! ## Validity safety (`deploy_safe`, `deployIdeal_safe`) -/

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

private theorem idealAbsorbClause_validSafe (a : Admitted V) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef) := by
  intro path args st _ hst
  cases args
  show ((idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef).code.denote
    (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
  rw [idealAbsorbClause_denote]
  refine ⟨trivial, fun msg hmsg => ?_⟩
  dsimp only
  obtain ⟨enc, henc, hencV⟩ := encodeRef.eval_done M a (.cons msg .nil) ⟨hmsg, trivial⟩
  have hTagLbl : ∀ b, b ∈ (2 :: label) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hm
    · exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 253))
    · exact hlabel b hm
  have hencS : M.Valid (.seq unitTy none) enc.single := by
    cases enc with | cons e en => cases en; exact hencV.1
  rw [henc]
  dsimp only [liftLocal_done, Process.map]
  change (aloneOut M verifier (aloneIn M verifier (.cons msg (.cons (idealPathPush M st (2 :: label) enc.single) .nil)))).All M.Valid
  rw [aloneOut_aloneIn]
  exact ⟨hmsg, idealPathPush_valid M st (2 :: label) enc.single hst hTagLbl hencS, trivial⟩

private theorem idealDeriveClause_nil_validSafe (a : Admitted V) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (part : Part V)
    (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (idealDeriveClause hfree verifier prover site part [] serviceKey reqKey toldKey
        label hlabel encodeRef) := by
  intro path args st _ hst
  cases args
  show ((idealDeriveClause hfree verifier prover site part [] serviceKey reqKey toldKey
      label hlabel encodeRef).code.denote
    (roleSem M verifier (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M verifier out).All M.Valid) (· ≠ .undefined)
  rw [idealDeriveClause_denote_nil]
  have hlblV : M.Valid bytesTy label := ⟨hlabel, (fun _ h => nomatch h)⟩
  refine ⟨⟨⟨hst, hlblV, trivial⟩, trivial⟩, fun coin hcoin => ?_⟩
  refine ⟨hcoin, fun _ _ => ?_⟩
  obtain ⟨enc, henc, hencV⟩ := encodeRef.eval_done M a (.cons coin .nil) ⟨hcoin, trivial⟩
  have hTagLbl : ∀ b, b ∈ (3 :: label) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hm
    · exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 252)))
    · exact hlabel b hm
  have hencS : M.Valid (.seq unitTy none) enc.single := by
    cases enc with | cons e en => cases en; exact hencV.1
  dsimp only
  rw [henc]
  dsimp only [liftLocal_done, Process.map]
  change (aloneOut M verifier (aloneIn M verifier (.cons coin (.cons (idealPathPush M st (3 :: label) enc.single) .nil)))).All M.Valid
  rw [aloneOut_aloneIn]
  exact ⟨hcoin, idealPathPush_valid M st (3 :: label) enc.single hst hTagLbl hencS, trivial⟩

private theorem proverSampleClause_validSafe (a : Admitted V) {heldP : List V.Ty} {τ : V.Ty}
    (htfree : Tys.anyLinear V (samplesStateTys heldP) = false)
    (prover : Role) (site : Site) (law : V.LawKey)
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (siteBytes : List Nat) (hsite : ∀ b, b ∈ siteBytes → b < 256)
    (sampleRef : TypedFnRef V a.program.headers.fns (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) :
    ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
      (proverSampleClause htfree prover site law sessionBytes hsess siteBytes hsite sampleRef) := by
  intro path args st _ hst
  cases args
  rcases st with ⟨att, seq, heldTuple, ⟨⟩⟩
  show ((proverSampleClause htfree prover site law sessionBytes hsess siteBytes hsite sampleRef).code.denote
    (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)) path
    (Env.positional (aloneIn M prover
      (.cons (a := samplesStateTy heldP) (att, (seq, (heldTuple, ()))) .nil)))).SafeWith M
      (ValidReply M) (ROp.ValidPayload M) (fun out => (aloneOut M prover out).All M.Valid) (· ≠ .undefined)
  rw [proverSampleClause_denote]
  have hArgsV : (HList.append
      (cast (congrArg (HList M.Val) (tysOfList_toList heldP))
        (Tys.toHList M (tysOfList heldP) heldTuple))
      (.cons (a := bytesTy) sessionBytes (.cons (a := bytesTy) siteBytes
        (.cons (a := Ty.nat) att (.cons (a := Ty.nat) seq .nil))))).All M.Valid := by
    apply hlist_all_append
    · exact hlist_all_cast (tysOfList_toList heldP) (tys_toHList_valid M (tysOfList heldP) heldTuple hst.2.2.1)
    · exact ⟨⟨hsess, fun _ h => nomatch h⟩, ⟨hsite, fun _ h => nomatch h⟩, trivial, trivial, trivial⟩
  obtain ⟨coin, hcoin, hcoinV⟩ := sampleRef.eval_done M a _ hArgsV
  rw [hcoin]
  change (aloneOut M prover (aloneIn M prover
    (.cons coin.single (.cons (a := samplesStateTy heldP) (att, (seq + 1, (heldTuple, ()))) .nil)))).All M.Valid
  rw [aloneOut_aloneIn]
  have hcS : M.Valid τ coin.single := by
    cases coin with | cons c cn => cases cn; exact hcoinV.1
  exact ⟨hcS, ⟨trivial, trivial, hst.2.2.1, trivial⟩, trivial⟩

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

private theorem buildSamplesClauses_validSafe {a : Admitted V} {heldP : List V.Ty}
    {htfree : Tys.anyLinear V (samplesStateTys heldP) = false}
    {prover : Role} {sKey : Key}
    {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256} {declKey : Key} :
    ∀ (es : List (ShapeEvent V))
      {cS : List (Clause V a.program.headers prover (samplesStateTy heldP))},
      buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey es = .ok cS →
      ∀ c ∈ cS, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c
  | [], _, h => by cases h; exact fun _ hc => nomatch hc
  | e :: rest, cS, h => by
      unfold buildSamplesClauses at h
      cases hRec : buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihS := buildSamplesClauses_validSafe rest hRec
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
                      · cases hLaw : V.law law with
                        | none => rw [hLaw] at h; cases h
                        | some sig =>
                            rw [hLaw] at h
                            cases sig with
                            | mk sIns sOut =>
                                cases sIns with
                                | cons _ _ => cases h
                                | nil =>
                                    dsimp only at h
                                    split at h
                                    · cases hS : findTypedFnRef a sKey (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [e.τ] with
                                      | none => rw [hS] at h; cases h
                                      | some sRef =>
                                          rw [hS] at h; cases h
                                          intro c hc
                                          rcases List.mem_cons.mp hc with rfl | hm
                                          · apply proverSampleClause_validSafe M a
                                          · exact ihS c hm
                                    · cases h
                      · cases h; exact ihS

private theorem buildConstructionClauses_go_validSafe {enc : VocabEncoder V} {a : Admitted V}
    {suite : ModuleRef} {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absorbRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      (∀ c ∈ cP, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c) ∧
      (∀ c ∈ cV, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c)
  | _, [], _, _, h => by
      cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, (e, needAbs) :: rest, cP, cV, h => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absorbRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := buildConstructionClauses_go_validSafe (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h; exact ⟨ihP, ihV⟩
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some encRef =>
                        rw [hEnc] at h; cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · apply proverAbsorbClause_validSafe M a
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · apply verifierAbsorbClause_validSafe M a
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
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive enc a suite stateTy law sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                refine ⟨fun c hc => ?_, fun c hc => ?_⟩
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
                    · cases h; exact ⟨ihP, ihV⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV⟩
                  · cases h

private theorem buildIdealVerifierClauses_go_validSafe {a : Admitted V} {suite : ModuleRef}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cV : List (Clause V a.program.headers verifier (idealPathTy unitTy))},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ c ∈ cV, ClauseValidSafe M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) c
  | _, [], _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, (e, needAbs) :: rest, cV, h => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihV := buildIdealVerifierClauses_go_validSafe (idx + 1) rest hRec
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
                        rcases List.mem_cons.mp hc with rfl | hm
                        · apply idealAbsorbClause_validSafe M a
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
  cases buildLayoutLayers_ok_elim h with
  | streaming w hLayP hLayV =>
      subst hLayP; subst hLayV
      obtain ⟨hP, hV⟩ := buildStreamingLayoutClauses_go_validSafe M 0 events w.hStr
      refine ⟨⟨⟨clause_answer_validSafe M _ _ _ hP,
                fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩,
              ⟨⟨clause_answer_validSafe M _ _ _ hV,
                fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩⟩
      · intro inputs t _ _
        cases t; dsimp only [HList.append]; rw [layoutPStart_denote]
        exact ⟨⟨(fun _ hu => nomatch hu), (fun _ hu => nomatch hu)⟩, trivial⟩
      · intro s hs; rw [identityFinish_denote]; exact ⟨hs, trivial⟩
      · intro inputs t _ ht
        cases t with
        | cons proof pn =>
            cases pn
            change ((layoutVStart w.unitTy).denote
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
                have hP := collectCompactWire_validSafe M 0 events hCW
                have hV := buildCompactVClauses_validSafe M 0 events hVC
                refine ⟨⟨⟨clause_answer_validSafe M _ _ _ hP,
                          fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩,
                        ⟨⟨clause_answer_validSafe M _ _ _ hV,
                          fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩⟩
                · intro inputs t _ _
                  cases t; dsimp only [HList.append]; rw [layoutPStart_denote]
                  exact ⟨⟨(fun _ hu => nomatch hu), (fun _ hu => nomatch hu)⟩, trivial⟩
                · intro s hs; rw [identityFinish_denote]; exact ⟨hs, trivial⟩
                · intro inputs t hin ht
                  cases t with
                  | cons proof pn =>
                      cases pn
                      refine compactStart_cast_safe M (Defs.fnTable M a.program.defs) (by simp) _ _ ?_
                      exact compactLayoutVStart_safe M a w.unitTy w.hfree _ _ _ proof ht.1
                        (heldValues M verifier inputs) (heldValues_valid M verifier inputs hin)
                · intro s _; rw [emptyFinish_denote]; trivial
          · cases hComp

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

private theorem layer_validSafe_idealConstruction {a : Admitted V} {unitTy : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    {r : Role} {ins : List (LTy V)}
    (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
    (stmtItems : List (StmtAbsorbItem V a.program.headers.fns unitTy (Ctx.positional (held r ins))))
    (clauses : List (Clause V a.program.headers r (idealPathTy unitTy)))
    (hClauses : ∀ c ∈ clauses, ClauseValidSafe M (Defs.fnTable M a.program.defs)
      (Defs.rTable M a.program.defs) c) :
    LayerValidSafe M a
      ({ line := .construction, state := idealPathTy unitTy, takes := [], gives := [],
         clauses := clauses, again := restoreAgain (idealPathTy unitTy),
         start := idealStart hfree sessBytes hSess stmtItems,
         finish := emptyFinish (idealPathTy unitTy) } : Layer V a.program.headers r ins) := by
  refine ⟨⟨clause_answer_validSafe M _ _ _ hClauses,
            fun _ e _ he _ => by dsimp only [Layer.handler]; rw [restoreAgain_denote]; exact he⟩, ?_, ?_⟩
  · intro inputs t hin _
    cases t
    dsimp only [HList.append]
    obtain ⟨stEnd, hDone, hStV⟩ := idealStart_done M a hfree sessBytes hSess
      stmtItems (heldValues M r inputs) (heldValues_valid M r inputs hin)
    rw [hDone]
    exact ⟨hStV, trivial⟩
  · intro s _
    rw [emptyFinish_denote]
    trivial

private theorem buildSamplesLayer_validSafe {a : Admitted V} {entry : ProtocolHeader V}
    {prover : Role} {samplesKey : Option Key}
    {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256}
    {declKey : Key} {events : List (ShapeEvent V)}
    {sampP : Layer V a.program.headers prover entry.ins}
    (h : buildSamplesLayer a entry prover samplesKey sessBytes hSess declKey events = .ok (some sampP)) :
    LayerValidSafe M a sampP := by
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
                    have hCS := buildSamplesClauses_validSafe M events hC
                    refine ⟨⟨clause_answer_validSafe M _ _ _ hCS, fun i e stop _ hstop => ?_⟩, ?_, ?_⟩
                    · dsimp only [Layer.handler]
                      rw [samplesAgain_denote]
                      exact ⟨trivial, trivial, hstop.2.2.1, trivial⟩
                    · intro inputs t hin _
                      cases t
                      dsimp only [HList.append]
                      exact samplesStart_valid M _ (heldValues M prover inputs)
                        (heldValues_valid M prover inputs hin)
                    · intro s _; rw [emptyFinish_denote]; trivial
              · cases h

private theorem layer_validSafe_cast {a : Admitted V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V a.program.headers r₂ hdr₂.ins))
    (h : ∀ l ∈ layers, LayerValidSafe M a l) :
    ∀ l ∈ (hr ▸ hHdr ▸ layers), LayerValidSafe M a l :=
  cast_layer_stack_elim hHdr hr layers (fun _ _ ls => ∀ l ∈ ls, LayerValidSafe M a l) h

private theorem layer_validSafe_cast_ins {a : Admitted V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V a.program.headers r₂ hdr₂.ins))
    (h : ∀ l ∈ layers, LayerValidSafe M a l) :
    ∀ l ∈ (hr ▸ (congrArg ProtocolHeader.ins hHdr) ▸ layers), LayerValidSafe M a l := by
  subst hHdr; subst hr; exact h

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
  rw [deployed_run_eq_runStack]
  cases deploy_ok_elim enc a declaration d hDep with
  | interactive w hEq =>
      subst hEq
      exact runStack_validSafe M hAdmit _ _ r [] (fun _ hl => nomatch hl) ins taken hIns hTaken
  | authored w hEq =>
      subst hEq
      apply runStack_validSafe M hAdmit _ _ r _ _ ins taken hIns hTaken
      obtain ⟨hLP, hLV⟩ := buildLayoutLayers_validSafe M w.hLay
      dsimp only [Deployed.entry]
      by_cases hP : r = w.prover
      · rw [dite_eq_left hP]
        apply layer_validSafe_cast M (by simp [w.hFound]) hP
        intro l hl; simp only [List.mem_singleton] at hl; subst hl; exact hLP
      · rw [dite_eq_right hP]
        by_cases hV : r = w.verifier
        · rw [dite_eq_left hV]
          apply layer_validSafe_cast M (by simp [w.hFound]) hV
          intro l hl; simp only [List.mem_singleton] at hl; subst hl; exact hLV
        · rw [dite_eq_right hV]; intro _ hl; cases hl
  | derived w hEq =>
      subst hEq
      apply runStack_validSafe M hAdmit _ _ r _ _ ins taken hIns hTaken
      obtain ⟨hCP, hCV⟩ := buildConstructionClauses_go_validSafe M 0 _ w.hCC
      obtain ⟨hLP, hLV⟩ := buildLayoutLayers_validSafe M w.hLay
      dsimp only [Deployed.entry]
      by_cases hP : r = w.prover
      · rw [dite_eq_left hP]
        apply layer_validSafe_cast_ins M (by simp [w.hFound]) hP
        cases hS : w.prep.sampLayer with
        | none =>
            intro l hl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact layer_validSafe_construction M _ _ _ _ _ _ hCP
            · exact hLP
        | some sampP =>
            have hSamp := buildSamplesLayer_validSafe M (hS ▸ w.prep.hSamp)
            intro l hl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl | rfl
            · exact hSamp
            · exact layer_validSafe_construction M _ _ _ _ _ _ hCP
            · exact hLP
      · rw [dite_eq_right hP]
        by_cases hV : r = w.verifier
        · rw [dite_eq_left hV]
          apply layer_validSafe_cast_ins M (by simp [w.hFound]) hV
          intro l hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact layer_validSafe_construction M _ _ _ _ _ _ hCV
          · exact hLV
        · rw [dite_eq_right hV]; intro _ hl; cases hl

/-- Every role of an ideal random-oracle deployment never stops `.undefined` on valid inputs,
valid taken values, and permitted replies. -/
theorem deployIdeal_safe (enc : VocabEncoder V) (serviceKey : Key)
    {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (hAdmit : admit named assoc = .ok a)
    {declaration : Declaration} {d : Deployed V}
    (hDep : deployIdeal enc serviceKey a declaration = .ok d)
    (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r)))
    (hIns : ins.All (RV.Valid M r)) (hTaken : taken.All M.Valid) :
    (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined) := by
  rw [deployed_run_eq_runStack]
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration d hDep
  subst hEq
  apply runStack_validSafe M hAdmit _ _ r _ _ ins taken hIns hTaken
  have hCV := buildIdealVerifierClauses_go_validSafe M 0 _ w.hIV
  obtain ⟨_, hLV⟩ := buildLayoutLayers_validSafe M w.hLay
  dsimp only [Deployed.entry]
  by_cases hV : r = w.verifier
  · rw [dite_eq_left hV]
    apply layer_validSafe_cast_ins M (by simp [w.hFound]) hV
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact layer_validSafe_idealConstruction M w.hSuiteFree _ _ _ _ hCV
    · exact hLV
  · rw [dite_eq_right hV]; intro _ hl; cases hl

end ValiditySafety


end Zkc.Core
