module

public import Zkc.Core.Scheme.Layer.StartLemmas

@[expose] public section

/-!
Exact denotation and event-key lemmas for every generated `Clause` builder.
-/

namespace Zkc.Core

namespace LayerBuild

section
variable {V : Vocabulary} (M : Model V)

/-! ## Exact denotation lemmas for every generated `Clause` -/

theorem layoutDropClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (path : List Frame) (x : M.Val τ) (s : M.Val stateTy) :
    (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters).code.denote
      (roleSem M r fnTable rTable) path (Env.positional (aloneIn M r (.cons x (.cons s .nil)))) =
      .done (aloneIn M r (.cons s .nil)) := by
  unfold layoutDropClause
  dsimp only
  erw [Term.denote_ret]
  show Process.done (HList.cons ((Env.positional _).get _) HList.nil) = _
  erw [env_get_positional_alone_1 M r x s .nil _ rfl]
  rfl

theorem layoutPWriteClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (writeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (path : List Frame) (msg : M.Val τ) (buf : List (M.Val unitTy)) :
    (layoutPWriteClause prover site kind getters writeRef).code.denote
      (roleSem M prover fnTable rTable) path
      (Env.positional (aloneIn M prover (.cons msg (.cons buf .nil)))) =
      (liftLocal id (writeRef.eval M fnTable (.cons msg .nil))).map fun chunk =>
        aloneIn M prover (.cons (buf ++ (chunk.single : List (M.Val unitTy))) .nil) := by
  unfold layoutPWriteClause
  dsimp only
  refine (letOp1_computeAlone1_eq M prover fnTable rTable _ _ _ msg _ _ _ _ _
    (by exact env_get_positional_alone_0 M prover msg (HList.cons (a := Ty.seq unitTy none) buf .nil) _ rfl)).trans ?_
  change (liftLocal id (writeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext chunk
  cases chunk with
  | cons ch chNil =>
      cases chNil
      refine (letOp1_computeAlone2_eq M prover fnTable rTable _ _ _ _ buf ch _ _ _ _ _
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
          exact env_get_positional_alone_1 M prover (τ₁ := Ty.seq unitTy none) msg buf .nil _ rfl)
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      change (liftLocal id (ownedOp M (.seqConcat unitTy none none) (.cons buf (.cons ch .nil)))).bind _ = _
      rw [ownedOp_seqConcat]
      dsimp only [liftLocal_done, Process.bind, HList.single]
      exact term_denote_ret1 M prover fnTable rTable _ _ _ _ (env_get_insert_eq _ _ _ rfl)

theorem layoutVReadClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (path : List Frame) (buf : List (M.Val unitTy)) (off : Nat) :
    (layoutVReadClause hfree verifier prover site kind readRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons (buf, (off, ())) .nil))) =
      (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).map fun res =>
        match res with
        | .cons v (.cons nextOff .nil) =>
            aloneIn M verifier (.cons v (.cons (buf, (nextOff, ())) .nil)) := by
  unfold layoutVReadClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by exact env_get_positional_alone_0 M verifier (τ := streamStateTy unitTy) (buf, (off, ())) .nil _ (by rfl))).trans ?_
  have htfree : Tys.anyLinear V (streamStateTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) .head htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M verifier (τ := streamStateTy unitTy) (buf, (off, ())) .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) (.tail .head) htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp2_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf off _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext res
  cases res with
  | cons v res1 =>
      cases res1 with
      | cons nextOff res2 =>
          cases res2
          refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf nextOff _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)
            (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
          dsimp only [localOp]
          refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
            (ownedOp_makeTuple M (streamStateTys unitTy) (.cons buf (.cons nextOff .nil))))) _).trans ?_
          dsimp only [Tys.ofHList, liftLocal_done, Process.bind, HList.single]
          exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)
            (env_get_insert_eq _ _ _ rfl)

theorem layoutVCarryClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (path : List Frame) (derived : M.Val τ) (buf : List (M.Val unitTy)) (off : Nat) :
    (layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons derived (.cons (buf, (off, ())) .nil)))) =
      (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).bind fun res =>
        match res with
        | .cons carried (.cons nextOff .nil) =>
            (liftLocal id (eqRef.eval M fnTable (.cons derived (.cons carried .nil)))).bind
              fun eqRes =>
                bif eqRes.single then
                  .done (aloneIn M verifier (.cons (buf, (nextOff, ())) .nil))
                else .halt (.declared .reject ⟨path, guardKey⟩) := by
  unfold layoutVCarryClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by exact env_get_positional_alone_1 M verifier (τ₁ := streamStateTy unitTy) derived (buf, (off, ())) .nil _ (by rfl))).trans ?_
  have htfree : Tys.anyLinear V (streamStateTys unitTy) = false := by
    simp [Tys.anyLinear, Ty.isLinear, hfree]
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) .head htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (buf, (off, ())) _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_1 M verifier (τ₁ := streamStateTy unitTy) derived (buf, (off, ())) .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M (streamStateTys unitTy) (.tail .head) htfree (buf, (off, ()))))) _).trans ?_
  dsimp only [Tys.getAt, liftLocal_done, Process.bind, HList.single]
  refine (letOp2_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf off _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (readRef.eval M fnTable (.cons buf (.cons off .nil)))).bind _ = _
  congr 1; funext res
  cases res with
  | cons carried res1 =>
      cases res1 with
      | cons nextOff res2 =>
          cases res2
          refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ derived carried _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
              exact env_get_positional_alone_0 M verifier derived
                (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil) _ (by rfl))
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)).trans ?_
          change (liftLocal id (eqRef.eval M fnTable (.cons derived (.cons carried .nil)))).bind _ = _
          congr 1; funext eqRes
          cases eqRes with
          | cons eqb eqNil =>
              cases eqNil
              refine (term_denote_guard_eq M verifier fnTable rTable _ _ _ _ _ _ _ eqb
                (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
              dsimp only [HList.single]
              cases eqb with
              | false => rfl
              | true =>
                  simp only [Bool.cond_true]
                  refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ buf nextOff _ _ _ _ _
                    (by
                      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                        env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                        env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                        env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
                      exact env_get_insert_eq _ _ _ rfl)
                    (by
                      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
                      exact env_get_insert_eq _ _ _ rfl)).trans ?_
                  dsimp only [localOp]
                  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
                    (ownedOp_makeTuple M (streamStateTys unitTy) (.cons buf (.cons nextOff .nil))))) _).trans ?_
                  dsimp only [Tys.ofHList, liftLocal_done, Process.bind, HList.single]
                  exact term_denote_ret1 M verifier fnTable rTable _ _ _ _ (env_get_insert_eq _ _ _ rfl)

theorem proverAbsorbClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (path : List Frame) (msg : M.Val τ) (st : M.Val stateTy) :
    (proverAbsorbClause prover site kind getters label hlabel encodeRef absorbRef).code.denote
      (roleSem M prover fnTable rTable) path
      (Env.positional (aloneIn M prover (.cons msg (.cons st .nil)))) =
      (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
        (liftLocal id (absorbRef.eval M fnTable
            (.cons st (.cons label (.cons enc.single .nil))))).bind fun nextSt =>
          .call (ROp.give kind getters ⟨path, site.key⟩ τ msg) fun _ =>
            .done (aloneIn M prover nextSt) := by
  unfold proverAbsorbClause
  dsimp only
  refine (letOp1_computeAlone0_denote M prover fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M prover fnTable rTable _ _ _ msg _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M prover msg (.cons st .nil) _ rfl)).trans ?_
  change (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      refine (letOp1_computeAlone3_eq M prover fnTable rTable _ _ _ _ _ st label encVal _ _ _ _ _
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
          exact env_get_positional_alone_1 M prover msg st .nil _ rfl)
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
          exact env_get_insert_eq _ _ _ rfl)
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      change (liftLocal id (absorbRef.eval M fnTable (.cons st (.cons label (.cons encVal .nil))))).bind _ = _
      congr 1; funext nextSt
      cases nextSt with
      | cons st' stNil =>
          cases stNil
          refine (letOp1_give_eq M prover fnTable rTable _ _ _ _ _ msg _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
              exact env_get_positional_alone_0 M prover msg (.cons st .nil) _ rfl)).trans ?_
          congr 1

theorem verifierAbsorbClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (path : List Frame) (st : M.Val stateTy) :
    (verifierAbsorbClause verifier prover site kind label hlabel encodeRef absorbRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons st .nil))) =
      .call (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg =>
        (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
          (liftLocal id (absorbRef.eval M fnTable
              (.cons st (.cons label (.cons enc.single .nil))))).map fun nextSt =>
            aloneIn M verifier (.cons msg nextSt) := by
  unfold verifierAbsorbClause
  dsimp only
  refine (letOp1_denote (roleSem M verifier fnTable rTable) _ _ _ _ _ _ _ _).trans ?_
  change (Process.call (S := RSig M) (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg => _).bind _ = _
  simp only [Process.bind]
  congr 1; funext msg
  refine (letOp1_keep_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      refine (letOp1_computeAlone3_eq M verifier fnTable rTable _ _ _ _ _ st label encVal _ _ _ _ _
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
            env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
          exact env_get_positional_alone_0 M verifier st .nil _ rfl)
        (by
          rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
          exact env_get_insert_eq _ _ _ rfl)
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      change (liftLocal id (absorbRef.eval M fnTable (.cons st (.cons label (.cons encVal .nil))))).bind _ = _
      rw [Process.map_eq_bind]
      congr 1; funext nextSt
      cases nextSt with
      | cons st' stNil =>
          cases stNil
          exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar]),
                env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)
            (env_get_insert_eq _ _ _ rfl)

theorem deriveClause_denote_nil {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (r peer : Role) (site : Site) (part : Part V)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (deriveRef : TypedFnRef V hs.fns [stateTy, bytesTy] [τ, stateTy])
    (path : List Frame) (st : M.Val stateTy) :
    (deriveClause r peer site part [] toldKey label hlabel deriveRef).code.denote
      (roleSem M r fnTable rTable) path
      (Env.positional (aloneIn M r (.cons st .nil))) =
      (liftLocal id (deriveRef.eval M fnTable (.cons st (.cons label .nil)))).bind fun res =>
        match res with
        | .cons coin (.cons nextSt .nil) =>
            .call (ROp.give .message [peer] ⟨path, toldKey⟩ τ coin) fun _ =>
              .done (aloneIn M r (.cons coin (.cons nextSt .nil))) := by
  unfold deriveClause
  dsimp only
  refine (letOp1_computeAlone0_denote M r fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single, List.nil_append, List.length_nil,
    takeVars, id, HList.reindex]
  refine (letOp2_computeAlone2_eq M r fnTable rTable _ _ _ _ st label _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, posVar])]
      exact env_get_positional_alone_0 M r st .nil _ rfl)
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (deriveRef.eval M fnTable (.cons st (.cons label .nil)))).bind _ = _
  congr 1; funext res
  cases res with
  | cons coin res1 =>
      cases res1 with
      | cons nextSt res2 =>
          cases res2
          refine (letOp1_give_eq M r fnTable rTable _ _ _ _ _ coin _ _ _ _ _
            (by
              rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
              exact env_get_insert_eq _ _ _ rfl)).trans ?_
          congr 1

theorem idealAbsorbClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (path : List Frame) (st : M.Val (idealPathTy unitTy)) :
    (idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons st .nil))) =
      .call (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg =>
        (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).map fun enc =>
          aloneIn M verifier (.cons msg (.cons (idealPathPush M st (2 :: label) enc.single) .nil)) := by
  have hTagLbl : ∀ b, b ∈ (2 :: label) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hm
    · exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 253))
    · exact hlabel b hm
  unfold idealAbsorbClause
  dsimp only
  refine (letOp1_denote (roleSem M verifier fnTable rTable) _ _ _ _ _ _ _ _).trans ?_
  change (Process.call (S := RSig M) (ROp.get kind prover ⟨path, site.key⟩ τ) fun msg => _).bind _ = _
  simp only [Process.bind]
  congr 1; funext msg
  refine (letOp1_keep_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M (2 :: label) hTagLbl]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ msg _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
      exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (encodeRef.eval M fnTable (.cons msg .nil))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      apply appendIdealPathRole_denote_eq M verifier fnTable rTable hfree _ _ _ _ _ _ path _
        st (2 :: label) encVal
      · rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
          env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
          env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
          env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
        exact env_get_positional_alone_0 M verifier st .nil _ rfl
      · rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, freshVar])]
        exact env_get_insert_eq _ _ _ rfl
      · exact env_get_insert_eq _ _ _ rfl
      · intro Γ' h' w nextSt env' hNext hAgree
        apply term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _ _ hNext
        rw [hAgree _ (by
          change (((((Ctx.positional (alone verifier [idealPathTy unitTy])).insert 1 _).insert 2 _).insert 3 _).insert 4 _).find? 2 = some ⟨τ, [verifier]⟩
          rw [Ctx.find?_insert, ite_eq_right, Ctx.find?_insert, ite_eq_right,
              Ctx.find?_insert, ite_eq_left rfl]
          · decide
          · decide),
          env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
        · rfl
        · dsimp only [Var.reindex, freshVar]; decide
        · dsimp only [Var.reindex, freshVar]; decide

theorem idealDeriveClause_denote_nil {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (part : Part V)
    (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (path : List Frame) (st : M.Val (idealPathTy unitTy)) :
    (idealDeriveClause hfree verifier prover site part [] serviceKey reqKey toldKey
        label hlabel encodeRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons st .nil))) =
      .call (ROp.own (.request serviceKey) [] ⟨path, reqKey⟩ [idealQueryTy unitTy]
          (.cons (st, (label, ())) .nil) τ) fun coin =>
        .call (ROp.give .message [prover] ⟨path, toldKey⟩ τ coin) fun _ =>
          (liftLocal id (encodeRef.eval M fnTable (.cons coin .nil))).map fun enc =>
            aloneIn M verifier (.cons coin (.cons (idealPathPush M st (3 :: label) enc.single) .nil)) := by
  have hTagLbl : ∀ b, b ∈ (3 :: label) → b < 256 := fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hm
    · exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 252)))
    · exact hlabel b hm
  unfold idealDeriveClause
  dsimp only [List.nil_append, List.length_singleton, List.length_nil]
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M label hlabel]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ st label _ _ _ _ _
    ?_ ?_).trans ?_
  · rw [env_get_insert_ne]
    · exact env_get_positional_alone_0 M verifier st .nil _ rfl
    · dsimp only [Var.reindex, posVar]; decide
  · exact env_get_insert_eq _ _ _ rfl
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_makeTuple M (idealQueryTys unitTy) (.cons st (.cons label .nil))))) _).trans ?_
  dsimp only [Tys.ofHList, liftLocal_done, Process.bind, HList.single]
  refine (letOp1_request1_eq M verifier fnTable rTable _ _ _ _ (st, (label, ())) _ _ _ _ _ ?_).trans ?_
  · exact env_get_insert_eq _ _ _ rfl
  congr 1; funext coin
  refine (letOp1_keep_eq M verifier fnTable rTable _ _ _ coin _ _ _ _ _ ?_).trans ?_
  · exact env_get_insert_eq _ _ _ rfl
  refine (letOp1_give_eq M verifier fnTable rTable _ _ _ _ _ coin _ _ _ _ _ ?_).trans ?_
  · exact env_get_insert_eq _ _ _ rfl
  congr 1; funext _
  refine (letOp1_computeAlone0_denote M verifier fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M (3 :: label) hTagLbl]
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ coin _ _ _ _ _ ?_).trans ?_
  · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
    · rfl
    · dsimp only [Var.reindex, freshVar]; decide
    · dsimp only [Var.reindex, freshVar]; decide
  change (liftLocal id (encodeRef.eval M fnTable (.cons coin .nil))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext enc
  cases enc with
  | cons encVal encNil =>
      cases encNil
      apply appendIdealPathRole_denote_eq M verifier fnTable rTable hfree _ _ _ _ _ _ path _
        st (3 :: label) encVal
      · rw [env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_ne,
            env_get_insert_ne, env_get_insert_ne, env_get_insert_ne]
        · exact env_get_positional_alone_0 M verifier st .nil _ rfl
        all_goals (dsimp only [Var.reindex, posVar]; decide)
      · rw [env_get_insert_ne, env_get_insert_eq]
        all_goals (try dsimp only [Var.reindex, freshVar]) <;> first | rfl | (show (_ : Nat) ≠ _; omega)
      · exact env_get_insert_eq _ _ _ rfl
      · intro Γ' h' w nextSt env' hNext hAgree
        apply term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _ _ hNext
        rw [hAgree _ (by
          change ((((((((Ctx.positional (alone verifier [idealPathTy unitTy])).insert 1 _).insert 2 _).insert 3 _).insert 4 _).insert 5 _).insert 6 _).insert 7 _).find? 4 = some ⟨τ, [verifier]⟩
          rw [Ctx.find?_insert, ite_eq_right, Ctx.find?_insert, ite_eq_right,
              Ctx.find?_insert, ite_eq_right, Ctx.find?_insert, ite_eq_left rfl]
          · decide
          · decide
          · decide),
          env_get_insert_ne, env_get_insert_ne, env_get_insert_ne, env_get_insert_eq]
        · rfl
        · dsimp only [Var.reindex, freshVar]; decide
        · dsimp only [Var.reindex, freshVar]; decide
        · dsimp only [Var.reindex, freshVar]; decide

theorem proverSampleClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {heldP : List V.Ty} {τ : V.Ty}
    (htfree : Tys.anyLinear V (samplesStateTys heldP) = false)
    (prover : Role) (site : Site) (law : V.LawKey)
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (siteBytes : List Nat) (hsite : ∀ b, b ∈ siteBytes → b < 256)
    (sampleRef : TypedFnRef V hs.fns (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [τ])
    (path : List Frame) (att seq : Nat) (heldTuple : (tysOfList heldP).Val M.toCarriers) :
    (proverSampleClause htfree prover site law sessionBytes hsess siteBytes hsite sampleRef).code.denote
      (roleSem M prover fnTable rTable) path
      (Env.positional (aloneIn M prover
        (.cons (a := samplesStateTy heldP) (att, (seq, (heldTuple, ()))) .nil))) =
      (liftLocal id (sampleRef.eval M fnTable
        (HList.append
          (cast (congrArg (HList M.Val) (tysOfList_toList heldP))
            (Tys.toHList M (tysOfList heldP) heldTuple))
          (.cons sessionBytes (.cons siteBytes (.cons att (.cons seq .nil))))))).map
        fun coin => aloneIn M prover
          (.cons coin.single (.cons (a := samplesStateTy heldP) (att, (seq + 1, (heldTuple, ()))) .nil)) := by
  let st : M.Val (samplesStateTy heldP) := (att, (seq, (heldTuple, ())))
  unfold proverSampleClause
  dsimp only
  refine (letOp1_computeAlone1_eq M prover fnTable rTable _ _ _ st _ _ _ _ _
    (env_get_positional_alone_0 M prover (τ := samplesStateTy heldP) st .nil _ rfl)).trans ?_
  dsimp only [localOp]
  have hGet0 : ownedOp M (.getTuple (samplesStateTys heldP) .head htfree) (.cons st .nil) =
      .done (.cons (a := Ty.nat) att .nil) :=
    ownedOp_getTuple M (samplesStateTys heldP) .head htfree st
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id) hGet0)) _).trans ?_
  simp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M prover fnTable rTable _ _ _ st _ _ _ _ _ ?_).trans ?_
  · rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
    exact env_get_positional_alone_0 M prover (τ := samplesStateTy heldP) st .nil _ rfl
  dsimp only [localOp]
  have hGet1 : ownedOp M (.getTuple (samplesStateTys heldP) (.tail .head) htfree) (.cons st .nil) =
      .done (.cons (a := Ty.nat) seq .nil) :=
    ownedOp_getTuple M (samplesStateTys heldP) (.tail .head) htfree st
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id) hGet1)) _).trans ?_
  simp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone1_eq M prover fnTable rTable _ _ _ st _ _ _ _ _ ?_).trans ?_
  · rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
        env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
    exact env_get_positional_alone_0 M prover (τ := samplesStateTy heldP) st .nil _ rfl
  dsimp only [localOp]
  have hGet2 : ownedOp M (.getTuple (samplesStateTys heldP) (.tail (.tail .head)) htfree) (.cons st .nil) =
      .done (.cons (a := Ty.tuple (tysOfList heldP)) heldTuple .nil) :=
    ownedOp_getTuple M (samplesStateTys heldP) (.tail (.tail .head)) htfree st
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id) hGet2)) _).trans ?_
  simp only [liftLocal_done, Process.bind, HList.single]
  let env3 := (((Env.positional (aloneIn M prover (.cons (a := samplesStateTy heldP) st .nil))).insert 1
      (hide M prover ⟨.nat, [prover]⟩ att)).insert 2
      (hide M prover ⟨.nat, [prover]⟩ seq)).insert 3
      (hide M prover ⟨.tuple (tysOfList heldP), [prover]⟩ heldTuple)
  refine (Term.denote_op (roleSem M prover fnTable rTable) _ _ _ _ _ _ _).trans ?_
  have hOp3 :
      (roleSem M prover fnTable rTable).op ⟨3⟩
          (computeAlone prover (.owned (.takeTuple (tysOfList heldP)))) path
          (env3.all (.cons (freshVar _ 3 (⟨.tuple (tysOfList heldP), [prover]⟩ : LTy V)) .nil)) =
        .done (aloneIn M prover (Tys.toHList M (tysOfList heldP) heldTuple)) := by
    have hAll :
        env3.all (.cons (freshVar _ 3 (⟨.tuple (tysOfList heldP), [prover]⟩ : LTy V)) .nil) =
        aloneIn M prover (.cons (a := .tuple (tysOfList heldP)) heldTuple .nil) := by
      show HList.cons _ .nil = HList.cons _ .nil
      exact congrArg (fun v => HList.cons v .nil) (env_get_insert_eq _ _ _ rfl)
    erw [hAll, computeAlone_denote]
    dsimp only [localOp]
    rw [ownedOp_takeTuple]
    rfl
  refine (congrFun (congrArg Process.bind hOp3) _).trans ?_
  simp only [Process.bind]
  refine (letOp1_computeAlone0_denote M prover fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M sessionBytes hsess]
  simp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone0_denote M prover fnTable rTable _ _ _ _ _ _ _).trans ?_
  dsimp only [localOp]
  rw [bytesLiteral_val M siteBytes hsite]
  simp only [liftLocal_done, Process.bind, HList.single]
  let fields := alone prover (tysOfList heldP).toList
  let fBase := 4 + fields.length
  let env4 := env3.extend (Names.counting 4 fields)
      (aloneIn M prover (Tys.toHList M (tysOfList heldP) heldTuple))
  let env5 := env4.insert fBase (hide M prover ⟨bytesTy, [prover]⟩ sessionBytes)
  let env6 := env5.insert (fBase + 1) (hide M prover ⟨bytesTy, [prover]⟩ siteBytes)
  have hEnv4Outside : ∀ (k : Nat) (hk : k < 4) {a : LTy V}
      (hIn : (_ : Ctx (LTy V)).find? k = some a),
      env4.get ⟨k, hIn⟩ = env3.get ⟨k, by
        rw [Ctx.find?_extend_counting] at hIn
        have hout : ¬ (4 ≤ k ∧ k < 4 + fields.length) := fun hm => Nat.not_le_of_lt hk hm.1
        rwa [ite_eq_right hout] at hIn⟩ := fun k hk _ hIn =>
    env_extend_counting_outside env3 4 _ k (.inl hk) hIn
  have hNeBase : ∀ (k m : Nat), k < 4 → k ≠ fBase + m := fun k m hk => by
    show k ≠ (4 + fields.length) + m; omega
  have hNeBase0 : ∀ (k : Nat), k < 4 → k ≠ fBase := fun k hk => by
    show k ≠ 4 + fields.length; omega
  have hAtt6 : ∀ (hIn : _), env6.get ⟨1, hIn⟩ = hide M prover ⟨.nat, [prover]⟩ att := fun hIn => by
    rw [env_get_insert_ne _ _ _ (hNeBase 1 1 (by omega)),
        env_get_insert_ne _ _ _ (hNeBase0 1 (by omega)),
        hEnv4Outside 1 (by omega),
        env_get_insert_ne _ _ _ (by dsimp only; decide),
        env_get_insert_ne _ _ _ (by dsimp only; decide),
        env_get_insert_eq _ _ _ rfl]
  have hSeq6 : ∀ (hIn : _), env6.get ⟨2, hIn⟩ = hide M prover ⟨.nat, [prover]⟩ seq := fun hIn => by
    rw [env_get_insert_ne _ _ _ (hNeBase 2 1 (by omega)),
        env_get_insert_ne _ _ _ (hNeBase0 2 (by omega)),
        hEnv4Outside 2 (by omega),
        env_get_insert_ne _ _ _ (by dsimp only; decide),
        env_get_insert_eq _ _ _ rfl]
  have hSess6 : ∀ (hIn : _), env6.get ⟨fBase, hIn⟩ = hide M prover ⟨bytesTy, [prover]⟩ sessionBytes := fun hIn => by
    rw [env_get_insert_ne _ _ _ (by show fBase ≠ fBase + 1; omega),
        env_get_insert_eq _ _ _ rfl]
  have hSite6 : ∀ (hIn : _), env6.get ⟨fBase + 1, hIn⟩ = hide M prover ⟨bytesTy, [prover]⟩ siteBytes := fun hIn =>
    env_get_insert_eq _ _ _ rfl
  refine (letOp1_computeAlone_eq M prover fnTable rTable _ _ _
    (HList.append
      (cast (congrArg (HList M.Val) (tysOfList_toList heldP))
        (Tys.toHList M (tysOfList heldP) heldTuple))
      (.cons sessionBytes (.cons siteBytes (.cons att (.cons seq .nil)))))
    _ _ _ _ _ ?_).trans ?_
  · erw [env_all_cast (by simp [alone, List.map_append]) env6, env_all_append env6, aloneIn_append]
    congr 1
    have hReCast : ∀ {ts₁ ts₂ : List V.Ty} (heq : ts₁ = ts₂)
        {Γ Δ : Ctx (LTy V)} (w : Γ.Within Δ)
        (xs : HList (Var Γ) (alone prover ts₁)),
        (cast (congrArg (fun ts => HList (Var Γ) (alone prover ts)) heq) xs).reindex w =
          cast (congrArg (fun ts => HList (Var Δ) (alone prover ts)) heq) (xs.reindex w) := by
      intro _ _ heq _ _ _ _; subst heq; rfl
    have hAllCast : ∀ {ts₁ ts₂ : List V.Ty} (heq : ts₁ = ts₂)
        (xs : HList (Var _) (alone prover ts₁)),
        env6.all (cast (congrArg (fun ts => HList (Var _) (alone prover ts)) heq) xs) =
          cast (congrArg (fun ts => HList (RV M prover) (alone prover ts)) heq) (env6.all xs) := by
      intro _ _ heq _; subst heq; rfl
    have hRePos : ∀ {Γ Δ : Ctx (LTy V)} (w : Γ.Within Δ) (start : Nat) (rem : List (LTy V)) (hIn),
        (positionalVars rem start hIn).reindex w =
          positionalVars rem start (fun k a ha => w _ _ (hIn k a ha)) := by
      intro Γ Δ w start rem
      induction rem generalizing start with
      | nil => intro _; rfl
      | cons _ _ ih => intro _; exact congrArg (HList.cons _) (ih _ _)
    congr 1
    · erw [hReCast (tysOfList_toList heldP), hAllCast (tysOfList_toList heldP),
          aloneIn_cast M prover (tysOfList_toList heldP)]
      congr 1
      rw [hRePos]
      exact env_all_positionalVars 4 env6 fields
        (aloneIn M prover (Tys.toHList M (tysOfList heldP) heldTuple)) _
        fun k a ha => by
          have hk : k < fields.length := by
            cases Nat.lt_or_ge k fields.length with
            | inl h => exact h
            | inr h => rw [List.getElem?_eq_none h] at ha; cases ha
          have h4k : 4 + k < 4 + fields.length := Nat.add_lt_add_left hk 4
          rw [env_get_insert_ne _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt h4k)),
              env_get_insert_ne _ _ _ (Nat.ne_of_lt h4k)]
          exact env_get_extend_counting_getAt env3 4 _ k ha _
    · show HList.cons _ (.cons _ (.cons _ (.cons _ .nil))) =
        HList.cons _ (.cons _ (.cons _ (.cons _ .nil)))
      erw [hSess6, hSite6, hAtt6, hSeq6]
  change (liftLocal id (sampleRef.eval M fnTable _)).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext coin
  cases coin with
  | cons coinV coinNil =>
      cases coinNil
      refine (letOp1_computeAlone0_denote M prover fnTable rTable _ _ _ _ _ _ _).trans ?_
      have hOne : localOp M fnTable (.literal .nat [1] rfl) .nil = .done (.cons (a := Ty.nat) 1 .nil) := rfl
      rw [hOne]
      simp only [liftLocal_done, Process.bind, HList.single]
      refine (letOp1_computeAlone2_eq M prover fnTable rTable _ _ _ _ seq (1 : Nat) _ _ _ _ _ ?_ ?_).trans ?_
      · rw [env_get_insert_ne _ _ _ (hNeBase 2 3 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 2 2 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 2 1 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase0 2 (by omega))]
        dsimp only [Var.reindex, freshVar]
        erw [hEnv4Outside 2 (by omega)]
        dsimp only [env3]
        rw [env_get_insert_ne _ _ _ (by dsimp only; decide),
            env_get_insert_eq _ _ _ rfl]
      · exact env_get_insert_eq _ _ _ rfl
      dsimp only [localOp]
      rw [ownedOp_natAdd]
      simp only [liftLocal_done, Process.bind, HList.single]
      refine (letOp1_computeAlone3_eq M prover fnTable rTable _ _ _ _ _ att (seq + 1) heldTuple _ _ _ _ _ ?_ ?_ ?_).trans ?_
      · rw [env_get_insert_ne _ _ _ (hNeBase 1 4 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 1 3 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 1 2 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 1 1 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase0 1 (by omega))]
        dsimp only [Var.reindex, freshVar]
        erw [hEnv4Outside 1 (by omega)]
        dsimp only [env3]
        rw [env_get_insert_ne _ _ _ (by dsimp only; decide),
            env_get_insert_ne _ _ _ (by dsimp only; decide),
            env_get_insert_eq _ _ _ rfl]
      · exact env_get_insert_eq _ _ _ rfl
      · rw [env_get_insert_ne _ _ _ (hNeBase 3 4 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 3 3 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 3 2 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase 3 1 (by omega)),
            env_get_insert_ne _ _ _ (hNeBase0 3 (by omega))]
        dsimp only [Var.reindex, freshVar]
        erw [hEnv4Outside 3 (by omega)]
        dsimp only [env3]
        rw [env_get_insert_eq _ _ _ rfl]
      dsimp only [localOp]
      have hMake : ownedOp M (.makeTuple (samplesStateTys heldP))
          (.cons (a := Ty.nat) att (.cons (a := Ty.nat) (seq + 1)
            (.cons (a := Ty.tuple (tysOfList heldP)) heldTuple .nil))) =
          .done (.cons (a := samplesStateTy heldP) (att, (seq + 1, (heldTuple, ()))) .nil) :=
        ownedOp_makeTuple M (samplesStateTys heldP) _
      refine (congrFun (congrArg Process.bind (congrArg (liftLocal id) hMake)) _).trans ?_
      simp only [liftLocal_done, Process.bind, HList.single]
      refine term_denote_ret2 M prover fnTable rTable _ _ _ _ _ _ ?_ ?_
      · rw [env_get_insert_ne _ _ _ (by dsimp only [Var.reindex, freshVar]; show fBase + 2 ≠ fBase + 5; omega),
            env_get_insert_ne _ _ _ (by dsimp only [Var.reindex, freshVar]; show fBase + 2 ≠ fBase + 4; omega),
            env_get_insert_ne _ _ _ (by dsimp only [Var.reindex, freshVar]; show fBase + 2 ≠ fBase + 3; omega),
            env_get_insert_eq _ _ _ rfl]
      · exact env_get_insert_eq _ _ _ rfl

theorem compactReadSlotClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ)
    (path : List Frame) (st : stateTys.Val M.toCarriers) :
    (compactReadSlotClause (hs := hs) htfree verifier prover site kind pos).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))) =
      .done (aloneIn M verifier (.cons (Tys.getAt M stateTys pos st) (.cons (a := Ty.tuple stateTys) st .nil))) := by
  unfold compactReadSlotClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (v₁ := (st : M.Val (.tuple stateTys))) _ _ _ _ _
    (by exact env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M stateTys pos htfree st))) _).trans ?_
  dsimp only [liftLocal_done, Process.bind, HList.single]
  exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
    (env_get_insert_eq _ _ _ rfl)
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil _ (by rfl))

theorem compactCompareClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ)
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (path : List Frame) (derived : M.Val τ) (st : stateTys.Val M.toCarriers) :
    (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons derived (.cons (a := Ty.tuple stateTys) st .nil)))) =
      (liftLocal id (eqRef.eval M fnTable
          (.cons derived (.cons (Tys.getAt M stateTys pos st) .nil)))).bind fun eqRes =>
        bif eqRes.single then .done (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))
        else .halt (.declared .reject ⟨path, guardKey⟩) := by
  unfold compactCompareClause
  dsimp only
  refine (letOp1_computeAlone1_eq M verifier fnTable rTable _ _ _ (v₁ := (st : M.Val (.tuple stateTys))) _ _ _ _ _
    (by exact env_get_positional_alone_1 M verifier (τ₁ := Ty.tuple stateTys) derived st .nil _ (by rfl))).trans ?_
  dsimp only [localOp]
  refine (congrFun (congrArg Process.bind (congrArg (liftLocal id)
    (ownedOp_getTuple M stateTys pos htfree st))) _).trans ?_
  dsimp only [liftLocal_done, Process.bind, HList.single]
  refine (letOp1_computeAlone2_eq M verifier fnTable rTable _ _ _ _ derived (Tys.getAt M stateTys pos st) _ _ _ _ _
    (by
      rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
      exact env_get_positional_alone_0 M verifier derived (.cons (a := Ty.tuple stateTys) st .nil) _ (by rfl))
    (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
  change (liftLocal id (eqRef.eval M fnTable (.cons derived (.cons (Tys.getAt M stateTys pos st) .nil)))).bind _ = _
  congr 1; funext eqRes
  cases eqRes with
  | cons eqb eqNil =>
      cases eqNil
      refine (term_denote_guard_eq M verifier fnTable rTable _ _ _ _ _ _ _ eqb
        (by exact env_get_insert_eq _ _ _ rfl)).trans ?_
      dsimp only [HList.single]
      cases eqb with
      | false => rfl
      | true =>
          simp only [Bool.cond_true]
          exact term_denote_ret1 M verifier fnTable rTable _ _ _ _ (by
            rw [env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar]),
              env_get_insert_ne _ _ _ (by simp [Var.reindex, alonePosVar, posVar])]
            exact env_get_positional_alone_1 M verifier (τ₁ := Ty.tuple stateTys) derived st .nil _ (by rfl))

theorem compactRecoverClause_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recoverRef : SafeFnRef V hs.fns stateTys.toList [τ])
    (path : List Frame) (st : stateTys.Val M.toCarriers) :
    (compactRecoverClause verifier prover site kind recoverRef).code.denote
      (roleSem M verifier fnTable rTable) path
      (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))) =
      (liftLocal id (recoverRef.eval M fnTable (Tys.toHList M stateTys st))).map fun res =>
        aloneIn M verifier (.cons res.single (.cons (a := Ty.tuple stateTys) st .nil)) := by
  unfold compactRecoverClause
  dsimp only
  refine (Term.denote_op (roleSem M verifier fnTable rTable) _ _ _ _ _ _ _).trans ?_
  have hOp0 :
      (roleSem M verifier fnTable rTable).op ⟨0⟩ (computeAlone verifier (.owned (.takeTuple stateTys))) path
        ((Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))).all
          (.cons (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) .nil)) =
      .done (aloneIn M verifier (Tys.toHList M stateTys st)) := by
    have hAll :
        (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))).all
          (.cons (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) .nil) =
        aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil) := by
      show HList.cons _ HList.nil = HList.cons _ HList.nil
      exact congrArg (fun v => HList.cons v HList.nil)
        (env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) rfl)
    erw [hAll, computeAlone_denote]
    dsimp only [localOp]
    rw [ownedOp_takeTuple]
    rfl
  refine (congrFun (congrArg Process.bind hOp0) _).trans ?_
  dsimp only [Process.bind]
  have hBuild : ∀ (start : Nat) {Γ : Ctx (LTy V)} (env : Env (RV M verifier) Γ)
      (tys : List (LTy V)) (vals : HList (RV M verifier) tys)
      (hΓ : ∀ k a, tys[k]? = some a → Γ.find? (start + k) = some a)
      (hEnv : ∀ k a (ha : tys[k]? = some a),
        env.get ⟨start + k, hΓ k a ha⟩ = HList.getAt vals k ha),
      env.all (compactRecoverClause.buildFieldVars start tys hΓ) = vals := by
    intro start Γ env tys
    induction tys generalizing start with
    | nil =>
        intro vals _ _
        cases vals
        rfl
    | cons a ts ih =>
        intro vals hΓ hEnv
        cases vals with
        | cons v vs =>
            show HList.cons (env.get ⟨start, hΓ 0 a rfl⟩) _ = HList.cons v vs
            congr 1
            · exact hEnv 0 a rfl
            · exact ih (start + 1) vs _ fun k b hb => by
                have hk := hEnv (k + 1) b hb
                simpa [HList.getAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
  refine (letOp1_computeAlone_eq M verifier fnTable rTable _ _ _ (Tys.toHList M stateTys st) _ _ _ _ _
    (hBuild 1 _ (alone verifier stateTys.toList)
      (aloneIn M verifier (Tys.toHList M stateTys st)) _ fun k a ha =>
      env_get_extend_counting_getAt _ 1 _ k ha _)).trans ?_
  change (liftLocal id (recoverRef.eval M fnTable (Tys.toHList M stateTys st))).bind _ = _
  rw [Process.map_eq_bind]
  congr 1; funext res
  cases res with
  | cons v vNil =>
      cases vNil
      exact term_denote_ret2 M verifier fnTable rTable _ _ _ _ _ _
        (env_get_insert_eq _ _ _ rfl)
        (by
          rw [env_get_insert_ne _ _ _ (by
            intro h
            change (0 : Nat) = 1 + (alone verifier stateTys.toList).length at h
            exact Nat.zero_ne_add_one _ (Nat.add_comm 1 _ ▸ h))]
          dsimp only [Var.reindex]
          refine (env_extend_counting_outside
            (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))) 1
            (aloneIn M verifier (Tys.toHList M stateTys st)) 0 (.inl (by omega)) _).trans ?_
          exact env_get_positional_alone_0 M verifier (τ := Ty.tuple stateTys) st .nil
            (alonePosVar verifier [Ty.tuple stateTys] 0 rfl) rfl)

end

/-! ## Event-key lemmas for every generated clause -/

theorem computeAlone_isEvent {V : Vocabulary} {hs : Headers V} (r : Role) {ins outs : List V.Ty}
    (o : LocalOp V hs.fns ins outs) :
    RoleOp.isEvent (computeAlone (hs := hs) r o) = false :=
  rfl

theorem proverAbsorbClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (proverAbsorbClause prover site kind getters label hlabel encodeRef absorbRef).code =
      [site.key] :=
  rfl

theorem verifierAbsorbClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absorbRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (verifierAbsorbClause verifier prover site kind label hlabel encodeRef absorbRef).code =
      [site.key] :=
  rfl

theorem deriveClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy τ : V.Ty}
    (r peer : Role) (site : Site) (part : Part V) (drawIns : List V.Ty)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (deriveRef : TypedFnRef V hs.fns (stateTy :: bytesTy :: drawIns) [τ, stateTy]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (deriveClause r peer site part drawIns toldKey label hlabel deriveRef).code =
      [toldKey] :=
  rfl

theorem idealAbsorbClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef).code =
      [site.key] :=
  rfl

theorem idealDeriveClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (part : Part V) (drawIns : List V.Ty)
    (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (idealDeriveClause hfree verifier prover site part drawIns serviceKey reqKey toldKey
        label hlabel encodeRef).code =
      [reqKey, toldKey] :=
  rfl

theorem layoutPWriteClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (writeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutPWriteClause prover site kind getters writeRef).code = [] :=
  rfl

theorem layoutDropClause_eventKeys {V : Vocabulary} {hs : Headers V} {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters).code = [] :=
  rfl

theorem layoutVReadClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutVReadClause hfree verifier prover site kind readRef).code = [] :=
  rfl

theorem layoutVCarryClause_eventKeys {V : Vocabulary} {hs : Headers V} {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef).code = [] :=
  rfl

theorem proverSampleClause_eventKeys {V : Vocabulary} {hs : Headers V}
    {heldP : List V.Ty} {τ : V.Ty}
    (htfree : Tys.anyLinear V (samplesStateTys heldP) = false)
    (prover : Role) (site : Site) (law : V.LawKey)
    (sessionBytes : List Nat) (hsess : ∀ b, b ∈ sessionBytes → b < 256)
    (siteBytes : List Nat) (hsite : ∀ b, b ∈ siteBytes → b < 256)
    (sampleRef : TypedFnRef V hs.fns (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (proverSampleClause htfree prover site law sessionBytes hsess siteBytes hsite sampleRef).code =
      [] :=
  rfl

theorem compactReadSlotClause_eventKeys {V : Vocabulary} {hs : Headers V}
    {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (compactReadSlotClause (hs := hs) htfree verifier prover site kind pos).code = [] :=
  rfl

theorem compactCompareClause_eventKeys {V : Vocabulary} {hs : Headers V}
    {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ)
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef).code = [] :=
  rfl

theorem compactRecoverClause_eventKeys {V : Vocabulary} {hs : Headers V}
    {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recoverRef : SafeFnRef V hs.fns stateTys.toList [τ]) :
    Term.eventKeys (fun o => RoleOp.isEvent o)
      (compactRecoverClause verifier prover site kind recoverRef).code = [] :=
  rfl

end LayerBuild

end Zkc.Core
