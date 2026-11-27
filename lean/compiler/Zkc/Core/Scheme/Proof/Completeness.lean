module

public import Zkc.Core.Scheme.Proof.CompletenessHelpers
public import Zkc.Core.Scheme.Deploy.Structural

@[expose] public section

/-!
Completeness proofs for non-interactive streaming deployments (`deploy_complete`,
`deploy_complete_streaming`) and deterministic prover sampling (`deploy_complete_samples`).

Both theorems share one unified coupled prover–verifier–protocol simulation (`simulate_derived`)
parameterized by `ProverAdapter`, avoiding duplication between the 2-layer prover stack
`[conP, layP]` (`samples = none`) and the 3-layer prover stack `[sampP, conP, layP]`
(`samples = some sKey`).
-/

namespace Zkc.Core

open LayerBuild

section Completeness

variable {V : Vocabulary} (M : Model V)

/-! ## Tuple round-trip, prover-private-coin membership, and generalized world predicates -/

theorem Tys.toHList_ofHList : ∀ (fields : Tys V.TypeKey) (vs : HList M.Val fields.toList),
    Tys.toHList M fields (Tys.ofHList M fields vs) = vs
  | .nil, .nil => rfl
  | .cons _ rest, .cons v vs => congrArg (HList.cons v) (Tys.toHList_ofHList rest vs)

theorem mem_proverPrivateCoins_of_event {prover : Role} {s : Shape V} {e : ShapeEvent V}
    (hE : e ∈ s.events [] id) {law : V.LawKey}
    (hCls : e.cls = .given (.coin law) prover []) :
    e.site ∈ s.proverPrivateCoins prover := by
  unfold Shape.proverPrivateCoins
  exact List.mem_filterMap.mpr ⟨e, hE, by simp [hCls]⟩

/-- World feeding predicate parameterized by `useSamples`: when `useSamples = false`, agrees with
`Fed` (skipping heard coins); when `useSamples = true`, also skips zero-argument private prover
coins, allowing a completely empty world `source = fun _ _ => none` for deterministic proving. -/
def FedFor (prover : Role) (useSamples : Bool) (source : Source M) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow ..) k => FedFor prover useSamples source (k ())
  | .call (.given (.coin law) _ (_ :: _) _ ins payload τ) k =>
      ∀ v, Allows M (.coin law) ins payload τ v → FedFor prover useSamples source (k v)
  | .call (.given (.coin law) owner [] at_ [] .nil τ) k =>
      if useSamples = true ∧ owner = prover then
        ∀ v, Allows M (.coin law) [] .nil τ v → FedFor prover useSamples source (k v)
      else
        ∃ v, source at_ τ = some v ∧ FedFor prover useSamples source (k v)
  | .call (.given _ _ _ at_ _ _ τ) k =>
      ∃ v, source at_ τ = some v ∧ FedFor prover useSamples source (k v)

/-- World lawfulness predicate matching `FedFor`. -/
def LawfulFor (prover : Role) (useSamples : Bool) (source : Source M) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow ..) k => LawfulFor prover useSamples source (k ())
  | .call (.given (.coin law) _ (_ :: _) _ ins payload τ) k =>
      ∀ v, Allows M (.coin law) ins payload τ v → LawfulFor prover useSamples source (k v)
  | .call (.given (.coin law) owner [] at_ [] .nil τ) k =>
      if useSamples = true ∧ owner = prover then
        ∀ v, Allows M (.coin law) [] .nil τ v → LawfulFor prover useSamples source (k v)
      else
        ∀ v, source at_ τ = some v → Allows M (.coin law) [] .nil τ v ∧ LawfulFor prover useSamples source (k v)
  | .call (.given kind _ _ at_ ins payload τ) k =>
      ∀ v, source at_ τ = some v → Allows M kind ins payload τ v ∧ LawfulFor prover useSamples source (k v)

/-- Deterministic-prover specialization of `FedFor` (`useSamples = true`). -/
def FedSampled (prover : Role) (source : Source M) {A : Type} (p : Protocol M A) : Prop :=
  FedFor M prover true source p

/-- Deterministic-prover specialization of `LawfulFor` (`useSamples = true`). -/
def LawfulSampled (prover : Role) (source : Source M) {A : Type} (p : Protocol M A) : Prop :=
  LawfulFor M prover true source p

theorem fed_to_fedFor_false {prover : Role} {source : Source M} {A : Type} :
    ∀ {p : Protocol M A}, Fed M source p → FedFor M prover false source p
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) k, h => fed_to_fedFor_false (p := k ()) h
  | .call (.given (.coin _) _ (_ :: _) ..) k, h => fun v hv => fed_to_fedFor_false (p := k v) (h v hv)
  | .call (.given (.coin _) _ [] _ [] .nil _) k, ⟨v, hv, hr⟩ => by
      dsimp only [FedFor]
      rw [ite_eq_right (fun hm => Bool.false_ne_true hm.1)]
      exact ⟨v, hv, fed_to_fedFor_false (p := k v) hr⟩
  | .call (.given (.coin _) _ [] _ (_ :: _) _ _) k, ⟨v, hv, hr⟩ =>
      ⟨v, hv, fed_to_fedFor_false (p := k v) hr⟩
  | .call (.given (.request _) ..) k, ⟨v, hv, hr⟩ =>
      ⟨v, hv, fed_to_fedFor_false (p := k v) hr⟩

theorem lawfulPrivate_to_lawfulFor_false {prover : Role} {source : Source M} {A : Type} :
    ∀ {p : Protocol M A}, LawfulPrivate M source p → LawfulFor M prover false source p
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) k, h => lawfulPrivate_to_lawfulFor_false (p := k ()) h
  | .call (.given (.coin _) _ (_ :: _) ..) k, h => fun v hv => lawfulPrivate_to_lawfulFor_false (p := k v) (h v hv)
  | .call (.given (.coin _) _ [] _ [] .nil _) k, h => by
      dsimp only [LawfulFor]
      rw [ite_eq_right (fun hm => Bool.false_ne_true hm.1)]
      exact fun v hv => ⟨(h v hv).1, lawfulPrivate_to_lawfulFor_false (p := k v) (h v hv).2⟩
  | .call (.given (.coin _) _ [] _ (_ :: _) _ _) k, h =>
      fun v hv => ⟨(h v hv).1, lawfulPrivate_to_lawfulFor_false (p := k v) (h v hv).2⟩
  | .call (.given (.request _) ..) k, h =>
      fun v hv => ⟨(h v hv).1, lawfulPrivate_to_lawfulFor_false (p := k v) (h v hv).2⟩

/-! ## 3-layer stack and `buildSamplesClauses` stepping lemmas -/

theorem stack3_clause_samp_done {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (samp con lay : Layer V hs r ins) (op : ROp M)
    (s s' : M.Val samp.state) (st : M.Val con.state) (lst : M.Val lay.state)
    (reply : (RSig M).Reply op)
    (hSamp : Clause.answer M fnTable rTable samp.clauses op s = .done (reply, s')) :
    (Stack.handler M fnTable rTable [samp, con, lay]).clause op (.cons s (.cons st (.cons lst .nil))) =
      .done (reply, .cons s' (.cons st (.cons lst .nil))) := by
  change ((((Layer.handler M fnTable rTable samp).over
      (Stack.handler M fnTable rTable [con, lay])).clause op (s, .cons st (.cons lst .nil))).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = _
  dsimp only [Layer.handler, Handler.over]
  rw [hSamp]; rfl

theorem stack3_clause_below_done {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (samp con lay : Layer V hs r ins) (op : ROp M)
    (s : M.Val samp.state) (st st' : M.Val con.state) (lst lst' : M.Val lay.state)
    (reply : (RSig M).Reply op)
    (hSamp : Clause.answer M fnTable rTable samp.clauses op s = .call op fun r => .done (r, s))
    (hBelow : (Stack.handler M fnTable rTable [con, lay]).clause op (.cons st (.cons lst .nil)) =
      .done (reply, .cons st' (.cons lst' .nil))) :
    (Stack.handler M fnTable rTable [samp, con, lay]).clause op (.cons s (.cons st (.cons lst .nil))) =
      .done (reply, .cons s (.cons st' (.cons lst' .nil))) := by
  change ((((Layer.handler M fnTable rTable samp).over
      (Stack.handler M fnTable rTable [con, lay])).clause op (s, .cons st (.cons lst .nil))).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = _
  dsimp only [Layer.handler, Handler.over]
  rw [hSamp]
  dsimp only [Handler.answer]
  rw [hBelow]; rfl

theorem stack3_clause_pass {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (samp con lay : Layer V hs r ins) (op : ROp M)
    (s : M.Val samp.state) (st : M.Val con.state) (lst : M.Val lay.state)
    (hSamp : Clause.answer M fnTable rTable samp.clauses op s = .call op fun r => .done (r, s))
    (hBelow : (Stack.handler M fnTable rTable [con, lay]).clause op (.cons st (.cons lst .nil)) =
      .call op fun r => .done (r, .cons st (.cons lst .nil))) :
    (Stack.handler M fnTable rTable [samp, con, lay]).clause op (.cons s (.cons st (.cons lst .nil))) =
      .call op fun r => .done (r, .cons s (.cons st (.cons lst .nil))) := by
  change ((((Layer.handler M fnTable rTable samp).over
      (Stack.handler M fnTable rTable [con, lay])).clause op (s, .cons st (.cons lst .nil))).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = _
  dsimp only [Layer.handler, Handler.over]
  rw [hSamp]
  dsimp only [Handler.answer]
  rw [hBelow]; rfl

theorem stack_finish_three {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} (l₁ l₂ l₃ : Layer V hs r ins)
    (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state) (s₃ : M.Val l₃.state) :
    Stack.finish M fnTable [l₁, l₂, l₃] (.cons s₁ (.cons s₂ (.cons s₃ .nil))) =
      (liftLocal id (l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)))).bind
        fun m₁ =>
          ((liftLocal id (l₂.finish.denote (localSem M hs.fns fnTable) []
            (Env.positional (.cons s₂ .nil)))).bind fun m₂ =>
              ((liftLocal id (l₃.finish.denote (localSem M hs.fns fnTable) []
                (Env.positional (.cons s₃ .nil)))).bind fun m₃ => .done (m₃.append .nil)).map
                fun o₂ => m₂.append o₂).map
            fun o₁ => m₁.append o₁ := rfl

theorem alone_cast_stack3 {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (hE : hdr₁ = hdr₂) (l₁ l₂ l₃ : Layer V a.program.headers r hdr₂.ins)
    {st₁ st₂ st₃ : V.Ty} (hSt₁ : l₁.state = st₁) (hSt₂ : l₂.state = st₂) (hSt₃ : l₃.state = st₃)
    {B : Type} {source : Source M} {p : Program M B}
    {rec : List (Happened M)} {out : B}
    {a0 a1 : M.Val st₁} {b0 b1 : M.Val st₂} {c0 c1 : M.Val st₃}
    (hAl : Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        [hE ▸ l₁, hE ▸ l₂, hE ▸ l₃]).run
        (retryOf M none) p
        (.cons ((layer_cast_state hE l₁).trans hSt₁ ▸ a0)
          (.cons ((layer_cast_state hE l₂).trans hSt₂ ▸ b0)
            (.cons ((layer_cast_state hE l₃).trans hSt₃ ▸ c0) .nil))))
      rec (.returned (out,
        .cons ((layer_cast_state hE l₁).trans hSt₁ ▸ a1)
          (.cons ((layer_cast_state hE l₂).trans hSt₂ ▸ b1)
            (.cons ((layer_cast_state hE l₃).trans hSt₃ ▸ c1) .nil))))) :
    Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
        (hE ▸ [l₁, l₂, l₃])).run
        (retryOf M none) p
        (cast (by subst hE; subst hSt₁; subst hSt₂; subst hSt₃; rfl)
          (HList.cons a0 (HList.cons b0 (HList.cons c0 HList.nil)))))
      rec (.returned (out,
        cast (by subst hE; subst hSt₁; subst hSt₂; subst hSt₃; rfl)
          (HList.cons a1 (HList.cons b1 (HList.cons c1 HList.nil))))) := by
  subst hE; subst hSt₁; subst hSt₂; subst hSt₃; exact hAl

private theorem buildSamplesClauses_unmatched {a : Admitted V} {heldP : List V.Ty}
    {htfree : Tys.anyLinear V (samplesStateTys heldP) = false}
    {prover : Role} {sKey : Key} {sessBytes : List Nat}
    {hSess : ∀ b, b ∈ sessBytes → b < 256} {declKey : Key} :
    ∀ (es : List (ShapeEvent V)) {sCs},
      buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey es = .ok sCs →
      ∀ (op : ROp M),
        (∀ law at_ τ, op = .own (.coin law) [] at_ [] .nil τ → False) →
        ∀ c ∈ sCs, ¬ ClauseMatches M c op
  | [], _, h, _, _ => fun _ hc => by cases h; cases hc
  | e :: rest, sCs, h, op, hNotCoin => by
      unfold buildSamplesClauses at h
      cases hRec : buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := buildSamplesClauses_unmatched rest hRec op hNotCoin
          cases hCls : e.cls with
          | flow _ _ _ => rw [hCls] at h; cases h; exact ih
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | request _ => cases h; exact ih
              | coin law =>
                  cases hearers with
                  | cons _ _ => cases h; exact ih
                  | nil =>
                      dsimp only at h
                      split at h
                      · cases hRef : findTypedFnRef a sKey
                            (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [e.τ] with
                        | none => rw [hRef] at h; cases h
                        | some sRef =>
                            rw [hRef] at h; cases h
                            intro c hc
                            rcases List.mem_cons.mp hc with rfl | hm
                            · intro hM
                              cases op with
                              | give | get | hear | «begin» | settle => cases hM.2.1
                              | own gkind' hearers' at_' gIns' payload' τ' =>
                                  have hP := Option.some.inj hM.2.1
                                  cases hP
                                  have hT : ([] : List V.Ty) = gIns' := hM.2.2.1
                                  subst hT
                                  cases payload'
                                  exact hNotCoin law at_' τ' rfl
                            · exact ih c hm
                      · cases h; exact ih

private theorem buildSamplesClauses_answer_coin {a : Admitted V} {heldP : List V.Ty}
    {htfree : Tys.anyLinear V (samplesStateTys heldP) = false}
    {prover : Role} {sKey : Key} {sessBytes : List Nat}
    {hSess : ∀ b, b ∈ sessBytes → b < 256} {declKey : Key} :
    ∀ (es : List (ShapeEvent V)) {sCs},
      buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey es = .ok sCs →
      ∀ (law : V.LawKey) (at_ : Occurrence) (τ : V.Ty)
        (att seq : Nat) (heldVals : HList M.Val heldP),
        heldVals.All M.Valid →
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧ e.cls = .given (.coin law) prover []) →
        let heldTuple : (tysOfList heldP).Val M.toCarriers :=
          Tys.ofHList M (tysOfList heldP) (cast (congrArg (HList M.Val) (tysOfList_toList heldP).symm) heldVals)
        ∃ (sRef : TypedFnRef V a.program.headers.fns (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [τ])
          (coin : M.Val τ),
          findTypedFnRef a sKey (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [τ] = some sRef ∧
          sRef.eval M (Defs.fnTable M a.program.defs)
            (HList.append heldVals (.cons sessBytes (.cons (encodeSite at_.site)
              (.cons (a := Ty.nat) att (.cons (a := Ty.nat) seq .nil))))) =
            .done (.cons coin .nil) ∧
          M.Valid τ coin ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) sCs
            (.own (.coin law) [] at_ [] .nil τ) (att, (seq, (heldTuple, ()))) =
            .done (coin, (att, (seq + 1, (heldTuple, ()))))
  | [], _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | e :: rest, sCs, h, law, at_, τ, att, seq, heldVals, hHeldV, ⟨e', he', hSite', hTy', hCls'⟩ => by
      unfold buildSamplesClauses at h
      cases hRec : buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => buildSamplesClauses_answer_coin rest hRec law at_ τ att seq heldVals hHeldV hIn
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; cases h
              rcases List.mem_cons.mp he' with rfl | hm
              · rw [hCls] at hCls'; cases hCls'
              · exact ih ⟨e', hm, hSite', hTy', hCls'⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hm
                  · rw [hCls] at hCls'; cases hCls'
                  · exact ih ⟨e', hm, hSite', hTy', hCls'⟩
              | coin law₀ =>
                  cases hearers with
                  | cons _ _ =>
                      cases h
                      rcases List.mem_cons.mp he' with rfl | hm
                      · rw [hCls] at hCls'; cases hCls'
                      · exact ih ⟨e', hm, hSite', hTy', hCls'⟩
                  | nil =>
                      dsimp only at h
                      split at h
                      · rename_i hOw
                        cases hRef : findTypedFnRef a sKey
                            (heldP ++ [bytesTy, bytesTy, .nat, .nat]) [e.τ] with
                        | none => rw [hRef] at h; cases h
                        | some sRef =>
                            rw [hRef] at h; cases h
                            by_cases hM : e.site = at_.site ∧
                                some (Part.own (.coin law₀) []) = some (.own (.coin law) []) ∧
                                ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                            · have hSEq : e.site = at_.site := hM.1
                              have hLEq : law₀ = law := by cases Option.some.inj hM.2.1; rfl
                              have hTEq : e.τ = τ := (List.cons.inj hM.2.2.2).1
                              subst hLEq; subst hTEq
                              let heldTuple := Tys.ofHList M (tysOfList heldP)
                                (cast (congrArg (HList M.Val) (tysOfList_toList heldP).symm) heldVals)
                              have hTupleRound :
                                  cast (congrArg (HList M.Val) (tysOfList_toList heldP))
                                    (Tys.toHList M (tysOfList heldP) heldTuple) = heldVals := by
                                dsimp only [heldTuple]
                                rw [Tys.toHList_ofHList]
                                exact cast_cast _ _ _
                              have hAllAppend : ∀ {as bs : List V.Ty} (xs : HList M.Val as)
                                  (ys : HList M.Val bs), xs.All M.Valid → ys.All M.Valid →
                                  (HList.append xs ys).All M.Valid := by
                                intro as bs xs ys hx hy
                                induction xs with
                                | nil => exact hy
                                | cons _ _ ihx => exact ⟨hx.1, ihx hx.2⟩
                              have hArgsV : (HList.append heldVals
                                  (.cons (a := bytesTy) sessBytes
                                    (.cons (a := bytesTy) (encodeSite at_.site)
                                      (.cons (a := Ty.nat) att (.cons (a := Ty.nat) seq .nil))))).All M.Valid :=
                                hAllAppend _ _ hHeldV
                                  ⟨⟨hSess, fun _ hm => nomatch hm⟩,
                                   ⟨encodeSite_bytes at_.site, fun _ hm => nomatch hm⟩,
                                   trivial, trivial, trivial⟩
                              obtain ⟨resH, hEv, hResV⟩ := sRef.eval_done M a _ hArgsV
                              cases resH with
                              | cons coin rNil =>
                                  cases rNil
                                  refine ⟨sRef, coin, hRef, hEv, hResV.1, ?_⟩
                                  unfold Clause.answer
                                  split
                                  · have hEvE : sRef.eval M (Defs.fnTable M a.program.defs)
                                        (HList.append heldVals (.cons (a := bytesTy) sessBytes
                                          (.cons (a := bytesTy) (encodeSite e.site)
                                            (.cons (a := Ty.nat) att (.cons (a := Ty.nat) seq .nil))))) =
                                        .done (.cons coin .nil) := by
                                      rw [hSEq]; exact hEv
                                    have hDen : (proverSampleClause htfree prover e.site law₀
                                          sessBytes hSess (encodeSite e.site) (encodeSite_bytes e.site) sRef).code.denote
                                        (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                                        at_.path
                                        (Env.positional (aloneIn M prover
                                          (.cons (a := samplesStateTy heldP) (att, (seq, (heldTuple, ()))) .nil))) =
                                        .done (aloneIn M prover
                                          (.cons coin (.cons (a := samplesStateTy heldP) (att, (seq + 1, (heldTuple, ()))) .nil))) := by
                                      rw [proverSampleClause_denote, hTupleRound, hEvE]; rfl
                                    have hMapArg : Process.mapHalt
                                        (fun why => (why, att, seq, heldTuple, ()))
                                        ((proverSampleClause htfree prover e.site law₀
                                          sessBytes hSess (encodeSite e.site) (encodeSite_bytes e.site) sRef).code.denote
                                        (roleSem M prover (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                                        at_.path
                                        (Env.positional (aloneIn M prover
                                          (.cons (a := samplesStateTy heldP) (att, (seq, (heldTuple, ()))) .nil)))) =
                                        .done (aloneIn M prover
                                          (.cons coin (.cons (a := samplesStateTy heldP) (att, (seq + 1, (heldTuple, ()))) .nil))) := by
                                      rw [hDen]; rfl
                                    erw [hMapArg]
                                    dsimp only [Process.map]
                                    erw [aloneOut_aloneIn]
                                    rfl
                                  · rename_i hNo
                                    exact absurd hM hNo
                            · rcases List.mem_cons.mp he' with rfl | hm
                              · rw [hCls] at hCls'; cases hCls'
                                exact absurd ⟨hSite', rfl, rfl, by cases hTy'; rfl⟩ hM
                              · obtain ⟨sRef', coin', h1, h2, h3, hAns⟩ := ih ⟨e', hm, hSite', hTy', hCls'⟩
                                refine ⟨sRef', coin', h1, h2, h3, ?_⟩
                                unfold Clause.answer
                                exact (dite_eq_right hM).trans hAns
                      · rename_i hNeOw
                        cases h
                        rcases List.mem_cons.mp he' with rfl | hm
                        · rw [hCls] at hCls'; cases hCls'; exact absurd rfl hNeOw
                        · exact ih ⟨e', hm, hSite', hTy', hCls'⟩

/-! ## Shared event-discipline lemmas and unified `ProverAdapter` -/

theorem construction_event_disc {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy suiteUnitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)) {cP' cV'},
      buildConstructionClauses.go enc a suite stateTy suiteUnitTy absRef
        prover verifier declKey events idx es = .ok (cP', cV') →
      ∀ p ∈ es, match p.1.cls with
        | .flow _ giver getters =>
            (giver = prover ∧ verifier ∈ getters) ∨
            (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
        | .given (.coin law) owner hearers =>
            (owner = verifier ∧ prover ∈ hearers ∧
              ∃ sig, V.law law = some sig ∧ sig.out = p.1.τ ∧ sig.ins = []) ∨
            hearers = []
        | .given (.request _) owner hearers =>
            (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers)
  | _, [], _, _, _, _, hp => nomatch hp
  | idx, p :: rest, cP', cV', hGo', p', hp' => by
      unfold buildConstructionClauses.go at hGo'
      cases hRec : buildConstructionClauses.go enc a suite stateTy suiteUnitTy
          absRef prover verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at hGo'; cases hGo'
      | ok tr =>
          rw [hRec] at hGo'; dsimp only [bind, Except.bind] at hGo'
          rcases List.mem_cons.mp hp' with rfl | hmem
          · cases hCls : p'.1.cls with
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
                            cases hDer : findSuiteDerive enc a suite stateTy law sig.ins p'.1.τ with
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
          · exact construction_event_disc (idx + 1) rest hRec p' hmem

theorem authored_event_disc {prover verifier : Role} {declKey : Key} :
    ∀ (es : List (ShapeEvent V)),
      checkAuthoredEvents prover verifier declKey es = .ok () →
      ∀ e ∈ es, match e.cls with
        | .flow _ giver getters =>
            (giver = prover ∧ verifier ∈ getters) ∨
            (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
        | .given (.coin _) _ hearers => hearers = []
        | .given (.request _) owner hearers =>
            (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers)
  | [], _, _, he => nomatch he
  | e :: rest, hGo', e', he' => by
      unfold checkAuthoredEvents at hGo'
      cases hRec : checkAuthoredEvents prover verifier declKey rest with
      | error _ => rw [hRec] at hGo'; cases hGo'
      | ok u =>
          cases u
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
          · exact authored_event_disc rest hRec e' hmem

def castStack2Handler {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    {s₁ s₂ : V.Ty} (l₁ l₂ : Layer V hs r ins) (h₁ : l₁.state = s₁) (h₂ : l₂.state = s₂) :
    Handler (RSig M) (RSig M) Stop (HList M.Val [s₁, s₂]) :=
  cast (by rw [← h₁, ← h₂]; rfl) (Stack.handler M fnTable rTable [l₁, l₂])

/-- Uniform interface abstracting a 2-layer prover stack `[conP, layP]` (`useSamples = false`)
and a 3-layer prover stack `[sampP, conP, layP]` (`useSamples = true`) over the same `[conP, layP]`
base handler. -/
structure ProverAdapter {stateTy unitTy : V.Ty}
    (prover : Role) (useSamples : Bool) (events : List (ShapeEvent V))
    (hBase : Handler (RSig M) (RSig M) Stop (HList M.Val [stateTy, .seq unitTy none])) where
  σ : Type
  h : Handler (RSig M) (RSig M) Stop σ
  Inv : σ → M.Val stateTy → List (M.Val unitTy) → Prop
  passMark : ∀ op s, (op = .begin (ROp.occurrence M op) ∨ op = .settle (ROp.occurrence M op)) →
    h.clause op s = .call op fun reply => .done (reply, s)
  passClosed : ∀ op s st buf, Inv s st buf → ROp.IsClosed M op →
    (∀ law at_ τ, op = .own (.coin law) [] at_ [] .nil τ → useSamples = false) →
    hBase.clause op (.cons st (.cons buf .nil)) =
      .call op (fun reply => .done (reply, .cons st (.cons buf .nil))) →
    h.clause op s = .call op (fun reply => .done (reply, s))
  stepBelow : ∀ op s st buf st' buf' reply, Inv s st buf →
    (∀ law at_ τ, op = .own (.coin law) [] at_ [] .nil τ → False) →
    hBase.clause op (.cons st (.cons buf .nil)) =
      .done (reply, .cons st' (.cons buf' .nil)) →
    ∃ s', Inv s' st' buf' ∧ h.clause op s = .done (reply, s')
  stepSampled : useSamples = true →
    ∀ law at_ τ s st buf, Inv s st buf →
      (∃ e ∈ events, e.site = at_.site ∧ e.τ = τ ∧ e.cls = .given (.coin law) prover []) →
      V.law law = some ⟨[], τ⟩ →
      ∃ coin s', Allows M (.coin law) [] .nil τ coin ∧ Inv s' st buf ∧
        h.clause (.own (.coin law) [] at_ [] .nil τ) s = .done (coin, s')

/-! ## Unified coupled simulation for streaming `.derived` (with or without `samples`) -/

theorem simulate_derived_gen {enc : VocabEncoder V} {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)} {layout : Layout} {stateTy suiteUnitTy unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    (cPClauses : List (Clause V d.admitted.program.headers prover stateTy))
    (cVClauses : List (Clause V d.admitted.program.headers verifier stateTy))
    (lPClauses : List (Clause V d.admitted.program.headers prover (.seq unitTy none)))
    (lVClauses : List (Clause V d.admitted.program.headers verifier (streamStateTy unitTy)))
    (conP' : Layer V d.admitted.program.headers prover d.entry.ins)
    (conV' : Layer V d.admitted.program.headers verifier d.entry.ins)
    (layP' : Layer V d.admitted.program.headers prover d.entry.ins)
    (layV' : Layer V d.admitted.program.headers verifier d.entry.ins)
    (hCPSt : conP'.state = stateTy) (hCVSt : conV'.state = stateTy)
    (hLPSt : layP'.state = .seq unitTy none) (hLVSt : layV'.state = streamStateTy unitTy)
    (hCPCl : hCPSt ▸ conP'.clauses = cPClauses) (hCVCl : hCVSt ▸ conV'.clauses = cVClauses)
    (hLPCl : hLPSt ▸ layP'.clauses = lPClauses) (hLVCl : hLVSt ▸ layV'.clauses = lVClauses)
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) = .ok (cPClauses, cVClauses))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) = .ok (lPClauses, lVClauses))
    (useSamples : Bool)
    (adapter : ProverAdapter M prover useSamples (d.entry.shape.events [] id)
      (castStack2Handler M (Defs.fnTable M d.admitted.program.defs)
        (Defs.rTable M d.admitted.program.defs) conP' layP' hCPSt hLPSt)) :
    let skipSites : List Site :=
      if useSamples then d.entry.shape.heardCoins ++ d.entry.shape.proverPrivateCoins prover
      else d.entry.shape.heardCoins
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (pP : Program M BP) (pV : Program M BV)
      (sP : adapter.σ) (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      adapter.Inv sP st buf →
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
      LawfulFor M prover useSamples source p →
      FedFor M prover useSamples source p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at_ τ, at_.site ∉ skipSites → source₁ at_ τ = source at_ τ) →
        ∀ e, GExec M source₁ p e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (sP' : adapter.σ) (finalSt : M.Val stateTy)
        (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
        adapter.Inv sP' finalSt (buf ++ suffix) ∧
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover (adapter.h.run (retryOf M none) pP sP) recP (.returned (outP, sP')) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
              (Defs.rTable M d.admitted.program.defs) [conV', layV']).run (retryOf M none) pV
                (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
            recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
              (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at_ τ, at_.site ∉ skipSites → source' at_ τ = source at_ τ) ∧
        GExec M source' p (.returned a) := by
  intro skipSites
  cases conP' with
  | mk cPLine cPSt cPTakes cPGives cPCl cPAgain cPStart cPFin =>
      cases conV' with
      | mk cVLine cVSt cVTakes cVGives cVCl cVAgain cVStart cVFin =>
          cases layP' with
          | mk lPLine lPSt lPTakes lPGives lPCl lPAgain lPStart lPFin =>
              cases layV' with
              | mk lVLine lVSt lVTakes lVGives lVCl lVAgain lVStart lVFin =>
                  dsimp only at hCPSt hCVSt hLPSt hLVSt
                  subst cPSt; subst cVSt; subst lPSt; subst lVSt
                  dsimp only at hCPCl hCVCl hLPCl hLVCl adapter
                  subst hCPCl; subst hCVCl; subst hLPCl; subst hLVCl
                  let conP0 : Layer V d.admitted.program.headers prover d.entry.ins :=
                    ⟨cPLine, stateTy, cPTakes, cPGives, cPCl, cPAgain, cPStart, cPFin⟩
                  let conV0 : Layer V d.admitted.program.headers verifier d.entry.ins :=
                    ⟨cVLine, stateTy, cVTakes, cVGives, cVCl, cVAgain, cVStart, cVFin⟩
                  let layP0 : Layer V d.admitted.program.headers prover d.entry.ins :=
                    ⟨lPLine, .seq unitTy none, lPTakes, lPGives, lPCl, lPAgain, lPStart, lPFin⟩
                  let layV0 : Layer V d.admitted.program.headers verifier d.entry.ins :=
                    ⟨lVLine, streamStateTy unitTy, lVTakes, lVGives, lVCl, lVAgain, lVStart, lVFin⟩
                  let fnTable := Defs.fnTable M d.admitted.program.defs
                  let rTable := Defs.rTable M d.admitted.program.defs
                  let events := d.entry.shape.events [] id
                  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
                  have hFst : eventsAbs.map Prod.fst = events :=
                    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
                  have hConUnm := fun op hCl =>
                    construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
                  have hLayUnm := fun op hCl =>
                    streaming_layout_unmatched_closed M 0 events hSL op hCl
                  have hPassBaseP : ∀ op (st : M.Val stateTy) (buf : List (M.Val unitTy)),
                      ROp.IsClosed M op →
                      (Stack.handler M fnTable rTable [conP0, layP0]).clause op (.cons st (.cons buf .nil)) =
                        .call op fun reply => .done (reply, .cons st (.cons buf .nil)) := fun op st buf hCl =>
                    stack2_clause_pass M fnTable rTable conP0 layP0 op st buf
                      (clause_answer_unmatched_all M fnTable rTable op st cPCl (hConUnm op hCl).1)
                      (clause_answer_unmatched_all M fnTable rTable op buf lPCl (hLayUnm op hCl).1)
                  have hPassV : ∀ op (st : M.Val stateTy) (lst : M.Val (streamStateTy unitTy)),
                      ROp.IsClosed M op →
                      (Stack.handler M fnTable rTable [conV0, layV0]).clause op (.cons st (.cons lst .nil)) =
                        .call op fun reply => .done (reply, .cons st (.cons lst .nil)) := fun op st lst hCl =>
                    stack2_clause_pass M fnTable rTable conV0 layV0 op st lst
                      (clause_answer_unmatched_all M fnTable rTable op st cVCl (hConUnm op hCl).2)
                      (clause_answer_unmatched_all M fnTable rTable op lst lVCl (hLayUnm op hCl).2)
                  have hHeardInSkip : ∀ s, s ∈ d.entry.shape.heardCoins → s ∈ skipSites := by
                    intro s hs
                    dsimp only [skipSites]
                    cases useSamples
                    · exact hs
                    · exact List.mem_append_left _ hs
                  have hEventDisc : ∀ e ∈ events,
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
                    intro e he
                    rw [← hFst] at he
                    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
                    exact construction_event_disc 0 eventsAbs hCC p hp
                  intro A BP BV p
                  let SimGoal := fun (p0 : Protocol M A) (postP : A → BP → Prop) (postV : A → BV → Prop)
                      (sP : adapter.σ) (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M)
                      (qP : Program M BP) (qV : Program M BV) =>
                    ∃ (a : A) (outP : BP) (outV : BV) (sP' : adapter.σ) (finalSt : M.Val stateTy)
                      (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
                      adapter.Inv sP' finalSt (buf ++ suffix) ∧
                      (∀ u ∈ suffix, M.Valid unitTy u) ∧
                      Alone M source prover (adapter.h.run (retryOf M none) qP sP) recP (.returned (outP, sP')) ∧
                      (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                        ∃ recV, Alone M source verifier
                          ((Stack.handler M fnTable rTable [conV0, layV0]).run (retryOf M none) qV
                              (.cons st (.cons (buf ++ suffix ++ post, (buf.length, ())) .nil)))
                          recV (.returned (outV, .cons finalSt
                            (.cons (buf ++ suffix ++ post, (buf.length + suffix.length, ())) .nil)))) ∧
                      postP a outP ∧ postV a outV ∧
                      Lawful M source' p0 ∧
                      (∀ at_ τ, at_.site ∉ skipSites → source' at_ τ = source at_ τ) ∧
                      GExec M source' p0 (.returned a)
                  induction p with
                  | done a =>
                      intro postP postV pP pV sP st buf source hInv hStV hBufV hProjP hProjV hSafeP hSafeV hShapeP hShapeV _ _ _ _ _
                      refine peelMarks_alone M (h := adapter.h) adapter.passMark
                        (fun qP => SimGoal (.done a) postP postV sP st buf source qP pV)
                        (fun qP hNotMP hPP hSP hShP => ?_)
                        (fun at_ kP h => by
                          obtain ⟨a', outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a', outP, outV, sP', fSt, suf, .began prover at_ :: recP, src', hI, h1,
                            by rw [stack_run_begin M _ at_ kP _ (adapter.passMark _ _ (.inl rfl))]; exact .begin h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        (fun at_ kP h => by
                          obtain ⟨a', outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a', outP, outV, sP', fSt, suf, .settled prover at_ :: recP, src', hI, h1,
                            by rw [stack_run_settle M _ at_ kP _ (adapter.passMark _ _ (.inr rfl))]; exact .settle h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        hProjP hSafeP hShapeP
                      cases hPP with
                      | done hPostP =>
                          refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conV0, layV0])
                            (fun op s hM => by
                              cases s with | cons st' s1 => cases s1 with | cons lst' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ _ trivial)
                            (fun qV => SimGoal (.done a) postP postV sP st buf source (.done _) qV)
                            (fun qV hNotMV hPV hSV hShV => ?_)
                            (fun at_ kV h => by
                              obtain ⟨a', outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                              exact ⟨a', outP, outV, sP', fSt, suf, recP, src', hI, h1, h2,
                                fun post hPost =>
                                  let ⟨recV, hAlV⟩ := h3 post hPost
                                  ⟨.began verifier at_ :: recV,
                                    by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hAlV⟩,
                                h4, h5, h6, h7, h8⟩)
                            (fun at_ kV h => by
                              obtain ⟨a', outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                              exact ⟨a', outP, outV, sP', fSt, suf, recP, src', hI, h1, h2,
                                fun post hPost =>
                                  let ⟨recV, hAlV⟩ := h3 post hPost
                                  ⟨.settled verifier at_ :: recV,
                                    by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hAlV⟩,
                                h4, h5, h6, h7, h8⟩)
                            hProjV hSafeV hShapeV
                          cases hPV with
                          | done hPostV =>
                              exact ⟨a, _, _, sP, st, [], [], source,
                                by simpa using hInv,
                                (fun _ h => nomatch h),
                                by simpa [Handler.run] using Alone.done,
                                fun post _ => ⟨[], by simpa [Handler.run] using Alone.done⟩,
                                hPostP, hPostV, trivial, fun _ _ _ => rfl, ⟨[], .done⟩⟩
                          | begins _ => exact False.elim (hNotMV trivial)
                          | settles _ => exact False.elim (hNotMV trivial)
                      | begins _ => exact False.elim (hNotMP trivial)
                      | settles _ => exact False.elim (hNotMP trivial)
                  | halt payload =>
                      intro _ _ _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ _ _ hNoHalt
                      obtain ⟨a, hContra⟩ := hNoHalt source trivial (fun _ _ _ => rfl)
                        (.stopped payload.1 payload.2) ⟨[], .halt⟩
                      cases hContra
                  | call op k ih =>
                      intro postP postV pP pV sP st buf source hInv hStV hBufV hProjP hProjV hSafeP hSafeV
                        hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt
                      refine peelMarks_alone M (h := adapter.h) adapter.passMark
                        (fun qP => SimGoal (.call op k) postP postV sP st buf source qP pV)
                        (fun qP hNotMP hPP hSP hShP => ?_)
                        (fun at_ kP h => by
                          obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, sP', fSt, suf, .began prover at_ :: recP, src', hI, h1,
                            by rw [stack_run_begin M _ at_ kP _ (adapter.passMark _ _ (.inl rfl))]; exact .begin h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        (fun at_ kP h => by
                          obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, sP', fSt, suf, .settled prover at_ :: recP, src', hI, h1,
                            by rw [stack_run_settle M _ at_ kP _ (adapter.passMark _ _ (.inr rfl))]; exact .settle h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        hProjP hSafeP hShapeP
                      refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conV0, layV0])
                        (fun op s hM => by
                          cases s with | cons st' s1 => cases s1 with | cons lst' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ _ trivial)
                        (fun qV => SimGoal (.call op k) postP postV sP st buf source qP qV)
                        (fun qV hNotMV hPV hSV hShV => ?_)
                        (fun at_ kV h => by
                          obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2,
                            fun post hPost =>
                              let ⟨recV, hAlV⟩ := h3 post hPost
                              ⟨.began verifier at_ :: recV,
                                by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hAlV⟩,
                            h4, h5, h6, h7, h8⟩)
                        (fun at_ kV h => by
                          obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2,
                            fun post hPost =>
                              let ⟨recV, hAlV⟩ := h3 post hPost
                              ⟨.settled verifier at_ :: recV,
                                by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hAlV⟩,
                            h4, h5, h6, h7, h8⟩)
                        hProjV hSafeV hShapeV
                      cases op with
                      | flow kind giver getters at_ τ x =>
                          have hNoHalt' : ∀ source₁, Lawful M source₁ (k ()) →
                              (∀ at' τ', at'.site ∉ skipSites → source₁ at' τ' = source at' τ') →
                              ∀ e, GExec M source₁ (k ()) e → ∃ a, e = .returned a := by
                            intro source₁ hL₁ hAg e ⟨evs, hRun⟩
                            exact hNoHalt source₁ hL₁ hAg e ⟨_, .flow hRun⟩
                          cases hPP with
                          | begins _ => exact False.elim (hNotMP trivial)
                          | settles _ => exact False.elim (hNotMP trivial)
                          | gave hNotIn hPP' =>
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
                                  have hEPInAbs : ∃ bP, (eP, bP) ∈ eventsAbs := by
                                    have hM : eP ∈ eventsAbs.map Prod.fst := hFst.symm ▸ hEP
                                    obtain ⟨⟨e₀, b₀⟩, hIn, hEq⟩ := List.mem_map.mp hM
                                    dsimp only at hEq; subst hEq
                                    exact ⟨b₀, hIn⟩
                                  obtain ⟨needP, hNeedP⟩ := hEPInAbs
                                  obtain ⟨wRef, chunk, hWFind, hWD, hChV, hLayPAns⟩ :=
                                    streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                                      kind getters ⟨at_.path, at_.site.key⟩ τ x buf hMsgV
                                      ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                                  have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                                    intro u hu
                                    rcases List.mem_append.mp hu with h1 | h2
                                    · exact hBufV u h1
                                    · exact hChV u h2
                                  cases needP with
                                  | true =>
                                      obtain ⟨encP, encVal, st', hEncFindP, hEncD, hAbsD, hSt'V, hConPAns⟩ :=
                                        construction_clauses_answer_prover_flow_abs M 0 eventsAbs hCC
                                          kind getters at_ τ x st hMsgV hStV ⟨eP, hNeedP, hSiteP, hTyP, hClsP⟩
                                      obtain ⟨encV, hEncFindV, hConVAns⟩ :=
                                        construction_clauses_answer_verifier_flow_abs M 0 eventsAbs hCC
                                          kind at_ τ st ⟨eP, hNeedP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                      have hEncEq : encP = encV := Option.some.inj (hEncFindP.symm.trans hEncFindV)
                                      subst hEncEq
                                      obtain ⟨rRef, hRFind, _⟩ :=
                                        streaming_layout_answer_verifier_flow M 0 events hSL
                                          kind ⟨at_.path, at_.site.key⟩ τ buf buf.length
                                          ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                      have hBaseStepP : (Stack.handler M fnTable rTable [conP0, layP0]).clause
                                          (.give kind getters at_ τ x) (.cons st (.cons buf .nil)) =
                                          .done ((), .cons st' (.cons (buf ++ chunk) .nil)) :=
                                        stack2_clause_step M fnTable rTable conP0 layP0 _ _ st st' buf (buf ++ chunk)
                                          () () _ hConPAns hLayPAns rfl
                                      obtain ⟨sP1, hInv1, hStepP⟩ :=
                                        adapter.stepBelow (.give kind getters at_ τ x) sP st buf st' (buf ++ chunk) ()
                                          hInv (fun _ _ _ h => nomatch h) hBaseStepP
                                      obtain ⟨a, outP, outV, sP', fSt, suf', recP, src', hInv', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih () _ _ sP1 st' (buf ++ chunk) source hInv1 hSt'V hBufChV hPP' hPV'
                                          (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                                          (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                      refine ⟨a, outP, outV, sP', fSt, chunk ++ suf', recP, src',
                                        by simpa [List.append_assoc] using hInv', ?_, ?_, ?_,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
                                      · intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hChV u h1
                                        · exact hSufV u h2
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        exact hAlP
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
                                        have hStepV : (Stack.handler M fnTable rTable [conV0, layV0]).clause
                                            (.get kind prover at_ τ)
                                            (.cons st (.cons (buf ++ chunk ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                            .done (x, .cons st' (.cons (buf ++ chunk ++ (suf' ++ post),
                                              (buf.length + chunk.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV0 layV0 _ _ st st'
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
                                  | false =>
                                      have hNoAbs : ∀ e' b', (e', b') ∈ eventsAbs → e'.site = at_.site →
                                          e'.τ = τ → (∃ gs, verifier ∈ gs ∧ e'.cls = .flow kind prover gs) →
                                          b' = false := by
                                        intro e' b' hIn hS hT ⟨gs, hVg, hC⟩
                                        exact eventsWithAbsorb_flow_consistent prover verifier [] id false
                                          d.entry.shape hIn hNeedP (hS.trans hSiteP.symm)
                                          (hT.trans hTyP.symm) hC hVg hClsP hVin
                                      obtain ⟨hUnmP, hUnmV⟩ :=
                                        construction_clauses_unmatched_elided_flow M 0 eventsAbs hCC
                                          kind getters at_ τ x hNoAbs
                                      have hConPPass : Clause.answer M fnTable rTable cPCl
                                          (.give kind getters at_ τ x) st =
                                          .call (.give kind getters at_ τ x) fun reply => .done (reply, st) :=
                                        clause_answer_unmatched_all M fnTable rTable _ st cPCl hUnmP
                                      have hConVPass : Clause.answer M fnTable rTable cVCl
                                          (.get kind prover at_ τ) st =
                                          .call (.get kind prover at_ τ) fun reply => .done (reply, st) :=
                                        clause_answer_unmatched_all M fnTable rTable _ st cVCl hUnmV
                                      obtain ⟨wRef', chunk', hWFind', hWD', hChV', hLayPAns'⟩ :=
                                        streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                                          kind getters at_ τ x buf hMsgV
                                          ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                                      have hBufChV' : ∀ u ∈ buf ++ chunk', M.Valid unitTy u := by
                                        intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hBufV u h1
                                        · exact hChV' u h2
                                      have hBaseStepP : (Stack.handler M fnTable rTable [conP0, layP0]).clause
                                          (.give kind getters at_ τ x) (.cons st (.cons buf .nil)) =
                                          .done ((), .cons st (.cons (buf ++ chunk') .nil)) :=
                                        stack2_clause_step M fnTable rTable conP0 layP0 _ _ st st buf (buf ++ chunk')
                                          () () _ hConPPass hLayPAns' rfl
                                      obtain ⟨sP1, hInv1, hStepP⟩ :=
                                        adapter.stepBelow (.give kind getters at_ τ x) sP st buf st (buf ++ chunk') ()
                                          hInv (fun _ _ _ h => nomatch h) hBaseStepP
                                      obtain ⟨a, outP, outV, sP', fSt, suf', recP, src', hInv', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih () _ _ sP1 st (buf ++ chunk') source hInv1 hStV hBufChV' hPP' hPV'
                                          (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                                          (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                      refine ⟨a, outP, outV, sP', fSt, chunk' ++ suf', recP, src',
                                        by simpa [List.append_assoc] using hInv', ?_, ?_, ?_,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
                                      · intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hChV' u h1
                                        · exact hSufV u h2
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        exact hAlP
                                      · intro post hPost
                                        have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                                          intro u hu
                                          rcases List.mem_append.mp hu with h1 | h2
                                          · exact hSufV u h1
                                          · exact hPost u h2
                                        obtain ⟨rRef', hRFind', hLayVAns'⟩ :=
                                          streaming_layout_answer_verifier_flow M 0 events hSL
                                            kind at_ τ (buf ++ chunk' ++ (suf' ++ post)) buf.length
                                            ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                        have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind' hRFind'
                                          hMsgV hBufV hSufPostV hWD'
                                        have hLayVDone := hLayVAns' x (buf.length + chunk'.length) hRD
                                        have hStepV : (Stack.handler M fnTable rTable [conV0, layV0]).clause
                                            (.get kind prover at_ τ)
                                            (.cons st (.cons (buf ++ chunk' ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                            .done (x, .cons st (.cons (buf ++ chunk' ++ (suf' ++ post),
                                              (buf.length + chunk'.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV0 layV0 _ _ st st
                                            (buf ++ chunk' ++ (suf' ++ post), (buf.length, ()))
                                            (buf ++ chunk' ++ (suf' ++ post), (buf.length + chunk'.length, ()))
                                            x x _ hConVPass hLayVDone rfl
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨recV, ?_⟩
                                        have hBufEq : buf ++ (chunk' ++ suf') ++ post = buf ++ chunk' ++ (suf' ++ post) := by
                                          simp [List.append_assoc]
                                        rw [hBufEq]
                                        rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                        have hLenEq : buf.length + (chunk' ++ suf').length =
                                            (buf ++ chunk').length + suf'.length := by
                                          simp [List.length_append, Nat.add_assoc]
                                        have hBufEq2 : buf ++ chunk' ++ (suf' ++ post) = (buf ++ chunk') ++ suf' ++ post := by
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
                                  obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                                    ih () _ _ sP st buf source hInv hStV hBufV hPP' hPV' hSP hSV hShP hShV
                                      (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                  exact ⟨a, outP, outV, sP', fSt, suf, recP, src', hI, h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
                      | given gkind owner hearers at_ gIns payload τ =>
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
                                    have hEVAbs : ∃ p ∈ eventsAbs, p.1 = eV := by
                                      have hM : eV ∈ eventsAbs.map Prod.fst := hFst.symm ▸ hEV
                                      obtain ⟨p, hp, hEq⟩ := List.mem_map.mp hM
                                      exact ⟨p, hp, hEq⟩
                                    obtain ⟨pV, hpV, hpVEq⟩ := hEVAbs
                                    have hSuf0 : ∀ k p, eventsAbs[k]? = some p → events[0 + k]? = some p.1 := by
                                      intro k p hk
                                      rw [Nat.zero_add, ← hFst, List.getElem?_map, hk]; rfl
                                    obtain ⟨idxP, ⟨ePSite, ePCls, ePτ⟩, derP, coinP, stP', hIdxP, hSiteP, hTyP,
                                      ⟨hsP, hPinP, hClsP⟩, hDerFindP, hDerDP, hCoinPV, hStP'V, hConPAns⟩ :=
                                      construction_clauses_answer_prover_coin M 0 eventsAbs hSuf0 hCC
                                        law at_ τ st hStV
                                        ⟨pV, hpV, hpVEq.symm ▸ hSiteV, hpVEq.symm ▸ hTyV,
                                          hearers, hPin, hpVEq.symm ▸ hClsV⟩
                                    obtain ⟨idxV, ⟨eV'Site, eV'Cls, eV'τ⟩, derV, coinV, stV', hIdxV, hSiteV', hTyV',
                                      hClsV', hLawV', hDerFindV, hDerDV, hCoinVV, hStV'V, hConVAns⟩ :=
                                      construction_clauses_answer_verifier_coin M 0 eventsAbs hSuf0 hCC
                                        law hearers at_ τ st hStV
                                        ⟨pV, hpV, hpVEq.symm ▸ hSiteV, hpVEq.symm ▸ hTyV,
                                          hPin, hpVEq.symm ▸ hClsV⟩
                                    dsimp only at hSiteP hTyP hClsP hSiteV' hTyV' hClsV'
                                    subst ePτ; subst eV'τ
                                    have hDerEq : derP = derV := Option.some.inj (hDerFindP.symm.trans hDerFindV)
                                    subst hDerEq
                                    have hEvalEq : Process.done (HList.cons coinP (HList.cons stP' HList.nil)) =
                                        .done (.cons coinV (.cons stV' .nil)) := hDerDP.symm.trans hDerDV
                                    cases hEvalEq
                                    have hAllowsCoin : Allows M (.coin law) [] .nil τ coinP :=
                                      suiteLawful_allows M hConDecl hSuiteLaw hDerFindV
                                        (List.mem_of_getElem? hIdxV) (hHCons ▸ hClsV') rfl hLawV'
                                        hStV (drawLabel_bytes at_.site) hDerDV
                                    have hAtSkip : at_.site ∈ skipSites := by
                                      apply hHeardInSkip
                                      rw [← hSiteV']
                                      exact mem_heardCoins_of_event (List.mem_of_getElem? hIdxV) (hHCons ▸ hClsV')
                                    have hLP' : LawfulFor M prover useSamples source (k coinP) := by
                                      subst hHCons; exact hLP coinP hAllowsCoin
                                    have hFed' : FedFor M prover useSamples source (k coinP) := by
                                      subst hHCons; exact hFed coinP hAllowsCoin
                                    have hOccK : Protocol.OccsIn M (· ≠ at_) (k coinP) := (hUniq coinP).1
                                    have hNoHalt' : ∀ source₁, Lawful M source₁ (k coinP) →
                                        (∀ at' τ', at'.site ∉ skipSites → source₁ at' τ' = source at' τ') →
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
                                      have hAg₂ : ∀ at' τ', at'.site ∉ skipSites →
                                          source₂ at' τ' = source at' τ' := by
                                        intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtSkip)
                                        dsimp only [source₂]
                                        rw [patchSource_ne M source₁ at_ τ coinP hne τ']
                                        exact hAg₁ at' τ' hNotIn
                                      have hRun₂ : GRun M source₂
                                          (.call (.given (.coin law) verifier hearers at_ [] .nil τ) k) _ e :=
                                        .given (patchSource_self M source₁ at_ τ coinP)
                                          (grun_of_agree M hAgree12 hOccK hRun₁)
                                      exact hNoHalt source₂ hL₂ hAg₂ e ⟨_, hRun₂⟩
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
                                      have hBaseStepP : (Stack.handler M fnTable rTable [conP0, layP0]).clause
                                          (.hear (.coin law) verifier at_ τ) (.cons st (.cons buf .nil)) =
                                          .done (coinP, .cons stP' (.cons (buf ++ chunk) .nil)) :=
                                        stack2_clause_step M fnTable rTable conP0 layP0 _ _ st stP' buf (buf ++ chunk)
                                          () coinP _ hConPAns (hLayPAns buf) rfl
                                      obtain ⟨sP1, hInv1, hStepP⟩ :=
                                        adapter.stepBelow (.hear (.coin law) verifier at_ τ) sP st buf stP' (buf ++ chunk) coinP
                                          hInv (fun _ _ _ h => nomatch h) hBaseStepP
                                      obtain ⟨a, outP, outV, sP', fSt, suf', recP, src', hInv', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih coinP _ _ sP1 stP' (buf ++ chunk) source hInv1 hStP'V hBufChV
                                          (hPP' coinP) (hPV' coinP)
                                          (hSP.2 coinP hCoinPV) (hSV.2 coinP hCoinPV)
                                          (hShP.2 coinP trivial) (hShV.2 coinP trivial)
                                          (hPShape.2 coinP) (hUniq coinP).2 hLP' hFed' hNoHalt'
                                      let src'' := patchSource M src' at_ τ coinP
                                      have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M src' at_ τ coinP hne τ').symm
                                      refine ⟨a, outP, outV, sP', fSt, chunk ++ suf', recP, src'',
                                        by simpa [List.append_assoc] using hInv', ?_, ?_, ?_,
                                        hPostP, hPostV, ?_, ?_, ?_⟩
                                      · intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hChV u h1
                                        · exact hSufV u h2
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        exact hAlP
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
                                        have hStepV : (Stack.handler M fnTable rTable [conV0, layV0]).clause
                                            (.own (.coin law) hearers at_ [] .nil τ)
                                            (.cons st (.cons (buf ++ chunk ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                            .done (coinP, .cons stP' (.cons (buf ++ chunk ++ (suf' ++ post),
                                              (buf.length + chunk.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV0 layV0 _ _ st stP'
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
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtSkip)
                                        dsimp only [src'']
                                        rw [patchSource_ne M src' at_ τ coinP hne τ']
                                        exact hAgSrc' at' τ' hNotIn
                                      · exact ⟨_, .given (patchSource_self M src' at_ τ coinP)
                                          (grun_of_agree M hAgPatch hOccK hRun')⟩
                                    · have hCarP : ePSite ∉ layout.carry := hSiteP.symm ▸ hCar
                                      have hCarV : eV'Site ∉ layout.carry := hSiteV'.symm ▸ hCar
                                      rw [ite_eq_right hCarP] at hCarryP
                                      rw [ite_eq_right hCarV] at hCarryV
                                      have hBaseStepP : (Stack.handler M fnTable rTable [conP0, layP0]).clause
                                          (.hear (.coin law) verifier at_ τ) (.cons st (.cons buf .nil)) =
                                          .done (coinP, .cons stP' (.cons buf .nil)) :=
                                        stack2_clause_step M fnTable rTable conP0 layP0 _ _ st stP' buf buf
                                          () coinP _ hConPAns (hCarryP.1 buf) rfl
                                      obtain ⟨sP1, hInv1, hStepP⟩ :=
                                        adapter.stepBelow (.hear (.coin law) verifier at_ τ) sP st buf stP' buf coinP
                                          hInv (fun _ _ _ h => nomatch h) hBaseStepP
                                      obtain ⟨a, outP, outV, sP', fSt, suf', recP, src', hInv', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih coinP _ _ sP1 stP' buf source hInv1 hStP'V hBufV
                                          (hPP' coinP) (hPV' coinP)
                                          (hSP.2 coinP hCoinPV) (hSV.2 coinP hCoinPV)
                                          (hShP.2 coinP trivial) (hShV.2 coinP trivial)
                                          (hPShape.2 coinP) (hUniq coinP).2 hLP' hFed' hNoHalt'
                                      let src'' := patchSource M src' at_ τ coinP
                                      have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M src' at_ τ coinP hne τ').symm
                                      refine ⟨a, outP, outV, sP', fSt, suf', recP, src'', hInv', hSufV, ?_, ?_,
                                        hPostP, hPostV, ?_, ?_, ?_⟩
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        exact hAlP
                                      · intro post hPost
                                        have hStepV : (Stack.handler M fnTable rTable [conV0, layV0]).clause
                                            (.own (.coin law) hearers at_ [] .nil τ)
                                            (.cons st (.cons (buf ++ suf' ++ post, (buf.length, ())) .nil)) =
                                            .done (coinP, .cons stP' (.cons (buf ++ suf' ++ post, (buf.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV0 layV0 _ _ st stP'
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
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtSkip)
                                        dsimp only [src'']
                                        rw [patchSource_ne M src' at_ τ coinP hne τ']
                                        exact hAgSrc' at' τ' hNotIn
                                      · exact ⟨_, .given (patchSource_self M src' at_ τ coinP)
                                          (grun_of_agree M hAgPatch hOccK hRun')⟩
                          | isFalse hHeardCoin =>
                            obtain ⟨eG, hEG, hSiteG, hTyG, hClsG⟩ := hPShape.1
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
                            have hSampDec : Decidable ((∃ law, gkind = .coin law) ∧ useSamples = true ∧ owner = prover ∧ hearers = [] ∧ gIns = []) :=
                              @instDecidableAnd _ _ hCoinDec
                                (@instDecidableAnd _ _ inferInstance
                                  (@instDecidableAnd _ _ inferInstance
                                    (@instDecidableAnd _ _ inferInstance inferInstance)))
                            cases hSampDec with
                            | isTrue hSampCoin =>
                                obtain ⟨⟨law, rfl⟩, hUseT, hOwnerEq, rfl, rfl⟩ := hSampCoin
                                subst owner
                                cases payload
                                cases hPP with
                                | begins _ => exact False.elim (hNotMP trivial)
                                | settles _ => exact False.elim (hNotMP trivial)
                                | heard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | unheard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | owned hPP' =>
                                    cases hPV with
                                    | begins _ => exact False.elim (hNotMV trivial)
                                    | settles _ => exact False.elim (hNotMV trivial)
                                    | owned _ => exact absurd rfl hNe
                                    | heard _ hInNil _ => cases hInNil
                                    | unheard _ _ hPV' =>
                                        obtain ⟨eP, hEP, hSiteP, hTyP, hClsP, hTypedP⟩ := hShP.1
                                        obtain ⟨sig, hLawSig, hSigIns, hSigOut⟩ := hTypedP
                                        have hLawEq : V.law law = some ⟨[], τ⟩ := by
                                          cases sig with
                                          | mk sI sO =>
                                              dsimp only at hSigIns hSigOut
                                              subst hSigIns; subst hSigOut; exact hLawSig
                                        obtain ⟨coin, sP1, hAllowsCoin, hInv1, hStepP⟩ :=
                                          adapter.stepSampled hUseT law at_ τ sP st buf hInv
                                            ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ hLawEq
                                        have hCoinV : M.Valid τ coin := allows_valid M hAllowsCoin
                                        have hAtSkip : at_.site ∈ skipSites := by
                                          dsimp only [skipSites]
                                          rw [hUseT]; simp only [↓reduceIte]
                                          refine List.mem_append_right _ ?_
                                          rw [← hSiteP]
                                          exact mem_proverPrivateCoins_of_event hEP hClsP
                                        have hLP' : LawfulFor M prover useSamples source (k coin) := by
                                          dsimp only [LawfulFor] at hLP
                                          rw [ite_eq_left ⟨hUseT, rfl⟩] at hLP
                                          exact hLP coin hAllowsCoin
                                        have hFed' : FedFor M prover useSamples source (k coin) := by
                                          dsimp only [FedFor] at hFed
                                          rw [ite_eq_left ⟨hUseT, rfl⟩] at hFed
                                          exact hFed coin hAllowsCoin
                                        have hOccK : Protocol.OccsIn M (· ≠ at_) (k coin) := (hUniq coin).1
                                        have hNoHalt' : ∀ source₁, Lawful M source₁ (k coin) →
                                            (∀ at' τ', at'.site ∉ skipSites → source₁ at' τ' = source at' τ') →
                                            ∀ e, GExec M source₁ (k coin) e → ∃ a, e = .returned a := by
                                          intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
                                          let source₂ := patchSource M source₁ at_ τ coin
                                          have hAgree12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = source₂ at' τ' :=
                                            fun at' τ' hne => (patchSource_ne M source₁ at_ τ coin hne τ').symm
                                          have hL₂ : Lawful M source₂ (.call (.given (.coin law) prover [] at_ [] .nil τ) k) := by
                                            intro v hv
                                            dsimp only [source₂] at hv
                                            rw [patchSource_self] at hv; cases hv
                                            exact ⟨hAllowsCoin, lawful_of_agree M hAgree12 hOccK hL₁⟩
                                          have hAg₂ : ∀ at' τ', at'.site ∉ skipSites → source₂ at' τ' = source at' τ' := by
                                            intro at' τ' hNotIn
                                            have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtSkip)
                                            dsimp only [source₂]
                                            rw [patchSource_ne M source₁ at_ τ coin hne τ']
                                            exact hAg₁ at' τ' hNotIn
                                          exact hNoHalt source₂ hL₂ hAg₂ e
                                            ⟨_, .given (patchSource_self M source₁ at_ τ coin)
                                              (grun_of_agree M hAgree12 hOccK hRun₁)⟩
                                        obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hInv', hSufV, hAlP, hAlV,
                                          hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                          ih coin _ _ sP1 st buf source hInv1 hStV hBufV (hPP' coin) (hPV' coin)
                                            (hSP.2 coin hCoinV) hSV (hShP.2 coin trivial) hShV
                                            (hPShape.2 coin) (hUniq coin).2 hLP' hFed' hNoHalt'
                                        let src'' := patchSource M src' at_ τ coin
                                        have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                          fun at' τ' hne => (patchSource_ne M src' at_ τ coin hne τ').symm
                                        refine ⟨a, outP, outV, sP', fSt, suf, recP, src'', hInv', hSufV, ?_, hAlV,
                                          hPostP, hPostV, ?_, ?_, ?_⟩
                                        · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                          exact hAlP
                                        · intro v hv
                                          dsimp only [src''] at hv
                                          rw [patchSource_self] at hv; cases hv
                                          exact ⟨hAllowsCoin, lawful_of_agree M hAgPatch hOccK hLSrc'⟩
                                        · intro at' τ' hNotIn
                                          have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtSkip)
                                          dsimp only [src'']
                                          rw [patchSource_ne M src' at_ τ coin hne τ']
                                          exact hAgSrc' at' τ' hNotIn
                                        · exact ⟨_, .given (patchSource_self M src' at_ τ coin)
                                            (grun_of_agree M hAgPatch hOccK hRun')⟩
                            | isFalse hNotSampCoin =>
                                have hSrcFed : ∃ v, source at_ τ = some v ∧ FedFor M prover useSamples source (k v) := by
                                  rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
                                  · cases gIns with
                                    | nil =>
                                        cases payload
                                        dsimp only [FedFor] at hFed
                                        have hNeg : ¬ (useSamples = true ∧ owner = prover) :=
                                          fun h => hNotSampCoin ⟨⟨law, rfl⟩, h.1, h.2, rfl, rfl⟩
                                        rw [ite_eq_right hNeg] at hFed
                                        exact hFed
                                    | cons _ _ => exact hFed
                                  · exact hFed
                                obtain ⟨v, hSrc, hFed'⟩ := hSrcFed
                                have hLPv : Allows M gkind gIns payload τ v ∧ LawfulFor M prover useSamples source (k v) := by
                                  rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
                                  · cases gIns with
                                    | nil =>
                                        cases payload
                                        dsimp only [LawfulFor] at hLP
                                        have hNeg : ¬ (useSamples = true ∧ owner = prover) :=
                                          fun h => hNotSampCoin ⟨⟨law, rfl⟩, h.1, h.2, rfl, rfl⟩
                                        rw [ite_eq_right hNeg] at hLP
                                        exact hLP v hSrc
                                    | cons _ _ => exact hLP v hSrc
                                  · exact hLP v hSrc
                                obtain ⟨hAllows, hLP'⟩ := hLPv
                                have hValV : M.Valid τ v := allows_valid M hAllows
                                have hIsClOwn : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ) := by
                                  rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩ <;> trivial
                                have hOccK : Protocol.OccsIn M (· ≠ at_) (k v) := (hUniq v).1
                                have hNoHalt' : ∀ source₁, Lawful M source₁ (k v) →
                                    (∀ at' τ', at'.site ∉ skipSites → source₁ at' τ' = source at' τ') →
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
                                  have hAg₂ : ∀ at' τ', at'.site ∉ skipSites → source₂ at' τ' = source at' τ' := by
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
                                    (∀ at' τ', at'.site ∉ skipSites → src' at' τ' = source at' τ') →
                                    GRun M src' (k v) evs' (.returned a) →
                                    ∃ src'', Lawful M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) ∧
                                      (∀ at' τ', at'.site ∉ skipSites → src'' at' τ' = source at' τ') ∧
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
                                        have hPassP : adapter.h.clause (.own gkind hearers at_ gIns payload τ) sP =
                                            .call (.own gkind hearers at_ gIns payload τ) fun reply => .done (reply, sP) := by
                                          refine adapter.passClosed _ sP st buf hInv hIsClOwn ?_ (hPassBaseP _ st buf hIsClOwn)
                                          intro law' at_' τ' hEqOp
                                          cases hEqOp
                                          cases hUse : useSamples with
                                          | false => rfl
                                          | true => exact False.elim (hNotSampCoin ⟨⟨law', rfl⟩, hUse, rfl, rfl, rfl⟩)
                                        obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hInv', hSufV, hAlP, hAlV,
                                          hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                          ih v _ _ sP st buf source hInv hStV hBufV (hPP' v) (hPV' v)
                                            (hSP.2 v hValV) hSV (hShP.2 v trivial) hShV
                                            (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                        obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                        refine ⟨a, outP, outV, sP', fSt, suf,
                                          .owned prover gkind at_ τ v :: recP, src'', hInv', hSufV, ?_, hAlV,
                                          hPostP, hPostV, hL'', hAg'', hGEx''⟩
                                        rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ hPassP]
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
                                        obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hInv', hSufV, hAlP, hAlV,
                                          hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                          ih v _ _ sP st buf source hInv hStV hBufV (hPP' v) (hPV' v)
                                            hSP (hSV.2 v hValV) hShP (hShV.2 v trivial)
                                            (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                        obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                        refine ⟨a, outP, outV, sP', fSt, suf, recP, src'', hInv', hSufV, hAlP, ?_,
                                          hPostP, hPostV, hL'', hAg'', hGEx''⟩
                                        intro post hPost
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨.owned verifier gkind at_ τ v :: recV, ?_⟩
                                        rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassV _ _ _ hIsClOwn)]
                                        exact .own hSrc hAlV'
                                    | unheard _ _ hPV' =>
                                        obtain ⟨a, outP, outV, sP', fSt, suf, recP, src', hInv', hSufV, hAlP, hAlV,
                                          hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                          ih v _ _ sP st buf source hInv hStV hBufV (hPP' v) (hPV' v)
                                            hSP hSV hShP hShV
                                            (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                        obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                        exact ⟨a, outP, outV, sP', fSt, suf, recP, src'', hInv', hSufV, hAlP, hAlV,
                                          hPostP, hPostV, hL'', hAg'', hGEx''⟩

/-! ## Coupled simulation for streaming `.authored` -/

private theorem simulate_authored {d : Deployed V} {layout : Layout} {unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {layP : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hLayDecl : d.declaration.layout = some layout)
    (hLayLaw : d.LayoutLawful M)
    (hLayPState : layP.state = .seq unitTy none) (hLayVState : layV.state = streamStateTy unitTy)
    (hAuth : checkAuthoredEvents prover verifier declKey
      (d.entry.shape.events [] id) = .ok ())
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
          have hEventDisc := authored_event_disc events hAuth
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
                      ∀ e, GExec M source₁ (k ()) e → ∃ a, e = .returned a := by
                    intro source₁ hL₁ hAg e ⟨evs, hRun⟩
                    exact hNoHalt source₁ hL₁ hAg e ⟨_, .flow hRun⟩
                  cases hPP with
                  | begins _ => exact False.elim (hNotMP trivial)
                  | settles _ => exact False.elim (hNotMP trivial)
                  | gave hNotIn hPP' =>
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
                          obtain ⟨wRef, chunk, hWFind, hWD, hChV, hLayPAns⟩ :=
                            streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                              kind getters at_ τ x buf hMsgV
                              ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                          have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                            intro u hu
                            rcases List.mem_append.mp hu with h1 | h2
                            · exact hBufV u h1
                            · exact hChV u h2
                          obtain ⟨a, outP, outV, suf', recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih () _ _ (buf ++ chunk) source hBufChV hPP' hPV'
                              (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                              (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                          have hStepP : (Stack.handler M fnTable rTable [layP']).clause
                              (.give kind getters at_ τ x) (.cons buf .nil) =
                              .done ((), .cons (buf ++ chunk) .nil) :=
                            stack1_clause_done M fnTable rTable layP' (.give kind getters at_ τ x) buf (buf ++ chunk) () hLayPAns
                          refine ⟨a, outP, outV, chunk ++ suf', recP, src', ?_, ?_, ?_,
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
                            obtain ⟨rRef, hRFind, hLayVAns⟩ :=
                              streaming_layout_answer_verifier_flow M 0 events hSL
                                kind at_ τ (buf ++ chunk ++ (suf' ++ post)) buf.length
                                ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                            have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind
                              hMsgV hBufV hSufPostV hWD
                            have hLayVDone := hLayVAns x (buf.length + chunk.length) hRD
                            have hStepV : (Stack.handler M fnTable rTable [layV']).clause
                                (.get kind prover at_ τ)
                                (.cons (buf ++ chunk ++ (suf' ++ post), (buf.length, ())) .nil) =
                                .done (x, .cons (buf ++ chunk ++ (suf' ++ post),
                                  (buf.length + chunk.length, ())) .nil) :=
                              stack1_clause_done M fnTable rTable layV' (.get kind prover at_ τ) _ _ x hLayVDone
                            obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                            refine ⟨recV, ?_⟩
                            have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                              simp [List.append_assoc]
                            rw [hBufEq, stack_run_clause_done M _ _ _ _ _ _ hStepV]
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
                          obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                            ih () _ _ buf source hBufV hPP' hPV' hSP hSV hShP hShV
                              (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                          exact ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
              | given gkind owner hearers at_ gIns payload τ =>
                  obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
                  have hDisc := hEventDisc eG hEG
                  rw [hClsG] at hDisc
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

private theorem cast_ins_eq_cast_hdr {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (ls : List (Layer V hs r hdr₂.ins)) :
    (congrArg ProtocolHeader.ins h) ▸ ls = h ▸ ls := by
  subst h; rfl

/-! ## Top-level streaming completeness (`deploy_complete`, `deploy_complete_streaming`) -/

/-- Streaming completeness for `deploy` under law-keyed `Deployed.SuiteLawfulFor enc M`. -/
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
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
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
  cases deploy_ok_elim enc a declaration d hDep with
  | interactive w _ => simp [Declaration.interactive, w.hCon] at hNonInt
  | authored w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hRecNil : w.layout.recover = [] := hNoRec w.layout w.hLayOpt
      cases buildLayoutLayers_ok_elim w.hLay with
      | compact wL _ => have hne := wL.hNonEmpty; simp [hRecNil] at hne
      | streaming wL hLPW hLVW =>
          have hEntryF : ((a.program.findProtocol declaration.entry).get
              (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
          let layP0 : Layer V a.program.headers w.prover w.foundPair.1.ins := wL.layP
          let layV0 : Layer V a.program.headers w.verifier w.foundPair.1.ins := wL.layV
          let layP' : Layer V a.program.headers w.prover _ := hEntryF ▸ layP0
          let layV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ layV0
          have hAuth' : checkAuthoredEvents w.prover w.verifier declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) = .ok () := by
            rw [hEntryF]; exact w.hAuth
          have hLayPSt : layP'.state = .seq wL.unitTy none := layer_cast_state hEntryF layP0
          have hLayVSt : layV'.state = streamStateTy wL.unitTy := layer_cast_state hEntryF layV0
          have hSL' : buildStreamingLayoutClauses.go a w.layout wL.unitTy wL.hfree
              w.prover w.verifier declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) =
              .ok (hLayPSt ▸ layP'.clauses, hLayVSt ▸ layV'.clauses) := by
            rw [layer_cast_clauses hEntryF layP0, layer_cast_clauses hEntryF layV0, hEntryF]
            exact wL.hStr
          obtain ⟨out, outP, outV, suffix, recP, source', hSufV, hAlP, hAlV,
            hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
            simulate_authored M w.hNe (d := w.toDeployed)
              w.hLayOpt hLayLaw hLayPSt hLayVSt hAuth' hSL'
              (protocolMeaning M a.program _ [] ins)
              (roleMeaning M a.program _ w.prover [] (hideAll M w.prover ins))
              (roleMeaning M a.program _ w.verifier [] (hideAll M w.verifier ins))
              [] source (fun _ h => nomatch h) hProjP hProjV hSafeP hSafeV
              hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt'
          have hFinish : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
              (callee : Member a.program.headers.protocols hdr)
              (ins' : HList (LVal M) hdr.ins)
              (first' : Stack.Takes (hE ▸ [layP0]) = [])
              (matched' : Stack.Gives (hE ▸ [layP0]) = Stack.Takes (hE ▸ [layV0]))
              (outP' : HList (RV M w.prover) hdr.outs)
              (outV' : HList (RV M w.verifier) hdr.outs)
              (recP' recV' : List (Happened M)),
              Alone M source w.prover
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [layP0])).run
                  (retryOf M none)
                  (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                  (cast (by subst hE; rfl) (HList.cons ([] : List (M.Val wL.unitTy)) HList.nil)))
                recP' (.returned (outP', cast (by subst hE; rfl) (HList.cons suffix HList.nil))) →
              Alone M source w.verifier
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [layV0])).run
                  (retryOf M none)
                  (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                  (cast (by subst hE; rfl) (HList.cons (suffix, ((0 : Nat), ())) HList.nil)))
                recV' (.returned (outV', cast (by subst hE; rfl) (HList.cons (suffix, (suffix.length, ())) HList.nil))) →
              ∃ gives givesV,
                Alone M source w.prover
                  (runStack a M callee none w.prover (hE ▸ [layP0])
                    (hideAll M w.prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                  recP' (.returned (outP', gives)) ∧
                Alone M source w.verifier
                  (runStack a M callee none w.verifier (hE ▸ [layV0])
                    (hideAll M w.verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                  recV' (.returned (outV', givesV)) := by
            intro hdr hE callee ins' first' matched' outP' outV' recP' recV' hAP hAV
            subst hE
            change Alone M source w.prover
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layP0]).run
                (retryOf M none) (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                (.cons ([] : List (M.Val wL.unitTy)) .nil))
              recP' (.returned (outP', .cons suffix .nil)) at hAP
            change Alone M source w.verifier
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layV0]).run
                (retryOf M none) (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                (.cons (suffix, ((0 : Nat), ())) .nil))
              recV' (.returned (outV', .cons (suffix, (suffix.length, ())) .nil)) at hAV
            refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
            · unfold runStack
              change Alone M source w.prover
                ((Stack.start M (Defs.fnTable M a.program.defs) [layP0]
                  (hideAll M w.prover ins') .nil).bind _) _ _
              have hStP : Stack.start M (Defs.fnTable M a.program.defs)
                  [layP0] (hideAll M w.prover ins') .nil =
                  .done (.cons ([] : List (M.Val wL.unitTy)) .nil) := by
                change ((liftLocal id ((layoutPStart wL.unitTy).denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun first =>
                    (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first.single others) = _
                rw [layoutPStart_denote]; rfl
              rw [hStP]; dsimp only [Process.bind]
              have hAP' := alone_mapHalt M (g := Prod.fst) hAP
              rw [← List.append_nil recP']
              refine alone_bind M hAP' ?_
              have hFinP : Stack.finish M (Defs.fnTable M a.program.defs)
                  [layP0] (.cons suffix .nil) = .done (.cons suffix .nil) := by
                rw [stack_finish_one]; dsimp only [layP0, BuildLayoutStreaming.layP]
                rw [identityFinish_denote]; rfl
              rw [hFinP]; exact .done
            · unfold runStack
              change Alone M source w.verifier
                ((Stack.start M (Defs.fnTable M a.program.defs) [layV0]
                  (hideAll M w.verifier ins') (.cons suffix .nil)).bind _) _ _
              have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                  [layV0] (hideAll M w.verifier ins') (.cons suffix .nil) =
                  .done (.cons (suffix, ((0 : Nat), ())) .nil) := by
                change ((liftLocal id ((layoutVStart wL.unitTy).denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (.cons suffix (heldValues M w.verifier (hideAll M w.verifier ins')))))).bind fun first =>
                    (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first.single others) = _
                rw [layoutVStart_denote]; rfl
              rw [hStV]; dsimp only [Process.bind]
              have hAV' := alone_mapHalt M (g := Prod.fst) hAV
              rw [← List.append_nil recV']
              refine alone_bind M hAV' ?_
              have hFinV : Stack.finish M (Defs.fnTable M a.program.defs)
                  [layV0] (.cons (suffix, (suffix.length, ())) .nil) = .done .nil := by
                rw [stack_finish_one]; dsimp only [layV0, BuildLayoutStreaming.layV]
                rw [layoutVFinish_denote]
                simp only [Nat.beq_refl, Bool.cond_true]; rfl
              rw [hFinV]; exact .done
          obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
          simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlV0
          have hStackPEq : w.toDeployed.stack w.prover = hEntryF ▸ [layP0] := by
            dsimp only [DeployAuthored.toDeployed]
            rw [dite_eq_left rfl, hLPW]
          have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [layV0] := by
            dsimp only [DeployAuthored.toDeployed]
            rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl, hLVW]
          have hFirst' : Stack.Takes (hEntryF ▸ [layP0]) = [] := by
            rw [← hStackPEq]; exact first
          have hMatched' : Stack.Gives (hEntryF ▸ [layP0]) = Stack.Takes (hEntryF ▸ [layV0]) := by
            rw [← hStackPEq, ← hStackVEq]; exact matched
          obtain ⟨gives, givesV, hRunP, hRunV⟩ := hFinish _ hEntryF _ ins hFirst' hMatched'
            outP outV recP recV
            (alone_cast_stack1 M hEntryF layP0 rfl hAlP)
            (alone_cast_stack1 M hEntryF layV0 rfl hAlV0)
          refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
            recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
            ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackPEq
              ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
              ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
              (cast_heq _ _) hRunV
  | derived w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hRecNil : w.layout.recover = [] := hNoRec w.layout w.hLayOpt
      cases buildLayoutLayers_ok_elim w.hLay with
      | compact wL _ => have hne := wL.hNonEmpty; simp [hRecNil] at hne
      | streaming wL hLPW hLVW =>
          have hEntryF : ((a.program.findProtocol declaration.entry).get
              (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
          let conPL : Layer V a.program.headers w.prover w.foundPair.1.ins :=
            { line := .construction, state := w.stateTy, takes := [],
              gives := [], clauses := w.cPClauses, again := restoreAgain w.stateTy,
              start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP,
              finish := emptyFinish w.stateTy }
          let conVL : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
            { line := .construction, state := w.stateTy, takes := [],
              gives := [], clauses := w.cVClauses, again := restoreAgain w.stateTy,
              start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtV,
              finish := emptyFinish w.stateTy }
          let layPL : Layer V a.program.headers w.prover w.foundPair.1.ins := wL.layP
          let layVL : Layer V a.program.headers w.verifier w.foundPair.1.ins := wL.layV
          have hStartEq : ∀ (ins' : HList (LVal M) w.foundPair.1.ins),
              ins'.All (fun a v => M.Valid a.ty v) →
              ∃ st0,
                conPL.start.denote (localSem M a.program.headers.fns
                  (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))) =
                  .done (.cons st0 .nil) ∧
                conVL.start.denote (localSem M a.program.headers.fns
                  (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.verifier (hideAll M w.verifier ins'))) =
                  .done (.cons st0 .nil) ∧
                M.Valid w.stateTy st0 := by
            intro ins' hIns'
            obtain ⟨st0, hDoneP, hSt0V⟩ := constructionStart_done M a
              w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP
              (heldValues M w.prover (hideAll M w.prover ins'))
              (heldValues_valid M w.prover _ (hideAll_valid M w.prover ins' hIns'))
            have hAgree := constructionStart_agree M a w.suite w.prover w.verifier
              w.foundPair.1.ins declaration.key w.sessBytes w.hSessBytes w.startRef w.absorbRef
              w.stmtP w.stmtV w.hSP w.hSV ins'
            exact ⟨st0, hDoneP, hAgree.symm.trans hDoneP, hSt0V⟩
          have hInsF := ins_cast_valid M hEntryF ins hIns
          obtain ⟨st0, hSt0P, hSt0V, hSt0Valid⟩ :=
            hStartEq (cast (congrArg (fun hdr => HList (LVal M) hdr.ins) hEntryF) ins) hInsF
          let conP' : Layer V a.program.headers w.prover _ := hEntryF ▸ conPL
          let conV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ conVL
          let layP' : Layer V a.program.headers w.prover _ := hEntryF ▸ layPL
          let layV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ layVL
          have hCPSt : conP'.state = w.stateTy := layer_cast_state hEntryF conPL
          have hCVSt : conV'.state = w.stateTy := layer_cast_state hEntryF conVL
          have hLPSt : layP'.state = .seq wL.unitTy none := layer_cast_state hEntryF layPL
          have hLVSt : layV'.state = streamStateTy wL.unitTy := layer_cast_state hEntryF layVL
          have hCPCl : hCPSt ▸ conP'.clauses = w.cPClauses := layer_cast_clauses hEntryF conPL
          have hCVCl : hCVSt ▸ conV'.clauses = w.cVClauses := layer_cast_clauses hEntryF conVL
          have hLPCl : hLPSt ▸ layP'.clauses = wL.pClauses := layer_cast_clauses hEntryF layPL
          have hLVCl : hLVSt ▸ layV'.clauses = wL.vClauses := layer_cast_clauses hEntryF layVL
          have hCC' : buildConstructionClauses.go enc a w.suite w.stateTy w.suiteUnitTy
              w.absorbRef w.prover w.verifier declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.eventsWithAbsorb w.prover w.verifier [] id false) =
              .ok (w.cPClauses, w.cVClauses) := by
            rw [hEntryF]; exact w.hCC
          have hSL' : buildStreamingLayoutClauses.go a w.layout wL.unitTy
              wL.hfree w.prover w.verifier declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) =
              .ok (wL.pClauses, wL.vClauses) := by
            rw [hEntryF]; exact wL.hStr
          -- Run unified simulation with 2-layer identity ProverAdapter (`useSamples = false`)
          have hRunSim2 : ∀ (cP lP : Layer V a.program.headers w.prover w.toDeployed.entry.ins)
              (hcS : cP.state = w.stateTy) (hlS : lP.state = .seq wL.unitTy none)
              (hcC : hcS ▸ cP.clauses = w.cPClauses) (hlC : hlS ▸ lP.clauses = wL.pClauses),
              ∃ (out : HList (LVal M) w.toDeployed.entry.outs × Fields.Val M w.toDeployed.entry.record)
                (outP : HList (RV M w.prover) w.toDeployed.entry.outs)
                (outV : HList (RV M w.verifier) w.toDeployed.entry.outs)
                (finalSt : M.Val w.stateTy) (suffix : List (M.Val wL.unitTy))
                (recP : List (Happened M)) (source' : Source M),
                (∀ u ∈ suffix, M.Valid wL.unitTy u) ∧
                Alone M source w.prover
                  ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                    [cP, lP]).run (retryOf M none)
                    (roleMeaning M a.program w.toDeployed.callee w.prover [] (hideAll M w.prover ins))
                    (.cons (hcS.symm ▸ st0) (.cons (hlS.symm ▸ ([] : List (M.Val wL.unitTy))) .nil)))
                  recP (.returned (outP, .cons (hcS.symm ▸ finalSt) (.cons (hlS.symm ▸ ([] ++ suffix)) .nil))) ∧
                (∀ (post : List (M.Val wL.unitTy)), (∀ u ∈ post, M.Valid wL.unitTy u) →
                  ∃ recV, Alone M source w.verifier
                    ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                      [conV', layV']).run (retryOf M none)
                      (roleMeaning M a.program w.toDeployed.callee w.verifier [] (hideAll M w.verifier ins))
                      (.cons (hCVSt.symm ▸ st0)
                        (.cons (hLVSt.symm ▸ ([] ++ suffix ++ post, (([] : List (M.Val wL.unitTy)).length, ()))) .nil)))
                    recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                      (.cons (hLVSt.symm ▸ ([] ++ suffix ++ post, (([] : List (M.Val wL.unitTy)).length + suffix.length, ()))) .nil)))) ∧
                outP = hideAll M w.prover out.1 ∧ outV = hideAll M w.verifier out.1 ∧
                Lawful M source' (protocolMeaning M a.program w.toDeployed.callee [] ins) ∧
                (∀ at_ τ, at_.site ∉ w.toDeployed.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
                GExec M source' (protocolMeaning M a.program w.toDeployed.callee [] ins) (.returned out) := by
            intro cP lP hcS hlS hcC hlC
            cases cP with | mk cL cSt cT cG cCl cAg cStart cFin =>
            cases lP with | mk lL lSt lT lG lCl lAg lStart lFin =>
            dsimp only at hcS hlS; subst cSt; subst lSt; dsimp only at hcC hlC
            subst hcC; subst hlC
            let cP0 : Layer V a.program.headers w.prover w.toDeployed.entry.ins :=
              ⟨cL, w.stateTy, cT, cG, w.cPClauses, cAg, cStart, cFin⟩
            let lP0 : Layer V a.program.headers w.prover w.toDeployed.entry.ins :=
              ⟨lL, .seq wL.unitTy none, lT, lG, wL.pClauses, lAg, lStart, lFin⟩
            let adapter2 : ProverAdapter M w.prover false (w.toDeployed.entry.shape.events [] id)
                (castStack2Handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                  cP0 lP0 rfl rfl) := {
              σ := HList M.Val [w.stateTy, .seq wL.unitTy none]
              h := Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [cP0, lP0]
              Inv := fun s st buf => s = .cons st (.cons buf .nil)
              passMark := fun op s hM =>
                match s with
                | .cons st1 (.cons buf1 .nil) => by
                    have hCl : ROp.IsClosed M op := by rcases hM with hM | hM <;> rw [hM] <;> trivial
                    have hCU := construction_clauses_unmatched_closed M 0 _ hCC' op hCl
                    have hLU := streaming_layout_unmatched_closed M 0 _ hSL' op hCl
                    exact stack2_clause_pass M _ _ cP0 lP0 op st1 buf1
                      (clause_answer_unmatched_all M _ _ op st1 w.cPClauses hCU.1)
                      (clause_answer_unmatched_all M _ _ op buf1 wL.pClauses hLU.1)
              passClosed := fun op s st buf hInv _ _ hBase => by
                subst hInv; simp only [castStack2Handler] at hBase; exact hBase
              stepBelow := fun op s st buf st' buf' reply hInv _ hBase => by
                subst hInv; simp only [castStack2Handler] at hBase
                exact ⟨.cons st' (.cons buf' .nil), rfl, hBase⟩
              stepSampled := fun h => by cases h
            }
            obtain ⟨out, outP, outV, sP', finalSt, suffix, recP, source',
              hInv', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
              simulate_derived_gen M w.hNe (d := w.toDeployed)
                w.cPClauses w.cVClauses wL.pClauses wL.vClauses
                cP0 conV' lP0 layV' rfl hCVSt rfl hLVSt rfl hCVCl rfl hLVCl
                w.hCon w.hLayOpt hSuiteLaw hLayLaw hCC' hSL' false adapter2
                (protocolMeaning M a.program _ [] ins)
                (roleMeaning M a.program _ w.prover [] (hideAll M w.prover ins))
                (roleMeaning M a.program _ w.verifier [] (hideAll M w.verifier ins))
                (.cons st0 (.cons [] .nil)) st0 [] source rfl hSt0Valid (fun _ h => nomatch h)
                hProjP hProjV hSafeP hSafeV hShapeP hShapeV hPShape hUniq
                (lawfulPrivate_to_lawfulFor_false M hLP) (fed_to_fedFor_false M hFed) hNoHalt'
            subst hInv'
            exact ⟨out, outP, outV, finalSt, suffix, recP, source', hSufV, hAlP, hAlV,
              hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩
          obtain ⟨out, outP, outV, finalSt, suffix, recP, source',
            hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
            hRunSim2 conP' layP' hCPSt hLPSt hCPCl hLPCl
          obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
          have hFinish : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
              (callee : Member a.program.headers.protocols hdr)
              (ins' : HList (LVal M) hdr.ins)
              (hStartP' : conPL.start.denote (localSem M a.program.headers.fns
                (Defs.fnTable M a.program.defs)) []
                (Env.positional (heldValues M w.prover (hideAll M w.prover (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                .done (.cons st0 .nil))
              (hStartV' : conVL.start.denote (localSem M a.program.headers.fns
                (Defs.fnTable M a.program.defs)) []
                (Env.positional (heldValues M w.verifier (hideAll M w.verifier (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                .done (.cons st0 .nil))
              (first' : Stack.Takes (hE ▸ [conPL, layPL]) = [])
              (matched' : Stack.Gives (hE ▸ [conPL, layPL]) = Stack.Takes (hE ▸ [conVL, layVL]))
              (outP' : HList (RV M w.prover) hdr.outs)
              (outV' : HList (RV M w.verifier) hdr.outs)
              (recP' recV' : List (Happened M)),
              Alone M source w.prover
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [conPL, layPL])).run
                  (retryOf M none)
                  (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                  (cast (by subst hE; rfl)
                    (HList.cons st0 (HList.cons ([] : List (M.Val wL.unitTy)) HList.nil))))
                recP' (.returned (outP', cast (by subst hE; rfl)
                  (HList.cons finalSt (HList.cons suffix HList.nil)))) →
              Alone M source w.verifier
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [conVL, layVL])).run
                  (retryOf M none)
                  (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                  (cast (by subst hE; rfl)
                    (HList.cons st0 (HList.cons (suffix, ((0 : Nat), ())) HList.nil))))
                recV' (.returned (outV', cast (by subst hE; rfl)
                  (HList.cons finalSt (HList.cons (suffix, (suffix.length, ())) HList.nil)))) →
              ∃ gives givesV,
                Alone M source w.prover
                  (runStack a M callee none w.prover (hE ▸ [conPL, layPL])
                    (hideAll M w.prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                  recP' (.returned (outP', gives)) ∧
                Alone M source w.verifier
                  (runStack a M callee none w.verifier (hE ▸ [conVL, layVL])
                    (hideAll M w.verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                  recV' (.returned (outV', givesV)) := by
            intro hdr hE callee ins' hSP' hSV' first' matched' outP' outV' recP' recV' hAP hAV
            subst hE
            dsimp only at hSP' hSV'
            simp only [cast_eq] at hSP' hSV'
            change Alone M source w.prover
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conPL, layPL]).run
                (retryOf M none) (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)))
              recP' (.returned (outP', .cons finalSt (.cons suffix .nil))) at hAP
            change Alone M source w.verifier
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conVL, layVL]).run
                (retryOf M none) (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)))
              recV' (.returned (outV', .cons finalSt (.cons (suffix, (suffix.length, ())) .nil))) at hAV
            refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
            · unfold runStack
              change Alone M source w.prover
                ((Stack.start M (Defs.fnTable M a.program.defs) [conPL, layPL]
                  (hideAll M w.prover ins') .nil).bind _) _ _
              have hStP : Stack.start M (Defs.fnTable M a.program.defs)
                  [conPL, layPL] (hideAll M w.prover ins') .nil =
                  .done (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)) := by
                change ((liftLocal id (conPL.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun f₁ =>
                    ((liftLocal id ((layoutPStart wL.unitTy).denote
                      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                      (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun f₂ =>
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
                rw [stack_finish_two]; dsimp only [conPL, layPL, BuildLayoutStreaming.layP]
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [identityFinish_denote]; rfl
              rw [hFinP]; exact .done
            · unfold runStack
              change Alone M source w.verifier
                ((Stack.start M (Defs.fnTable M a.program.defs) [conVL, layVL]
                  (hideAll M w.verifier ins') (.cons suffix .nil)).bind _) _ _
              have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                  [conVL, layVL] (hideAll M w.verifier ins') (.cons suffix .nil) =
                  .done (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)) := by
                change ((liftLocal id (conVL.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.verifier (hideAll M w.verifier ins'))))).bind fun f₁ =>
                    ((liftLocal id ((layoutVStart wL.unitTy).denote
                      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                      (Env.positional (.cons suffix (heldValues M w.verifier (hideAll M w.verifier ins')))))).bind fun f₂ =>
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
                rw [stack_finish_two]; dsimp only [conVL, layVL, BuildLayoutStreaming.layV]
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [layoutVFinish_denote]
                simp only [Nat.beq_refl, Bool.cond_true]; rfl
              rw [hFinV]; exact .done
          simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlV0
          have hNoSampLayer : w.prep.sampLayer = none := by
            have h := w.prep.hSamp
            unfold buildSamplesLayer at h
            rw [hNoSamp] at h
            exact (Except.ok.inj h).symm
          have hStackPEq : w.toDeployed.stack w.prover = hEntryF ▸ [conPL, layPL] := by
            dsimp only [DeployDerived.toDeployed]
            rw [dite_eq_left rfl, hNoSampLayer, hLPW]
            exact cast_ins_eq_cast_hdr hEntryF _
          have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [conVL, layVL] := by
            dsimp only [DeployDerived.toDeployed]
            rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl, hLVW]
            exact cast_ins_eq_cast_hdr hEntryF _
          have hFirst' : Stack.Takes (hEntryF ▸ [conPL, layPL]) = [] := by
            rw [← hStackPEq]; exact first
          have hMatched' : Stack.Gives (hEntryF ▸ [conPL, layPL]) = Stack.Takes (hEntryF ▸ [conVL, layVL]) := by
            rw [← hStackPEq, ← hStackVEq]; exact matched
          obtain ⟨gives, givesV, hRunP, hRunV⟩ :=
            hFinish _ hEntryF _ ins hSt0P hSt0V hFirst' hMatched'
              outP outV recP recV
              (alone_cast_stack2 M hEntryF conPL layPL rfl rfl hAlP)
              (alone_cast_stack2 M hEntryF conVL layVL rfl rfl hAlV0)
          refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
            recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
            ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackPEq
              ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
              ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
              (cast_heq _ _) hRunV

/-- Streaming completeness (`Statements.completeStreaming`) under standard `Deployed.SuiteLawful`. -/
theorem deploy_complete_streaming (enc : VocabEncoder V) {named : NamedProgram V} {assoc : Association}
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
        outP = hideAll M prover out.1 ∧ outV = hideAll M verifier out.1 :=
  deploy_complete M enc hAdmit hDep hNonInt hNoRetry hNoSamp hNoRec prover verifier hRoles
    first matched ins hIns (Deployed.SuiteLawful.toFor enc M hSuiteLaw) hLayLaw hNoHalt source hLP hFed

/-! ## Deterministic prover sampling completeness (`deploy_complete_samples`) -/

/-- Completeness for `.derived` streaming deployments with deterministic prover sampling
(`declaration.samples = some sKey`) under `SuiteLawfulFor`, `LayoutLawful`, and `SamplesLawful`.
Notice that `source` does NOT need to feed zero-argument prover private coins (`FedSampled`,
`LawfulSampled`): on a deterministic prover with no requests or verifier private coins, the
completely empty world `source = fun _ _ => none` suffices. -/
theorem deploy_complete_samples (enc : VocabEncoder V) {named : NamedProgram V} {assoc : Association}
    {a : Admitted V} (hAdmit : admit named assoc = .ok a)
    {declaration : Declaration} {d : Deployed V} (hDep : deploy enc a declaration = .ok d)
    {sKey : Key} (hSamp : declaration.samples = some sKey)
    (hNoRetry : declaration.retry = none)
    (hNoRec : ∀ l, declaration.layout = some l → l.recover = [])
    (prover verifier : Role) (hRoles : d.roles = some (prover, verifier))
    (first : Stack.Takes (d.stack prover) = [])
    (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
    (ins : HList (LVal M) d.entry.ins) (hIns : ins.All (fun a v => M.Valid a.ty v))
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M) (hSampLaw : d.SamplesLawful M)
    (hNoHalt : ∀ source, Lawful M source (protocolMeaning M d.admitted.program d.callee [] ins) →
      ∀ e, GExec M source (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out)
    (source : Source M)
    (hLP : LawfulSampled M prover source (protocolMeaning M d.admitted.program d.callee [] ins))
    (hFed : FedSampled M prover source (protocolMeaning M d.admitted.program d.callee [] ins)) :
    ∃ outP gives recordP outV givesV recordV,
      Alone M source prover
        (d.run M prover (hideAll M prover ins) (cast (congrArg (HList M.Val) first.symm) .nil))
        recordP (.returned (outP, gives)) ∧
      Alone M source verifier
        (d.run M verifier (hideAll M verifier ins) (cast (congrArg (HList M.Val) matched) gives))
        recordV (.returned (outV, givesV)) ∧
      ∃ source' out,
        Lawful M source' (protocolMeaning M d.admitted.program d.callee [] ins) ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins ++ d.entry.shape.proverPrivateCoins prover →
          source' at_ τ = source at_ τ) ∧
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
      (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins ++ d.entry.shape.proverPrivateCoins prover →
        source₁ at_ τ = source at_ τ) →
      ∀ e, GExec M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out := fun s₁ hL₁ _ e hEx => hNoHalt s₁ hL₁ e hEx
  cases deploy_ok_elim enc a declaration d hDep with
  | interactive w _ =>
      have hNone := w.hInt
      simp [checkInteractive, hSamp] at hNone
  | authored w _ =>
      have hNoS := w.hNoSamp
      rw [hSamp] at hNoS; cases hNoS
  | derived w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hRecNil : w.layout.recover = [] := hNoRec w.layout w.hLayOpt
      -- Unpack `buildSamplesLayer` under `declaration.samples = some sKey`
      have hSampBuild := w.prep.hSamp
      unfold buildSamplesLayer at hSampBuild
      rw [hSamp] at hSampBuild
      dsimp only at hSampBuild
      cases hFindS : a.program.find sKey with
      | none => rw [hFindS] at hSampBuild; cases hSampBuild
      | some defS =>
          rw [hFindS] at hSampBuild
          cases defS with
          | protocol _ => cases hSampBuild
          | fn _ =>
              dsimp only at hSampBuild
              split at hSampBuild
              · rename_i htfreeS
                cases hSC : buildSamplesClauses a (held w.prover w.foundPair.1.ins) htfreeS
                    w.prover sKey w.sessBytes w.hSessBytes declaration.key
                    (w.foundPair.1.shape.events [] id) with
                | error _ => rw [hSC] at hSampBuild; cases hSampBuild
                | ok sClauses =>
                    rw [hSC] at hSampBuild
                    dsimp only [bind, Except.bind, pure, Except.pure] at hSampBuild
                    have hSampLayerEq : w.prep.sampLayer = some {
                        line := .samples
                        state := samplesStateTy (held w.prover w.foundPair.1.ins)
                        takes := []
                        gives := []
                        clauses := sClauses
                        again := samplesAgain (held w.prover w.foundPair.1.ins) htfreeS
                        start := samplesStart
                        finish := emptyFinish (samplesStateTy (held w.prover w.foundPair.1.ins))
                      } := (Except.ok.inj hSampBuild).symm
                    let sampPL : Layer V a.program.headers w.prover w.foundPair.1.ins := {
                      line := .samples
                      state := samplesStateTy (held w.prover w.foundPair.1.ins)
                      takes := []
                      gives := []
                      clauses := sClauses
                      again := samplesAgain (held w.prover w.foundPair.1.ins) htfreeS
                      start := samplesStart
                      finish := emptyFinish (samplesStateTy (held w.prover w.foundPair.1.ins))
                    }
                    cases buildLayoutLayers_ok_elim w.hLay with
                    | compact wL _ => have hne := wL.hNonEmpty; simp [hRecNil] at hne
                    | streaming wL hLPW hLVW =>
                        have hEntryF : ((a.program.findProtocol declaration.entry).get
                            (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
                        let conPL : Layer V a.program.headers w.prover w.foundPair.1.ins :=
                          { line := .construction, state := w.stateTy, takes := [],
                            gives := [], clauses := w.cPClauses, again := restoreAgain w.stateTy,
                            start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP,
                            finish := emptyFinish w.stateTy }
                        let conVL : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
                          { line := .construction, state := w.stateTy, takes := [],
                            gives := [], clauses := w.cVClauses, again := restoreAgain w.stateTy,
                            start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtV,
                            finish := emptyFinish w.stateTy }
                        let layPL : Layer V a.program.headers w.prover w.foundPair.1.ins := wL.layP
                        let layVL : Layer V a.program.headers w.verifier w.foundPair.1.ins := wL.layV
                        have hInsF := ins_cast_valid M hEntryF ins hIns
                        let insF : HList (LVal M) w.foundPair.1.ins :=
                          cast (congrArg (fun hdr => HList (LVal M) hdr.ins) hEntryF) ins
                        let heldValsP : HList M.Val (held w.prover w.foundPair.1.ins) :=
                          heldValues M w.prover (hideAll M w.prover insF)
                        have hHeldPV : heldValsP.All M.Valid :=
                          heldValues_valid M w.prover _ (hideAll_valid M w.prover insF hInsF)
                        let heldTupleP : (tysOfList (held w.prover w.foundPair.1.ins)).Val M.toCarriers :=
                          Tys.ofHList M (tysOfList (held w.prover w.foundPair.1.ins))
                            (cast (congrArg (HList M.Val) (tysOfList_toList (held w.prover w.foundPair.1.ins)).symm) heldValsP)
                        obtain ⟨st0, hSt0P, hSt0Valid⟩ := constructionStart_done M a
                          w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP heldValsP hHeldPV
                        have hSt0V : conVL.start.denote (localSem M a.program.headers.fns
                            (Defs.fnTable M a.program.defs)) []
                            (Env.positional (heldValues M w.verifier (hideAll M w.verifier insF))) =
                            .done (.cons st0 .nil) :=
                          (constructionStart_agree M a w.suite w.prover w.verifier
                            w.foundPair.1.ins declaration.key w.sessBytes w.hSessBytes w.startRef w.absorbRef
                            w.stmtP w.stmtV w.hSP w.hSV insF).symm.trans hSt0P
                        let sampP' : Layer V a.program.headers w.prover _ := hEntryF ▸ sampPL
                        let conP' : Layer V a.program.headers w.prover _ := hEntryF ▸ conPL
                        let conV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ conVL
                        let layP' : Layer V a.program.headers w.prover _ := hEntryF ▸ layPL
                        let layV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ layVL
                        have hSPSt : sampP'.state = samplesStateTy (held w.prover w.foundPair.1.ins) :=
                          layer_cast_state hEntryF sampPL
                        have hCPSt : conP'.state = w.stateTy := layer_cast_state hEntryF conPL
                        have hCVSt : conV'.state = w.stateTy := layer_cast_state hEntryF conVL
                        have hLPSt : layP'.state = .seq wL.unitTy none := layer_cast_state hEntryF layPL
                        have hLVSt : layV'.state = streamStateTy wL.unitTy := layer_cast_state hEntryF layVL
                        have hSPCl : hSPSt ▸ sampP'.clauses = sClauses := layer_cast_clauses hEntryF sampPL
                        have hCPCl : hCPSt ▸ conP'.clauses = w.cPClauses := layer_cast_clauses hEntryF conPL
                        have hCVCl : hCVSt ▸ conV'.clauses = w.cVClauses := layer_cast_clauses hEntryF conVL
                        have hLPCl : hLPSt ▸ layP'.clauses = wL.pClauses := layer_cast_clauses hEntryF layPL
                        have hLVCl : hLVSt ▸ layV'.clauses = wL.vClauses := layer_cast_clauses hEntryF layVL
                        have hCC' : buildConstructionClauses.go enc a w.suite w.stateTy w.suiteUnitTy
                            w.absorbRef w.prover w.verifier declaration.key
                            ((((a.program.findProtocol declaration.entry).get
                              (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
                            ((((a.program.findProtocol declaration.entry).get
                              (by rw [w.hFound]; rfl)).1).shape.eventsWithAbsorb w.prover w.verifier [] id false) =
                            .ok (w.cPClauses, w.cVClauses) := by
                          rw [hEntryF]; exact w.hCC
                        have hSL' : buildStreamingLayoutClauses.go a w.layout wL.unitTy
                            wL.hfree w.prover w.verifier declaration.key
                            ((((a.program.findProtocol declaration.entry).get
                              (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
                            ((((a.program.findProtocol declaration.entry).get
                              (by rw [w.hFound]; rfl)).1).shape.events [] id) =
                            .ok (wL.pClauses, wL.vClauses) := by
                          rw [hEntryF]; exact wL.hStr
                        -- Run unified simulation with 3-layer ProverAdapter (`useSamples = true`)
                        have hEntryIns : w.toDeployed.entry.ins = w.foundPair.1.ins :=
                          congrArg ProtocolHeader.ins hEntryF
                        have hRunSim3 : ∀ (sP cP lP : Layer V a.program.headers w.prover w.toDeployed.entry.ins)
                            (hsS : sP.state = samplesStateTy (held w.prover w.foundPair.1.ins))
                            (hcS : cP.state = w.stateTy) (hlS : lP.state = .seq wL.unitTy none)
                            (hsC : hsS ▸ sP.clauses = sClauses)
                            (hcC : hcS ▸ cP.clauses = w.cPClauses) (hlC : hlS ▸ lP.clauses = wL.pClauses),
                            ∃ (out : HList (LVal M) w.toDeployed.entry.outs × Fields.Val M w.toDeployed.entry.record)
                              (outP : HList (RV M w.prover) w.toDeployed.entry.outs)
                              (outV : HList (RV M w.verifier) w.toDeployed.entry.outs)
                              (att' seq' : Nat) (finalSt : M.Val w.stateTy)
                              (suffix : List (M.Val wL.unitTy)) (recP : List (Happened M))
                              (source' : Source M),
                              (∀ u ∈ suffix, M.Valid wL.unitTy u) ∧
                              Alone M source w.prover
                                ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                                  [sP, cP, lP]).run (retryOf M none)
                                  (roleMeaning M a.program w.toDeployed.callee w.prover [] (hideAll M w.prover ins))
                                  (.cons (hsS.symm ▸ ((0 : Nat), ((0 : Nat), (heldTupleP, ()))))
                                    (.cons (hcS.symm ▸ st0) (.cons (hlS.symm ▸ ([] : List (M.Val wL.unitTy))) .nil))))
                                recP (.returned (outP,
                                  .cons (hsS.symm ▸ (att', (seq', (heldTupleP, ()))))
                                    (.cons (hcS.symm ▸ finalSt) (.cons (hlS.symm ▸ ([] ++ suffix)) .nil)))) ∧
                              (∀ (post : List (M.Val wL.unitTy)), (∀ u ∈ post, M.Valid wL.unitTy u) →
                                ∃ recV, Alone M source w.verifier
                                  ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                                    [conV', layV']).run (retryOf M none)
                                    (roleMeaning M a.program w.toDeployed.callee w.verifier [] (hideAll M w.verifier ins))
                                    (.cons (hCVSt.symm ▸ st0)
                                      (.cons (hLVSt.symm ▸ ([] ++ suffix ++ post, (([] : List (M.Val wL.unitTy)).length, ()))) .nil)))
                                  recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                                    (.cons (hLVSt.symm ▸ ([] ++ suffix ++ post, (([] : List (M.Val wL.unitTy)).length + suffix.length, ()))) .nil)))) ∧
                              outP = hideAll M w.prover out.1 ∧ outV = hideAll M w.verifier out.1 ∧
                              Lawful M source' (protocolMeaning M a.program w.toDeployed.callee [] ins) ∧
                              (∀ at_ τ, at_.site ∉ w.toDeployed.entry.shape.heardCoins ++
                                w.toDeployed.entry.shape.proverPrivateCoins w.prover →
                                source' at_ τ = source at_ τ) ∧
                              GExec M source' (protocolMeaning M a.program w.toDeployed.callee [] ins) (.returned out) := by
                          intro sP cP lP hsS hcS hlS hsC hcC hlC
                          cases sP with | mk sL sSt sT sG sCl sAg sStart sFin =>
                          cases cP with | mk cL cSt cT cG cCl cAg cStart cFin =>
                          cases lP with | mk lL lSt lT lG lCl lAg lStart lFin =>
                          dsimp only at hsS hcS hlS; subst sSt; subst cSt; subst lSt
                          dsimp only at hsC hcC hlC; subst hsC; subst hcC; subst hlC
                          let sP0 : Layer V a.program.headers w.prover w.toDeployed.entry.ins :=
                            ⟨sL, samplesStateTy (held w.prover w.foundPair.1.ins), sT, sG, sCl, sAg, sStart, sFin⟩
                          let cP0 : Layer V a.program.headers w.prover w.toDeployed.entry.ins :=
                            ⟨cL, w.stateTy, cT, cG, w.cPClauses, cAg, cStart, cFin⟩
                          let lP0 : Layer V a.program.headers w.prover w.toDeployed.entry.ins :=
                            ⟨lL, .seq wL.unitTy none, lT, lG, wL.pClauses, lAg, lStart, lFin⟩
                          let adapter3 : ProverAdapter M w.prover true (w.toDeployed.entry.shape.events [] id)
                              (castStack2Handler M (Defs.fnTable M a.program.defs)
                                (Defs.rTable M a.program.defs) cP0 lP0 rfl rfl) := {
                            σ := HList M.Val [samplesStateTy (held w.prover w.foundPair.1.ins), w.stateTy, .seq wL.unitTy none]
                            h := Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [sP0, cP0, lP0]
                            Inv := fun s st buf => ∃ att seq : Nat,
                              s = .cons (att, (seq, (heldTupleP, ()))) (.cons st (.cons buf .nil))
                            passMark := fun op s hM =>
                              match s with
                              | .cons s0 (.cons st1 (.cons buf1 .nil)) => by
                                  have hCl : ROp.IsClosed M op := by rcases hM with hM | hM <;> rw [hM] <;> trivial
                                  have hNotC : ∀ law at_ τ, op = .own (.coin law) [] at_ [] .nil τ → False := by
                                    intro _ _ _ hEq; rcases hM with hM | hM <;> rw [hM] at hEq <;> cases hEq
                                  have hSU := buildSamplesClauses_unmatched M _ hSC op hNotC
                                  have hCU := construction_clauses_unmatched_closed M 0 _ hCC' op hCl
                                  have hLU := streaming_layout_unmatched_closed M 0 _ hSL' op hCl
                                  exact stack3_clause_pass M _ _ sP0 cP0 lP0 op s0 st1 buf1
                                    (clause_answer_unmatched_all M _ _ op s0 sCl hSU)
                                    (stack2_clause_pass M _ _ cP0 lP0 op st1 buf1
                                      (clause_answer_unmatched_all M _ _ op st1 w.cPClauses hCU.1)
                                      (clause_answer_unmatched_all M _ _ op buf1 wL.pClauses hLU.1))
                            passClosed := fun op s st buf hInv _ hNotC hBase => by
                              obtain ⟨att, seq, rfl⟩ := hInv
                              simp only [castStack2Handler] at hBase
                              have hNotCoin : ∀ law at_ τ, op = .own (.coin law) [] at_ [] .nil τ → False :=
                                fun law at_ τ hEq => by
                                  have hF := hNotC law at_ τ hEq
                                  cases hF
                              exact stack3_clause_pass M _ _ sP0 cP0 lP0 op _ st buf
                                (clause_answer_unmatched_all M _ _ op _ sCl
                                  (buildSamplesClauses_unmatched M _ hSC op hNotCoin))
                                hBase
                            stepBelow := fun op s st buf st' buf' reply hInv hNotC hBase => by
                              obtain ⟨att, seq, rfl⟩ := hInv
                              simp only [castStack2Handler] at hBase
                              refine ⟨.cons (att, (seq, (heldTupleP, ()))) (.cons st' (.cons buf' .nil)), ⟨att, seq, rfl⟩, ?_⟩
                              exact stack3_clause_below_done M _ _ sP0 cP0 lP0 op _ st st' buf buf' reply
                                (clause_answer_unmatched_all M _ _ op _ sCl
                                  (buildSamplesClauses_unmatched M _ hSC op hNotC))
                                hBase
                            stepSampled := fun _ law at_ τ s st buf hInv ⟨e, hE, hSiteE, hTyE, hClsE⟩ hLaw => by
                              obtain ⟨att, seq, rfl⟩ := hInv
                              have hEF : e ∈ w.foundPair.1.shape.events [] id := by
                                rw [← hEntryF]; exact hE
                              obtain ⟨sRef, coin, hFindRef, hEvRef, _, hAnsS⟩ :=
                                buildSamplesClauses_answer_coin M _ hSC law at_ τ att seq heldValsP hHeldPV
                                  ⟨e, hEF, hSiteE, hTyE, hClsE⟩
                              have hAllows : Allows M (.coin law) [] .nil τ coin := by
                                have hHeldEq : held w.prover w.toDeployed.entry.ins = held w.prover w.foundPair.1.ins :=
                                  congrArg (held w.prover) hEntryIns
                                have hFindCast : findTypedFnRef a sKey
                                    (held w.prover w.toDeployed.entry.ins ++ [bytesTy, bytesTy, .nat, .nat]) [τ] =
                                    some (cast (congrArg (fun ts => TypedFnRef V a.program.headers.fns
                                      (ts ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) hHeldEq.symm) sRef) := by
                                  have hG : ∀ {ts₁ ts₂ : List V.Ty} (heq : ts₁ = ts₂)
                                      (r0 : TypedFnRef V a.program.headers.fns (ts₂ ++ [bytesTy, bytesTy, .nat, .nat]) [τ]),
                                      findTypedFnRef a sKey (ts₂ ++ [bytesTy, bytesTy, .nat, .nat]) [τ] = some r0 →
                                      findTypedFnRef a sKey (ts₁ ++ [bytesTy, bytesTy, .nat, .nat]) [τ] =
                                        some (cast (congrArg (fun ts => TypedFnRef V a.program.headers.fns
                                          (ts ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) heq.symm) r0) := by
                                    intro _ _ heq _ h0; subst heq; exact h0
                                  exact hG hHeldEq sRef hFindRef
                                have hEvCast : (cast (congrArg (fun ts => TypedFnRef V a.program.headers.fns
                                    (ts ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) hHeldEq.symm) sRef).eval
                                    M (Defs.fnTable M a.program.defs)
                                    (HList.append (cast (congrArg (HList M.Val) hHeldEq.symm) heldValsP)
                                      (.cons (a := bytesTy) w.sessBytes (.cons (a := bytesTy) (encodeSite at_.site)
                                        (.cons (a := Ty.nat) att (.cons (a := Ty.nat) seq .nil))))) =
                                    .done (.cons coin .nil) := by
                                  have hG : ∀ {ts₁ ts₂ : List V.Ty} (heq : ts₁ = ts₂)
                                      (r0 : TypedFnRef V a.program.headers.fns (ts₂ ++ [bytesTy, bytesTy, .nat, .nat]) [τ])
                                      (hv0 : HList M.Val ts₂),
                                      (cast (congrArg (fun ts => TypedFnRef V a.program.headers.fns
                                        (ts ++ [bytesTy, bytesTy, .nat, .nat]) [τ]) heq.symm) r0).eval
                                        M (Defs.fnTable M a.program.defs)
                                        (HList.append (cast (congrArg (HList M.Val) heq.symm) hv0)
                                          (.cons (a := bytesTy) w.sessBytes (.cons (a := bytesTy) (encodeSite at_.site)
                                            (.cons (a := Ty.nat) att (.cons (a := Ty.nat) seq .nil))))) =
                                      r0.eval M (Defs.fnTable M a.program.defs)
                                        (HList.append hv0 (.cons (a := bytesTy) w.sessBytes (.cons (a := bytesTy) (encodeSite at_.site)
                                          (.cons (a := Ty.nat) att (.cons (a := Ty.nat) seq .nil))))) := by
                                    intro _ _ heq _ _; subst heq; rfl
                                  exact (hG hHeldEq sRef heldValsP).trans hEvRef
                                have hValidCast : (cast (congrArg (HList M.Val) hHeldEq.symm) heldValsP).All M.Valid := by
                                  have hG : ∀ {ts₁ ts₂ : List V.Ty} (heq : ts₁ = ts₂) (hv0 : HList M.Val ts₂),
                                      hv0.All M.Valid → (cast (congrArg (HList M.Val) heq.symm) hv0).All M.Valid := by
                                    intro _ _ heq _ h0; subst heq; exact h0
                                  exact hG hHeldEq heldValsP hHeldPV
                                exact samplesLawful_allows M hSamp hRoles hSampLaw hFindCast hE hClsE hTyE hLaw
                                  hValidCast w.hSessBytes (encodeSite_bytes at_.site) trivial hEvCast
                              refine ⟨coin, .cons (att, (seq + 1, (heldTupleP, ()))) (.cons st (.cons buf .nil)),
                                hAllows, ⟨att, seq + 1, rfl⟩, ?_⟩
                              exact stack3_clause_samp_done M _ _ sP0 cP0 lP0
                                (.own (.coin law) [] at_ [] .nil τ) _ _ st buf coin hAnsS
                          }
                          obtain ⟨out, outP, outV, sP', finalSt, suffix, recP, source',
                            hInv', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
                            simulate_derived_gen M w.hNe (d := w.toDeployed)
                              w.cPClauses w.cVClauses wL.pClauses wL.vClauses
                              cP0 conV' lP0 layV' rfl hCVSt rfl hLVSt rfl hCVCl rfl hLVCl
                              w.hCon w.hLayOpt hSuiteLaw hLayLaw hCC' hSL' true adapter3
                              (protocolMeaning M a.program _ [] ins)
                              (roleMeaning M a.program _ w.prover [] (hideAll M w.prover ins))
                              (roleMeaning M a.program _ w.verifier [] (hideAll M w.verifier ins))
                              (.cons ((0 : Nat), ((0 : Nat), (heldTupleP, ()))) (.cons st0 (.cons [] .nil)))
                              st0 [] source ⟨0, 0, rfl⟩ hSt0Valid (fun _ h => nomatch h)
                              hProjP hProjV hSafeP hSafeV hShapeP hShapeV hPShape hUniq
                              hLP hFed hNoHalt'
                          obtain ⟨att', seq', rfl⟩ := hInv'
                          exact ⟨out, outP, outV, att', seq', finalSt, suffix, recP, source',
                            hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩
                        obtain ⟨out, outP, outV, att', seq', finalSt, suffix, recP, source',
                          hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
                          hRunSim3 sampP' conP' layP' hSPSt hCPSt hLPSt hSPCl hCPCl hLPCl
                        obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
                        simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlV0
                        have hFinish3 : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
                            (callee : Member a.program.headers.protocols hdr)
                            (ins' : HList (LVal M) hdr.ins)
                            (hInsEq : cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins' = insF)
                            (first' : Stack.Takes (hE ▸ [sampPL, conPL, layPL]) = [])
                            (matched' : Stack.Gives (hE ▸ [sampPL, conPL, layPL]) = Stack.Takes (hE ▸ [conVL, layVL]))
                            (outP' : HList (RV M w.prover) hdr.outs)
                            (outV' : HList (RV M w.verifier) hdr.outs)
                            (recP' recV' : List (Happened M)),
                            Alone M source w.prover
                              ((Stack.handler M (Defs.fnTable M a.program.defs)
                                (Defs.rTable M a.program.defs) (hE ▸ [sampPL, conPL, layPL])).run
                                (retryOf M none)
                                (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                                (cast (by subst hE; rfl)
                                  (HList.cons ((0 : Nat), ((0 : Nat), (heldTupleP, ())))
                                    (HList.cons st0 (HList.cons ([] : List (M.Val wL.unitTy)) HList.nil)))))
                              recP' (.returned (outP', cast (by subst hE; rfl)
                                (HList.cons (att', (seq', (heldTupleP, ())))
                                  (HList.cons finalSt (HList.cons suffix HList.nil))))) →
                            Alone M source w.verifier
                              ((Stack.handler M (Defs.fnTable M a.program.defs)
                                (Defs.rTable M a.program.defs) (hE ▸ [conVL, layVL])).run
                                (retryOf M none)
                                (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                                (cast (by subst hE; rfl)
                                  (HList.cons st0 (HList.cons (suffix, ((0 : Nat), ())) HList.nil))))
                              recV' (.returned (outV', cast (by subst hE; rfl)
                                (HList.cons finalSt (HList.cons (suffix, (suffix.length, ())) HList.nil)))) →
                            ∃ gives givesV,
                              Alone M source w.prover
                                (runStack a M callee none w.prover (hE ▸ [sampPL, conPL, layPL])
                                  (hideAll M w.prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                                recP' (.returned (outP', gives)) ∧
                              Alone M source w.verifier
                                (runStack a M callee none w.verifier (hE ▸ [conVL, layVL])
                                  (hideAll M w.verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                                recV' (.returned (outV', givesV)) := by
                          intro hdr hE callee ins' hInsEq first' matched' outP' outV' recP' recV' hAP hAV
                          subst hE
                          simp only [cast_eq] at hInsEq
                          subst hInsEq
                          change Alone M source w.prover
                            ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                              [sampPL, conPL, layPL]).run (retryOf M none)
                              (roleMeaning M a.program callee w.prover [] (hideAll M w.prover insF))
                              (.cons ((0 : Nat), ((0 : Nat), (heldTupleP, ())))
                                (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil))))
                            recP' (.returned (outP', .cons (att', (seq', (heldTupleP, ())))
                              (.cons finalSt (.cons suffix .nil)))) at hAP
                          change Alone M source w.verifier
                            ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conVL, layVL]).run
                              (retryOf M none) (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier insF))
                              (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)))
                            recV' (.returned (outV', .cons finalSt (.cons (suffix, (suffix.length, ())) .nil))) at hAV
                          refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
                          · unfold runStack
                            change Alone M source w.prover
                              ((Stack.start M (Defs.fnTable M a.program.defs) [sampPL, conPL, layPL]
                                (hideAll M w.prover insF) .nil).bind _) _ _
                            have hStP3 : Stack.start M (Defs.fnTable M a.program.defs)
                                [sampPL, conPL, layPL] (hideAll M w.prover insF) .nil =
                                .done (.cons ((0 : Nat), ((0 : Nat), (heldTupleP, ())))
                                  (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil))) := by
                              change ((liftLocal id (sampPL.start.denote
                                (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                (Env.positional (heldValues M w.prover (hideAll M w.prover insF))))).bind fun f₀ =>
                                  (((liftLocal id (conPL.start.denote
                                    (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                    (Env.positional (heldValues M w.prover (hideAll M w.prover insF))))).bind fun f₁ =>
                                      ((liftLocal id ((layoutPStart wL.unitTy).denote
                                        (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                        (Env.positional (heldValues M w.prover (hideAll M w.prover insF))))).bind fun f₂ =>
                                          (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map
                                        fun others => HList.cons f₁.single others).map fun others => HList.cons f₀.single others)) = _
                              dsimp only [sampPL]
                              rw [samplesStart_denote, liftLocal_done]
                              dsimp only [Process.bind, HList.single]
                              rw [hSt0P, liftLocal_done]
                              dsimp only [Process.bind, HList.single]
                              rw [layoutPStart_denote]; rfl
                            rw [hStP3]; dsimp only [Process.bind]
                            have hAP' := alone_mapHalt M (g := Prod.fst) hAP
                            rw [← List.append_nil recP']
                            refine alone_bind M hAP' ?_
                            have hFinP3 : Stack.finish M (Defs.fnTable M a.program.defs)
                                [sampPL, conPL, layPL]
                                (.cons (att', (seq', (heldTupleP, ()))) (.cons finalSt (.cons suffix .nil))) =
                                .done (.cons suffix .nil) := by
                              rw [stack_finish_three]; dsimp only [sampPL, conPL, layPL, BuildLayoutStreaming.layP]
                              rw [emptyFinish_denote]
                              dsimp only [liftLocal_done, Process.bind]
                              rw [emptyFinish_denote]
                              dsimp only [liftLocal_done, Process.bind]
                              rw [identityFinish_denote]; rfl
                            rw [hFinP3]; exact .done
                          · unfold runStack
                            change Alone M source w.verifier
                              ((Stack.start M (Defs.fnTable M a.program.defs) [conVL, layVL]
                                (hideAll M w.verifier insF) (.cons suffix .nil)).bind _) _ _
                            have hStV2 : Stack.start M (Defs.fnTable M a.program.defs)
                                [conVL, layVL] (hideAll M w.verifier insF) (.cons suffix .nil) =
                                .done (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)) := by
                              change ((liftLocal id (conVL.start.denote
                                (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                (Env.positional (heldValues M w.verifier (hideAll M w.verifier insF))))).bind fun f₁ =>
                                  ((liftLocal id ((layoutVStart wL.unitTy).denote
                                    (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                    (Env.positional (.cons suffix (heldValues M w.verifier (hideAll M w.verifier insF)))))).bind fun f₂ =>
                                      (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map
                                    fun others => HList.cons f₁.single others) = _
                              rw [hSt0V, liftLocal_done]
                              dsimp only [Process.bind, HList.single]
                              rw [layoutVStart_denote]; rfl
                            rw [hStV2]; dsimp only [Process.bind]
                            have hAV' := alone_mapHalt M (g := Prod.fst) hAV
                            rw [← List.append_nil recV']
                            refine alone_bind M hAV' ?_
                            have hFinV2 : Stack.finish M (Defs.fnTable M a.program.defs)
                                [conVL, layVL] (.cons finalSt (.cons (suffix, (suffix.length, ())) .nil)) =
                                .done .nil := by
                              rw [stack_finish_two]; dsimp only [conVL, layVL, BuildLayoutStreaming.layV]
                              rw [emptyFinish_denote]
                              dsimp only [liftLocal_done, Process.bind]
                              rw [layoutVFinish_denote]
                              simp only [Nat.beq_refl, Bool.cond_true]; rfl
                            rw [hFinV2]; exact .done
                        have hStackPEq : w.toDeployed.stack w.prover = hEntryF ▸ [sampPL, conPL, layPL] := by
                          dsimp only [DeployDerived.toDeployed]
                          rw [dite_eq_left rfl, hSampLayerEq, hLPW]
                          exact cast_ins_eq_cast_hdr hEntryF _
                        have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [conVL, layVL] := by
                          dsimp only [DeployDerived.toDeployed]
                          rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl, hLVW]
                          exact cast_ins_eq_cast_hdr hEntryF _
                        have hFirst' : Stack.Takes (hEntryF ▸ [sampPL, conPL, layPL]) = [] := by
                          rw [← hStackPEq]; exact first
                        have hMatched' : Stack.Gives (hEntryF ▸ [sampPL, conPL, layPL]) = Stack.Takes (hEntryF ▸ [conVL, layVL]) := by
                          rw [← hStackPEq, ← hStackVEq]; exact matched
                        obtain ⟨gives, givesV, hRunP, hRunV⟩ :=
                          hFinish3 _ hEntryF _ ins rfl hFirst' hMatched'
                            outP outV recP recV
                            (alone_cast_stack3 M hEntryF sampPL conPL layPL rfl rfl rfl hAlP)
                            (alone_cast_stack2 M hEntryF conVL layVL rfl rfl hAlV0)
                        refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
                          recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
                          ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
                        · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackPEq
                            ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
                        · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
                            ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
                            (cast_heq _ _) hRunV
              · cases hSampBuild

end Completeness

end Zkc.Core
