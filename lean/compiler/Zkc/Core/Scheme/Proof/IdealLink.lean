module

public import Zkc.Core.Scheme.Proof.CompletenessHelpers

@[expose] public section

/-!
Ideal random-oracle verifier linkage (`deployIdeal_link`), pure ideal-path step injectivity,
and non-malleable canonical compact proof parsing (`buildCompactParse_written`,
`compactLayoutVStart_written`).
-/

namespace Zkc.Core

open LayerBuild


open LayerBuild

/-! ## Pure collision-free ideal random-oracle linkage (`deployIdeal_link`) -/

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

private theorem idealRO_asOracle_query {unitTy : V.Ty} (ro : IdealRO M unitTy)
    (st : M.Val (idealPathTy unitTy)) (lbl : List Nat) (τ : V.Ty) :
    IdealRO.asOracle M ro [idealQueryTy unitTy] (.cons (st, (lbl, ())) .nil) τ = ro st lbl τ := by
  change (if h : idealQueryTy unitTy = idealQueryTy unitTy then
      let q' : M.Val (idealQueryTy unitTy) := cast (congrArg M.Val h) (st, (lbl, ()))
      ro q'.1 q'.2.1 τ
    else none) = ro st lbl τ
  rw [dite_eq_left rfl]
  rfl

private theorem answerService_request_some {H A : Type} (service : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    {hearers : List Role} {at_ : Occurrence} {ins : List V.Ty}
    {payload : HList M.Val ins} {τ : V.Ty} {k : M.Val τ → Process (RSig M) H A}
    {v : M.Val τ} (hAns : oracle ins payload τ = some v) :
    Process.answerService service oracle
      (.call (.own (.request service) hearers at_ ins payload τ) k) =
      Process.answerService service oracle (k v) := by
  conv => lhs; unfold Process.answerService
  rw [ite_eq_left rfl, hAns]

private theorem tag_bytes_cons (tag : Nat) (htag : tag < 256) (lbl : List Nat)
    (hlbl : ∀ b, b ∈ lbl → b < 256) : ∀ b, b ∈ tag :: lbl → b < 256 := fun b hb => by
  rcases List.mem_cons.mp hb with rfl | hm
  · exact htag
  · exact hlbl b hm

private theorem alone_own_returned_iff {source : Source M} {r : Role} {H A : Type}
    {gk : GivenKind V} {hs : List Role} {at_ : Occurrence} {gIns : List V.Ty}
    {payload : HList M.Val gIns} {τ : V.Ty} {k : M.Val τ → Process (RSig M) H A} {x : A} :
    (∃ rec, Alone M source r (.call (.own gk hs at_ gIns payload τ) k) rec (.returned x)) ↔
      ∃ v, source at_ τ = some v ∧ ∃ rec, Alone M source r (k v) rec (.returned x) := by
  constructor
  · rintro ⟨rec, hAl⟩
    cases hAl with
    | own hSrc hRest => exact ⟨_, hSrc, _, hRest⟩
  · rintro ⟨v, hSrc, rec, hRest⟩
    exact ⟨_, .own hSrc hRest⟩

private theorem alone_begin_returned_iff {source : Source M} {r : Role} {H A : Type}
    {at_ : Occurrence} {k : Nat → Process (RSig M) H A} {x : A} :
    (∃ rec, Alone M source r (.call (.begin at_) k) rec (.returned x)) ↔
      ∃ rec, Alone M source r (k 0) rec (.returned x) := by
  constructor
  · rintro ⟨rec, hAl⟩; cases hAl with | «begin» hRest => exact ⟨_, hRest⟩
  · rintro ⟨rec, hRest⟩; exact ⟨_, .begin hRest⟩

private theorem alone_settle_returned_iff {source : Source M} {r : Role} {H A : Type}
    {at_ : Occurrence} {k : Unit → Process (RSig M) H A} {x : A} :
    (∃ rec, Alone M source r (.call (.settle at_) k) rec (.returned x)) ↔
      ∃ rec, Alone M source r (k ()) rec (.returned x) := by
  constructor
  · rintro ⟨rec, hAl⟩; cases hAl with | settle hRest => exact ⟨_, hRest⟩
  · rintro ⟨rec, hRest⟩; exact ⟨_, .settle hRest⟩

private theorem alone_map_nil_iff {source : Source M} {r : Role} {H A : Type}
    {gTys : List V.Ty} (hG : gTys = [])
    (p : Process (RSig M) H (A × HList M.Val gTys)) (outV : A) :
    (∃ rec givesV, Alone M source r p rec (.returned (outV, givesV))) ↔
      ∃ rec, Alone M source r
        (p.map fun out => (out.1, cast (congrArg (HList M.Val) hG) out.2))
        rec (.returned (outV, .nil)) := by
  subst hG
  simp only [cast_eq]
  have hMap : p.map (fun out : A × HList M.Val [] => (out.1, out.2)) = p :=
    (congrArg (fun f => p.map f) (funext fun ⟨_, _⟩ => rfl)).trans (Process.map_id' p)
  rw [hMap]
  constructor
  · rintro ⟨rec, givesV, hAl⟩
    cases givesV
    exact ⟨rec, hAl⟩
  · rintro ⟨rec, hAl⟩
    exact ⟨rec, .nil, hAl⟩

private theorem stack2_lay_enc_step {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {verifier : Role} {ins : List (LTy V)}
    {suiteUnitTy τ : V.Ty}
    (layV' : Layer V hs verifier ins)
    (st : M.Val (idealPathTy suiteUnitTy))
    (lst : M.Val layV'.state)
    (val : M.Val τ) (tagLbl : List Nat)
    (encRef : TypedFnRef V hs.fns [τ] [.seq suiteUnitTy none])
    (encV : List (M.Val suiteUnitTy))
    (hEnc : encRef.eval M fnTable (.cons val .nil) = .done (.cons encV .nil)) :
    Process.map
      (fun (out : M.Val τ × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
        (out.1, HList.cons out.2.1 out.2.2))
      (Process.mapHalt
        (fun (stop : Stop × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
          (stop.1, HList.cons stop.2.1 stop.2.2))
        ((Process.mapHalt
          (fun (stop : Stop × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
            (stop.1, stop.2.1, stop.2.2))
          ((Stack.handler M fnTable rTable [layV']).answer
            (Process.map
              (fun out =>
                let values := HList.split [τ] (aloneOut M verifier out)
                (values.1.single, values.2.single))
              (Process.mapHalt (fun why => (why, st))
                (Process.map
                  (fun enc => aloneIn M verifier (.cons val (.cons (idealPathPush M st tagLbl enc.single) .nil)))
                  (liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons val .nil))))))
            st (HList.cons lst .nil))).bind
          fun out => Process.done (out.1.1, out.1.2, out.2))) =
    .done (val, HList.cons (idealPathPush M st tagLbl encV) (HList.cons lst .nil)) := by
  rw [hEnc, liftLocal_done]
  dsimp only [Process.map, Process.mapHalt, Handler.answer, Process.bind, HList.single]
  rw [aloneOut_aloneIn]; rfl

private theorem idealAbsorbClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (at_ : Occurrence) (hSite : site = at_.site) (st : M.Val (idealPathTy unitTy))
    (cs : List (Clause V hs verifier (idealPathTy unitTy))) :
    Clause.answer M fnTable rTable
        (idealAbsorbClause hfree verifier prover site kind label hlabel encRef :: cs)
        (.get kind prover at_ τ) st =
      .call (.get kind prover ⟨at_.path, site.key⟩ τ) fun msg =>
        (((liftLocal id (encRef.eval M fnTable (.cons msg .nil))).map fun enc =>
          aloneIn M verifier (.cons msg (.cons (idealPathPush M st (2 :: label) enc.single) .nil))).mapHalt
            fun why => (why, st)).map fun out =>
          let values := HList.split [τ] (aloneOut M verifier out)
          (values.1.single, values.2.single) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((idealAbsorbClause hfree verifier prover site kind label hlabel encRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt _).map _ = _
  rw [idealAbsorbClause_denote]
  dsimp only [Process.mapHalt, Process.map, idealAbsorbClause, Clause.site, ROp.reply]
  congr 1; funext msg; congr 1; funext out
  cases hsp : HList.split [τ] (aloneOut M verifier out) with
  | mk v1 v2 =>
      cases v1 with | cons a an => cases an; rfl

private theorem ideal_clauses_answer_flow_abs {a : Admitted V} {suite : ModuleRef}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cV : List (Clause V a.program.headers verifier (idealPathTy unitTy))},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty) (st : M.Val (idealPathTy unitTy)),
        (∃ e, (e, true) ∈ es ∧ e.site = at_.site ∧ e.τ = τ ∧
          e.cls = .flow kind prover [verifier]) →
        ∃ (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]),
          findSuiteEncode a suite unitTy τ = some encRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.get kind prover at_ τ) st =
            .call (.get kind prover ⟨at_.path, at_.site.key⟩ τ) fun msg =>
              (((liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil))).map fun enc =>
                aloneIn M verifier (.cons msg (.cons (idealPathPush M st (2 :: msgLabel at_.site) enc.single) .nil))).mapHalt
                  fun why => (why, st)).map fun out =>
                let values := HList.split [τ] (aloneOut M verifier out)
                (values.1.single, values.2.single)
  | _, [], _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, cV, h, kind, at_, τ, st,
      ⟨e', he', hSite, hTy, hECls⟩ => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => ideal_clauses_answer_flow_abs (idx + 1) rest hRec kind at_ τ st hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
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
                          exact idealAbsorbClause_answer M _ _ hfree verifier prover e.site kind
                            (msgLabel e.site) (msgLabel_bytes e.site) encRef at_ hSiteEq st vRest
                        · rcases List.mem_cons.mp he' with hEqP | hmem
                          · cases hEqP
                            rw [hCls] at hECls; cases hECls
                            exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                          · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                            refine ⟨encR, hE, ?_⟩
                            unfold Clause.answer
                            exact (dite_eq_right hMatch).trans hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
                    rcases List.mem_cons.mp he' with hEqP | hmem
                    · cases hEqP
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
              · split at h
                · rename_i hOut; cases h
                  rcases List.mem_cons.mp he' with hEqP | hmem
                  · cases hEqP; rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
                  · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
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
                                  rcases List.mem_cons.mp he' with hEqP | hmem
                                  · cases hEqP; rw [hCls] at hECls; cases hECls
                                  · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                                    refine ⟨encR, hE, ?_⟩
                                    unfold Clause.answer
                                    rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                    exact hAns
                        · cases h
                  · split at h
                    · cases h
                      rcases List.mem_cons.mp he' with hEqP | hmem
                      · cases hEqP; rw [hCls] at hECls; cases hECls
                      · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with hEqP | hmem
                    · cases hEqP; rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                  · cases h

private theorem ideal_clauses_unmatched_elided_flow {a : Admitted V} {suite : ModuleRef}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cV : List (Clause V a.program.headers verifier (idealPathTy unitTy))},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty),
        (∀ e b, (e, b) ∈ es → e.site = at_.site → e.τ = τ →
          e.cls = .flow kind prover [verifier] → b = false) →
        ∀ c ∈ cV, ¬ ClauseMatches M c (.get kind prover at_ τ)
  | _, [], _, h, _, _, _, _ => by cases h; exact fun _ hc => nomatch hc
  | idx, (e, needAbs) :: rest, cV, h, kind, at_, τ, hNoAbs => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := ideal_clauses_unmatched_elided_flow (idx + 1) rest hRec kind at_ τ
            (fun e' b' hm => hNoAbs e' b' (List.mem_cons_of_mem _ hm))
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some _ =>
                        rw [hEnc] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · intro hM
                          have hSite : e.site = at_.site := hM.1
                          have hKind : kind₀ = kind := by
                            have hp := Option.some.inj hM.2.1; cases hp; rfl
                          have hTy : e.τ = τ := (List.cons.inj hM.2.2.2).1
                          have hF := hNoAbs e true List.mem_cons_self hSite hTy
                            (hKind ▸ hPV.1 ▸ hPV.2 ▸ hCls)
                          cases hF
                        · exact ih c hm
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h; exact ih
              · split at h
                · cases h; exact ih
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
                                  intro c hc
                                  rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hM; cases hM.2.1
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

private theorem ideal_clauses_answer_coin {a : Admitted V} {suite : ModuleRef}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)),
      (∀ k p, es[k]? = some p → events[idx + k]? = some p.1) →
      ∀ {cV : List (Clause V a.program.headers verifier (idealPathTy unitTy))},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ (law : V.LawKey) (at_ : Occurrence) (τ : V.Ty)
        (st : M.Val (idealPathTy unitTy)),
        (∃ p ∈ es, p.1.site = at_.site ∧ p.1.τ = τ ∧
          p.1.cls = .given (.coin law) verifier [prover]) →
        ∃ (idxV : Nat) (eV : ShapeEvent V)
          (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]),
          events[idxV]? = some eV ∧ eV.site = at_.site ∧ eV.τ = τ ∧
          eV.cls = .given (.coin law) verifier [prover] ∧
          findSuiteEncode a suite unitTy τ = some encRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.own (.coin law) [prover] at_ [] .nil τ) st =
            .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                [idealQueryTy unitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ) fun coin =>
              .call (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin) fun _ =>
                (((liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil))).map fun enc =>
                  aloneIn M verifier (.cons coin (.cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single) .nil))).mapHalt
                    fun why => (why, st)).map fun out =>
                  let values := HList.split [τ] (aloneOut M verifier out)
                  (values.1.single, values.2.single)
  | _, [], _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, hSuf, cV, h, law, at_, τ, st,
      ⟨p', hp', hSite, hTy, hECls⟩ => by
      unfold buildIdealVerifierClauses.go at h
      have hSufRest : ∀ k p'', rest[k]? = some p'' → events[(idx + 1) + k]? = some p''.1 := by
        intro k p'' hk; have := hSuf (k + 1) p'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 (e, needAbs) rfl
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => ideal_clauses_answer_coin (idx + 1) rest hSufRest hRec
            law at_ τ st hIn
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some _ =>
                        rw [hEnc] at h; cases h
                        rcases List.mem_cons.mp hp' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨idxV, eV, encR, h1, h2, h3, h4, h5, hAns⟩ :=
                            ih ⟨p', hmem, hSite, hTy, hECls⟩
                          refine ⟨idxV, eV, encR, h1, h2, h3, h4, h5, ?_⟩
                          unfold Clause.answer; rw [dite_eq_right (fun hm => by cases hm.2.1)]; exact hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
              · split at h
                · cases h
                  rcases List.mem_cons.mp hp' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
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
                                      some (Part.own (.coin law₀) hearers₀) = some (.own (.coin law) [prover]) ∧
                                      ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                                  · have hSiteEq : e.site = at_.site := hMatch.1
                                    have hPartEq : Part.own (.coin law₀) hearers₀ = .own (.coin law) [prover] :=
                                      Option.some.inj hMatch.2.1
                                    cases hPartEq
                                    have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                                    cases e with
                                    | mk eSite eCls eτ =>
                                        dsimp only at hIdx hCls hEnc hSiteEq hTyEq hMatch hCoin
                                        subst eτ; subst eSite
                                        refine ⟨idx, ⟨at_.site, eCls, τ⟩, encRef, hIdx, rfl, rfl, hCoin.1 ▸ hCls, hEnc, ?_⟩
                                        unfold Clause.answer
                                        have hM : (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) [prover])
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.site =
                                            (ROp.occurrence M (.own (.coin law) [prover] at_ [] .nil τ)).site ∧
                                            some (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) [prover])
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.part =
                                            ROp.part M (.own (.coin law) [prover] at_ [] .nil τ) ∧
                                            (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) [prover])
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.takes =
                                            ROp.takes M (.own (.coin law) [prover] at_ [] .nil τ) ∧
                                            (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) [prover])
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.gives =
                                            ROp.gives M (.own (.coin law) [prover] at_ [] .nil τ) := ⟨rfl, rfl, rfl, rfl⟩
                                        rw [dite_eq_left hM]
                                        change (((idealDeriveClause hfree verifier prover at_.site (.own (.coin law) [prover])
                                          [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                          (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).code.denote
                                          (roleSem M verifier _ _) at_.path
                                          (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt _).map _ = _
                                        rw [idealDeriveClause_denote_nil]
                                        dsimp only [Process.mapHalt, Process.map, idealDeriveClause, Clause.site]
                                        congr 1; funext coin; congr 1; funext _; congr 1; funext out
                                        cases hsp : HList.split [τ] (aloneOut M verifier out) with
                                        | mk v1 v2 => cases v1 with | cons a an => cases an; rfl
                                  · rcases List.mem_cons.mp hp' with rfl | hmem
                                    · rw [hCls] at hECls; cases hECls
                                      exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                                    · obtain ⟨idxV, eV, encR, h1, h2, h3, h4, h5, hAns⟩ :=
                                        ih ⟨p', hmem, hSite, hTy, hECls⟩
                                      refine ⟨idxV, eV, encR, h1, h2, h3, h4, h5, ?_⟩
                                      unfold Clause.answer
                                      exact (dite_eq_right hMatch).trans hAns
                        · cases h
                  · split at h
                    · rename_i hNil
                      cases h
                      rcases List.mem_cons.mp hp' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; cases hNil
                      · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
                  · cases h

private theorem ideal_clauses_unmatched_closed {a : Admitted V} {suite : ModuleRef}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cV : List (Clause V a.program.headers verifier (idealPathTy unitTy))},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
        declKey events idx es = .ok cV →
      ∀ op, ROp.IsClosed M op → ∀ c ∈ cV, ¬ ClauseMatches M c op
  | _, [], _, h, _, _ => by cases h; exact fun _ hc => nomatch hc
  | idx, (e, needAbs) :: rest, cV, h, op, hCl => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover
          verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := ideal_clauses_unmatched_closed (idx + 1) rest hRec op hCl
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some _ =>
                        rw [hEnc] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · intro hM; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, idealAbsorbClause] at hCl hM
                        · exact ih c hm
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h; exact ih
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
                                                cases hCoin.2
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
          e.cls = .flow kind prover [verifier]) →
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
      ⟨e', he', hSite, hTy, hECls⟩ => by
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
                    · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                      refine ⟨rR, h1, ?_⟩
                      unfold Clause.answer
                      exact (dite_eq_right hMatch).trans hAns
              · rename_i hNotPV; cases h
                rcases List.mem_cons.mp he' with rfl | hmem
                · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, rfl⟩ hNotPV
                · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
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
                        · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                          refine ⟨rR, h1, ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                        refine ⟨rR, h1, ?_⟩
                        unfold Clause.answer
                        rw [dite_eq_right (fun hm => by cases hm.2.1)]
                        exact hAns
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, hECls⟩

private theorem streaming_layout_answer_told_drop {a : Admitted V} {layout : Layout}
    (hNoCarry : layout.carry = []) {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ e ∈ es, e ∈ events) →
      ∀ {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
        {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (k : Nat) (e₀ : ShapeEvent V), es[k]? = some e₀ →
        ∀ (law : V.LawKey) (at_ : Occurrence) (coin : M.Val e₀.τ),
          e₀.cls = .given (.coin law) verifier [prover] →
          at_.site = ⟨e₀.site.through, drawToldKey events (idx + k)⟩ →
          ∀ buf off,
            Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              vCs (.give .message [prover] at_ e₀.τ coin) (buf, (off, ())) =
              .done ((), (buf, (off, ())))
  | _, [], _, _, _, _, _, _, hk, _, _, _, _, _, _, _ => by simp at hk
  | idx, e :: rest, hSub, pCs, vCs, h, k, e₀, hk, law, at_, coin, hE₀Cls, hAtSite, buf, off => by
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
              rw [ite_eq_left ⟨rfl, rfl⟩] at h
              rw [ite_eq_right (by simp [hNoCarry])] at h; cases h
              have hSiteEq : ⟨e.site.through, drawToldKey events idx⟩ = at_.site := by
                simpa using hAtSite.symm
              exact layoutDropClause_answer M _ _ verifier _ .message [prover] at_ hSiteEq coin (buf, (off, ())) pair.2
          | succ k' =>
              have hShiftSite : at_.site = ⟨e₀.site.through, drawToldKey events ((idx + 1) + k')⟩ := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAtSite
              have hToldNoMatch : (⟨e.site.through, drawToldKey events idx⟩ : Site) ≠ at_.site := by
                intro heq
                have hkEq : (drawToldKey events idx).number = (drawToldKey events (idx + (k' + 1))).number := by
                  have := congrArg (fun s : Site => s.key.number) heq
                  rw [hAtSite] at this; exact this
                simp only [drawToldKey] at hkEq; omega
              have ih := streaming_layout_answer_told_drop hNoCarry (idx + 1) rest hSubRest hRec k' e₀ hk
                law at_ coin hE₀Cls hShiftSite buf off
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

private theorem ideal_verifier_bare_iff {a : Admitted V} {suite : ModuleRef} {layout : Layout}
    (hNoCarry : layout.carry = []) {suiteUnitTy unitTy : V.Ty}
    {hSuiteFree : Ty.isLinear V suiteUnitTy = false}
    {hfree : Ty.isLinear V unitTy = false}
    {serviceKey : Key} {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {shape : Shape V} {entryIns : List (LTy V)}
    (idealConV layV : Layer V a.program.headers verifier entryIns)
    (hConSt : idealConV.state = idealPathTy suiteUnitTy) (hLaySt : layV.state = streamStateTy unitTy)
    (hConGives : idealConV.gives = []) (hLayGives : layV.gives = [])
    (hConFin : idealConV.finish = hConGives.symm ▸ hConSt.symm ▸ emptyFinish (idealPathTy suiteUnitTy))
    (hLayFin : layV.finish = hLayGives.symm ▸ hLaySt.symm ▸ layoutVFinish unitTy hfree (finishGuardKey (shape.events [] id)))
    (hIV : buildIdealVerifierClauses.go a suite suiteUnitTy hSuiteFree serviceKey prover verifier
      declKey (shape.events [] id) 0 (shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hConSt ▸ idealConV.clauses))
    (hSL : ∃ pCs, buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
      (shape.events [] id) 0 (shape.events [] id) = .ok (pCs, hLaySt ▸ layV.clauses))
    (source : Source M) (ro : IdealRO M suiteUnitTy)
    (hRo : ro.AnswersDraws M prover verifier (shape.events [] id)) :
    ∀ {A : Type} (p : Program M A) (st : M.Val (idealPathTy suiteUnitTy))
      (buf : List (M.Val unitTy)) (off : Nat) (outV : A),
      M.Valid (idealPathTy suiteUnitTy) st →
      M.Valid (.seq unitTy none) buf →
      p.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (shape.events [] id))
        (fun _ => True) (fun _ => True) →
      ((∃ record,
        Alone M source verifier
          (Process.answerService serviceKey (IdealRO.asOracle M ro)
            ((((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              [idealConV, layV]).run (retryOf M none) p
                (.cons (hConSt.symm ▸ st) (.cons (hLaySt.symm ▸ (buf, (off, ())))
                  (.nil : HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns))))))).mapHalt Prod.fst).bind
              fun out => (Stack.finish M (Defs.fnTable M a.program.defs) [idealConV, layV] out.2).map
                fun gives => (out.1, cast (by simp [Stack.Gives, hConGives, hLayGives]) gives)))
          record (.returned (outV, (.nil : HList M.Val [])))) ↔
      BareIdealReturn M a suite layout serviceKey prover verifier
        (shape.eventsWithAbsorb prover verifier [] id false)
        source ro p st buf off outV) := by
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
          let events := shape.events [] id
          let eventsAbs := shape.eventsWithAbsorb prover verifier [] id false
          have hFst : eventsAbs.map Prod.fst = events :=
            eventsWithAbsorb_fst prover verifier [] id false shape
          have hIdealDisc : ∀ e ∈ events,
              match e.cls with
              | .flow _ giver getters =>
                  (giver = prover ∧ getters = [verifier]) ∨
                  (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
              | .given (.coin law) owner hearers =>
                  (owner = verifier ∧ hearers = [prover] ∧
                    ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
                  hearers = []
              | .given (.request _) owner hearers =>
                  (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
            have hGo : ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)) {cV'},
                buildIdealVerifierClauses.go a suite suiteUnitTy hSuiteFree serviceKey
                  prover verifier declKey events idx es = .ok cV' →
                ∀ p ∈ es, match p.1.cls with
                  | .flow _ giver getters =>
                      (giver = prover ∧ getters = [verifier]) ∨
                      (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                  | .given (.coin law) owner hearers =>
                      (owner = verifier ∧ hearers = [prover] ∧
                        ∃ sig, V.law law = some sig ∧ sig.out = p.1.τ ∧ sig.ins = []) ∨
                      hearers = []
                  | .given (.request _) owner hearers =>
                      (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
              intro idx es
              induction es generalizing idx with
              | nil => intro _ _ _ hp; cases hp
              | cons p rest ih =>
                  intro cV' hGo' p' hp'
                  unfold buildIdealVerifierClauses.go at hGo'
                  cases hRec : buildIdealVerifierClauses.go a suite suiteUnitTy hSuiteFree
                      serviceKey prover verifier declKey events (idx + 1) rest with
                  | error _ => rw [hRec] at hGo'; cases hGo'
                  | ok vRest =>
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
                      · exact ih (idx + 1) hRec p' hmem
            intro e he
            rw [← hFst] at he
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
            exact hGo 0 eventsAbs hIV p hp
          let idealConV' : Layer V a.program.headers verifier entryIns :=
            ⟨cLine, idealPathTy suiteUnitTy, cTakes, [], cClauses, cAgain, cStart,
              emptyFinish (idealPathTy suiteUnitTy)⟩
          let layV' : Layer V a.program.headers verifier entryIns :=
            ⟨lLine, streamStateTy unitTy, lTakes, [], lClauses, lAgain, lStart,
              layoutVFinish unitTy hfree (finishGuardKey events)⟩
          have hPassV : ∀ op (st : M.Val (idealPathTy suiteUnitTy)) (lst : M.Val (streamStateTy unitTy)),
              ROp.IsClosed M op →
              (Stack.handler M fnTable rTable [idealConV', layV']).clause op
                  (.cons st (.cons lst (.nil : HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns)))))) =
                .call op fun reply =>
                  .done (reply, .cons st (.cons lst (.nil : HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns)))))) := fun op st lst hCl =>
            stack2_clause_pass M fnTable rTable idealConV' layV' op st lst
              (clause_answer_unmatched_all M fnTable rTable op st cClauses
                (ideal_clauses_unmatched_closed M 0 eventsAbs hIV op hCl))
              (clause_answer_unmatched_all M fnTable rTable op lst lClauses
                (streaming_layout_unmatched_closed M 0 events hSL' op hCl).2)
          have hLay1Step : ∀ (op : ROp M) (buf : List (M.Val unitTy)) (off : Nat),
              (Stack.handler M fnTable rTable [layV']).clause op (.cons (buf, (off, ())) .nil) =
              ((Clause.answer M fnTable rTable lClauses op (buf, (off, ()))).mapHalt
                fun stop => (stop.1, .cons stop.2 .nil)).map fun out => (out.1, .cons out.2 .nil) := by
            intro op buf off
            change ((((Layer.handler M fnTable rTable layV').over
                (Stack.handler M fnTable rTable [])).clause op
                ((buf, (off, ())), .nil)).mapHalt _).map _ = _
            dsimp only [Layer.handler, Handler.over, layV']
            have hAns0 : ∀ (p0 : Process (RSig M) (Stop × M.Val (streamStateTy unitTy))
                ((RSig M).Reply op × M.Val (streamStateTy unitTy))),
                Process.map (fun (out : (RSig M).Reply op × M.Val (streamStateTy unitTy) × HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns)))) =>
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
              | call op' k' ih' =>
                  dsimp only [Handler.answer, Stack.handler, Process.map, Process.mapHalt, Process.bind]
                  congr 1; funext x; exact ih' x
            exact hAns0 _
          intro A p
          induction p with
          | done aOut =>
              intro st buf off outV _ _ _
              have hFin : Stack.finish M (Defs.fnTable M a.program.defs) [idealConV', layV']
                  (.cons st (.cons (buf, (off, ())) .nil)) =
                  bif Nat.beq off buf.length then .done .nil
                  else .halt (.declared .reject ⟨[], finishGuardKey events⟩) := by
                rw [stack_finish_two]; dsimp only [idealConV', layV']
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [layoutVFinish_denote]
                cases Nat.beq off buf.length <;> rfl
              dsimp only [Handler.run, Process.mapHalt, Process.bind]
              rw [hFin]
              cases hBeq : Nat.beq off buf.length with
              | false =>
                  dsimp only [cond, Process.map, Process.answerService]
                  constructor
                  · rintro ⟨_, hAl⟩; cases hAl
                  · intro hBare; cases hBare with
                    | done hLen => rw [hLen, Nat.beq_refl] at hBeq; cases hBeq
              | true =>
                  dsimp only [cond, Process.map, Process.answerService]
                  have hLen : off = buf.length := Nat.eq_of_beq_eq_true hBeq
                  constructor
                  · rintro ⟨_, hAl⟩; cases hAl; exact .done hLen
                  · intro hBare; cases hBare; exact ⟨[], .done⟩
          | halt why =>
              intro _ _ _ _ _ _ _
              dsimp only [Handler.run, Process.mapHalt, Process.bind, Process.answerService]
              constructor
              · rintro ⟨_, hAl⟩; cases hAl
              · intro hBare; cases hBare
          | call op k ih =>
              intro st buf off outV hStV hBufV ⟨hOpSh, hKSh⟩
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
                  have hGivP : giver = prover ∧ gs' = [verifier] := by
                    rcases hD with ⟨hEqP, hEqGs⟩ | ⟨_, _, _, hNotV⟩
                    · exact ⟨hEqP, hEqGs⟩
                    · exact absurd hVin hNotV
                  rcases hGivP with ⟨rfl, rfl⟩
                  have hEInAbs : ∃ need, (e, need) ∈ eventsAbs := by
                    have hM : e ∈ eventsAbs.map Prod.fst := hFst.symm ▸ he
                    obtain ⟨⟨e₀, b₀⟩, hIn, hEq⟩ := List.mem_map.mp hM
                    dsimp only at hEq; subst hEq
                    exact ⟨b₀, hIn⟩
                  obtain ⟨need, hNeed⟩ := hEInAbs
                  cases need with
                  | true =>
                      have hNeedTrue : needIdealAbsorb giver verifier eventsAbs at_.site kind τ = true := by
                        unfold needIdealAbsorb
                        exact List.any_eq_true.mpr ⟨(e, true), hNeed, by simp [hSite, hTy, hCls]⟩
                      obtain ⟨encRef, hEncFind, hConAns⟩ :=
                        ideal_clauses_answer_flow_abs M 0 eventsAbs hIV kind at_ τ st
                          ⟨e, hNeed, hSite, hTy, hCls⟩
                      obtain ⟨rRef, hRFind, hLayAns⟩ :=
                        streaming_layout_answer_verifier_flow_full M 0 events hSL' kind ⟨at_.path, at_.site.key⟩ τ buf off
                          ⟨e, he, hSite, hTy, hCls⟩
                      have hReadSafe := rRef.eval_safe M a (.cons buf (.cons off .nil)) ⟨hBufV, trivial, trivial⟩
                      cases hREval : rRef.eval M fnTable (.cons buf (.cons off .nil)) with
                      | call op _ => cases op
                      | halt why =>
                          have hClauseHalt : (Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                              (.cons st (.cons (buf, (off, ())) .nil)) =
                              .halt (why, .cons st (.cons (buf, (off, ())) .nil)) := by
                            change ((((Layer.handler M fnTable rTable idealConV').over
                                (Stack.handler M fnTable rTable [layV'])).clause (.get kind giver at_ τ)
                                (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                            dsimp only [Layer.handler, Handler.over, idealConV']
                            rw [hConAns]
                            dsimp only [Handler.answer]
                            rw [hLay1Step, hLayAns, hREval]
                            rfl
                          dsimp only [Handler.run]
                          change (∃ record, Alone M source verifier
                            (Process.answerService serviceKey (IdealRO.asOracle M ro)
                              (((((Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                                (.cons st (.cons (buf, (off, ())) .nil))).bind _).mapHalt _).bind _))
                            record (.returned (outV, HList.nil))) ↔ _
                          rw [hClauseHalt]
                          dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                          constructor
                          · rintro ⟨_, hAl⟩; cases hAl
                          · intro hBare
                            cases hBare with
                            | getAbsorb _ hRead' hEvalR' _ _ _ =>
                                have hrEq := Option.some.inj (hRFind.symm.trans hRead')
                                subst hrEq
                                rw [hREval] at hEvalR'; cases hEvalR'
                            | getElided hNoNeed _ _ _ =>
                                rw [hNeedTrue] at hNoNeed; cases hNoNeed
                      | done res =>
                          cases res with
                          | cons msg r1 =>
                              cases r1 with
                              | cons nextOff r2 =>
                                  cases r2
                                  rw [hREval] at hReadSafe
                                  have hMsgV : M.Valid τ msg := hReadSafe.1
                                  obtain ⟨encH, hEncD, hEncV⟩ := encRef.eval_done M a (.cons msg .nil) ⟨hMsgV, trivial⟩
                                  cases encH with
                                  | cons encV en =>
                                      cases en
                                      have hClauseDone : (Stack.handler M fnTable rTable [idealConV', layV']).clause
                                          (.get kind giver at_ τ) (.cons st (.cons (buf, (off, ())) .nil)) =
                                          .done (msg, .cons (idealPathPush M st (2 :: msgLabel at_.site) encV)
                                            (.cons (buf, (nextOff, ())) .nil)) := by
                                        change ((((Layer.handler M fnTable rTable idealConV').over
                                            (Stack.handler M fnTable rTable [layV'])).clause (.get kind giver at_ τ)
                                            (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                                        dsimp only [Layer.handler, Handler.over, idealConV']
                                        rw [hConAns]
                                        dsimp only [Handler.answer]
                                        rw [hLay1Step, hLayAns, hREval]
                                        dsimp only [liftLocal_done, Process.map, Process.mapHalt, Process.bind]
                                        exact stack2_lay_enc_step M fnTable rTable layV' st (buf, (nextOff, ()))
                                          msg (2 :: msgLabel at_.site) encRef encV hEncD
                                      dsimp only [Handler.run]
                                      change (∃ record, Alone M source verifier
                                        (Process.answerService serviceKey (IdealRO.asOracle M ro)
                                          (((((Stack.handler M fnTable rTable [idealConV', layV']).clause
                                            (.get kind giver at_ τ) (.cons st (.cons (buf, (off, ())) .nil))).bind _).mapHalt _).bind _))
                                        record (.returned (outV, HList.nil))) ↔ _
                                      rw [hClauseDone]
                                      dsimp only [Process.bind]
                                      have hSt'V : M.Valid (idealPathTy suiteUnitTy)
                                          (idealPathPush M st (2 :: msgLabel at_.site) encV) :=
                                        idealPathPush_valid M st (2 :: msgLabel at_.site) encV hStV
                                          (tag_bytes_cons 2 (by decide) (msgLabel at_.site) (msgLabel_bytes at_.site))
                                          hEncV.1
                                      rw [ih msg (idealPathPush M st (2 :: msgLabel at_.site) encV)
                                        buf nextOff outV hSt'V hBufV (hKSh msg trivial)]
                                      constructor
                                      · exact fun hRest =>
                                          .getAbsorb hNeedTrue hRFind hREval hEncFind hEncD hRest
                                      · intro hBare
                                        cases hBare with
                                        | getAbsorb _ hRead' hEvalR' hEnc' hEvalE' hRest =>
                                            have hrEq := Option.some.inj (hRFind.symm.trans hRead')
                                            subst hrEq
                                            have hRRes := Process.done.inj (hREval.symm.trans hEvalR')
                                            cases hRRes
                                            have heEq := Option.some.inj (hEncFind.symm.trans hEnc')
                                            subst heEq
                                            have hERes := Process.done.inj (hEncD.symm.trans hEvalE')
                                            cases hERes
                                            exact hRest
                                        | getElided hNoNeed _ _ _ =>
                                            rw [hNeedTrue] at hNoNeed; cases hNoNeed
                  | false =>
                      have hNoAbs : ∀ e' b', (e', b') ∈ eventsAbs → e'.site = at_.site →
                          e'.τ = τ → e'.cls = .flow kind giver [verifier] →
                          b' = false := by
                        intro e' b' hIn hS hT hC
                        exact eventsWithAbsorb_flow_consistent giver verifier [] id false shape
                          hIn hNeed (hS.trans hSite.symm) (hT.trans hTy.symm) hC hCls
                      have hNeedFalse : needIdealAbsorb giver verifier eventsAbs at_.site kind τ = false := by
                        unfold needIdealAbsorb
                        apply Bool.eq_false_iff.mpr
                        intro hTrue
                        obtain ⟨⟨e', b'⟩, hIn, hCond⟩ := List.any_eq_true.mp hTrue
                        simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
                        cases hC' : e'.cls with
                        | flow k₀ g₀ gs₀ =>
                            rw [hC'] at hCond
                            simp only [decide_eq_true_eq] at hCond
                            have hbFalse := hNoAbs e' b' hIn hCond.1.1.2 hCond.1.2
                              (hCond.2.1 ▸ hCond.2.2.1 ▸ hCond.2.2.2 ▸ hC')
                            rw [hbFalse] at hCond; cases hCond.1.1.1
                        | given _ _ _ => rw [hC'] at hCond; cases hCond.2
                      have hConPass : Clause.answer M fnTable rTable cClauses (.get kind giver at_ τ) st =
                          .call (.get kind giver at_ τ) fun reply => .done (reply, st) :=
                        clause_answer_unmatched_all M fnTable rTable _ st cClauses
                          (ideal_clauses_unmatched_elided_flow M 0 eventsAbs hIV kind at_ τ hNoAbs)
                      obtain ⟨rRef, hRFind, hLayAns⟩ :=
                        streaming_layout_answer_verifier_flow_full M 0 events hSL' kind at_ τ buf off
                          ⟨e, he, hSite, hTy, hCls⟩
                      cases hREval : rRef.eval M fnTable (.cons buf (.cons off .nil)) with
                      | call op _ => cases op
                      | halt why =>
                          have hClauseHalt : (Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                              (.cons st (.cons (buf, (off, ())) .nil)) =
                              .halt (why, .cons st (.cons (buf, (off, ())) .nil)) := by
                            change ((((Layer.handler M fnTable rTable idealConV').over
                                (Stack.handler M fnTable rTable [layV'])).clause (.get kind giver at_ τ)
                                (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                            dsimp only [Layer.handler, Handler.over, idealConV']
                            rw [hConPass]
                            dsimp only [Handler.answer]
                            rw [hLay1Step, hLayAns, hREval]
                            rfl
                          dsimp only [Handler.run]
                          change (∃ record, Alone M source verifier
                            (Process.answerService serviceKey (IdealRO.asOracle M ro)
                              (((((Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                                (.cons st (.cons (buf, (off, ())) .nil))).bind _).mapHalt _).bind _))
                            record (.returned (outV, HList.nil))) ↔ _
                          rw [hClauseHalt]
                          dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                          constructor
                          · rintro ⟨_, hAl⟩; cases hAl
                          · intro hBare
                            cases hBare with
                            | getAbsorb hNeedT _ _ _ _ _ =>
                                rw [hNeedFalse] at hNeedT; cases hNeedT
                            | getElided _ hRead' hEvalR' _ =>
                                have hrEq := Option.some.inj (hRFind.symm.trans hRead')
                                subst hrEq
                                rw [hREval] at hEvalR'; cases hEvalR'
                      | done res =>
                          cases res with
                          | cons msg r1 =>
                              cases r1 with
                              | cons nextOff r2 =>
                                  cases r2
                                  have hClauseDone : (Stack.handler M fnTable rTable [idealConV', layV']).clause
                                      (.get kind giver at_ τ) (.cons st (.cons (buf, (off, ())) .nil)) =
                                      .done (msg, .cons st (.cons (buf, (nextOff, ())) .nil)) := by
                                    change ((((Layer.handler M fnTable rTable idealConV').over
                                        (Stack.handler M fnTable rTable [layV'])).clause (.get kind giver at_ τ)
                                        (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                                    dsimp only [Layer.handler, Handler.over, idealConV']
                                    rw [hConPass]
                                    dsimp only [Handler.answer]
                                    rw [hLay1Step, hLayAns, hREval]
                                    rfl
                                  dsimp only [Handler.run]
                                  change (∃ record, Alone M source verifier
                                    (Process.answerService serviceKey (IdealRO.asOracle M ro)
                                      (((((Stack.handler M fnTable rTable [idealConV', layV']).clause
                                        (.get kind giver at_ τ) (.cons st (.cons (buf, (off, ())) .nil))).bind _).mapHalt _).bind _))
                                    record (.returned (outV, HList.nil))) ↔ _
                                  rw [hClauseDone]
                                  dsimp only [Process.bind]
                                  rw [ih msg st buf nextOff outV hStV hBufV (hKSh msg trivial)]
                                  constructor
                                  · exact fun hRest => .getElided hNeedFalse hRFind hREval hRest
                                  · intro hBare
                                    cases hBare with
                                    | getAbsorb hNeedT _ _ _ _ _ =>
                                        rw [hNeedFalse] at hNeedT; cases hNeedT
                                    | getElided _ hRead' hEvalR' hRest =>
                                        have hrEq := Option.some.inj (hRFind.symm.trans hRead')
                                        subst hrEq
                                        have hRRes := Process.done.inj (hREval.symm.trans hEvalR')
                                        cases hRRes
                                        exact hRest
              | own gkind hearers at_ gIns payload τ =>
                  cases gkind with
                  | coin law =>
                      cases hearers with
                      | nil =>
                          have hP := hPassV (.own (.coin law) [] at_ gIns payload τ) st (buf, (off, ())) trivial
                          dsimp only [Handler.run]
                          change (∃ record, Alone M source verifier
                            (Process.answerService serviceKey (IdealRO.asOracle M ro)
                              (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _))
                            record (.returned (outV, HList.nil))) ↔ _
                          rw [hP]
                          dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                          rw [alone_own_returned_iff]
                          constructor
                          · rintro ⟨v, hSrc, hRest⟩
                            exact .privateCoin hSrc ((ih v st buf off outV hStV hBufV (hKSh v trivial)).mp hRest)
                          · intro hBare
                            cases hBare with
                            | privateCoin hSrc hRest =>
                                exact ⟨_, hSrc, (ih _ st buf off outV hStV hBufV (hKSh _ trivial)).mpr hRest⟩
                      | cons h0 hs =>
                          obtain ⟨e, he, hSite, hTy, hCls, hTyped⟩ := hOpSh
                          have hD := hIdealDisc e he; rw [hCls] at hD
                          rcases hD with ⟨_, hHEq, sig, hLaw, _, hSigIns⟩ | hNil
                          · obtain ⟨hH0, hHs⟩ := List.cons.inj hHEq
                            subst h0; subst hs
                            have hGInsNil : gIns = [] := by
                              obtain ⟨s, hsLaw, hsIns, _⟩ := hTyped
                              rw [hLaw] at hsLaw
                              cases Option.some.inj hsLaw
                              exact hsIns.symm.trans hSigIns
                            subst hGInsNil
                            cases payload
                            have hEInAbs : ∃ p ∈ eventsAbs, p.1 = e := by
                              have hM : e ∈ eventsAbs.map Prod.fst := hFst.symm ▸ he
                              obtain ⟨p, hp, hEq⟩ := List.mem_map.mp hM
                              exact ⟨p, hp, hEq⟩
                            obtain ⟨pV, hpV, hpVEq⟩ := hEInAbs
                            have hSuf0 : ∀ k p, eventsAbs[k]? = some p → events[0 + k]? = some p.1 := by
                              intro k p hk; rw [Nat.zero_add, ← hFst, List.getElem?_map, hk]; rfl
                            obtain ⟨idxV, eV, encRef, hIdxV, hSiteV, hTyV, hClsV, hEncFind, hConAns⟩ :=
                              ideal_clauses_answer_coin M 0 eventsAbs hSuf0 hIV
                                law at_ τ st
                                ⟨pV, hpV, hpVEq.symm ▸ hSite, hpVEq.symm ▸ hTy, hpVEq.symm ▸ hCls⟩
                            have hToldSite : (⟨at_.path, drawToldKey events idxV⟩ : Occurrence).site =
                                ⟨eV.site.through, drawToldKey events (0 + idxV)⟩ := by
                              simpa using site_told_from_match hSiteV (k := drawToldKey events idxV)
                            have hLayDrop : ∀ coin : M.Val τ,
                                Clause.answer M fnTable rTable lClauses
                                  (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
                                  (buf, (off, ())) = .done ((), (buf, (off, ()))) := fun coin => by
                              have hd := streaming_layout_answer_told_drop M hNoCarry 0 events (fun _ h => h) hSL'
                                idxV eV hIdxV law ⟨at_.path, drawToldKey events idxV⟩
                                (hTyV.symm ▸ coin) hClsV hToldSite buf off
                              subst hTyV; exact hd
                            have hReqUnm : Clause.answer M fnTable rTable lClauses
                                (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                  [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                (buf, (off, ())) =
                                .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                  [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                  fun reply => .done (reply, (buf, (off, ()))) :=
                              clause_answer_unmatched_all M fnTable rTable
                                (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                  [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                (buf, (off, ())) lClauses
                                (streaming_layout_unmatched_closed M 0 events hSL'
                                  (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                    [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ) trivial).2
                            have hCoinEx : ∃ coin, ro st (drawLabel at_.site) τ = some coin ∧ M.Valid τ coin := by
                              obtain ⟨c, hRoC, hCV⟩ := hRo eV (List.mem_of_getElem? hIdxV) law [prover]
                                hClsV List.mem_cons_self st (drawLabel at_.site) hStV (drawLabel_bytes at_.site)
                              subst hTyV
                              exact ⟨c, hRoC, hCV⟩
                            obtain ⟨coin, hRoCoin, hCoinV⟩ := hCoinEx
                            obtain ⟨encH, hEncD, hEncV⟩ := encRef.eval_done M a (.cons coin .nil) ⟨hCoinV, trivial⟩
                            cases encH with
                            | cons encV en =>
                                cases en
                                let stepCont : M.Val τ → Process (RSig M)
                                    (Stop × HList M.Val (Stack.States [idealConV', layV']))
                                    (M.Val τ × HList M.Val (Stack.States [idealConV', layV'])) := fun c =>
                                  Process.map
                                    (fun (out : M.Val τ × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
                                      (out.1, HList.cons out.2.1 out.2.2))
                                    (Process.mapHalt
                                      (fun (stop : Stop × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
                                        (stop.1, HList.cons stop.2.1 stop.2.2))
                                      ((Process.mapHalt
                                        (fun (stop : Stop × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
                                          (stop.1, stop.2.1, stop.2.2))
                                        ((Stack.handler M fnTable rTable [layV']).answer
                                          (Process.map
                                            (fun out =>
                                              let values := HList.split [τ] (aloneOut M verifier out)
                                              (values.1.single, values.2.single))
                                            (Process.mapHalt (fun why => (why, st))
                                              (Process.map
                                                (fun enc => aloneIn M verifier (.cons c (.cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single) .nil)))
                                                (liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons c .nil))))))
                                          st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind
                                        fun out => Process.done (out.1.1, out.1.2, out.2)))
                                have hClauseStep : (Stack.handler M fnTable rTable [idealConV', layV']).clause
                                    (.own (.coin law) [prover] at_ [] .nil τ)
                                    (.cons st (.cons (buf, (off, ())) .nil)) =
                                    .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                        [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                      stepCont := by
                                  change ((((Layer.handler M fnTable rTable idealConV').over
                                      (Stack.handler M fnTable rTable [layV'])).clause
                                      (.own (.coin law) [prover] at_ [] .nil τ)
                                      (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                                  dsimp only [Layer.handler, Handler.over, idealConV']
                                  rw [hConAns]
                                  dsimp only [Handler.answer]
                                  rw [stack1_clause_pass M fnTable rTable layV' _ (buf, (off, ())) hReqUnm]
                                  dsimp only [Process.map, Process.mapHalt, Process.bind]
                                  congr 1; funext c
                                  have hDropLay : (Stack.handler M fnTable rTable [layV']).clause
                                      (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ c)
                                      (.cons (buf, (off, ())) .nil) =
                                      .done ((), .cons (buf, (off, ())) .nil) :=
                                    stack1_clause_done M fnTable rTable layV'
                                      (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ c)
                                      (buf, (off, ())) (buf, (off, ())) () (hLayDrop c)
                                  change Process.map _ (Process.mapHalt _ ((Process.mapHalt _
                                    ((Process.mapHalt _ ((Stack.handler M fnTable rTable [layV']).clause
                                      (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ c)
                                      (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind _)).bind _)) = _
                                  rw [hDropLay]; rfl
                                have hStepCoin : stepCont coin =
                                    .done (coin, HList.cons (idealPathPush M st (3 :: drawLabel at_.site) encV)
                                      (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)) :=
                                  stack2_lay_enc_step M fnTable rTable layV' st (buf, (off, ()))
                                    coin (3 :: drawLabel at_.site) encRef encV hEncD
                                dsimp only [Handler.run]
                                change (∃ record, Alone M source verifier
                                  (Process.answerService serviceKey (IdealRO.asOracle M ro)
                                    (((((Stack.handler M fnTable rTable [idealConV', layV']).clause _ _).bind _).mapHalt _).bind _))
                                  record (.returned (outV, HList.nil))) ↔ _
                                rw [hClauseStep]
                                dsimp only [Process.bind, Process.mapHalt]
                                rw [answerService_request_some M serviceKey (IdealRO.asOracle M ro)
                                  ((idealRO_asOracle_query M ro st (drawLabel at_.site) τ).trans hRoCoin),
                                  hStepCoin]
                                dsimp only [Process.bind]
                                have hSt'V : M.Valid (idealPathTy suiteUnitTy)
                                    (idealPathPush M st (3 :: drawLabel at_.site) encV) :=
                                  idealPathPush_valid M st (3 :: drawLabel at_.site) encV hStV
                                    (tag_bytes_cons 3 (by decide) (drawLabel at_.site) (drawLabel_bytes at_.site))
                                    hEncV.1
                                rw [ih coin (idealPathPush M st (3 :: drawLabel at_.site) encV)
                                  buf off outV hSt'V hBufV (hKSh coin trivial)]
                                constructor
                                · exact fun hRest => .draw hRoCoin hEncFind hEncD hRest
                                · intro hBare
                                  cases hBare with
                                  | draw hRo' hEnc' hEvalE' hRest =>
                                      have hcEq := Option.some.inj (hRoCoin.symm.trans hRo')
                                      subst hcEq
                                      have heEq := Option.some.inj (hEncFind.symm.trans hEnc')
                                      subst heEq
                                      have hERes := Process.done.inj (hEncD.symm.trans hEvalE')
                                      cases hERes
                                      exact hRest
                          · cases hNil
                  | request svc =>
                      have hP := hPassV (.own (.request svc) hearers at_ gIns payload τ) st (buf, (off, ())) trivial
                      dsimp only [Handler.run]
                      change (∃ record, Alone M source verifier
                        (Process.answerService serviceKey (IdealRO.asOracle M ro)
                          (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _))
                        record (.returned (outV, HList.nil))) ↔ _
                      rw [hP]
                      dsimp only [Process.bind, Process.mapHalt]
                      unfold Process.answerService
                      by_cases hs : svc = serviceKey
                      · rw [ite_eq_left hs]
                        cases hAns : IdealRO.asOracle M ro gIns payload τ with
                        | some v =>
                            dsimp only
                            rw [ih v st buf off outV hStV hBufV (hKSh v trivial)]
                            constructor
                            · exact fun hRest => .requestOracle hs hAns hRest
                            · intro hBare
                              cases hBare with
                              | requestOracle _ hAns' hRest =>
                                  have hvEq := Option.some.inj (hAns.symm.trans hAns')
                                  subst hvEq; exact hRest
                              | requestSource hNot _ _ =>
                                  rcases hNot with hNeS | hNone
                                  · exact absurd hs hNeS
                                  · rw [hAns] at hNone; cases hNone
                        | none =>
                            dsimp only
                            rw [alone_own_returned_iff]
                            constructor
                            · rintro ⟨v, hSrc, hRest⟩
                              exact .requestSource (.inr hAns) hSrc
                                ((ih v st buf off outV hStV hBufV (hKSh v trivial)).mp hRest)
                            · intro hBare
                              cases hBare with
                              | requestOracle _ hAns' _ => rw [hAns] at hAns'; cases hAns'
                              | requestSource _ hSrc hRest =>
                                  exact ⟨_, hSrc, (ih _ st buf off outV hStV hBufV (hKSh _ trivial)).mpr hRest⟩
                      · rw [ite_eq_right hs]
                        rw [alone_own_returned_iff]
                        constructor
                        · rintro ⟨v, hSrc, hRest⟩
                          exact .requestSource (.inl hs) hSrc
                            ((ih v st buf off outV hStV hBufV (hKSh v trivial)).mp hRest)
                        · intro hBare
                          cases hBare with
                          | requestOracle hEq _ _ => exact absurd hEq hs
                          | requestSource _ hSrc hRest =>
                              exact ⟨_, hSrc, (ih _ st buf off outV hStV hBufV (hKSh _ trivial)).mpr hRest⟩
              | «begin» at_ =>
                  have hP := hPassV (.begin at_) st (buf, (off, ())) trivial
                  dsimp only [Handler.run]
                  change (∃ record, Alone M source verifier
                    (Process.answerService serviceKey (IdealRO.asOracle M ro)
                      (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _))
                    record (.returned (outV, HList.nil))) ↔ _
                  rw [hP]
                  dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                  rw [alone_begin_returned_iff, ih 0 st buf off outV hStV hBufV (hKSh 0 trivial)]
                  exact ⟨fun hRest => .begin hRest, fun hBare => by cases hBare with | «begin» hRest => exact hRest⟩
              | settle at_ =>
                  have hP := hPassV (.settle at_) st (buf, (off, ())) trivial
                  dsimp only [Handler.run]
                  change (∃ record, Alone M source verifier
                    (Process.answerService serviceKey (IdealRO.asOracle M ro)
                      (((((Stack.handler M fnTable rTable [_, _]).clause _ _).bind _).mapHalt _).bind _))
                    record (.returned (outV, HList.nil))) ↔ _
                  rw [hP]
                  dsimp only [Process.bind, Process.mapHalt, Process.answerService]
                  rw [alone_settle_returned_iff, ih () st buf off outV hStV hBufV (hKSh () trivial)]
                  exact ⟨fun hRest => .settle hRest, fun hBare => by cases hBare with | settle hRest => exact hRest⟩

/-- Exact non-vacuous ideal random-oracle linkage theorem (`Statements.idealLink`):
for any non-carry streaming `deployIdeal` verifier without retry, starting from the canonical
initial collision-free transcript path `st0` (explicitly pinned to `resolveSessionBytes` and every
statement input via `idealInitialPath`), answering `.own (.request serviceKey)` with any partial
random oracle `ro : IdealRO M suiteUnitTy` that answers the protocol's verifier draws makes the
deployed ideal verifier return `outV` on a valid proof if and only if the bare verifier role
program `roleMeaning` satisfies `BareIdealReturn` from `(st0, proof, 0)`. -/
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
    ∃ (suiteUnitTy unitTy : V.Ty)
      (hSuiteFree : Ty.isLinear V suiteUnitTy = false)
      (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
      (st0 : M.Val (idealPathTy suiteUnitTy))
      (hTakes : Stack.Takes (dIdeal.stack verifier) = [.seq unitTy none]),
      findSuiteUnit a suite = some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩ ∧
      resolveSessionBytes enc a declaration sessionTag = .ok ⟨sessBytes, hSess⟩ ∧
      idealInitialPath M a suite suiteUnitTy prover verifier sessBytes ins = some st0 ∧
      ∀ (proof : List (M.Val unitTy)), M.Valid (.seq unitTy none) proof →
        ∀ (source : Source M) (ro : IdealRO M suiteUnitTy),
          ro.AnswersDraws M prover verifier (dIdeal.entry.shape.events [] id) →
          ∀ (outV : HList (RV M verifier) dIdeal.entry.outs),
            (∃ record givesV,
              Alone M source verifier
                (Process.answerService serviceKey (IdealRO.asOracle M ro)
                  (dIdeal.run M verifier ins
                    (cast (congrArg (HList M.Val) hTakes.symm) (.cons proof .nil))))
                record (.returned (outV, givesV))) ↔
            BareIdealReturn M a suite layout serviceKey prover verifier
              (dIdeal.entry.shape.eventsWithAbsorb prover verifier [] id false)
              source ro
              (roleMeaning M dIdeal.admitted.program dIdeal.callee verifier [] ins)
              st0 proof 0 outV := by
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration dIdeal hDep
  subst hEq
  have hConEq : Construction.derived w.suite w.sessionTag = .derived suite sessionTag :=
    w.hCon.symm.trans hCon
  have hSuiteEq : w.suite = suite := (Construction.derived.inj hConEq).1
  have hTagEq : w.sessionTag = sessionTag := (Construction.derived.inj hConEq).2
  have hLayEq : w.layout = layout := Option.some.inj (w.hLayOpt.symm.trans hLay)
  have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
    simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
  rw [w.hPV] at hRolesEq; cases hRolesEq
  cases buildLayoutLayers_ok_elim w.hLay with
  | compact wL _ =>
      have hne := wL.hNonEmpty
      dsimp only [DeployIdealWitness.layout] at hLayEq
      rw [hLayEq, hNoRec] at hne; cases hne
  | streaming wL hLPW hLVW =>
      have hEntryF : ((a.program.findProtocol declaration.entry).get
          (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
      have hInsF := insRV_cast_valid M hEntryF ins hIns
      obtain ⟨st0, hSt0Done, hInitF, hSt0V⟩ := idealInitialPath_eq_idealStart M a w.suite w.hSuiteFree
        w.prover w.verifier declaration.key w.sessBytes w.hSessBytes w.stmtV w.hSV
        (cast (congrArg (fun hdr => HList (RV M w.verifier) hdr.ins) hEntryF) ins) hInsF
      have hInit : idealInitialPath M a suite w.suiteUnitTy w.prover w.verifier w.sessBytes ins = some st0 := by
        have hCast : ∀ {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
            (xs : HList (RV M w.verifier) hdr₁.ins),
            idealInitialPath M a w.suite w.suiteUnitTy w.prover w.verifier w.sessBytes xs =
              idealInitialPath M a w.suite w.suiteUnitTy w.prover w.verifier w.sessBytes
                (cast (congrArg (fun hdr => HList (RV M w.verifier) hdr.ins) h) xs) := by
          intro _ _ h _; subst h; rfl
        rw [← hSuiteEq]
        erw [hCast hEntryF ins]
        exact hInitF
      let idealConV0 : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
        { line := .construction, state := idealPathTy w.suiteUnitTy,
          takes := [], gives := [], clauses := w.idealVClauses,
          again := restoreAgain (idealPathTy w.suiteUnitTy),
          start := idealStart w.hSuiteFree w.sessBytes w.hSessBytes w.stmtV,
          finish := emptyFinish (idealPathTy w.suiteUnitTy) }
      let layV0 : Layer V a.program.headers w.verifier w.foundPair.1.ins := wL.layV
      have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [idealConV0, layV0] := by
        dsimp only [DeployIdealWitness.toDeployed]
        rw [dite_eq_left rfl, hLVW]
        have hC : ∀ {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
            (ls : List (Layer V a.program.headers w.verifier hdr₂.ins)),
            (congrArg ProtocolHeader.ins h) ▸ ls = h ▸ ls := by intro _ _ h _; subst h; rfl
        exact hC hEntryF _
      have hTakes : Stack.Takes (w.toDeployed.stack w.verifier) = [.seq wL.unitTy none] := by
        rw [hStackVEq, stack_takes_cast_hdr hEntryF]; rfl
      have hGives : Stack.Gives (w.toDeployed.stack w.verifier) = [] := by
        rw [hStackVEq, stack_gives_cast_hdr hEntryF]; rfl
      refine ⟨w.suiteUnitTy, wL.unitTy, w.hSuiteFree, w.sessBytes, w.hSessBytes, st0, hTakes,
        hSuiteEq ▸ w.hUnit, hTagEq ▸ w.hSess, hInit, fun proof hProofV source ro hRo outV => ?_⟩
      rw [alone_map_nil_iff M hGives]
      have hT2 : Stack.Takes (hEntryF ▸ [idealConV0, layV0]) = [.seq wL.unitTy none] := by
        rw [stack_takes_cast_hdr hEntryF]; rfl
      have hG2 : Stack.Gives (hEntryF ▸ [idealConV0, layV0]) = [] := by
        rw [stack_gives_cast_hdr hEntryF]; rfl
      rw [ideal_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
        ((cast_heq _ _).trans (cast_heq _ _).symm)
        (hG₁ := hGives) (hG₂ := hG2) serviceKey (IdealRO.asOracle M ro)]
      have hBridge : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
          (callee : Member a.program.headers.protocols hdr)
          (ins' : HList (RV M w.verifier) hdr.ins)
          (hStart' : (idealStart w.hSuiteFree w.sessBytes w.hSessBytes w.stmtV).denote
            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
            (Env.positional (heldValues M w.verifier (cast (congrArg (fun h => HList (RV M w.verifier) h.ins) hE) ins'))) =
            .done (.cons st0 .nil))
          (hT' : Stack.Takes (hE ▸ [idealConV0, layV0]) = [.seq wL.unitTy none])
          (hG' : Stack.Gives (hE ▸ [idealConV0, layV0]) = [])
          (hRo' : ro.AnswersDraws M w.prover w.verifier (hdr.shape.events [] id))
          (outV' : HList (RV M w.verifier) hdr.outs),
          (∃ record, Alone M source w.verifier
            ((Process.answerService serviceKey (IdealRO.asOracle M ro)
              (runStack a M callee none w.verifier
                (hE ▸ [idealConV0, layV0])
                ins' (cast (congrArg (HList M.Val) hT'.symm) (.cons proof .nil)))).map
              (fun out => (out.1, cast (congrArg (HList M.Val) hG') out.2)))
            record (.returned (outV', .nil))) ↔
          BareIdealReturn M a suite layout serviceKey w.prover w.verifier
            (hdr.shape.eventsWithAbsorb w.prover w.verifier [] id false)
            source ro
            (roleMeaning M a.program callee w.verifier [] ins') st0 proof 0 outV' := by
        intro hdr hE callee ins' hStart' hT' hG' hRo' outV'
        subst hE
        dsimp only at hStart'
        simp only [cast_eq] at hStart'
        unfold runStack
        have hStV : Stack.start M (Defs.fnTable M a.program.defs)
            [idealConV0, layV0] ins' (.cons proof .nil) =
            .done (.cons st0 (.cons (proof, ((0 : Nat), ())) .nil)) := by
          change ((liftLocal id (idealConV0.start.denote
            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
            (Env.positional (heldValues M w.verifier ins')))).bind fun f₁ =>
              ((liftLocal id ((layoutVStart wL.unitTy).denote
                (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                (Env.positional (.cons proof (heldValues M w.verifier ins'))))).bind fun f₂ =>
                  (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                    HList.cons f₁.single others) = _
          rw [hStart', liftLocal_done]
          dsimp only [Process.bind, HList.single]
          rw [layoutVStart_denote]
          rfl
        have hProcEq :
            (Process.answerService serviceKey (IdealRO.asOracle M ro)
              ((Stack.start M (Defs.fnTable M a.program.defs) [idealConV0, layV0]
                ins' (cast (congrArg (HList M.Val) hT'.symm) (.cons proof .nil))).bind fun first =>
                (((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                    [idealConV0, layV0]).run (retryOf M none)
                    (roleMeaning M a.program callee w.verifier [] ins') first).mapHalt Prod.fst).bind
                  fun out => (Stack.finish M (Defs.fnTable M a.program.defs) [idealConV0, layV0] out.2).map
                    fun gives => (out.1, gives))).map
              (fun out => (out.1, cast (congrArg (HList M.Val) hG') out.2)) =
            Process.answerService serviceKey (IdealRO.asOracle M ro)
              ((((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                [idealConV0, layV0]).run (retryOf M none)
                (roleMeaning M a.program callee w.verifier [] ins')
                (.cons st0 (.cons (proof, ((0 : Nat), ())) .nil))).mapHalt Prod.fst).bind
                fun out => (Stack.finish M (Defs.fnTable M a.program.defs) [idealConV0, layV0] out.2).map
                  fun gives => (out.1, cast (by simp [Stack.Gives, idealConV0, layV0]) gives)) := by
          change (Process.answerService serviceKey (IdealRO.asOracle M ro)
            ((Stack.start M (Defs.fnTable M a.program.defs) [idealConV0, layV0]
              ins' (.cons proof .nil)).bind _)).map _ = _
          rw [hStV]
          dsimp only [Process.bind]
          rw [← answerService_map]
          congr 1
          simp [Process.map_bind, Process.map_map]
        rw [hProcEq]
        exact ideal_verifier_bare_iff M (suite := suite) (layout := layout) (serviceKey := serviceKey)
          hNoCarry w.hNe idealConV0 layV0
          rfl rfl rfl rfl rfl rfl (hSuiteEq ▸ w.hIV) ⟨wL.pClauses, hLayEq ▸ wL.hStr⟩
          source ro hRo'
          (roleMeaning M a.program callee w.verifier [] ins') st0 proof 0 outV'
          hSt0V hProofV (roleMeaning_matchesShape M a.program callee w.verifier [] ins')
      exact hBridge _ hEntryF w.toDeployed.callee ins hSt0Done hT2 hG2 hRo outV

end IdealLink

/-! ## Collision-free ideal transcript step injectivity -/

section IdealPathInjectivity

variable {V : Vocabulary} (M : Model V)

/-- Message absorption steps on the pure ideal transcript path are unconditionally injective
under `Deployed.SuiteLawful` (encoding injectivity + site-label injectivity + collision-free path append). -/
theorem idealPath_msgStep_injective {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawful M)
    {unitTy τ : V.Ty}
    {encRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
    (hFind : findSuiteEncode d.admitted suite unitTy τ = some encRef)
    {st₁ st₂ : M.Val (idealPathTy unitTy)} {s₁ s₂ : Site}
    {v₁ v₂ : M.Val τ} {enc₁ enc₂ : List (M.Val unitTy)}
    (hV₁ : M.Valid τ v₁) (hV₂ : M.Valid τ v₂)
    (hE₁ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v₁ .nil) = .done (.cons enc₁ .nil))
    (hE₂ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v₂ .nil) = .done (.cons enc₂ .nil))
    (hPath : idealPathPush M st₁ (2 :: msgLabel s₁) enc₁ =
      idealPathPush M st₂ (2 :: msgLabel s₂) enc₂) :
    st₁ = st₂ ∧ s₁ = s₂ ∧ v₁ = v₂ := by
  obtain ⟨hSt, hLbl, hEnc⟩ := idealPathPush_injective M hPath
  have hSite : s₁ = s₂ := msgLabel_injective (List.cons.inj hLbl).2
  subst hEnc
  have hVal := suiteLawful_encode_injective M hCon hSuite hFind hV₁ hV₂ hE₁ hE₂
  exact ⟨hSt, hSite, hVal⟩

/-- Draw absorption steps on the pure ideal transcript path are unconditionally injective
under `Deployed.SuiteLawful`. -/
theorem idealPath_drawStep_injective {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawful M)
    {unitTy τ : V.Ty}
    {encRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
    (hFind : findSuiteEncode d.admitted suite unitTy τ = some encRef)
    {st₁ st₂ : M.Val (idealPathTy unitTy)} {s₁ s₂ : Site}
    {c₁ c₂ : M.Val τ} {enc₁ enc₂ : List (M.Val unitTy)}
    (hV₁ : M.Valid τ c₁) (hV₂ : M.Valid τ c₂)
    (hE₁ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons c₁ .nil) = .done (.cons enc₁ .nil))
    (hE₂ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons c₂ .nil) = .done (.cons enc₂ .nil))
    (hPath : idealPathPush M st₁ (3 :: drawLabel s₁) enc₁ =
      idealPathPush M st₂ (3 :: drawLabel s₂) enc₂) :
    st₁ = st₂ ∧ s₁ = s₂ ∧ c₁ = c₂ := by
  obtain ⟨hSt, hLbl, hEnc⟩ := idealPathPush_injective M hPath
  have hSite : s₁ = s₂ := drawLabel_injective (List.cons.inj hLbl).2
  subst hEnc
  have hVal := suiteLawful_encode_injective M hCon hSuite hFind hV₁ hV₂ hE₁ hE₂
  exact ⟨hSt, hSite, hVal⟩

/-- A message absorption step (`tag 2`) can never collide with a draw absorption step (`tag 3`). -/
theorem idealPath_msg_ne_draw {unitTy : V.Ty}
    (st₁ st₂ : M.Val (idealPathTy unitTy)) (s₁ s₂ : Site)
    (enc₁ enc₂ : List (M.Val unitTy)) :
    idealPathPush M st₁ (2 :: msgLabel s₁) enc₁ ≠
      idealPathPush M st₂ (3 :: drawLabel s₂) enc₂ := by
  intro h
  obtain ⟨_, hLbl, _⟩ := idealPathPush_injective M h
  have hTag := (List.cons.inj hLbl).1
  cases hTag

end IdealPathInjectivity

/-! ## Non-malleable canonical compact proof parsing (`compact_parse_written`) -/

section CompactCanonical

variable {V : Vocabulary} (M : Model V)

/-- Witness that each wire item parsed by `readers` corresponds to a valid value whose canonical
`LayoutSlot.write` output is the corresponding chunk in `chunks`. -/
inductive CanonicalChunks (d : Deployed V) (layout : Layout) {unitTy : V.Ty} :
    List ((τ : V.Ty) × SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]) →
    List (List (M.Val unitTy)) → Prop where
  | nil : CanonicalChunks d layout [] []
  | cons {τ : V.Ty} {rRef : SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
      {rest : List ((τ : V.Ty) × SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat])}
      {wRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
      {v : M.Val τ} {chunk : List (M.Val unitTy)} {restChunks : List (List (M.Val unitTy))}
      (hW : findLayoutWrite d.admitted layout.module unitTy τ = some wRef)
      (hV : M.Valid τ v)
      (hEval : wRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil) = .done (.cons chunk .nil))
      (hRest : CanonicalChunks d layout rest restChunks) :
      CanonicalChunks d layout (⟨τ, rRef⟩ :: rest) (chunk :: restChunks)

private theorem list_drop_eq_of_take_append {α : Type} {buf chunk tail : List α} {off : Nat}
    (hOff : off ≤ buf.length) (hEq : buf = buf.take off ++ chunk ++ tail) :
    buf.drop off = chunk ++ tail := by
  have hLen : (buf.take off).length = off := List.length_take_of_le hOff
  have h1 : buf.drop off = (buf.take off ++ (chunk ++ tail)).drop off := by
    rw [← List.append_assoc, ← hEq]
  rw [h1, List.drop_append, hLen, Nat.sub_self,
      List.drop_of_length_le (by rw [hLen]; exact Nat.le_refl _)]
  rfl

/-- Every proof tail accepted by `buildCompactParse` under a canonical `LayoutLawful` layout is
the exact concatenation of canonical `LayoutSlot.write` outputs (non-malleability, zero trailing
garbage). -/
theorem buildCompactParse_written {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (wireTys : List V.Ty) :
    ∀ {Γ : Ctx V.Ty} (fresh : Nat) (hfresh : FreshFrom Γ fresh) (env : Env M.Val Γ)
      (bufVar : Var Γ (.seq unitTy none)) (offVar : Var Γ .nat)
      (parsedAcc : List V.Ty) (accVars : HList (Var Γ) parsedAcc)
      (readers : List ((τ : V.Ty) × SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]))
      (hMatch : parsedAcc ++ readers.map Sigma.fst = wireTys)
      (out : HList M.Val [.tuple (tysOfList wireTys)]),
      (∀ u ∈ env.get bufVar, M.Valid unitTy u) →
      env.get offVar ≤ (env.get bufVar).length →
      (∀ item ∈ readers,
        findLayoutRead d.admitted layout.module unitTy item.1 = some item.2 ∧
        ∃ wRef, findLayoutWrite d.admitted layout.module unitTy item.1 = some wRef) →
      (buildCompactParse unitTy hfree guardKey wireTys fresh hfresh bufVar offVar
          parsedAcc accVars readers hMatch).denote
        (localSem M d.admitted.program.headers.fns (Defs.fnTable M d.admitted.program.defs)) [] env =
        .done out →
      ∃ chunks, CanonicalChunks M d layout readers chunks ∧
        (env.get bufVar).drop (env.get offVar) = chunks.flatten
  | Γ, fresh, hfresh, env, bufVar, offVar, parsedAcc, accVars, [], hMatch, out, _, hOff, _, hDone => by
      unfold buildCompactParse at hDone
      rw [letOp1_local_owned_denote] at hDone
      simp only [Env.all] at hDone
      rw [ownedOp_seqLength] at hDone
      simp only [Process.bind, HList.single] at hDone
      rw [letOp1_local_owned_denote] at hDone
      simp only [Env.all] at hDone
      rw [env_get_insert_reindex env hfresh, env_get_insert_self, ownedOp_natEqual] at hDone
      simp only [Process.bind, HList.single] at hDone
      erw [Term.denote_guard, env_get_insert_self, localSem_holds, localSem_stop] at hDone
      cases hBeq : Nat.beq (env.get offVar) (env.get bufVar).length with
      | false => rw [hBeq] at hDone; cases hDone
      | true =>
          have hLenEq : env.get offVar = (env.get bufVar).length := Nat.eq_of_beq_eq_true hBeq
          refine ⟨[], .nil, ?_⟩
          rw [hLenEq, List.drop_length]; rfl
  | Γ, fresh, hfresh, env, bufVar, offVar, parsedAcc, accVars, ⟨τ, readRef⟩ :: rest, hMatch, out,
      hBuf, hOff, hReaders, hDone => by
      obtain ⟨hRFind, wRef, hWFind⟩ := hReaders ⟨τ, readRef⟩ List.mem_cons_self
      unfold buildCompactParse at hDone
      erw [letOp2_denote, localSem_op] at hDone
      simp only [Env.all] at hDone
      change (readRef.eval M (Defs.fnTable M d.admitted.program.defs)
          (.cons (env.get bufVar) (.cons (env.get offVar) .nil))).bind _ = .done out at hDone
      cases hREval : readRef.eval M (Defs.fnTable M d.admitted.program.defs)
          (.cons (env.get bufVar) (.cons (env.get offVar) .nil)) with
      | halt why => rw [hREval] at hDone; cases hDone
      | call op _ => cases op
      | done res =>
          rw [hREval] at hDone
          cases res with
          | cons v r1 =>
              cases r1 with
              | cons nextOff r2 =>
                  cases r2
                  dsimp only [Process.bind] at hDone
                  obtain ⟨hVal, _, hNextLe, chunk, hWEval, hBufSplit⟩ :=
                    layoutLawful_written M hLayOpt hLayLaw hWFind hRFind hBuf hOff hREval
                  have hBuf' : ((env.insert fresh v).insert (fresh + 1) nextOff).get
                      (bufVar.reindex ((hfresh.within τ).trans ((hfresh.insert τ).within .nat))) =
                      env.get bufVar :=
                    env_get_insert2_reindex env hfresh _ _ _ bufVar
                  have hOff' : ((env.insert fresh v).insert (fresh + 1) nextOff).get
                      (freshVar (Γ.insert fresh τ) (fresh + 1) .nat) = nextOff :=
                    env_get_insert_self _ _ _
                  obtain ⟨restChunks, hCanonRest, hDropNext⟩ :=
                    buildCompactParse_written hLayOpt hLayLaw unitTy hfree guardKey wireTys
                      (fresh + 2) ((hfresh.insert τ).insert .nat)
                      ((env.insert fresh v).insert (fresh + 1) nextOff)
                      (bufVar.reindex ((hfresh.within τ).trans ((hfresh.insert τ).within .nat)))
                      (freshVar (Γ.insert fresh τ) (fresh + 1) .nat)
                      (parsedAcc ++ [τ])
                      (HList.append (accVars.reindex ((hfresh.within τ).trans ((hfresh.insert τ).within .nat)))
                        (.cons ((freshVar Γ fresh τ).reindex ((hfresh.insert τ).within .nat)) .nil))
                      rest (by simpa [List.append_assoc] using hMatch) out
                      (hBuf' ▸ hBuf) (by rw [hBuf', hOff']; exact hNextLe)
                      (fun item hm => hReaders item (List.mem_cons_of_mem _ hm)) hDone
                  rw [hBuf', hOff'] at hDropNext
                  refine ⟨chunk :: restChunks, .cons hWFind hVal hWEval hCanonRest, ?_⟩
                  have hDropCur := list_drop_eq_of_take_append hOff hBufSplit
                  rw [hDropCur, hDropNext]; rfl

/-- Corollary for `compactLayoutVStart`: every proof buffer `proof` accepted by a compact verifier's
`start` term equals the exact canonical concatenation of `LayoutSlot.write` chunks of its parsed
wire items (zero malleability, zero trailing garbage). -/
theorem compactLayoutVStart_written {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    {r : Role} {ins : List (LTy V)}
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (stmtItems : List ((τ : V.Ty) × Var (Ctx.positional (.seq unitTy none :: held r ins)) τ))
    (readers : List ((τ : V.Ty) × SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]))
    (proof : List (M.Val unitTy)) (hProof : ∀ u ∈ proof, M.Valid unitTy u)
    (heldVals : HList M.Val (held r ins))
    (hReaders : ∀ item ∈ readers,
      findLayoutRead d.admitted layout.module unitTy item.1 = some item.2 ∧
      ∃ wRef, findLayoutWrite d.admitted layout.module unitTy item.1 = some wRef)
    {out : HList M.Val [.tuple (tysOfList (stmtItems.map Sigma.fst ++ readers.map Sigma.fst))]}
    (hDone : (compactLayoutVStart unitTy hfree guardKey stmtItems readers).denote
      (localSem M d.admitted.program.headers.fns (Defs.fnTable M d.admitted.program.defs)) []
      (Env.positional (.cons proof heldVals)) = .done out) :
    ∃ chunks, CanonicalChunks M d layout readers chunks ∧
      proof = chunks.flatten := by
  unfold compactLayoutVStart at hDone
  erw [letOp1_denote, localSem_op_literal] at hDone
  simp only [Process.bind, HList.single] at hDone
  change (buildCompactParse unitTy hfree guardKey
    (stmtItems.map Sigma.fst ++ readers.map Sigma.fst)
    ((.seq unitTy none :: held r ins).length + 1)
    ((positional_freshFrom (.seq unitTy none :: held r ins)).insert .nat)
    ((posVar (.seq unitTy none :: held r ins) 0 rfl).reindex
      ((positional_freshFrom (.seq unitTy none :: held r ins)).within .nat))
    (freshVar (Ctx.positional (.seq unitTy none :: held r ins))
      (.seq unitTy none :: held r ins).length .nat)
    (stmtItems.map Sigma.fst) _ readers rfl).denote
    (localSem M d.admitted.program.headers.fns (Defs.fnTable M d.admitted.program.defs)) []
    ((Env.positional (.cons proof heldVals)).insert (.seq unitTy none :: held r ins).length (0 : Nat)) =
    .done out at hDone
  have hBufEq : ((Env.positional (.cons (a := .seq unitTy none) proof heldVals)).insert
        (.seq unitTy none :: held r ins).length (0 : Nat)).get
      ((posVar (.seq unitTy none :: held r ins) 0 rfl).reindex
        ((positional_freshFrom (.seq unitTy none :: held r ins)).within .nat)) = proof := by
    rw [env_get_insert_reindex _ (positional_freshFrom _)]
    exact env_get_positional (.cons (a := .seq unitTy none) proof heldVals) 0 rfl
  have hOffEq : ((Env.positional (.cons (a := .seq unitTy none) proof heldVals)).insert
        (.seq unitTy none :: held r ins).length (0 : Nat)).get
      (freshVar (Ctx.positional (.seq unitTy none :: held r ins))
        (.seq unitTy none :: held r ins).length .nat) = 0 :=
    env_get_insert_self _ _ _
  obtain ⟨chunks, hCanon, hDrop⟩ :=
    buildCompactParse_written M hLayOpt hLayLaw unitTy hfree guardKey
      (stmtItems.map Sigma.fst ++ readers.map Sigma.fst)
      ((.seq unitTy none :: held r ins).length + 1)
      ((positional_freshFrom (.seq unitTy none :: held r ins)).insert .nat)
      ((Env.positional (.cons (a := .seq unitTy none) proof heldVals)).insert
        (.seq unitTy none :: held r ins).length (0 : Nat))
      ((posVar (.seq unitTy none :: held r ins) 0 rfl).reindex
        ((positional_freshFrom (.seq unitTy none :: held r ins)).within .nat))
      (freshVar (Ctx.positional (.seq unitTy none :: held r ins))
        (.seq unitTy none :: held r ins).length .nat)
      (stmtItems.map Sigma.fst) _ readers rfl out
      (by rw [hBufEq]; exact hProof) (by rw [hOffEq]; exact Nat.zero_le _) hReaders hDone
  rw [hBufEq, hOffEq, List.drop_zero] at hDrop
  exact ⟨chunks, hCanon, hDrop⟩

end CompactCanonical

end Zkc.Core
