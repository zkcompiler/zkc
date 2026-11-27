module

public import Zkc.Core.Scheme.Completeness

@[expose] public section

/-!
Ideal random-oracle verifier linkage (`deployIdeal_link`), collision-free ideal transcript path
step injectivity (`idealPath_msgStep_injective`, `idealPath_drawStep_injective`,
`idealPath_msg_ne_draw`), and non-malleable canonical compact proof parsing
(`buildCompactParse_written`, `compactLayoutVStart_written`).
-/

namespace Zkc.Core

open LayerBuild

/-! ## Section 1: Pure collision-free ideal random-oracle linkage (`deployIdeal_link`) -/

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

/-- Whether the prover→verifier flow `(site, kind, τ)` is marked for transcript absorption in
`eventsAbs` (false for trailing messages elided under Chiesa-Orru Construction 4.3). -/
def needIdealAbsorb (prover verifier : Role) (eventsAbs : List (ShapeEvent V × Bool))
    (site : Site) (kind : FlowKind) (τ : V.Ty) : Bool :=
  eventsAbs.any fun p =>
    p.2 && decide (p.1.site = site) && decide (p.1.τ = τ) &&
      match p.1.cls with
      | .flow k g gs => decide (k = kind ∧ g = prover ∧ verifier ∈ gs)
      | _ => false

/-- Direct pure-path ideal-RO verifier state machine (completely independent of `Layer`/`Stack`/
`Handler`/`Clause` and of concrete `SuiteSlot.start`/`SuiteSlot.absorb`), parameterized directly
by a total random oracle `ro` on `(idealPath, drawLabel, ty)` for a non-carry streaming verifier. -/
def evalIdealVerifierLoop {A : Type} (a : Admitted V) (suite : ModuleRef) (layout : Layout)
    {suiteUnitTy unitTy : V.Ty}
    (serviceKey : Key) (prover verifier : Role) (finishGuard : Key)
    (eventsAbs : List (ShapeEvent V × Bool))
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    (ro : M.Val (idealPathTy suiteUnitTy) → List Nat → (τ : V.Ty) → M.Val τ) :
    Program M A → M.Val (idealPathTy suiteUnitTy) → List (M.Val unitTy) → Nat →
    Process (RSig M) Stop (A × HList M.Val [])
  | .done outV, _, buf, off =>
      bif Nat.beq off buf.length then .done (outV, .nil)
      else .halt (.declared .reject ⟨[], finishGuard⟩)
  | .halt why, _, _, _ => .halt why
  | .call op k, st, buf, off =>
      match op with
      | .get knd giver at_ τ =>
          if giver = prover then
            if needIdealAbsorb prover verifier eventsAbs at_.site knd τ then
              match findLayoutRead a layout.module unitTy τ, findSuiteEncode a suite suiteUnitTy τ with
              | some rRef, some encRef =>
                  (liftLocal id (rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)))).bind
                    fun res => match res with
                    | .cons msg (.cons nextOff .nil) =>
                        (liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil))).bind
                          fun enc =>
                            evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                              eventsAbs oracle ro (k msg)
                              (idealPathPush M st (2 :: msgLabel at_.site) enc.single) buf nextOff
              | _, _ => .call (.get knd giver at_ τ) fun v =>
                  evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                    eventsAbs oracle ro (k v) st buf off
            else
              match findLayoutRead a layout.module unitTy τ with
              | some rRef =>
                  (liftLocal id (rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)))).bind
                    fun res => match res with
                    | .cons msg (.cons nextOff .nil) =>
                        evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                          eventsAbs oracle ro (k msg) st buf nextOff
              | none => .call (.get knd giver at_ τ) fun v =>
                  evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                    eventsAbs oracle ro (k v) st buf off
          else
            .call (.get knd giver at_ τ) fun v =>
              evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                eventsAbs oracle ro (k v) st buf off
      | .own (.coin law) (h0 :: hs) at_ [] .nil τ =>
          match findSuiteEncode a suite suiteUnitTy τ with
          | some encRef =>
              let coin := ro st (drawLabel at_.site) τ
              (liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil))).bind
                fun enc =>
                  evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                    eventsAbs oracle ro (k coin)
                    (idealPathPush M st (3 :: drawLabel at_.site) enc.single) buf off
          | none => .call (.own (.coin law) (h0 :: hs) at_ [] .nil τ) fun v =>
              evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                eventsAbs oracle ro (k v) st buf off
      | .own (.request svc) hearers at_ ins payload τ =>
          if svc = serviceKey then
            match oracle ins payload τ with
            | some v =>
                evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                  eventsAbs oracle ro (k v) st buf off
            | none => .call (.own (.request svc) hearers at_ ins payload τ) fun v =>
                evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
                  eventsAbs oracle ro (k v) st buf off
          else .call (.own (.request svc) hearers at_ ins payload τ) fun v =>
            evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
              eventsAbs oracle ro (k v) st buf off
      | op' => .call op' fun v =>
          evalIdealVerifierLoop a suite layout serviceKey prover verifier finishGuard
            eventsAbs oracle ro (k v) st buf off

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
          ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
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
      ⟨e', he', hSite, hTy, gs', hVin, hECls⟩ => by
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
                          · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                            refine ⟨encR, hE, ?_⟩
                            unfold Clause.answer
                            exact (dite_eq_right hMatch).trans hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
                    rcases List.mem_cons.mp he' with hEqP | hmem
                    · cases hEqP
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
              · split at h
                · rename_i hOut; cases h
                  rcases List.mem_cons.mp he' with hEqP | hmem
                  · cases hEqP; rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
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
                                  rcases List.mem_cons.mp he' with hEqP | hmem
                                  · cases hEqP; rw [hCls] at hECls; cases hECls
                                  · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                                    refine ⟨encR, hE, ?_⟩
                                    unfold Clause.answer
                                    rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                    exact hAns
                        · cases h
                  · split at h
                    · cases h
                      rcases List.mem_cons.mp he' with hEqP | hmem
                      · cases hEqP; rw [hCls] at hECls; cases hECls
                      · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with hEqP | hmem
                    · cases hEqP; rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
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
          (∃ gs, verifier ∈ gs ∧ e.cls = .flow kind prover gs) → b = false) →
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
                            ⟨getters₀, hPV.2, hKind ▸ hPV.1 ▸ hCls⟩
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
      ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (τ : V.Ty)
        (st : M.Val (idealPathTy unitTy)),
        (∃ p ∈ es, p.1.site = at_.site ∧ p.1.τ = τ ∧ prover ∈ hearers ∧
          p.1.cls = .given (.coin law) verifier hearers) →
        ∃ (idxV : Nat) (eV : ShapeEvent V)
          (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]),
          events[idxV]? = some eV ∧ eV.site = at_.site ∧ eV.τ = τ ∧
          eV.cls = .given (.coin law) verifier hearers ∧
          findSuiteEncode a suite unitTy τ = some encRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.own (.coin law) hearers at_ [] .nil τ) st =
            .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                [idealQueryTy unitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ) fun coin =>
              .call (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin) fun _ =>
                (((liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil))).map fun enc =>
                  aloneIn M verifier (.cons coin (.cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single) .nil))).mapHalt
                    fun why => (why, st)).map fun out =>
                  let values := HList.split [τ] (aloneOut M verifier out)
                  (values.1.single, values.2.single)
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, hSuf, cV, h, law, hearers, at_, τ, st,
      ⟨p', hp', hSite, hTy, hPin, hECls⟩ => by
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
            law hearers at_ τ st hIn
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
                            ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                          refine ⟨idxV, eV, encR, h1, h2, h3, h4, h5, ?_⟩
                          unfold Clause.answer; rw [dite_eq_right (fun hm => by cases hm.2.1)]; exact hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
              · split at h
                · cases h
                  rcases List.mem_cons.mp hp' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
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
                                        have hM : (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.site =
                                            (ROp.occurrence M (.own (.coin law) hearers at_ [] .nil τ)).site ∧
                                            some (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.part =
                                            ROp.part M (.own (.coin law) hearers at_ [] .nil τ) ∧
                                            (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.takes =
                                            ROp.takes M (.own (.coin law) hearers at_ [] .nil τ) ∧
                                            (idealDeriveClause hfree verifier prover at_.site (.own (.coin law) hearers)
                                            [] serviceKey (idealReqKey events idx) (drawToldKey events idx)
                                            (drawLabel at_.site) (drawLabel_bytes at_.site) encRef).site.gives =
                                            ROp.gives M (.own (.coin law) hearers at_ [] .nil τ) := ⟨rfl, rfl, rfl, rfl⟩
                                        rw [dite_eq_left hM]
                                        change (((idealDeriveClause hfree verifier prover at_.site (.own (.coin law) hearers)
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
                                        ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                                      refine ⟨idxV, eV, encR, h1, h2, h3, h4, h5, ?_⟩
                                      unfold Clause.answer
                                      exact (dite_eq_right hMatch).trans hAns
                        · cases h
                  · split at h
                    · rename_i hNil
                      cases h
                      rcases List.mem_cons.mp hp' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; subst hNil; cases hPin
                      · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
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
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        refine ⟨rR, h1, ?_⟩
                        unfold Clause.answer
                        rw [dite_eq_right (fun hm => by cases hm.2.1)]
                        exact hAns
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
    (hNoCarry : layout.carry = []) {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
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
          ∀ buf off,
            Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
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
              rw [ite_eq_left ⟨rfl, hPin⟩] at h
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
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
    (ro : M.Val (idealPathTy suiteUnitTy) → List Nat → (τ : V.Ty) → M.Val τ)
    (hOracleRo : ∀ st lbl τ,
      oracle [idealQueryTy suiteUnitTy] (.cons (st, (lbl, ())) .nil) τ = some (ro st lbl τ)) :
    ∀ {A : Type} (p : Program M A) (st : M.Val (idealPathTy suiteUnitTy))
      (buf : List (M.Val unitTy)) (off : Nat),
      p.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (shape.events [] id))
        (fun _ => True) (fun _ => True) →
      Process.answerService serviceKey oracle
        ((((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
          [idealConV, layV]).run (retryOf M none) p
            (.cons (hConSt.symm ▸ st) (.cons (hLaySt.symm ▸ (buf, (off, ())))
              (.nil : HList M.Val (Stack.States ([] : List (Layer V a.program.headers verifier entryIns))))))).mapHalt Prod.fst).bind
          fun out => (Stack.finish M (Defs.fnTable M a.program.defs) [idealConV, layV] out.2).map
            fun gives => (out.1, cast (by simp [Stack.Gives, hConGives, hLayGives]) gives)) =
        evalIdealVerifierLoop M a suite layout serviceKey prover verifier
          (finishGuardKey (shape.events [] id))
          (shape.eventsWithAbsorb prover verifier [] id false)
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
          let events := shape.events [] id
          let eventsAbs := shape.eventsWithAbsorb prover verifier [] id false
          have hFst : eventsAbs.map Prod.fst = events :=
            eventsWithAbsorb_fst prover verifier [] id false shape
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
            have hGo : ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)) {cV'},
                buildIdealVerifierClauses.go a suite suiteUnitTy hSuiteFree serviceKey
                  prover verifier declKey events idx es = .ok cV' →
                ∀ p ∈ es, match p.1.cls with
                  | .flow _ giver getters =>
                      (giver = prover ∧ verifier ∈ getters) ∨
                      (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                  | .given (.coin law) owner hearers =>
                      (owner = verifier ∧ prover ∈ hearers ∧
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
                        exact List.any_eq_true.mpr ⟨(e, true), hNeed, by simp [hSite, hTy, hCls, hVin]⟩
                      obtain ⟨encRef, hEncFind, hConAns⟩ :=
                        ideal_clauses_answer_flow_abs M 0 eventsAbs hIV kind at_ τ st
                          ⟨e, hNeed, hSite, hTy, gs', hVin, hCls⟩
                      obtain ⟨rRef, hRFind, hLayAns⟩ :=
                        streaming_layout_answer_verifier_flow_full M 0 events hSL' kind ⟨at_.path, at_.site.key⟩ τ buf off
                          ⟨e, he, hSite, hTy, gs', hVin, hCls⟩
                      conv =>
                        rhs
                        rw [evalIdealVerifierLoop]
                        dsimp only
                        rw [ite_eq_left rfl, hNeedTrue]
                        simp only [↓reduceIte]
                        rw [hRFind, hEncFind]
                      dsimp only [Handler.run]
                      change Process.answerService serviceKey oracle
                        (((((Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                          (.cons st (.cons (buf, (off, ())) .nil))).bind _).mapHalt _).bind _) = _
                      have hClauseEq : (Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                          (.cons st (.cons (buf, (off, ())) .nil)) =
                          (liftLocal (fun why => (why, .cons st (.cons (buf, (off, ())) .nil)))
                            (rRef.eval M fnTable (.cons buf (.cons off .nil)))).bind fun res =>
                            match res with
                            | .cons msg (.cons nextOff .nil) =>
                                (liftLocal (fun why => (why, .cons st (.cons (buf, (nextOff, ())) .nil)))
                                  (encRef.eval M fnTable (.cons msg .nil))).map fun enc =>
                                    (msg, .cons (idealPathPush M st (2 :: msgLabel at_.site) enc.single)
                                      (.cons (buf, (nextOff, ())) .nil)) := by
                        change ((((Layer.handler M fnTable rTable idealConV').over
                            (Stack.handler M fnTable rTable [layV'])).clause (.get kind giver at_ τ)
                            (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                        dsimp only [Layer.handler, Handler.over, idealConV']
                        rw [hConAns]
                        dsimp only [Handler.answer]
                        rw [hLay1Step, hLayAns]
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
                                                ((HList.split [τ] (aloneOut M verifier out)).1.single,
                                                  (HList.split [τ] (aloneOut M verifier out)).2.single))
                                              (Process.mapHalt (fun why => (why, st))
                                                (Process.map
                                                  (fun enc => aloneIn M verifier (.cons msg (.cons (idealPathPush M st (2 :: msgLabel at_.site) enc.single) .nil)))
                                                  (liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons msg .nil))))))
                                            st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).bind
                                          fun out => Process.done (out.1.1, out.1.2, out.2))) =
                                      Process.map
                                        (fun enc => (msg, HList.cons (idealPathPush M st (2 :: msgLabel at_.site) enc.single)
                                          (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                        (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                          (encRef.eval M fnTable (.cons msg .nil)))
                                    cases encRef.eval M fnTable (.cons msg .nil) with
                                    | halt why => rfl
                                    | call op _ => cases op
                                    | done enc =>
                                        cases enc with
                                        | cons encV en =>
                                            cases en
                                            change Process.done
                                              ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                                                (.cons msg (.cons (idealPathPush M st (2 :: msgLabel at_.site) encV) .nil))))).1.single,
                                                HList.cons ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                                                  (.cons msg (.cons (idealPathPush M st (2 :: msgLabel at_.site) encV) .nil))))).2.single)
                                                  (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)) =
                                              Process.done (msg, HList.cons (idealPathPush M st (2 :: msgLabel at_.site) encV)
                                                (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))
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
                                      (((Process.map
                                          (fun enc => (msg, HList.cons (idealPathPush M st (2 :: msgLabel at_.site) enc.single)
                                            (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                          (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil)))
                                            (encRef.eval M fnTable (.cons msg .nil)))).bind _))).bind _) =
                                    (liftLocal id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
                                      evalIdealVerifierLoop M a suite layout serviceKey giver verifier
                                        (finishGuardKey events) eventsAbs oracle ro (k msg)
                                        (idealPathPush M st (2 :: msgLabel at_.site) enc.single) buf nextOff
                                  cases encRef.eval M fnTable (.cons msg .nil) with
                                  | halt why => rfl
                                  | call op _ => cases op
                                  | done enc =>
                                      cases enc with
                                      | cons encV en =>
                                          cases en
                                          exact ih msg (idealPathPush M st (2 :: msgLabel at_.site) encV)
                                            buf nextOff (hKSh msg trivial)
                  | false =>
                      -- Trailing message elided: construction passes through, layout reads without changing `st`
                      have hNoAbs : ∀ e' b', (e', b') ∈ eventsAbs → e'.site = at_.site →
                          e'.τ = τ → (∃ gs, verifier ∈ gs ∧ e'.cls = .flow kind giver gs) →
                          b' = false := by
                        intro e' b' hIn hS hT ⟨gs, hVg, hC⟩
                        exact eventsWithAbsorb_flow_consistent giver verifier [] id false shape
                          hIn hNeed (hS.trans hSite.symm) (hT.trans hTy.symm) hC hVg hCls hVin
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
                              ⟨gs₀, hCond.2.2.2, hCond.2.1 ▸ hCond.2.2.1 ▸ hC'⟩
                            rw [hbFalse] at hCond; cases hCond.1.1.1
                        | given _ _ _ => rw [hC'] at hCond; cases hCond.2
                      have hConPass : Clause.answer M fnTable rTable cClauses (.get kind giver at_ τ) st =
                          .call (.get kind giver at_ τ) fun reply => .done (reply, st) :=
                        clause_answer_unmatched_all M fnTable rTable _ st cClauses
                          (ideal_clauses_unmatched_elided_flow M 0 eventsAbs hIV kind at_ τ hNoAbs)
                      obtain ⟨rRef, hRFind, hLayAns⟩ :=
                        streaming_layout_answer_verifier_flow_full M 0 events hSL' kind at_ τ buf off
                          ⟨e, he, hSite, hTy, gs', hVin, hCls⟩
                      conv =>
                        rhs
                        rw [evalIdealVerifierLoop]
                        dsimp only
                        rw [ite_eq_left rfl, hNeedFalse]
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        rw [hRFind]
                      dsimp only [Handler.run]
                      change Process.answerService serviceKey oracle
                        (((((Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                          (.cons st (.cons (buf, (off, ())) .nil))).bind _).mapHalt _).bind _) = _
                      have hClauseEq : (Stack.handler M fnTable rTable [idealConV', layV']).clause (.get kind giver at_ τ)
                          (.cons st (.cons (buf, (off, ())) .nil)) =
                          (liftLocal (fun why => (why, .cons st (.cons (buf, (off, ())) .nil)))
                            (rRef.eval M fnTable (.cons buf (.cons off .nil)))).map fun res =>
                            match res with
                            | .cons msg (.cons nextOff .nil) =>
                                (msg, .cons st (.cons (buf, (nextOff, ())) .nil)) := by
                        change ((((Layer.handler M fnTable rTable idealConV').over
                            (Stack.handler M fnTable rTable [layV'])).clause (.get kind giver at_ τ)
                            (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                        dsimp only [Layer.handler, Handler.over, idealConV']
                        rw [hConPass]
                        dsimp only [Handler.answer]
                        rw [hLay1Step, hLayAns]
                        cases rRef.eval M fnTable (.cons buf (.cons off .nil)) with
                        | halt why => rfl
                        | call op _ => cases op
                        | done res =>
                            cases res with
                            | cons msg r1 =>
                                cases r1 with
                                | cons nextOff r2 =>
                                    cases r2; rfl
                      rw [hClauseEq]
                      cases rRef.eval M fnTable (.cons buf (.cons off .nil)) with
                      | halt why => rfl
                      | call op _ => cases op
                      | done res =>
                          cases res with
                          | cons msg r1 =>
                              cases r1 with
                              | cons nextOff r2 =>
                                  cases r2
                                  exact ih msg st buf nextOff (hKSh msg trivial)
              | own gkind hearers at_ gIns payload τ =>
                  cases gkind with
                  | coin law =>
                      cases hearers with
                      | nil =>
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
                            have hEInAbs : ∃ p ∈ eventsAbs, p.1 = e := by
                              have hM : e ∈ eventsAbs.map Prod.fst := hFst.symm ▸ he
                              obtain ⟨p, hp, hEq⟩ := List.mem_map.mp hM
                              exact ⟨p, hp, hEq⟩
                            obtain ⟨pV, hpV, hpVEq⟩ := hEInAbs
                            have hSuf0 : ∀ k p, eventsAbs[k]? = some p → events[0 + k]? = some p.1 := by
                              intro k p hk; rw [Nat.zero_add, ← hFst, List.getElem?_map, hk]; rfl
                            obtain ⟨idxV, eV, encRef, hIdxV, hSiteV, hTyV, hClsV, hEncFind, hConAns⟩ :=
                              ideal_clauses_answer_coin M 0 eventsAbs hSuf0 hIV
                                law (h0 :: hs) at_ τ st
                                ⟨pV, hpV, hpVEq.symm ▸ hSite, hpVEq.symm ▸ hTy, hPin, hpVEq.symm ▸ hCls⟩
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
                                    [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ) fun coin =>
                                  (liftLocal (fun why => (why, .cons st (.cons (buf, (off, ())) .nil)))
                                    (encRef.eval M fnTable (.cons coin .nil))).map fun enc =>
                                      (coin, .cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single)
                                        (.cons (buf, (off, ())) .nil)) := by
                              change ((((Layer.handler M fnTable rTable idealConV').over
                                  (Stack.handler M fnTable rTable [layV'])).clause
                                  (.own (.coin law) (h0 :: hs) at_ [] .nil τ)
                                  (st, .cons (buf, (off, ())) .nil)).mapHalt _).map _ = _
                              dsimp only [Layer.handler, Handler.over, idealConV']
                              rw [hConAns]
                              dsimp only [Handler.answer]
                              have hReqLay : (Stack.handler M fnTable rTable [layV']).clause
                                  (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                    [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
                                  (.cons (buf, (off, ())) .nil) =
                                  .call (.own (.request serviceKey) [] ⟨at_.path, idealReqKey events idxV⟩
                                    [idealQueryTy suiteUnitTy] (.cons (st, (drawLabel at_.site, ())) .nil) τ)
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
                                (fun (out : M.Val τ × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
                                  (out.1, HList.cons out.2.1 out.2.2))
                                (Process.mapHalt
                                  (fun (stop : Stop × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
                                    (stop.1, HList.cons stop.2.1 stop.2.2))
                                  ((Process.mapHalt
                                    (fun (stop : Stop × M.Val (idealPathTy suiteUnitTy) × HList M.Val (Stack.States [layV'])) =>
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
                                              (Process.map
                                                (fun enc => aloneIn M verifier (.cons coin (.cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single) .nil)))
                                                (liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons coin .nil))))))
                                          st out.2)).bind
                                    fun out => Process.done (out.1.1, out.1.2, out.2))) = _
                              rw [hDropLay]
                              change Process.map
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
                                          ((HList.split [τ] (aloneOut M verifier out)).1.single,
                                            (HList.split [τ] (aloneOut M verifier out)).2.single))
                                        (Process.mapHalt (fun why => (why, st))
                                          (Process.map
                                            (fun enc => aloneIn M verifier (.cons coin (.cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single) .nil)))
                                            (liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons coin .nil))))))
                                      st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))).bind
                                    fun out => Process.done (out.1.1, out.1.2, out.2))) =
                                Process.map
                                  (fun enc => (coin, HList.cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single)
                                    (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                  (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                    (encRef.eval M fnTable (.cons coin .nil)))
                              cases encRef.eval M fnTable (.cons coin .nil) with
                              | halt why => rfl
                              | call op _ => cases op
                              | done enc =>
                                  cases enc with
                                  | cons encV en =>
                                      cases en
                                      change Process.done
                                        ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                                          (.cons coin (.cons (idealPathPush M st (3 :: drawLabel at_.site) encV) .nil))))).1.single,
                                          HList.cons ((HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                                            (.cons coin (.cons (idealPathPush M st (3 :: drawLabel at_.site) encV) .nil))))).2.single)
                                            (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)) =
                                        Process.done (coin, HList.cons (idealPathPush M st (3 :: drawLabel at_.site) encV)
                                          (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))
                                      rw [aloneOut_aloneIn]; rfl
                            rw [hClauseEq]
                            dsimp only [Process.bind, Process.mapHalt]
                            unfold Process.answerService
                            rw [ite_eq_left rfl, hOracleRo st (drawLabel at_.site) τ]
                            let coin := ro st (drawLabel at_.site) τ
                            change Process.answerService serviceKey oracle
                              ((Process.mapHalt Prod.fst
                                (((Process.map
                                    (fun enc => (coin, HList.cons (idealPathPush M st (3 :: drawLabel at_.site) enc.single)
                                      (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                    (liftLocal (fun why => (why, HList.cons st (HList.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))
                                      (encRef.eval M fnTable (.cons coin .nil)))).bind _))).bind _) =
                              (liftLocal id (encRef.eval M fnTable (.cons coin .nil))).bind fun enc =>
                                evalIdealVerifierLoop M a suite layout serviceKey prover verifier
                                  (finishGuardKey events) eventsAbs oracle ro (k coin)
                                  (idealPathPush M st (3 :: drawLabel at_.site) enc.single) buf off
                            cases encRef.eval M fnTable (.cons coin .nil) with
                            | halt why => rfl
                            | call op _ => cases op
                            | done enc =>
                                cases enc with
                                | cons encV en =>
                                    cases en
                                    exact ih coin (idealPathPush M st (3 :: drawLabel at_.site) encV)
                                      buf off (hKSh coin trivial)
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

/-- Exact pure-path ideal-RO linkage theorem:
for any non-carry streaming `deployIdeal` verifier without retry, answering
`.own (.request serviceKey)` with any oracle extending a total random oracle `ro` on the
collision-free transcript path `idealPathTy suiteUnitTy` yields the direct state-machine
interpreter `evalIdealVerifierLoop` over the bare verifier role program `roleMeaning`, completely
eliminating `Layer`, `Stack`, `Handler`, `Clause`, and concrete `SuiteSlot.start`/`SuiteSlot.absorb`. -/
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
      (st0 : M.Val (idealPathTy suiteUnitTy))
      (hTakes : Stack.Takes (dIdeal.stack verifier) = [.seq unitTy none])
      (hGives : Stack.Gives (dIdeal.stack verifier) = []),
      findSuiteUnit a suite = some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩ ∧
      ∀ (proof : List (M.Val unitTy))
        (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ))
        (ro : M.Val (idealPathTy suiteUnitTy) → List Nat → (τ : V.Ty) → M.Val τ),
        (∀ st lbl τ, oracle [idealQueryTy suiteUnitTy] (.cons (st, (lbl, ())) .nil) τ = some (ro st lbl τ)) →
        (Process.answerService serviceKey oracle
          (dIdeal.run M verifier ins (cast (congrArg (HList M.Val) hTakes.symm) (.cons proof .nil)))).map
          (fun out => (out.1, cast (congrArg (HList M.Val) hGives) out.2)) =
          evalIdealVerifierLoop M a suite layout serviceKey prover verifier
            (finishGuardKey (dIdeal.entry.shape.events [] id))
            (dIdeal.entry.shape.eventsWithAbsorb prover verifier [] id false)
            oracle ro
            (roleMeaning M dIdeal.admitted.program dIdeal.callee verifier [] ins) st0 proof 0 := by
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration dIdeal hDep
  subst hEq
  have hConEq : Construction.derived w.suite w.sessionTag = .derived suite sessionTag :=
    w.hCon.symm.trans hCon
  have hSuiteEq : w.suite = suite := (Construction.derived.inj hConEq).1
  have hLayEq : w.layout = layout := Option.some.inj (w.hLayOpt.symm.trans hLay)
  have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
    simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
  rw [w.hPV] at hRolesEq; cases hRolesEq
  cases buildLayoutLayers_ok_elim w.hLay with
  | compact wL _ =>
      have hne := wL.hNonEmpty
      rw [hLayEq, hNoRec] at hne; cases hne
  | streaming wL hLPW hLVW =>
      have hEntryF : ((a.program.findProtocol declaration.entry).get
          (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
      have hInsF := insRV_cast_valid M hEntryF ins hIns
      obtain ⟨st0, hSt0Done, _⟩ := idealStart_done M a w.hSuiteFree
        w.sessBytes w.hSessBytes w.stmtV
        (heldValues M w.verifier (cast (congrArg (fun hdr => HList (RV M w.verifier) hdr.ins) hEntryF) ins))
        (heldValues_valid M w.verifier _ hInsF)
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
      have hTakes : Stack.Takes (w.toDeployed.stack w.verifier) = [.seq wL.unitTy none] := by
        rw [hStackVEq, stack_takes_cast_hdr hEntryF]; rfl
      have hGives : Stack.Gives (w.toDeployed.stack w.verifier) = [] := by
        rw [hStackVEq, stack_gives_cast_hdr hEntryF]; rfl
      refine ⟨w.suiteUnitTy, wL.unitTy, w.hSuiteFree, st0, hTakes, hGives,
        hSuiteEq ▸ w.hUnit, fun proof oracle ro hOR => ?_⟩
      have hBridge : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
          (callee : Member a.program.headers.protocols hdr)
          (ins' : HList (RV M w.verifier) hdr.ins)
          (hStart' : (idealStart w.hSuiteFree w.sessBytes w.hSessBytes w.stmtV).denote
            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
            (Env.positional (heldValues M w.verifier (cast (congrArg (fun h => HList (RV M w.verifier) h.ins) hE) ins'))) =
            .done (.cons st0 .nil))
          (hT' : Stack.Takes (hE ▸ [idealConV0, layV0]) = [.seq wL.unitTy none])
          (hG' : Stack.Gives (hE ▸ [idealConV0, layV0]) = []),
          (Process.answerService serviceKey oracle
            (runStack a M callee none w.verifier
              (hE ▸ [idealConV0, layV0])
              ins' (cast (congrArg (HList M.Val) hT'.symm) (.cons proof .nil)))).map
            (fun out => (out.1, cast (congrArg (HList M.Val) hG') out.2)) =
            evalIdealVerifierLoop M a suite layout serviceKey w.prover w.verifier
              (finishGuardKey (hdr.shape.events [] id))
              (hdr.shape.eventsWithAbsorb w.prover w.verifier [] id false)
              oracle ro
              (roleMeaning M a.program callee w.verifier [] ins') st0 proof 0 := by
        intro hdr hE callee ins' hStart' hT' hG'
        subst hE
        dsimp only at hStart'
        simp only [cast_eq] at hStart'
        unfold runStack
        change Process.map (fun (out : HList (RV M w.verifier) w.foundPair.1.outs × HList M.Val (Stack.Gives [idealConV0, layV0])) => (out.1, cast (congrArg (HList M.Val) hG') out.2))
          (Process.answerService serviceKey oracle
            ((Stack.start M (Defs.fnTable M a.program.defs) [idealConV0, layV0]
              ins' (.cons proof .nil)).bind _)) = _
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
        rw [hStV]
        dsimp only [Process.bind]
        rw [← answerService_map]
        have hLoop := ideal_verifier_loop_eq M (suite := suite) (layout := layout)
          hNoCarry w.hNe idealConV0 layV0
          rfl rfl rfl rfl rfl rfl (hSuiteEq ▸ w.hIV) ⟨wL.pClauses, hLayEq ▸ wL.hStr⟩
          oracle ro hOR
          (roleMeaning M a.program callee w.verifier [] ins') st0 proof 0
          (roleMeaning_matchesShape M a.program callee w.verifier [] ins')
        simpa [Process.map_id', Process.map_bind, Process.map_map] using hLoop
      have hT2 : Stack.Takes (hEntryF ▸ [idealConV0, layV0]) = [.seq wL.unitTy none] := by
        rw [stack_takes_cast_hdr hEntryF]; rfl
      have hG2 : Stack.Gives (hEntryF ▸ [idealConV0, layV0]) = [] := by
        rw [stack_gives_cast_hdr hEntryF]; rfl
      exact (ideal_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
        ((cast_heq _ _).trans (cast_heq _ _).symm)
        (hG₁ := hGives) (hG₂ := hG2) serviceKey oracle).trans
        (hBridge _ hEntryF w.toDeployed.callee ins hSt0Done hT2 hG2)

end IdealLink

/-! ## Section 2: Collision-free ideal transcript step injectivity -/

section IdealPathInjectivity

variable {V : Vocabulary} (M : Model V)

/-- Message absorption steps on the pure ideal transcript path are unconditionally injective
under `Deployed.SuiteLawful` (encoding injectivity + collision-free path append). -/
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
    st₁ = st₂ ∧ msgLabel s₁ = msgLabel s₂ ∧ v₁ = v₂ := by
  obtain ⟨hSt, hLbl, hEnc⟩ := idealPathPush_injective M hPath
  have hLbl' : msgLabel s₁ = msgLabel s₂ := (List.cons.inj hLbl).2
  subst hEnc
  have hVal := suiteLawful_encode_injective M hCon hSuite hFind hV₁ hV₂ hE₁ hE₂
  exact ⟨hSt, hLbl', hVal⟩

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
    st₁ = st₂ ∧ drawLabel s₁ = drawLabel s₂ ∧ c₁ = c₂ := by
  obtain ⟨hSt, hLbl, hEnc⟩ := idealPathPush_injective M hPath
  have hLbl' : drawLabel s₁ = drawLabel s₂ := (List.cons.inj hLbl).2
  subst hEnc
  have hVal := suiteLawful_encode_injective M hCon hSuite hFind hV₁ hV₂ hE₁ hE₂
  exact ⟨hSt, hLbl', hVal⟩

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

/-! ## Section 3: Non-malleable canonical compact proof parsing (`compact_parse_written`) -/

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
      erw [letOp1_denote, localSem_op_owned] at hDone
      simp only [Env.all] at hDone
      rw [ownedOp_seqLength] at hDone
      simp only [Process.bind, HList.single] at hDone
      erw [letOp1_denote, localSem_op_owned] at hDone
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
