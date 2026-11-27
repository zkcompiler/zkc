module

public import Zkc.Core.Scheme.Deploy.Elim

@[expose] public section

/-!
Structural deployment theorems: `deploy_keeps`, `deploy_findsRoles`, `deploy_matches`,
`deploy_scoped`, `deployIdeal_scoped`, `deploy_wellNestedRetry`, `deployIdeal_wellNestedRetry`,
`deploy_fresh`, and `deployIdeal_fresh`.
-/

namespace Zkc.Core

open LayerBuild

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

/-- Every `samples` layer produced by `buildSamplesLayer` takes and gives nothing. -/
theorem buildSamplesLayer_io {a : Admitted V} {entry : ProtocolHeader V} {prover : Role}
    {samplesKey : Option Key} {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256}
    {declKey : Key} {events : List (ShapeEvent V)}
    {sampP : Layer V a.program.headers prover entry.ins}
    (h : buildSamplesLayer a entry prover samplesKey sessBytes hSess declKey events = .ok (some sampP)) :
    sampP.takes = [] ∧ sampP.gives = [] := by
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
              · cases hC : buildSamplesClauses a (held prover entry.ins) _ prover sKey sessBytes hSess declKey events with
                | error _ => rw [hC] at h; cases h
                | ok cs => rw [hC] at h; cases h; exact ⟨rfl, rfl⟩
              · cases h

theorem stack_takes_cast_ins {hs : Headers V} {ins₁ ins₂ : List (LTy V)}
    (hIns : ins₁ = ins₂) {r : Role}
    (layers : List (Layer V hs r ins₂)) :
    Stack.Takes (hIns ▸ layers) = Stack.Takes layers := by
  subst hIns; rfl

theorem stack_gives_cast_ins {hs : Headers V} {ins₁ ins₂ : List (LTy V)}
    (hIns : ins₁ = ins₂) {r : Role}
    (layers : List (Layer V hs r ins₂)) :
    Stack.Gives (hIns ▸ layers) = Stack.Gives layers := by
  subst hIns; rfl

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
      simp [Stack.Takes, Stack.Gives, hPt, hPg, hVt]
  | derived w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      obtain ⟨unitTy, hPt, hPg, hVt, _⟩ := buildLayoutLayers_io w.hLay
      have hNeSym : w.verifier ≠ w.prover := Ne.symm w.hNe
      dsimp only
      rw [dite_eq_left rfl, dite_eq_right hNeSym, dite_eq_left rfl,
          stack_takes_cast_ins (by simp [w.hFound]),
          stack_gives_cast_ins (by simp [w.hFound]),
          stack_takes_cast_ins (by simp [w.hFound])]
      cases hS : w.prep.sampLayer with
      | none => simp [Stack.Takes, Stack.Gives, hPt, hPg, hVt]
      | some sampP =>
          obtain ⟨hSt, hSg⟩ := buildSamplesLayer_io (hS ▸ w.prep.hSamp)
          simp [Stack.Takes, Stack.Gives, hSt, hSg, hPt, hPg, hVt]

/-- Every accepted deployment satisfies `Deployed.Scoped`. -/
theorem deploy_scoped (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.Scoped := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq =>
      subst hEq; unfold Deployed.Scoped Deployed.entry
      simpa [w.hFound] using (checkInteractiveScope_sound w.foundPair.1 declaration w.hScope).2
  | authored w hEq =>
      subst hEq; unfold Deployed.Scoped Deployed.entry
      simpa [w.hFound] using checkNonInteractiveScope_sound w.foundPair.1 w.prover declaration w.hScope
  | derived w hEq =>
      subst hEq; unfold Deployed.Scoped Deployed.entry
      simpa [w.hFound] using checkNonInteractiveScope_sound w.foundPair.1 w.prover declaration w.hScope

/-- Every accepted ideal random-oracle deployment satisfies `Deployed.Scoped`. -/
theorem deployIdeal_scoped (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.Scoped := by
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration d h
  subst hEq; unfold Deployed.Scoped Deployed.entry
  simpa [w.hFound] using checkNonInteractiveScope_sound w.foundPair.1 w.prover declaration w.hScope

/-- Every accepted deployment satisfies `Deployed.WellNestedRetry` unconditionally. -/
theorem deploy_wellNestedRetry (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.WellNestedRetry := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq =>
      subst hEq
      intro bound site hret
      have hNone := (checkInteractiveScope_sound w.foundPair.1 declaration w.hScope).1
      dsimp only [Deployed.retry] at hret
      rw [hNone] at hret; cases hret
  | authored w hEq =>
      subst hEq
      intro bound site hret
      have hwn := checkNonInteractiveScope_wellNested w.foundPair.1 w.prover declaration w.hScope bound site hret
      simpa [Deployed.entry, w.hFound] using hwn
  | derived w hEq =>
      subst hEq
      intro bound site hret
      have hwn := checkNonInteractiveScope_wellNested w.foundPair.1 w.prover declaration w.hScope bound site hret
      simpa [Deployed.entry, w.hFound] using hwn

/-- Every accepted ideal random-oracle deployment satisfies `Deployed.WellNestedRetry` unconditionally. -/
theorem deployIdeal_wellNestedRetry (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (h : deployIdeal enc serviceKey a declaration = .ok d) : d.WellNestedRetry := by
  let ⟨w, hEq⟩ := deployIdeal_ok_elim enc serviceKey a declaration d h
  subst hEq
  intro bound site hret
  have hwn := checkNonInteractiveScope_wellNested w.foundPair.1 w.prover declaration w.hScope bound site hret
  simpa [Deployed.entry, w.hFound] using hwn

/-! ### Freshness (`Deployed.Fresh`) -/

/-- A single clause satisfies the freshness condition relative to `events`. -/
def ClauseFresh {hs : Headers V} {r : Role} {state : V.Ty}
    (events : List (ShapeEvent V)) (c : Clause V hs r state) : Prop :=
  ∀ key, key ∈ Term.eventKeys (fun o => RoleOp.isEvent o) c.code → key ≠ c.site.site.key →
    key ∉ events.map (·.site.key)

theorem buildSamplesClauses_fresh {a : Admitted V} {heldP : List V.Ty}
    {htfree : Tys.anyLinear V (samplesStateTys heldP) = false}
    {prover : Role} {sKey : Key}
    {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256}
    {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (es : List (ShapeEvent V))
      {cS : List (Clause V a.program.headers prover (samplesStateTy heldP))},
      buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey es = .ok cS →
      ∀ c ∈ cS, ClauseFresh events c
  | [], _, h => by cases h; exact fun _ hc => nomatch hc
  | e :: rest, cS, h => by
      unfold buildSamplesClauses at h
      cases hRec : buildSamplesClauses a heldP htfree prover sKey sessBytes hSess declKey rest with
      | error _ => rw [hRec] at h; cases h
      | ok sRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ihS := buildSamplesClauses_fresh (events := events) rest hRec
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
                            · intro key hk _; rw [proverSampleClause_eventKeys] at hk; cases hk
                            · exact ihS c hm
                      · cases h; exact ihS

theorem buildSamplesLayer_fresh {a : Admitted V} {entry : ProtocolHeader V} {prover : Role}
    {samplesKey : Option Key} {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256}
    {declKey : Key} {events : List (ShapeEvent V)}
    {sampP : Layer V a.program.headers prover entry.ins}
    (h : buildSamplesLayer a entry prover samplesKey sessBytes hSess declKey events = .ok (some sampP)) :
    ∀ c ∈ sampP.clauses, ClauseFresh events c := by
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
              · cases hC : buildSamplesClauses a (held prover entry.ins) _ prover sKey sessBytes hSess declKey events with
                | error _ => rw [hC] at h; cases h
                | ok cs => rw [hC] at h; cases h; exact buildSamplesClauses_fresh events hC
              · cases h

theorem buildConstructionClauses_go_fresh {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absorbRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absorbRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      (∀ c ∈ cP, ClauseFresh events c) ∧
      (∀ c ∈ cV, ClauseFresh events c)
  | _, [], _, _, h => by
      cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, (e, needAbs) :: rest, cP, cV, h => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absorbRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h
          dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := buildConstructionClauses_go_fresh (idx + 1) rest hRec
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
                        refine ⟨?_, ?_⟩
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
                              · cases h
                                refine ⟨?_, ?_⟩
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
                    · cases h; exact ⟨ihP, ihV⟩
                    · cases h
              | request svc =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV⟩
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

theorem stack_fresh_cast_ins {hs : Headers V} {hdr₁ hdr₂ : ProtocolHeader V}
    (hHdr : hdr₁ = hdr₂) {r₁ r₂ : Role} (hr : r₁ = r₂)
    (layers : List (Layer V hs r₂ hdr₂.ins))
    (h : ∀ l ∈ layers, ∀ c ∈ l.clauses, ClauseFresh (hdr₂.shape.events [] id) c) :
    ∀ l ∈ (hr ▸ (congrArg ProtocolHeader.ins hHdr) ▸ layers),
      ∀ c ∈ l.clauses, ClauseFresh (hdr₁.shape.events [] id) c := by
  subst hHdr; subst hr; exact h

/-- Every accepted deployment satisfies `Deployed.Fresh`. -/
theorem deploy_fresh (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (h : deploy enc a declaration = .ok d) : d.Fresh := by
  cases deploy_ok_elim enc a declaration d h with
  | interactive w hEq =>
      subst hEq
      intro _ _ hl; cases hl
  | authored w hEq =>
      subst hEq
      obtain ⟨hLP, hLV⟩ := buildLayoutLayers_fresh w.hLay
      intro r
      dsimp only [Deployed.entry]
      by_cases hP : r = w.prover
      · rw [dite_eq_left hP]
        apply stack_fresh_cast (by simp [w.hFound]) hP
        intro l hl
        simp only [List.mem_singleton] at hl; subst hl; exact hLP
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
      obtain ⟨hCP, hCV⟩ := buildConstructionClauses_go_fresh 0 _ w.hCC
      obtain ⟨hLP, hLV⟩ := buildLayoutLayers_fresh w.hLay
      intro r
      dsimp only [Deployed.entry]
      by_cases hP : r = w.prover
      · rw [dite_eq_left hP]
        apply stack_fresh_cast_ins (by simp [w.hFound]) hP
        cases hS : w.prep.sampLayer with
        | none =>
            intro l hl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact hCP
            · exact hLP
        | some sampP =>
            have hCS := buildSamplesLayer_fresh (hS ▸ w.prep.hSamp)
            intro l hl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl | rfl
            · exact hCS
            · exact hCP
            · exact hLP
      · rw [dite_eq_right hP]
        by_cases hV : r = w.verifier
        · rw [dite_eq_left hV]
          apply stack_fresh_cast_ins (by simp [w.hFound]) hV
          intro l hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact hCV
          · exact hLV
        · rw [dite_eq_right hV]
          intro _ hl; cases hl

/-- Every accepted ideal random-oracle deployment satisfies `Deployed.Fresh`. -/
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
    apply stack_fresh_cast_ins (by simp [w.hFound]) hV
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hCV
    · exact hLV
  · rw [dite_eq_right hV]
    intro _ hl; cases hl

end StructuralTheorems

end Zkc.Core
