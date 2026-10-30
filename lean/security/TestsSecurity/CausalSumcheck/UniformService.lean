import ZkcSecurityExamples.CausalSumcheck.UniformService

/-! Focused controls for the concrete uniform service. These are action and
short-script equations, not an independent Sumcheck round or source-security
argument. Complete records, including stopped branches, remain observable. -/

namespace TestsSecurity.CausalSumcheck.UniformService

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.VCVio.Execution
open ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open scoped ENNReal

variable {F G S E : Type}

def query (key : Key) : PIR.Process (participantInterface F G) F :=
  participantActions F G (.query key.1 key.2.1 (.cons key.2.2 .nil))

/-- An arbitrary query branch, including cached replies or stops. -/
def replaceNetworkQueries
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (replacement : Key → Phase S E F) :
    PIR.MonadHandler ProbComp (participantInterface F G) S E
  | .receive ty site peer, s => network (.receive ty site peer) s
  | .send site peer value, s => network (.send site peer value) s
  | .query site field (.cons handle .nil), s => replacement (site, field, handle) s

section General

variable [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (ports : List Key) (before : Key → Phase S E Unit)
    (after : Key → F → Phase S E Unit)

theorem network_query_branch_irrelevant (replacement : Key → Phase S E F) :
    withUniformQueries (replaceNetworkQueries network replacement) ports before after =
      withUniformQueries network ports before after := by
  funext action s
  cases action with
  | receive => rfl
  | send => rfl
  | query site field args =>
    cases args with | cons handle tail => cases tail; rfl

theorem ports_extensional (other : List Key)
    (same : ∀ key, key ∈ ports ↔ key ∈ other) :
    withUniformQueries network ports before after =
      withUniformQueries network other before after := by
  funext action s
  cases action with
  | receive => rfl
  | send => rfl
  | query site field args =>
    cases args with | cons handle tail =>
      cases tail
      simp only [withUniformQueries, same]

theorem ports_reorder_duplicate (first second : Key) :
    withUniformQueries network [first, second, first] before after =
      withUniformQueries network [second, first] before after := by
  apply ports_extensional
  intro key
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem query_exact (key : Key) (member : key ∈ ports) (s : S) :
    (query (F := F) (G := G) key).runM
        (withUniformQueries network ports before after) s =
      freshQuery (before key) (after key) s :=
  withUniformQueries_query network ports before after key.1 key.2.1 key.2.2 member s

theorem wrong_route_refuses (installed requested : Key) (different : requested ≠ installed)
    (s : S) :
    (query (F := F) (G := G) requested).runM
        (withUniformQueries network [installed] before after) s =
      pure ⟨.stopped .refused, s, []⟩ := by
  exact withUniformQueries_unconfigured network [installed] before after _ _ _
    (by simpa using different) s

theorem wrong_site_domain_handle (site field : String) (handle : Nat)
    (wrongSite wrongField : String) (wrongHandle : Nat)
    (siteChanged : wrongSite ≠ site) (fieldChanged : wrongField ≠ field)
    (handleChanged : wrongHandle ≠ handle) (s : S) :
    let installed := (site, field, handle)
    let handler := withUniformQueries network [installed] before after
    (query (F := F) (G := G) (wrongSite, field, handle)).runM handler s =
        pure ⟨.stopped .refused, s, []⟩ ∧
    (query (F := F) (G := G) (site, wrongField, handle)).runM handler s =
        pure ⟨.stopped .refused, s, []⟩ ∧
    (query (F := F) (G := G) (site, field, wrongHandle)).runM handler s =
        pure ⟨.stopped .refused, s, []⟩ := by
  exact ⟨wrong_route_refuses network before after _ _ (by simp [siteChanged]) s,
    wrong_route_refuses network before after _ _ (by simp [fieldChanged]) s,
    wrong_route_refuses network before after _ _ (by simp [handleChanged]) s⟩

end General

/-- These are the two actual child entry labels under a nonidentity root map. -/
def sourceChild : ProtocolContext :=
  (⟨some "outer", roleSubstitution [2, 0]⟩ : ProtocolContext).enter
    "label_726564756365" [0, 1]

def reductionChild : ProtocolContext :=
  (⟨some "outer", roleSubstitution [2, 0]⟩ : ProtocolContext).enter "s3" [0, 1]

theorem mapped_clients (handle : Nat) :
    sourceChild.roles 1 = 0 ∧ sourceChild.roles 0 = 2 ∧
    reductionChild.roles 1 = 0 ∧ reductionChild.roles 0 = 2 ∧
    queryKey sourceChild handle ≠ queryKey reductionChild handle := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro same
  have sites := congrArg Prod.fst same
  exact (by decide : (queryKey sourceChild 0).1 ≠ (queryKey reductionChild 0).1) sites

/-- Logging callbacks may use the entire shared state and the actual draw. -/
def logBefore (update : Key → S → S) (events : Key → S → List E) :
    Key → Phase S E Unit := fun key s => pure ⟨.returned (), update key s, events key s⟩

def logAfter (update : Key → F → S → S) (events : Key → F → S → List E) :
    Key → F → Phase S E Unit := fun key r s =>
  pure ⟨.returned (), update key r s, events key r s⟩

section Records

variable [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (ports : List Key) (key : Key) (member : key ∈ ports)

include member

theorem query_logged (prepare : Key → S → S) (preEvents : Key → S → List E)
    (record : Key → F → S → S) (postEvents : Key → F → S → List E) (s : S) :
    (query (F := F) (G := G) key).runM
        (withUniformQueries network ports (logBefore prepare preEvents)
          (logAfter record postEvents)) s = (do
      let r ← ($ᵗ F)
      pure ⟨.returned r, record key r (prepare key s),
        preEvents key s ++ postEvents key r (prepare key s)⟩) := by
  rw [query_exact network ports _ _ key member]
  simp [freshQuery, logBefore, logAfter, PIR.Execution.followM, result]

theorem before_stop_suppresses_suffix {A : Type} (why : PIR.Stop) (t : S) (events : List E)
    (after : Key → F → Phase S E Unit)
    (suffix : F → PIR.Process (participantInterface F G) A) (s : S) :
    ((query key).bind suffix).runM
        (withUniformQueries network ports (fun _ _ => pure ⟨.stopped why, t, events⟩)
          after) s = pure ⟨.stopped why, t, events⟩ := by
  rw [PIR.runM_bind, query_exact network ports _ _ key member]
  simp [freshQuery, PIR.Execution.followM]

theorem after_stop_suppresses_suffix {A : Type}
    (prepare : Key → S → S) (preEvents : Key → S → List E)
    (why : F → PIR.Stop) (record : F → S → S) (postEvents : F → S → List E)
    (suffix : F → PIR.Process (participantInterface F G) A) (s : S) :
    ((query key).bind suffix).runM
        (withUniformQueries network ports (logBefore prepare preEvents)
          (fun _ r t => pure ⟨.stopped (why r), record r t, postEvents r t⟩)) s = (do
      let r ← ($ᵗ F)
      pure ⟨.stopped (why r), record r (prepare key s),
        preEvents key s ++ postEvents r (prepare key s)⟩) := by
  rw [PIR.runM_bind, query_exact network ports _ _ key member]
  simp [freshQuery, logBefore, PIR.Execution.followM]

end Records

def twoQueries (first second : Key) : PIR.Process (participantInterface F G) (F × F) :=
  (query first).bind fun a => (query second).bind fun b => .done (a, b)

section Pairs

variable [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (ports : List Key) (first second : Key)
    (firstMember : first ∈ ports) (secondMember : second ∈ ports)

include firstMember secondMember

theorem two_queries_logged
    (prepare : Key → S → S) (preEvents : Key → S → List E)
    (record : Key → F → S → S) (postEvents : Key → F → S → List E) (s : S) :
    (twoQueries (F := F) (G := G) first second).runM
        (withUniformQueries network ports (logBefore prepare preEvents)
          (logAfter record postEvents)) s = (do
      let a ← ($ᵗ F)
      let b ← ($ᵗ F)
      let t := prepare first s
      let u := record first a t
      let v := prepare second u
      pure ⟨.returned (a, b), record second b v,
        preEvents first s ++ postEvents first a t ++
          preEvents second u ++ postEvents second b v⟩) := by
  simp only [twoQueries, runM_bind_function, query_logged network ports first firstMember,
    query_logged network ports second secondMember]
  simp [PIR.Execution.followM, PIR.Process.runM, List.append_assoc]

theorem two_queries_fresh (s : S) :
    (twoQueries (F := F) (G := G) first second).runM
        (withUniformQueries network ports (fun _ => noOp) (fun _ _ => noOp)) s = (do
      let a ← ($ᵗ F)
      let b ← ($ᵗ F)
      pure (result (a, b) s)) := by
  simp only [twoQueries, runM_bind_function, query_exact network ports _ _ first firstMember,
    query_exact network ports _ _ second secondMember]
  simp [freshQuery, noOp, result, PIR.Execution.followM, PIR.Process.runM]

end Pairs

/-- The send sees the exact post-query state and may stop with its own effects. -/
theorem send_stop_after_query [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (ports : List Key) (key : Key) (member : key ∈ ports)
    (prepare : Key → S → S) (preEvents : Key → S → List E)
    (record : Key → F → S → S) (postEvents : Key → F → S → List E)
    (site : String) (peer : Nat) (why : F → S → PIR.Stop)
    (delivered : F → S → S) (sendEvents : F → S → List E)
    (sendLaw : ∀ r t, network (.send (ty := .field key.2.1) site peer r) t =
      pure ⟨.stopped (why r t), delivered r t, sendEvents r t⟩) (s : S) :
    ((query key).bind fun r =>
      participantActions F G (.send (ty := .field key.2.1) site peer r)).runM
        (withUniformQueries network ports (logBefore prepare preEvents)
          (logAfter record postEvents)) s = (do
      let r ← ($ᵗ F)
      let t := record key r (prepare key s)
      pure ⟨.stopped (why r t), delivered r t,
        preEvents key s ++ postEvents key r (prepare key s) ++ sendEvents r t⟩) := by
  simp only [runM_bind_function, query_logged network ports key member]
  simp [PIR.Execution.followM, participantActions_runM (F := F) (G := G), sendLaw,
    List.append_assoc]

/-- Both actual entered routes are installed, with arbitrary handles and state. -/
theorem two_clients [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (firstHandle secondHandle : Nat)
    (prepare : Key → S → S) (preEvents : Key → S → List E)
    (record : Key → F → S → S) (postEvents : Key → F → S → List E) (s : S) :
    let first := queryKey sourceChild firstHandle
    let second := queryKey reductionChild secondHandle
    (twoQueries (F := F) (G := G) first second).runM
        (withUniformQueries network [first, second] (logBefore prepare preEvents)
          (logAfter record postEvents)) s = (do
      let a ← ($ᵗ F)
      let b ← ($ᵗ F)
      let t := prepare first s
      let u := record first a t
      let v := prepare second u
      pure ⟨.returned (a, b), record second b v,
        preEvents first s ++ postEvents first a t ++
          preEvents second u ++ postEvents second b v⟩) := by
  exact two_queries_logged network _ _ _ (by simp) (by simp) _ _ _ _ s

section FiniteWitnesses

abbrev F2 := ZMod 2

/-- Off-diagonal mass is unconditional, and the network is arbitrary. -/
theorem fresh_pair_off_diagonal
    (network : PIR.MonadHandler ProbComp (participantInterface F2 G) S E)
    (ports : List Key) (first second : Key)
    (firstMember : first ∈ ports) (secondMember : second ∈ ports) (s : S) :
    mass (do
      let e ← (twoQueries (F := F2) (G := G) first second).runM
        (withUniformQueries network ports (fun _ => noOp) (fun _ _ => noOp)) s
      pure (returnedSatisfies (fun p => p.1 ≠ p.2) e)) = 1 / 2 := by
  rw [two_queries_fresh network ports first second firstMember secondMember]
  simp only [bind_assoc, pure_bind, result, returnedSatisfies]
  change Pr{let a ← ($ᵗ F2); let b ← ($ᵗ F2)}[a ≠ b] = _
  rw [← SampleableType.prEvent_uniformSample_prod (fun p : F2 × F2 => p.1 ≠ p.2),
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun p : F2 × F2 => p.1 ≠ p.2)).card = 2 := by decide
  rw [count]
  norm_num [F2]
  have cancel := ENNReal.mul_div_mul_left (1 : ENNReal) 2
    (c := 2) (by norm_num) (by simp)
  norm_num at cancel
  exact cancel

/-- The same key and handle still produce two fresh, independent draws. -/
theorem repeated_handle_off_diagonal
    (network : PIR.MonadHandler ProbComp (participantInterface F2 G) S E)
    (key : Key) (s : S) :
    mass (do
      let e ← (twoQueries (F := F2) (G := G) key key).runM
        (withUniformQueries network [key] (fun _ => noOp) (fun _ _ => noOp)) s
      pure (returnedSatisfies (fun p => p.1 ≠ p.2) e)) = 1 / 2 :=
  fresh_pair_off_diagonal network [key] key key (by simp) (by simp) s

def cachedDraw : Phase (Option F2) Unit F2
  | some r => pure (result r (some r))
  | none => do
      let r ← ($ᵗ F2)
      pure (result r (some r))

/-- A deliberately cached query implementation for comparison with the service. -/
def cachedNetwork : PIR.MonadHandler ProbComp (participantInterface F2 Unit)
    (Option F2) Unit
  | .receive .., s => pure ⟨.stopped .refused, s, []⟩
  | .send .., s => pure ⟨.stopped .refused, s, []⟩
  | .query _ _ (.cons _ .nil), s => cachedDraw s

theorem cached_pair_exact (key : Key) :
    (twoQueries (F := F2) (G := Unit) key key).runM cachedNetwork none = (do
      let r ← ($ᵗ F2)
      pure (result (r, r) (some r))) := by
  have queryLaw (s : Option F2) :
      (query (F := F2) (G := Unit) key).runM cachedNetwork s = cachedDraw s := by
    exact participantActions_runM cachedNetwork _ s
  have second (a : F2) :
      ((query key).bind fun b => PIR.Process.done (a, b)).runM cachedNetwork (some a) =
        pure (result (a, a) (some a)) := by
    rw [PIR.runM_bind, queryLaw]
    simp [cachedDraw, PIR.Process.runM, result, PIR.Execution.followM]
  rw [twoQueries, PIR.runM_bind, queryLaw]
  simp only [cachedDraw, bind_assoc, pure_bind, follow_result]
  apply bind_congr
  intro a
  exact second a

theorem cached_pair_off_diagonal (key : Key) :
    mass (do
      let e ← (twoQueries (F := F2) (G := Unit) key key).runM cachedNetwork none
      pure (returnedSatisfies (fun p => p.1 ≠ p.2) e)) = 0 := by
  rw [cached_pair_exact]
  simp [result, returnedSatisfies, mass]

/-- An observer of returned pairs separates wrapping from cache reuse. -/
theorem fresh_pair_not_cached (key : Key) :
    ¬ SameDist
      ((twoQueries (F := F2) (G := Unit) key key).runM
        (withUniformQueries cachedNetwork [key] (fun _ => noOp) (fun _ _ => noOp)) none)
      ((twoQueries (F := F2) (G := Unit) key key).runM cachedNetwork none) := by
  intro same
  have measured := same.bind_left
    (fun e => pure (returnedSatisfies (fun p => p.1 ≠ p.2) e))
  have unequal := congrArg (fun measure => measure {True}) measured
  change mass _ = mass _ at unequal
  rw [repeated_handle_off_diagonal, cached_pair_off_diagonal] at unequal
  norm_num at unequal

/-- The after callback logs every draw but returns only on zero. -/
def selectiveAfter (_key : Key) (r : F2) : Phase (List F2) F2 Unit := fun s =>
  pure ⟨if r = 0 then .returned () else .stopped .exhausted, s ++ [r], [r]⟩

theorem selective_after_exact
    (network : PIR.MonadHandler ProbComp (participantInterface F2 G) (List F2) F2)
    (key : Key) (s : List F2) :
    (query (F := F2) (G := G) key).runM
        (withUniformQueries network [key] (fun _ => noOp) selectiveAfter) s = (do
      let r ← ($ᵗ F2)
      pure ⟨if r = 0 then .returned r else .stopped .exhausted, s ++ [r], [r]⟩) := by
  rw [query_exact network [key] _ _ key (by simp)]
  simp only [freshQuery, noOp, pure_bind, follow_result, selectiveAfter]
  apply bind_congr
  intro r
  by_cases h : r = 0 <;> simp [h, PIR.Execution.followM, result]

theorem selective_after_return_mass
    (network : PIR.MonadHandler ProbComp (participantInterface F2 G) (List F2) F2)
    (key : Key) (s : List F2) :
    mass (do
      let e ← (query (F := F2) (G := G) key).runM
        (withUniformQueries network [key] (fun _ => noOp) selectiveAfter) s
      pure (returnedSatisfies (fun _ => True) e)) = 1 / 2 := by
  rw [selective_after_exact]
  simp only [bind_assoc, pure_bind]
  have observe (r : F2) :
      returnedSatisfies (fun _ : F2 => True)
        ⟨if r = 0 then .returned r else .stopped .exhausted, s ++ [r], [r]⟩ = (r = 0) := by
    by_cases h : r = 0 <;> simp [h, returnedSatisfies]
  simp_rw [observe]
  change Pr{let r ← ($ᵗ F2)}[r = 0] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [F2]

theorem selective_after_no_nonzero_return
    (network : PIR.MonadHandler ProbComp (participantInterface F2 G) (List F2) F2)
    (key : Key) (s : List F2) :
    mass (do
      let e ← (query (F := F2) (G := G) key).runM
        (withUniformQueries network [key] (fun _ => noOp) selectiveAfter) s
      pure (returnedSatisfies (fun r => r ≠ 0) e)) = 0 := by
  rw [selective_after_exact]
  simp only [bind_assoc, pure_bind]
  have observe (r : F2) :
      returnedSatisfies (fun r : F2 => r ≠ 0)
        ⟨if r = 0 then .returned r else .stopped .exhausted, s ++ [r], [r]⟩ = False := by
    by_cases h : r = 0 <;> simp [h, returnedSatisfies]
  simp_rw [observe]
  simp [mass]

end FiniteWitnesses

end TestsSecurity.CausalSumcheck.UniformService
