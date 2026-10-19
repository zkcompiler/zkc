import ZkcSecurity.Examples.CausalSumcheck.Iteration
import Mathlib.Algebra.Field.ZMod

/-! Discriminating controls for the source owner's shared Sumcheck process.
These equations retain complete executions. They do not establish the pending
literal-source association or a whole-root verifier theorem. -/

namespace TestsSecurity.CausalSumcheck.Iteration

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.VCVio.Execution
open ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open ZkcSecurity.Examples.CausalSumcheck.Iteration
open ZkcExamples.Structured.SumcheckVerifierLaws
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open Zkc.Polynomial.Multilinear
open scoped ENNReal

variable {F S E : Type}

/-- The actual source child label under a nonidentity immutable root role map. -/
def child : ProtocolContext :=
  (⟨some "outer", roleSubstitution [2, 0]⟩ : ProtocolContext).enter
    "label_726564756365" [0, 1]

def serviceHandle : Nat := 7
def serviceKey : Key := queryKey child serviceHandle
def lowSite : String := ZkcExamples.Structured.SumcheckVerifierLaws.lowSite child
def highSite : String := ZkcExamples.Structured.SumcheckVerifierLaws.highSite child
def sendSite : String := ZkcExamples.Structured.SumcheckVerifierLaws.deliverySite child

theorem mapped_roles : child.roles 0 = 2 ∧ child.roles 1 = 0 := ⟨rfl, rfl⟩

private theorem high_site_distinct :
    ZkcExamples.Structured.SumcheckVerifierLaws.highSite child ≠
      ZkcExamples.Structured.SumcheckVerifierLaws.lowSite child := by decide

private theorem query_handler {G : Type} [SampleableType F]
    (net : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (pre : Key → Phase S E Unit) (post : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle : Nat) (s : S) :
    withUniformQueries net [queryKey context handle] pre post
      (.query (challengeSite context)
        "bls12-381.fr" (.cons handle .nil)) s =
      freshQuery (F := F) (pre (queryKey context handle))
        (post (queryKey context handle)) s := by
  have law := withUniformQueries_queryKey net pre post context handle s
  rw [participantActions_runM (F := F) (G := G)] at law
  exact law

inductive Event (F : Type) where
  | low (site : String) (peer : Nat) (value : F)
  | high (site : String) (peer : Nat) (value : F)
  | before (key : Key)
  | after (key : Key) (value : F)
  | sent (site : String) (peer : Nat) (value : F)
  | oldQuery (key : Key) (value : F)
  deriving DecidableEq

/-- The adversary learns the first challenge only through the actual send.
The history is private state, separately retained from execution events. -/
structure State (F : Type) where
  high : F
  cached : F
  history : List (Event F)
  deriving DecidableEq

def record (event : Event F) (s : State F) : State F :=
  { s with history := s.history ++ [event] }

def before (key : Key) : Phase (State F) (Event F) Unit := fun s =>
  pure ⟨.returned (), record (.before key) s, [.before key]⟩

def after (key : Key) (r : F) : Phase (State F) (Event F) Unit := fun s =>
  pure ⟨.returned (), record (.after key r) s, [.after key r]⟩

def zeroLow [Zero F] : Phase (State F) (Event F) F := fun s =>
  pure ⟨.returned 0, record (.low lowSite 2 0) s, [.low lowSite 2 0]⟩

/-- Arbitrary LOW behavior is supplied as a phase. HIGH depends on network
state, send updates that state, and the old query reuses the cached value. -/
def network (low : Phase (State F) (Event F) F) :
    PIR.MonadHandler ProbComp (participantInterface F Unit) (State F) (Event F)
  | .receive (.field _) site peer, s =>
      if site = lowSite ∧ peer = 2 then low s
      else if site = highSite ∧ peer = 2 then
        pure ⟨.returned s.high, record (.high site peer s.high) s,
          [.high site peer s.high]⟩
      else pure ⟨.stopped .refused, s, []⟩
  | .receive .., s => pure ⟨.stopped .refused, s, []⟩
  | .send (ty := .field _) site peer r, s =>
      if site = sendSite ∧ peer = 2 then
        pure ⟨.returned (), record (.sent site peer r) { s with high := r },
          [.sent site peer r]⟩
      else pure ⟨.stopped .refused, s, []⟩
  | .send .., s => pure ⟨.stopped .refused, s, []⟩
  | .query site field (.cons handle .nil), s =>
      pure ⟨.returned s.cached, record (.oldQuery (site, field, handle) s.cached) s,
        [.oldQuery (site, field, handle) s.cached]⟩

def handler [SampleableType F] (low : Phase (State F) (Event F) F) :=
  withUniformQueries (network low) [serviceKey] before after

def roundEvents [Zero F] (hi r : F) : List (Event F) :=
  [.low lowSite 2 0, .high highSite 2 hi, .before serviceKey,
    .after serviceKey r, .sent sendSite 2 r]

def nextState [Zero F] (s : State F) (r : F) : State F :=
  ⟨r, s.cached, s.history ++ roundEvents s.high r⟩

section LoggedRounds

variable [Field F] [DecidableEq F] [SampleableType F]

set_option backward.isDefEq.respectTransparency false in
/-- HIGH is unconstrained by any honest public table. The only guard condition
here is that its reply equals the current claim, because LOW replies zero. -/
theorem round_logged (point : List F) (s : State F) :
    (roundPresent (G := Unit) child serviceHandle (point, s.high)).runM
        (handler zeroLow) s = (do
      let r ← ($ᵗ F)
      pure ⟨.returned (point ++ [r], r * s.high), nextState s r,
        roundEvents s.high r⟩) := by
  simp [roundPresent, PIR.Proc.runM, handler,
    query_handler (network (zeroLow (F := F))) before after child serviceHandle,
    network, zeroLow,
    mapped_roles.1, high_site_distinct,
    lowSite, highSite, sendSite, serviceKey,
    freshQuery, before, after, record, nextState, roundEvents,
    PIR.Execution.followM, result, List.append_assoc]

def initial : State F := ⟨1, 0, []⟩

/-- Two uses of the same route perform two draws. The second HIGH reply is r1,
read from the state written by the first send, rather than a repeated constant. -/
theorem two_rounds_exact :
    (PIR.repeatN 2 (roundPresent (G := Unit) child serviceHandle) ([], (1 : F))).runM
        (handler zeroLow) initial = (do
      let r1 ← ($ᵗ F)
      let r2 ← ($ᵗ F)
      pure ⟨.returned ([r1, r2], r1 * r2),
        nextState (nextState initial r1) r2,
        roundEvents 1 r1 ++ roundEvents r1 r2⟩) := by
  rw [PIR.repeatN, PIR.runM_bind]
  rw [show (1 : F) = (initial (F := F)).high from rfl, round_logged]
  simp only [bind_assoc, pure_bind, PIR.Execution.followM]
  apply bind_congr
  intro r1
  have second := round_logged [r1] (nextState (initial (F := F)) r1)
  simp only [nextState, initial, List.nil_append] at second
  simp only [PIR.repeatN, PIR.runM_bind, initial, mul_one, List.nil_append,
    nextState]
  rw [second]
  simp [PIR.Proc.runM, PIR.Execution.followM, mul_comm]

end LoggedRounds

section Stops

variable [Field F] [DecidableEq F] [SampleableType F]
    (net : PIR.MonadHandler ProbComp (participantInterface F Unit) S E)
    (pre : Key → Phase S E Unit) (post : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle n : Nat) (point : List F) (claim : F)

/-- An arbitrary LOW stop prevents HIGH, every service effect and all later rounds. -/
theorem low_stop (s t : S) (events : List E) (why : PIR.Stop)
    (law : net (lowAction context) s = pure ⟨.stopped why, t, events⟩) :
    (PIR.repeatN (n + 1) (roundPresent context handle) (point, claim)).runM
        (withUniformQueries net [queryKey context handle] pre post) s =
      pure ⟨.stopped why, t, events⟩ := by
  rw [PIR.repeatN]
  simp only [roundPresent, PIR.Proc.bind, PIR.Proc.runM, withUniformQueries_receive,
    law, pure_bind, PIR.Execution.followM]

/-- HIGH sees the actual post-LOW state; its stop retains both event prefixes. -/
theorem high_stop (s t u : S) (lo : F) (lowEvents highEvents : List E) (why : PIR.Stop)
    (lowLaw : net (lowAction context) s = pure ⟨.returned lo, t, lowEvents⟩)
    (highLaw : net (highAction context) t = pure ⟨.stopped why, u, highEvents⟩) :
    (PIR.repeatN (n + 1) (roundPresent context handle) (point, claim)).runM
        (withUniformQueries net [queryKey context handle] pre post) s =
      pure ⟨.stopped why, u, lowEvents ++ highEvents⟩ := by
  rw [PIR.repeatN]
  simp only [roundPresent, PIR.Proc.bind, PIR.Proc.runM, withUniformQueries_receive,
    lowLaw, highLaw, pure_bind, PIR.Execution.followM]

/-- Rejection has no before/after callbacks, designated draw, send or next round. -/
theorem guard_reject (s t u : S) (lo hi : F) (lowEvents highEvents : List E)
    (lowLaw : net (lowAction context) s = pure ⟨.returned lo, t, lowEvents⟩)
    (highLaw : net (highAction context) t = pure ⟨.returned hi, u, highEvents⟩)
    (wrong : claim ≠ lo + hi) :
    (PIR.repeatN (n + 1) (roundPresent context handle) (point, claim)).runM
        (withUniformQueries net [queryKey context handle] pre post) s =
      pure ⟨.stopped .reject, u, lowEvents ++ highEvents⟩ := by
  rw [PIR.repeatN]
  simp only [roundPresent, PIR.Proc.bind, PIR.Proc.runM, withUniformQueries_receive,
    lowLaw, highLaw, pure_bind, PIR.Execution.followM, wrong, ite_false,
    List.append_nil]

set_option backward.isDefEq.respectTransparency false in
/-- A pre-draw stop retains its actual state and suppresses the draw and suffix. -/
theorem before_stop (s t u v : S) (lo hi : F)
    (lowEvents highEvents preEvents : List E) (why : PIR.Stop)
    (lowLaw : net (lowAction context) s = pure ⟨.returned lo, t, lowEvents⟩)
    (highLaw : net (highAction context) t = pure ⟨.returned hi, u, highEvents⟩)
    (guard : claim = lo + hi)
    (preLaw : pre (queryKey context handle) u = pure ⟨.stopped why, v, preEvents⟩) :
    (PIR.repeatN (n + 1) (roundPresent context handle) (point, claim)).runM
        (withUniformQueries net [queryKey context handle] pre post) s =
      pure ⟨.stopped why, v, lowEvents ++ highEvents ++ preEvents⟩ := by
  rw [PIR.repeatN]
  simp only [roundPresent, PIR.Proc.bind, PIR.Proc.runM, withUniformQueries_receive,
    lowLaw, highLaw, pure_bind, PIR.Execution.followM, guard, ite_true]
  simp [query_handler net pre post context handle, freshQuery, preLaw, PIR.Execution.followM,
    List.append_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The designated draw occurs, but an after stop prevents send and later rounds. -/
theorem after_stop (s t u v : S) (lo hi : F)
    (lowEvents highEvents preEvents : List E) (why : F → PIR.Stop)
    (finalState : F → S) (postEvents : F → List E)
    (lowLaw : net (lowAction context) s = pure ⟨.returned lo, t, lowEvents⟩)
    (highLaw : net (highAction context) t = pure ⟨.returned hi, u, highEvents⟩)
    (guard : claim = lo + hi)
    (preLaw : pre (queryKey context handle) u = pure ⟨.returned (), v, preEvents⟩)
    (postLaw : ∀ r, post (queryKey context handle) r v =
      pure ⟨.stopped (why r), finalState r, postEvents r⟩) :
    (PIR.repeatN (n + 1) (roundPresent context handle) (point, claim)).runM
        (withUniformQueries net [queryKey context handle] pre post) s = (do
      let r ← ($ᵗ F)
      pure ⟨.stopped (why r), finalState r,
        lowEvents ++ highEvents ++ preEvents ++ postEvents r⟩) := by
  rw [PIR.repeatN]
  simp only [roundPresent, PIR.Proc.bind, PIR.Proc.runM, withUniformQueries_receive,
    lowLaw, highLaw, pure_bind, PIR.Execution.followM, guard, ite_true]
  simp [query_handler net pre post context handle, freshQuery, preLaw, postLaw,
    PIR.Execution.followM, List.append_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Send observes the post-callback state and can stop with its own effects. -/
theorem send_stop (s t u v : S) (lo hi : F)
    (lowEvents highEvents preEvents : List E) (why : F → PIR.Stop)
    (afterState finalState : F → S) (postEvents sendEvents : F → List E)
    (lowLaw : net (lowAction context) s = pure ⟨.returned lo, t, lowEvents⟩)
    (highLaw : net (highAction context) t = pure ⟨.returned hi, u, highEvents⟩)
    (guard : claim = lo + hi)
    (preLaw : pre (queryKey context handle) u = pure ⟨.returned (), v, preEvents⟩)
    (postLaw : ∀ r, post (queryKey context handle) r v =
      pure ⟨.returned (), afterState r, postEvents r⟩)
    (sendLaw : ∀ r, net (sendAction context r) (afterState r) =
      pure ⟨.stopped (why r), finalState r, sendEvents r⟩) :
    (PIR.repeatN (n + 1) (roundPresent context handle) (point, claim)).runM
        (withUniformQueries net [queryKey context handle] pre post) s = (do
      let r ← ($ᵗ F)
      pure ⟨.stopped (why r), finalState r,
        lowEvents ++ highEvents ++ preEvents ++ postEvents r ++ sendEvents r⟩) := by
  rw [PIR.repeatN]
  simp only [roundPresent, PIR.Proc.bind, PIR.Proc.runM, withUniformQueries_receive,
    lowLaw, highLaw, pure_bind, PIR.Execution.followM, guard, ite_true]
  simp [query_handler net pre post context handle, freshQuery, preLaw, postLaw, sendLaw,
    PIR.Execution.followM, result, List.append_assoc]

end Stops

section FiniteWitnesses

abbrev F2 := ZMod 2
abbrev F5 := ZMod 5

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem zero_table_one (r claim : F2) :
    Causal.tableTerminal (n := 1) (fun _ => (0 : F2)) [r] claim ↔ claim = 0 := by
  change Causal.tableTerminal (fun _ => (0 : F2)) (List.ofFn ![r]) claim ↔ _
  rw [Causal.tableTerminal_ofFn]
  simp [extension, eq_comm]

theorem zero_table_two (a b claim : F5) :
    Causal.tableTerminal (n := 2) (fun _ => (0 : F5)) [a, b] claim ↔ claim = 0 := by
  change Causal.tableTerminal (fun _ => (0 : F5)) (List.ofFn ![a, b]) claim ↔ _
  rw [Causal.tableTerminal_ofFn]
  simp [extension, eq_comm]

theorem initial_claim_false :
    (1 : F2) ≠ booleanSum (n := 1) (fun _ => 0) ∧
    (1 : F5) ≠ booleanSum (n := 2) (fun _ => 0) := by
  norm_num [booleanSum, half]

/-- The zero-table terminal observation on a returned endpoint. -/
def zeroClaim [Zero F] {S E : Type} (e : PIR.Execution S E (List F × F)) : Prop :=
  returnedSatisfies (fun pc => pc.2 = 0) e

theorem two_rounds_zero_mass :
    mass (do
      let e ← (PIR.repeatN 2 (roundPresent (F := F5) (G := Unit) child serviceHandle)
        ([], 1)).runM (handler zeroLow) initial
      pure (zeroClaim e)) = 9 / 25 := by
  rw [two_rounds_exact]
  simp only [bind_assoc, pure_bind, zeroClaim, returnedSatisfies]
  change Pr{let a ← ($ᵗ F5); let b ← ($ᵗ F5)}[a * b = 0] = _
  rw [← SampleableType.prEvent_uniformSample_prod (fun p : F5 × F5 => p.1 * p.2 = 0),
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun p : F5 × F5 => p.1 * p.2 = 0)).card = 9 := by
    decide
  rw [count]
  norm_num [F5]

theorem two_rounds_strict_bound :
    mass (do
      let e ← (PIR.repeatN 2 (roundPresent (F := F5) (G := Unit) child serviceHandle)
        ([], 1)).runM (handler zeroLow) initial
      pure (zeroClaim e)) < 2 / 5 := by
  rw [two_rounds_zero_mass]
  have scale := ENNReal.mul_div_mul_left (2 : ENNReal) 5
    (c := 5) (by norm_num) (by simp)
  norm_num at scale
  rw [← scale, ENNReal.div_lt_div_iff_left (by norm_num) (by simp)]
  norm_num

/-- An adversarial LOW samples early, then arranges HIGH around that old coin. -/
def earlyLow : Phase (State F2) (Event F2) F2 := fun s => do
  let x ← ($ᵗ F2)
  pure ⟨.returned x, record (.low lowSite 2 x) { s with high := 1 - x, cached := x },
    [.low lowSite 2 x]⟩

def earlyEvents (x r : F2) : List (Event F2) :=
  [.low lowSite 2 x, .high highSite 2 (1 - x), .before serviceKey,
    .after serviceKey r, .sent sendSite 2 r]

def cachedEvents (x : F2) : List (Event F2) :=
  [.low lowSite 2 x, .high highSite 2 (1 - x), .oldQuery serviceKey x,
    .sent sendSite 2 x]

theorem cached_interpolation (x : F2) : (1 - x) * x + x * (1 - x) = 0 := by
  revert x
  decide

theorem fresh_interpolation (x r : F2) :
    ((1 - r) * x + r * (1 - x) = 0) ↔ r = x := by
  revert x r
  decide

set_option backward.isDefEq.respectTransparency false in
theorem early_cached_exact (s : State F2) :
    (roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (network earlyLow) s = (do
      let x ← ($ᵗ F2)
      pure ⟨.returned ([x], 0), ⟨x, x, s.history ++ cachedEvents x⟩,
        cachedEvents x⟩) := by
  simp [roundPresent, PIR.Proc.runM, network, earlyLow,
    mapped_roles.1, high_site_distinct,
    lowSite, highSite, sendSite, serviceKey, serviceHandle, queryKey,
    record, cachedEvents, PIR.Execution.followM, List.append_assoc,
    cached_interpolation]

set_option backward.isDefEq.respectTransparency false in
theorem early_wrapped_exact (s : State F2) :
    (roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (handler earlyLow) s = (do
      let x ← ($ᵗ F2)
      let r ← ($ᵗ F2)
      pure ⟨.returned ([r], (1 - r) * x + r * (1 - x)),
        ⟨r, x, s.history ++ earlyEvents x r⟩, earlyEvents x r⟩) := by
  simp [roundPresent, PIR.Proc.runM, handler,
    query_handler (network earlyLow) before after child serviceHandle, network, earlyLow,
    mapped_roles.1, high_site_distinct,
    lowSite, highSite, sendSite, serviceKey,
    freshQuery, before, after, record, earlyEvents,
    PIR.Execution.followM, result, List.append_assoc]

theorem early_cached_mass (s : State F2) :
    mass (do
      let e ← (roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (network earlyLow) s
      pure (zeroClaim e)) = 1 := by
  rw [early_cached_exact]
  simp [zeroClaim, returnedSatisfies, mass]

theorem early_wrapped_mass (s : State F2) :
    mass (do
      let e ← (roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (handler earlyLow) s
      pure (zeroClaim e)) = 1 / 2 := by
  rw [early_wrapped_exact]
  simp only [bind_assoc, pure_bind, zeroClaim, returnedSatisfies]
  simp_rw [fresh_interpolation]
  change Pr{let x ← ($ᵗ F2); let r ← ($ᵗ F2)}[r = x] = _
  rw [← SampleableType.prEvent_uniformSample_prod (fun p : F2 × F2 => p.2 = p.1),
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun p : F2 × F2 => p.2 = p.1)).card = 2 := by decide
  rw [count]
  norm_num [F2]
  have cancel := ENNReal.mul_div_mul_left (1 : ENNReal) 2
    (c := 2) (by norm_num) (by simp)
  norm_num at cancel
  exact cancel

/-- The endpoint observation is exactly the zero public-table observation. -/
theorem two_rounds_table_acceptance :
    mass (do
      let e ← (PIR.repeatN 2 (roundPresent (F := F5) (G := Unit) child serviceHandle)
        ([], 1)).runM (handler zeroLow) initial
      pure (Causal.accepts (Causal.tableTerminal (n := 2) (fun _ => (0 : F5))) e)) =
        9 / 25 := by
  have same := two_rounds_zero_mass
  rw [two_rounds_exact] at same ⊢
  simpa only [bind_assoc, pure_bind, Causal.accepts, zero_table_two,
    zeroClaim, returnedSatisfies] using same

theorem early_table_acceptance (s : State F2) :
    mass (do
      let e ← (roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (network earlyLow) s
      pure (Causal.accepts (Causal.tableTerminal (n := 1) (fun _ => (0 : F2))) e)) = 1 ∧
    mass (do
      let e ← (roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (handler earlyLow) s
      pure (Causal.accepts (Causal.tableTerminal (n := 1) (fun _ => (0 : F2))) e)) =
        1 / 2 := by
  constructor
  · have same := early_cached_mass s
    rw [early_cached_exact] at same ⊢
    simpa only [bind_assoc, pure_bind, Causal.accepts, zero_table_one,
      zeroClaim, returnedSatisfies] using same
  · have same := early_wrapped_mass s
    rw [early_wrapped_exact] at same ⊢
    simpa only [bind_assoc, pure_bind, Causal.accepts, zero_table_one,
      zeroClaim, returnedSatisfies] using same

/-- A returned-outcome observer separates the actual old and wrapped processes. -/
theorem early_query_not_uniform (s : State F2) :
    ¬ SameDist
      ((roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (network earlyLow) s)
      ((roundPresent (G := Unit) child serviceHandle ([], (1 : F2))).runM
        (handler earlyLow) s) := by
  intro same
  have observed := same.bind_left (fun e => pure (zeroClaim e))
  have unequal := congrArg (fun measure => measure {True}) observed
  change mass _ = mass _ at unequal
  rw [early_cached_mass, early_wrapped_mass] at unequal
  have inverse := congrArg (fun x : ENNReal => x⁻¹) unequal
  norm_num at inverse

/-- The general transport bound also applies to every network and callback
state at this actual mapped child route; no honest-message premise is supplied. -/
theorem arbitrary_network_two_round_bound
    (net : PIR.MonadHandler ProbComp (participantInterface F5 Unit) S E)
    (pre : Key → Phase S E Unit) (post : Key → F5 → Phase S E Unit) (s : S) :
    mass (do
      let e ← (PIR.repeatN 2 (roundPresent (G := Unit) child serviceHandle)
        ([], (1 : F5))).runM (withUniformQueries net [serviceKey] pre post) s
      pure (Causal.accepts (Causal.rawTerminal 2 [0, 0, 0, 0]) e)) ≤ 2 / 5 := by
  have decoded : ofList? 2 ([0, 0, 0, 0] : List F5) = some (fun _ => 0) := by decide
  simpa [serviceKey] using
    repeat_uniform_publicTable_soundness net pre post child serviceHandle 2
      [0, 0, 0, 0] (fun _ => 0) decoded 1 (by norm_num) s

end FiniteWitnesses

end TestsSecurity.CausalSumcheck.Iteration
