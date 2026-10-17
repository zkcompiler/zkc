module

public import ZkcSecurity.Examples.CausalSumcheck.Terminal
public import TestsSecurity.CausalSumcheck.Handlers

@[expose] public section

namespace TestsSecurity.CausalSumcheck.Contracts
open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open OracleComp OracleSpec Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear Zkc.Polynomial.Multilinear ZkcSecurity.Examples.CausalSumcheck
open TestsSecurity.CausalSumcheck.Handlers
open scoped ENNReal

noncomputable local instance : SampleableType F := SampleableType.ofFintype _

/-- At the reachable state false the query uses a bijective postprocessing.
The unreachable true state is deliberately a constant challenge provider. -/
noncomputable def postprocessedHandler : PIR.MonadHandler ProbComp Actual Bool String
  | .receive (.field _) site _, s =>
      pure ⟨.returned (if site = names.low then 0 else 1), s, [site]⟩
  | .receive _ _ _, s => pure ⟨.stopped .refused, s, ["unexpected"]⟩
  | .query _ _ _, s =>
      if s then pure ⟨.returned (0 : F), s, ["query"]⟩
      else do
        let r ← ($ᵗ F)
        pure ⟨.returned (1-r), s, ["query"]⟩
  | .send .., s => pure ⟨.returned (), s, ["delivered"]⟩

def afterQuery (_ : F) : Phase Bool String Unit := fun s =>
  pure ⟨.returned (), s, ["query"]⟩

theorem postprocessed_local_law (s : Bool) (reachable : s = false) :
    SameDist ((participantActions F F (queryAction names.query 7)).runM postprocessedHandler s)
      (freshQuery (F := F) noOp afterQuery s) := by
  subst s
  let : MeasurableSpace (PIR.Execution Bool String F) := ⊤
  simp only [SameDist, participantActions, PIR.Proc.runM, postprocessedHandler,
    Bool.false_eq_true, ite_eq_right, not_false_eq_true, freshQuery, noOp,
    result, PIR.Execution.followM, afterQuery, bind_assoc, pure_bind, List.nil_append,
    List.append_nil]
  dsimp only [services] at *
  exact evalDist_bind_bijective_of_uniform ($ᵗ F) SampleableType.evalDist_uniformSample
    (fun r : F => 1-r)
    (show Function.Involutive (fun r : F => 1-r) from fun r => by ring).bijective
    (fun r => pure (⟨.returned r, false, ["query"]⟩ : PIR.Execution Bool String F))

theorem reachable_prefix :
    Reaches ((queryPrefix (.silent Actual) (participantActions F F) names (1 : F)).runM
      postprocessedHandler false) (fun _ s => s = false) := by
  simp only [queryPrefix, SiteObservations.silent, participantActions, PIR.Proc.bind,
    PIR.Proc.runM, postprocessedHandler, names, boundary]
  simp [PIR.Execution.followM, PIR.Proc.runM, Reaches]

/-- The weaker interface is used by the final theorem, including the bad state
which the premise correctly excludes. No syntactic query equality is supplied. -/
theorem postprocessed_round_bound :
    mass (acceptanceOf postprocessedHandler
      (calculatedRound (.silent Actual) (participantActions F F) names 7 (1 : F)
        tail (fun _ _ => .done ())) false (tableTerminal zeroTable)) ≤ (1 : ENNReal)/2 := by
  have bound := calculatedRound_soundness (.silent Actual) (participantActions F F)
    postprocessedHandler names tail (fun _ _ => .done ()) noOp afterQuery
    7 1 false (fun _ s => s = false) reachable_prefix
    (fun _ s hs => postprocessed_local_law s hs) zeroTable
    (by simp [zeroTable, booleanSum, half])
  simpa [F] using bound

/-- Exact reply marginal for the early-coin negative control: it is uniform even
though LOW and the residual query state are correlated with that same coin. -/
theorem early_query_marginal :
    (do let e ← (participant 1).runM earlyHandler 0
        pure e.state) = ($ᵗ F) := by
  rw [early_execution]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Direct marginal of the actual query result at the proved canonical cut.
Both receives and the guard precede this action; no final-state proxy is used. -/
theorem early_actual_query_marginal :
    (do let e ← ((queryPrefix (.silent Actual) (participantActions F F) names (1 : F)).bind
          (fun _ => participantActions F F (queryAction names.query 7))).runM earlyHandler 0
        pure e.outcome) = (do let r ← ($ᵗ F); pure (PIR.Outcome.returned r)) := by
  have passed (r : F) : boundary (r, 1-r) = 1 := by dsimp [boundary]; ring
  simp [queryPrefix, SiteObservations.silent, participantActions, PIR.Proc.bind,
    PIR.Proc.runM, PIR.Execution.followM, earlyHandler, names, passed]

set_option backward.isDefEq.respectTransparency false in
/-- The state projected above is precisely the reply reused at the query. -/
theorem early_query_reply (s : F) :
    (participantActions F F (queryAction names.query 7)).runM earlyHandler s =
      pure (⟨.returned s, s, ["reused-query"]⟩ : PIR.Execution F String F) := by
  simp [participantActions, PIR.Proc.runM, earlyHandler, PIR.Execution.followM]

/-- A constant-challenge provider cannot implement the fresh-query contract. -/
theorem constant_high_not_factorizable :
    ¬ ∃ (before : Phase F String Unit) (after : F → Phase F String Unit),
      ∀ s, (participantActions F F (queryAction names.query 7)).runM constantChallengeHandler s =
        freshQuery (F := F) before after s := by
  rintro ⟨before, after, law⟩
  have bound := one_round_soundness (.silent Actual) (participantActions F F)
    constantChallengeHandler names before after tail tail tables 7 1 0 law zeroTable
    (by simp [zeroTable, booleanSum, half])
  apply constant_challenge_exceeds_bound
  simpa only [acceptedGame, participant, acceptanceOf] using bound

/-- Positive full canonical fragment control, now including typed arithmetic and append. -/
theorem calculated_honest_mass :
    mass (acceptanceOf honestHandler
      (calculatedRound (.silent Actual) (participantActions F F) names 7 (0 : F)
        tail (fun _ _ => .done ())) 0 (tableTerminal zeroTable)) = 1 := by
  rw [calculatedRound_eq]
  simpa only [participant, scalarRound_eq, tail] using honest_participant_mass

/-- The unreachable true flag really violates the full-distribution query law. -/
theorem bad_state_not_fresh :
    ¬ SameDist ((participantActions F F (queryAction names.query 7)).runM postprocessedHandler true)
      (freshQuery (F := F) noOp afterQuery true) := by
  intro same
  have obs := same.bind_left (fun e => pure (e.outcome = .returned (0 : F)))
  have left : mass (do
      let e ← (participantActions F F (queryAction names.query 7)).runM postprocessedHandler true
      pure (e.outcome = .returned (0 : F))) = 1 := by
    simp [participantActions, PIR.Proc.runM, postprocessedHandler, PIR.Execution.followM, mass]
  have right : mass (do
      let e ← freshQuery (F := F) noOp afterQuery true
      pure (e.outcome = .returned (0 : F))) = (1 : ENNReal)/2 := by
    simp only [freshQuery, noOp, result, afterQuery, PIR.Execution.followM,
      bind_assoc, pure_bind, List.nil_append, List.append_nil, PIR.Outcome.returned.injEq]
    change Pr{let r ← ($ᵗ F)}[r = 0] = _
    rw [SampleableType.prEvent_uniformSample_eq_singleton]
    norm_num [F]
  dsimp only [services] at *
  have impossible : (1 : ENNReal) ≤ 1/2 :=
    le_of_eq (left.symm.trans ((congrArg (fun μ => μ {True}) obs).trans right))
  norm_num at impossible

theorem calculated_early_mass :
    mass (acceptanceOf earlyHandler
      (calculatedRound (.silent Actual) (participantActions F F) names 7 (1 : F)
        tail (fun _ _ => .done ())) 0 (tableTerminal zeroTable)) = 1 := by
  rw [calculatedRound_eq]
  simpa only [acceptedGame, acceptanceOf, participant, scalarRound_eq, tail] using early_handler_mass

/-- Even the weaker reachable full-distribution law excludes the early sampler.
The marginal theorem above therefore cannot discharge the new interface. -/
theorem early_reachable_not_factorizable :
    ¬ ∃ (invariant : Message F → F → Prop)
      (before : Phase F String Unit) (after : F → Phase F String Unit),
      Reaches ((queryPrefix (.silent Actual) (participantActions F F) names (1 : F)).runM
        earlyHandler 0) invariant ∧
      (∀ pair s, invariant pair s → SameDist
        ((participantActions F F (queryAction names.query 7)).runM earlyHandler s)
        (freshQuery (F := F) before after s)) := by
  rintro ⟨invariant, before, after, reachable, law⟩
  have bound := calculatedRound_soundness (.silent Actual) (participantActions F F)
    earlyHandler names tail (fun _ _ => .done ()) before after
    7 1 0 invariant reachable law zeroTable (by simp [zeroTable, booleanSum, half])
  rw [calculated_early_mass] at bound
  norm_num [F] at bound

/-- Compose two adaptive query steps with invariant false. The generic hybrid
law transfers reachability across the first full-distribution replacement. -/
theorem postprocessed_two_queries :
    SameDist
      (do let e ← (participantActions F F (queryAction names.query 7)).runM postprocessedHandler false
          e.followM fun _ s =>
            (participantActions F F (queryAction names.query 7)).runM postprocessedHandler s)
      (do let e ← freshQuery (F := F) noOp afterQuery false
          e.followM fun _ s => freshQuery (F := F) noOp afterQuery s) := by
  have reachesFresh : Reaches (freshQuery (F := F) noOp afterQuery false)
      (fun _ s => s = false) := by
    intro e he a ha
    simp [freshQuery, noOp, afterQuery, result, PIR.Execution.followM] at he
    obtain ⟨r, _, he⟩ := he
    rfl
  have same := postprocessed_local_law false rfl
  exact same.follow_congr (fun _ s => s = false) _ _
    ((same.reaches_iff _).mpr reachesFresh) (fun _ s hs => postprocessed_local_law s hs)

end TestsSecurity.CausalSumcheck.Contracts
