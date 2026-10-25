module

public import ZkcArkLib.Sumcheck.Multilinear.Causal.Phase

@[expose] public section


namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal

open OracleComp OracleSpec
open Zkc.Protocols.Sumcheck.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open Zkc.Polynomial.Multilinear
open _root_.Interaction.Oracle _root_.Sumcheck.Interaction
open ZkcSecurity.VCVio.Execution
open scoped ENNReal

variable {F S E K : Type}
variable [Field F] [DecidableEq F]

def observeFollow {A : Type} (r : PIR.Execution S E A)
    (next : A → S → ProbComp Prop) : ProbComp Prop :=
  match r.outcome with
  | .stopped _ => pure False
  | .returned a => next a r.state

omit [Field F] [DecidableEq F] in
theorem observe_follow {A : Type} (r : PIR.Execution S E A)
    (next : A → S → ProbComp (PIR.Execution S E (List F × F)))
    (terminal : List F → F → Prop) :
    (do let e ← r.followM next; return accepts terminal e) =
      observeFollow r (fun a s => do let e ← next a s; return accepts terminal e) := by
  rcases r with ⟨outcome, s, events⟩
  cases outcome with
  | stopped why => rfl
  | returned a =>
      simp only [PIR.Execution.followM, bind_assoc, pure_bind, observeFollow]
      apply bind_congr
      intro e
      cases e with | mk out state es => cases out <;> rfl

theorem phaseGame_succ [SampleableType F] (n : Nat) (claim : F) (point : List F)
    (strategy : Strategy F S E (n+1)) (s : S) (terminal : List F → F → Prop) :
    phaseGame (n+1) claim point strategy s terminal = (do
      let ready ← prepare claim strategy s
      observeFollow ready fun (pair, tail) s =>
        if boundary pair = claim then do
          let r ← ($ᵗ F)
          let queried ← tail.afterDraw r s
          observeFollow queried fun _ s => do
            let sent ← tail.deliver r s
            observeFollow sent fun next s => do
              let advanced ← tail.advance r s
              observeFollow advanced fun _ s => phaseGame n (evaluate pair r) (point ++ [r]) next s terminal
        else do
          let _ ← tail.publicAbort s
          pure False) := by
  simp only [phaseGame, run, bind_assoc]
  apply bind_congr
  intro ready
  rw [observe_follow]
  cases ready with | mk out s es =>
    cases out with
    | stopped why => rfl
    | returned pair =>
      simp only [observeFollow]
      split
      · simp only [bind_assoc]
        apply bind_congr; intro r
        apply bind_congr; intro queried
        rw [observe_follow]
        cases queried with | mk out s es =>
          cases out with
          | stopped why => rfl
          | returned u =>
            simp only [observeFollow, bind_assoc]
            apply bind_congr; intro sent
            rw [observe_follow]
            cases sent with | mk out s es =>
              cases out with
              | stopped why => rfl
              | returned next =>
                simp only [observeFollow, bind_assoc]
                apply bind_congr; intro advanced
                rw [observe_follow]
                rfl
      · simp only [bind_assoc, pure_bind, stopped, accepts]

/-- Unconditional domination for every finite number of rounds. No successful
    delivery conditioning or normalization occurs anywhere in this statement. -/
theorem domination [SampleableType F] (n : Nat) (claim : F) (point : List F)
    (strategy : Strategy F S E n) (s : S) (terminal : List F → F → Prop) :
    mass (phaseGame n claim point strategy s terminal) ≤
      mass (endpointGame n claim point (complete n claim strategy s) terminal) := by
  induction n generalizing claim point s with
  | zero =>
      simp only [phaseGame, run, endpointGame, bind_assoc]
      change mass (do let checked ← strategy s
                      let e ← checked.followM (fun _ s => pure (result (point, claim) s))
                      pure (accepts terminal e)) ≤ mass (pure (terminal point claim))
      have h := mass_bind_mono (strategy s)
        (fun checked => do
          let e ← checked.followM (fun _ s => pure (result (point, claim) s))
          pure (accepts terminal e)) (fun _ => pure (terminal point claim)) (by
            intro checked
            cases checked with | mk out s es =>
              cases out with
              | stopped why => simp [PIR.Execution.followM, accepts]
              | returned u => simp [PIR.Execution.followM, result, accepts])
      simpa only [mass, OracleComp.evalDist_bind_const] using h
  | succ n ih =>
    rw [phaseGame_succ]
    simp only [endpointGame, complete, bind_assoc]
    apply mass_bind_mono
    intro ready
    cases ready with | mk out s es =>
      cases out with
      | stopped why => simp only [observeFollow, mass_false]; exact zero_le
      | returned value =>
        rcases value with ⟨pair, tail⟩
        simp only [observeFollow, pure_bind]
        split
        · apply mass_bind_mono
          intro r
          simp only [bind_assoc]
          apply mass_bind_mono
          intro queried
          cases queried with | mk out s es =>
            cases out with
            | stopped why => simp only [mass_false]; exact zero_le
            | returned u =>
              simp only [bind_assoc]
              apply mass_bind_mono
              intro sent
              cases sent with | mk out s es =>
                cases out with
                | stopped why => simp only [mass_false]; exact zero_le
                | returned next =>
                  simp only [bind_assoc]
                  apply mass_bind_mono
                  intro advanced
                  cases advanced with | mk out s es =>
                    cases out with
                    | stopped why => simp only [mass_false]; exact zero_le
                    | returned u =>
                      exact ih (evaluate pair r) (point ++ [r]) next s
        · simp only [bind_assoc]
          exact le_rfl

/-- A caller's capacity filter can exclude observations without conditioning or
    resampling the protocol. This is distinct from a delivery stop in run. -/
theorem observer_capacity_exclusion [SampleableType F] (n : Nat) (claim : F)
    (point : List F) (strategy : Strategy F S E n) (s : S)
    (terminal : List F → F → Prop) (allowed : PIR.Execution S E (List F × F) → Prop) :
    mass (do let e ← run n claim point strategy s
             pure (allowed e ∧ accepts terminal e)) ≤
      mass (phaseGame n claim point strategy s terminal) := by
  apply mass_bind_mono
  intro e
  by_cases a : allowed e <;> by_cases b : accepts terminal e <;> simp [a, b, mass]

/-- Integration over outer histories does not establish freshness: each chosen
    strategy already has a new draw after every reached prefix. A separate
    false-claim premise is required per supported history for a numeric bound. -/
theorem history_domination [SampleableType F] {H : Type} (histories : ProbComp H)
    (n : Nat) (claim : H → F) (point : H → List F) (strategy : H → Strategy F S E n)
    (state : H → S) (terminal : H → List F → F → Prop) :
    mass (do let history ← histories
             phaseGame n (claim history) (point history) (strategy history) (state history)
               (terminal history)) ≤
    mass (do let history ← histories
             endpointGame n (claim history) (point history)
               (complete n (claim history) (strategy history) (state history)) (terminal history)) := by
  apply mass_bind_mono
  intro history
  exact domination n (claim history) (point history) (strategy history) (state history) (terminal history)


end ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal
