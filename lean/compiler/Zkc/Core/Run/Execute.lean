module

public import Zkc.Core.Run.Run
public import Zkc.Core.Scheme.Deploy
public import Zkc.Core.Statements

@[expose] public section

/-!
The total, fuel-bounded Lean reference executor for deployed roles and two-party interactive
protocols.

This module provides:
1. `runProcess`: total fuel-bounded execution of any `Process (RSig M) Stop (A × G)` against a
   `Source M`, with exact soundness (`runProcess_sound`) and completeness (`runProcess_complete`)
   relative to `Alone` and `AlonePrefix`.
2. `execute`: an `Executor V` for `Deployed V` proving `Statements.executorRuns` in full.
3. `executePlanProver`, `executePlanVerifier`, `provePlan`, `verifyPlan`, and
   `proveAndVerifyPlan`: end-to-end execution of a validated `DeploymentPlan`, together with
   `deploy_execute_complete`.
4. `runInteractive`: a deterministic fuel-bounded scheduler for executing two projected online
   roles against a shared `Pending` network and `Source`.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-! ## Fuel-bounded single-role execution -/

/-- Run a single role's process against `source` for at most `limit` effect steps.
Returning, halting, or waiting on an unhandled `.get` finishes immediately; running out of
fuel or encountering an unanswered `source` returns `.limit` with the legal prefix executed
so far, and never `.failed`. -/
def runProcess (source : Source M) (r : Role) {A G : Type} :
    Process (RSig M) Stop (A × G) → Nat → Outcome A G × List (Happened M)
  | .done res, _ => (.ended (.returned res), [])
  | .halt why, _ => (.ended (.stopped why), [])
  | .call (.get _ _ at_ _) _, _ => (.ended (.blocked at_), [])
  | .call (.give ..) _, 0 => (.limit, [])
  | .call (.own ..) _, 0 => (.limit, [])
  | .call (.hear ..) _, 0 => (.limit, [])
  | .call (.begin _) _, 0 => (.limit, [])
  | .call (.settle _) _, 0 => (.limit, [])
  | .call (.give kind getters at_ τ x) k, n + 1 =>
      let (out, rec) := runProcess source r (k ()) n
      (out, .gave r kind getters at_ τ x :: rec)
  | .call (.own kind _ at_ _ _ τ) k, n + 1 =>
      match source at_ τ with
      | some v =>
          let (out, rec) := runProcess source r (k v) n
          (out, .owned r kind at_ τ v :: rec)
      | none => (.limit, [])
  | .call (.hear kind owner at_ τ) k, n + 1 =>
      match source at_ τ with
      | some v =>
          let (out, rec) := runProcess source r (k v) n
          (out, .heard r kind owner at_ τ v :: rec)
      | none => (.limit, [])
  | .call (.begin at_) k, n + 1 =>
      let (out, rec) := runProcess source r (k 0) n
      (out, .began r at_ :: rec)
  | .call (.settle at_) k, n + 1 =>
      let (out, rec) := runProcess source r (k ()) n
      (out, .settled r at_ :: rec)

/-- Soundness of `runProcess`: every `.ended` result witnesses an `Alone` derivation, every
`.limit` result witnesses an `AlonePrefix`, and `.failed` is never returned. -/
theorem runProcess_sound (source : Source M) (r : Role) {A G : Type} :
    ∀ (limit : Nat) (p : Process (RSig M) Stop (A × G)),
      match runProcess M source r p limit with
      | (.ended ending, record) => Alone M source r p record ending
      | (.limit, record) => AlonePrefix M source r p record
      | (.failed _, _) => False
  | 0, .done _ => Alone.done
  | 0, .halt _ => Alone.halt
  | 0, .call (.get ..) _ => Alone.waits
  | 0, .call (.give ..) _ => AlonePrefix.start
  | 0, .call (.own ..) _ => AlonePrefix.start
  | 0, .call (.hear ..) _ => AlonePrefix.start
  | 0, .call (.begin _) _ => AlonePrefix.start
  | 0, .call (.settle _) _ => AlonePrefix.start
  | _ + 1, .done _ => Alone.done
  | _ + 1, .halt _ => Alone.halt
  | _ + 1, .call (.get ..) _ => Alone.waits
  | n + 1, .call (.give kind getters at_ τ x) k => by
      have ih := runProcess_sound source r n (k ())
      simp only [runProcess]
      cases h : runProcess M source r (k ()) n with
      | mk out rec =>
          rw [h] at ih
          cases out with
          | ended ending => exact Alone.give ih
          | limit => exact AlonePrefix.give ih
          | failed _ => exact ih
  | n + 1, .call (.own kind hearers at_ ins payload τ) k => by
      simp only [runProcess]
      cases hsrc : source at_ τ with
      | none => exact AlonePrefix.start
      | some v =>
          dsimp only
          have ih := runProcess_sound source r n (k v)
          cases h : runProcess M source r (k v) n with
          | mk out rec =>
              rw [h] at ih
              dsimp only
              cases out with
              | ended ending => exact Alone.own hsrc ih
              | limit => exact AlonePrefix.own hsrc ih
              | failed _ => exact ih
  | n + 1, .call (.hear kind owner at_ τ) k => by
      simp only [runProcess]
      cases hsrc : source at_ τ with
      | none => exact AlonePrefix.start
      | some v =>
          dsimp only
          have ih := runProcess_sound source r n (k v)
          cases h : runProcess M source r (k v) n with
          | mk out rec =>
              rw [h] at ih
              dsimp only
              cases out with
              | ended ending => exact Alone.hear hsrc ih
              | limit => exact AlonePrefix.hear hsrc ih
              | failed _ => exact ih
  | n + 1, .call (.begin at_) k => by
      have ih := runProcess_sound source r n (k 0)
      simp only [runProcess]
      cases h : runProcess M source r (k 0) n with
      | mk out rec =>
          rw [h] at ih
          cases out with
          | ended ending => exact Alone.begin ih
          | limit => exact AlonePrefix.begin ih
          | failed _ => exact ih
  | n + 1, .call (.settle at_) k => by
      have ih := runProcess_sound source r n (k ())
      simp only [runProcess]
      cases h : runProcess M source r (k ()) n with
      | mk out rec =>
          rw [h] at ih
          cases out with
          | ended ending => exact Alone.settle ih
          | limit => exact AlonePrefix.settle ih
          | failed _ => exact ih

/-- Completeness of `runProcess`: every `Alone` derivation is reproduced exactly once
`limit` reaches the number of steps in the derivation. -/
theorem runProcess_complete {source : Source M} {r : Role} {A G : Type}
    {p : Process (RSig M) Stop (A × G)} {record : List (Happened M)}
    {ending : Ending (A × G) Stop}
    (h : Alone M source r p record ending) :
    ∃ limit, runProcess M source r p limit = (.ended ending, record) := by
  induction h with
  | done => exact ⟨0, rfl⟩
  | halt => exact ⟨0, rfl⟩
  | waits => exact ⟨0, rfl⟩
  | give _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [runProcess, hn]⟩
  | own hsrc _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [runProcess, hsrc, hn]⟩
  | hear hsrc _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [runProcess, hsrc, hn]⟩
  | begin _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [runProcess, hn]⟩
  | settle _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [runProcess, hn]⟩

end

/-! ## Core `Executor` for `Deployed` -/

/-- The reference executor for a `Deployed` scheme: runs `d.run` via `runProcess`. -/
def execute {V : Vocabulary} : Executor V :=
  fun d M r ins taken source limit =>
    runProcess M source r (d.run M r ins taken) limit

/-- `execute` satisfies `Statements.executorRuns` in full. -/
theorem execute_runs {V : Vocabulary} (c : Functions V) (h : c.execute = execute) :
    Statements.executorRuns c := by
  intro d M r ins taken source
  rw [h]
  unfold execute
  refine ⟨fun limit => ?_, fun _ _ halone => runProcess_complete M halone⟩
  have hs := runProcess_sound M source r limit (d.run M r ins taken)
  cases hres : runProcess M source r (d.run M r ins taken) limit with
  | mk out rec =>
      rw [hres] at hs
      cases out <;> exact hs

/-! ## Reference execution for a `DeploymentPlan` -/

section PlanExecution
variable {V : Vocabulary} (M : Model V)

/-- Execute the deployed prover of `plan` for at most `limit` steps. -/
def executePlanProver (plan : DeploymentPlan V) (codecs : ValidCodecs M)
    (tm : TranscriptModel V M) (ins : HList (RV M plan.prover) plan.entry.ins)
    (source : Source M) (limit : Nat) :
    Outcome (HList (RV M plan.prover) plan.entry.outs) (List Nat) × List (Happened M) :=
  runProcess M source plan.prover (plan.proverProcess M codecs tm ins) limit

/-- Execute the deployed verifier of `plan` on `proof` for at most `limit` steps. -/
def executePlanVerifier (plan : DeploymentPlan V) (codecs : ValidCodecs M)
    (tm : TranscriptModel V M) (ins : HList (RV M plan.verifier) plan.entry.ins)
    (proof : List Nat) (source : Source M) (limit : Nat) :
    Outcome (HList (RV M plan.verifier) plan.entry.outs) Unit × List (Happened M) :=
  runProcess M source plan.verifier
    ((plan.verifierProcess M codecs tm ins proof).map fun outs => (outs, ())) limit

/-- Run the deployed prover of `plan`, returning the canonical proof bytes on acceptance. -/
def provePlan (plan : DeploymentPlan V) (codecs : ValidCodecs M) (tm : TranscriptModel V M)
    (ins : HList (RV M plan.prover) plan.entry.ins) (source : Source M) (limit : Nat) :
    Option (List Nat) :=
  match (executePlanProver M plan codecs tm ins source limit).1 with
  | .ended (.returned (_, proof)) => some proof
  | _ => none

/-- Run the deployed verifier of `plan` on `proof`, returning its outputs on acceptance. -/
def verifyPlan (plan : DeploymentPlan V) (codecs : ValidCodecs M) (tm : TranscriptModel V M)
    (ins : HList (RV M plan.verifier) plan.entry.ins) (proof : List Nat)
    (source : Source M) (limit : Nat) :
    Option (HList (RV M plan.verifier) plan.entry.outs) :=
  match (executePlanVerifier M plan codecs tm ins proof source limit).1 with
  | .ended (.returned (outs, ())) => some outs
  | _ => none

/-- Run the deployed prover and then the deployed verifier on the emitted proof bytes. -/
def proveAndVerifyPlan (plan : DeploymentPlan V) (codecs : ValidCodecs M)
    (tm : TranscriptModel V M) (proverIns : HList (RV M plan.prover) plan.entry.ins)
    (verifierIns : HList (RV M plan.verifier) plan.entry.ins)
    (source : Source M) (limit : Nat) :
    Option (HList (RV M plan.verifier) plan.entry.outs) :=
  (provePlan M plan codecs tm proverIns source limit).bind fun proof =>
    verifyPlan M plan codecs tm verifierIns proof source limit

/-- End-to-end executable completeness: under the hypotheses of `deploy_complete`, there
exist finite fuel budgets under which `provePlan` emits canonical proof bytes (`< 256`) and
`verifyPlan` accepts them, returning the verifier's projected outputs. -/
theorem deploy_execute_complete (plan : DeploymentPlan V) (hretry : plan.declaration.retry = none)
    (codecs : ValidCodecs M) (tm : TranscriptModel V M) (htm : tm.Lawful)
    (ins : HList (LVal M) plan.entry.ins) (source : Source M)
    (hcomp : ProtoCompatible M plan.prover plan.verifier
      (protocolMeaning M plan.admitted.program plan.callee [] ins))
    (hnohalt : ProtoNoHalt M
      (protocolMeaning M plan.admitted.program plan.callee [] ins))
    (hlaw : LawfulPrivate M source
      (protocolMeaning M plan.admitted.program plan.callee [] ins))
    (hfed : Fed M source
      (protocolMeaning M plan.admitted.program plan.callee [] ins)) :
    ∃ (out : HList (LVal M) plan.entry.outs × plan.entry.record.Val M) (proof : List Nat)
      (limitP limitV : Nat),
      (∀ b, b ∈ proof → b < 256) ∧
      provePlan M plan codecs tm (hideAll M plan.prover ins) source limitP = some proof ∧
      verifyPlan M plan codecs tm (hideAll M plan.verifier ins) proof source limitV =
        some (hideAll M plan.verifier out.1) := by
  obtain ⟨out, proof, recP, recV, hbytes, haloneP, haloneV⟩ :=
    deploy_complete M plan hretry codecs tm htm ins source hcomp hnohalt hlaw hfed
  obtain ⟨limitP, hrunP⟩ := runProcess_complete M haloneP
  have haloneV' :
      Alone M source plan.verifier
        ((plan.verifierProcess M codecs tm (hideAll M plan.verifier ins) proof).map
          fun outs => (outs, ()))
        recV (.returned (hideAll M plan.verifier out.1, ())) := by
    generalize hp : plan.verifierProcess M codecs tm (hideAll M plan.verifier ins) proof = p at haloneV ⊢
    clear hp
    generalize he : Ending.returned (hideAll M plan.verifier out.1) = end_ at haloneV
    induction haloneV with
    | done => cases he; exact .done
    | halt => cases he
    | waits => cases he
    | give _ ih => exact .give (ih he)
    | own hsrc _ ih => exact .own hsrc (ih he)
    | hear hsrc _ ih => exact .hear hsrc (ih he)
    | begin _ ih => exact .begin (ih he)
    | settle _ ih => exact .settle (ih he)
  obtain ⟨limitV, hrunV⟩ := runProcess_complete M haloneV'
  refine ⟨out, proof, limitP, limitV, hbytes, ?_, ?_⟩
  · simp only [provePlan, executePlanProver, hrunP]
  · simp only [verifyPlan, executePlanVerifier, hrunV]

/-! ## Fuel-bounded two-role interactive scheduler -/

/-- Attempt one network step for a single role `r` against `(pending, source)`. -/
def stepOneRole {A : Type} (source : Source M) (r : Role)
    (p : Program M A) (pending : Pending M) :
    Option (Program M A × Pending M × Happened M) :=
  match p with
  | .done _ => none
  | .halt _ => none
  | .call (.give kind getters at_ τ x) k =>
      some (k (), pending.post M at_ getters ⟨r, kind, τ, x⟩, .gave r kind getters at_ τ x)
  | .call (.get kind giver at_ τ) k =>
      match pending at_ r with
      | some ⟨sender, kind', τ', x⟩ =>
          if h : sender = giver ∧ kind' = kind ∧ τ' = τ then
            some (k (cast (congrArg M.Val h.2.2) x), pending.take M at_ r,
              .got r kind giver at_ τ (cast (congrArg M.Val h.2.2) x))
          else none
      | none => none
  | .call (.own kind _ at_ _ _ τ) k =>
      (source at_ τ).map fun v => (k v, pending, .owned r kind at_ τ v)
  | .call (.hear kind owner at_ τ) k =>
      (source at_ τ).map fun v => (k v, pending, .heard r kind owner at_ τ v)
  | .call (.begin at_) k =>
      some (k 0, pending, .began r at_)
  | .call (.settle at_) k =>
      some (k (), pending, .settled r at_)

/-- Convert a quiescent or fuel-exhausted role process into its `Outcome`. -/
def roleOutcome {A : Type} (fuelExhausted : Bool) : Program M A → Outcome A Unit
  | .done a => .ended (.returned (a, ()))
  | .halt why => .ended (.stopped why)
  | .call (.get _ _ at_ _) _ => if fuelExhausted then .limit else .ended (.blocked at_)
  | .call _ _ => .limit

/-- Deterministically schedule two online roles `r1` and `r2` together for at most `limit`
total steps against a shared `Pending` network and `Source`. -/
def runInteractiveAux {A B : Type} (source : Source M) (r1 r2 : Role) :
    Program M A → Program M B → Pending M → Nat →
    Outcome A Unit × Outcome B Unit × List (Happened M)
  | p1, p2, _, 0 => (roleOutcome M true p1, roleOutcome M true p2, [])
  | p1, p2, pending, n + 1 =>
      match stepOneRole M source r1 p1 pending with
      | some (p1', pending', ev) =>
          let (o1, o2, rec) := runInteractiveAux source r1 r2 p1' p2 pending' n
          (o1, o2, ev :: rec)
      | none =>
          match stepOneRole M source r2 p2 pending with
          | some (p2', pending', ev) =>
              let (o1, o2, rec) := runInteractiveAux source r1 r2 p1 p2' pending' n
              (o1, o2, ev :: rec)
          | none =>
              (roleOutcome M false p1, roleOutcome M false p2, [])

/-- Run two projected roles of an interactive protocol against `source` starting from an empty
network, for at most `limit` steps. -/
def runInteractive {A B : Type} (source : Source M) (r1 r2 : Role)
    (p1 : Program M A) (p2 : Program M B) (limit : Nat) :
    Outcome A Unit × Outcome B Unit × List (Happened M) :=
  runInteractiveAux M source r1 r2 p1 p2 (Pending.empty M) limit

end PlanExecution

end Zkc.Core
