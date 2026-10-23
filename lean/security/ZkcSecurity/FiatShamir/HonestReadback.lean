module

public import ZkcSecurity.FiatShamir.HonestCompiled
public import Zkc.Construction.DomainExecutionLaws

@[expose] public section

/-! Successful read-back of actual constructed producer and validator Processes.

This derivation relates existing Process terms. Its theorem uses the existing
Domain handlers and runner, including all checkpoints, observations, full
returns and proof buffers. It defines no protocol evaluator. A query rule
requires the very same history and nominal origin on both sides and covers
every typed reply. Stopping computations have no successful terminal rule.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir
open Zkc.Source Zkc.Construction OracleComp OracleSpec

variable {carriers : Structured.Carriers} {A B C D : Type}

inductive Readback (Post : A → B → Prop) :
    PIR.Process (Domain.effects carriers) A → PIR.Process (Domain.effects carriers) B → Prop
  | done {left right} : Post left right → Readback Post (.done left) (.done right)
  | checkpointLeft {left right} (environment : Domain.Environment carriers) :
      Readback Post left right →
      Readback Post (.call (.checkpoint environment) (fun _ => left)) right
  | checkpointRight {left right} (environment : Domain.Environment carriers) :
      Readback Post left right →
      Readback Post left (.call (.checkpoint environment) (fun _ => right))
  | observeLeft {left right} (event : Domain.Event carriers) :
      Readback Post left right → Readback Post (.call (.observe event) (fun _ => left)) right
  | observeRight {left right} (event : Domain.Event carriers) :
      Readback Post left right → Readback Post left (.call (.observe event) (fun _ => right))
  | sendReceive {ty : Structured.Ty} {left : PIR.Process (Domain.effects carriers) A}
      {next : carriers.Value ty → PIR.Process (Domain.effects carriers) B}
      (site schema peer receiveSite receiveSchema receivePeer : String)
      (payload : Domain.Payload carriers) (value : carriers.Value ty)
      (decoded : payload.value ty = some value) :
      Readback Post left (next value) →
      Readback Post (.call (.send site schema peer payload) (fun _ => left))
        (.call (.receive ty receiveSite receiveSchema receivePeer) next)
  | sendRight {left right} (site schema peer : String) (payload : Domain.Payload carriers) :
      Readback Post left right →
      Readback Post left (.call (.send site schema peer payload) (fun _ => right))
  | query (history : Domain.History carriers) (origin : Origin)
      {left : Domain.Raw (.challenge origin : Domain.Event carriers) →
        PIR.Process (Domain.effects carriers) A}
      {right : Domain.Raw (.challenge origin : Domain.Event carriers) →
        PIR.Process (Domain.effects carriers) B}
      (supported : Domain.drawRequest origin = true) :
      (∀ reply : Domain.Raw (.challenge origin : Domain.Event carriers),
        Readback Post (left reply) (right reply)) →
      Readback Post (.call (.query history origin) left) (.call (.query history origin) right)

namespace Readback

/-- Sequential read-back carries actual returned values to both continuations.
Captures and the next child's history are therefore ordinary caller data. -/
theorem bind {Post : A → B → Prop} {Final : C → D → Prop}
    {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process (Domain.effects carriers) B}
    (aligned : Readback Post left right)
    (nextLeft : A → PIR.Process (Domain.effects carriers) C)
    (nextRight : B → PIR.Process (Domain.effects carriers) D)
    (next : ∀ a b, Post a b → Readback Final (nextLeft a) (nextRight b)) :
    Readback Final (left.bind nextLeft) (right.bind nextRight) := by
  induction aligned with
  | done holds => exact next _ _ holds
  | checkpointLeft environment _ ih => exact .checkpointLeft environment ih
  | checkpointRight environment _ ih => exact .checkpointRight environment ih
  | observeLeft event _ ih => exact .observeLeft event ih
  | observeRight event _ ih => exact .observeRight event ih
  | sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded _ ih =>
      exact .sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded ih
  | sendRight site schema peer payload _ ih => exact .sendRight site schema peer payload ih
  | query history origin supported _ ih => exact .query history origin supported ih

/-- Strengthen only the mathematical conclusion, preserving both complete
open processes and all typed replies. -/
theorem mono {Post Final : A → B → Prop}
    {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process (Domain.effects carriers) B}
    (aligned : Readback Post left right) (implies : ∀ a b, Post a b → Final a b) :
    Readback Final left right := by
  induction aligned with
  | done holds => exact .done (implies _ _ holds)
  | checkpointLeft environment _ ih => exact .checkpointLeft environment ih
  | checkpointRight environment _ ih => exact .checkpointRight environment ih
  | observeLeft event _ ih => exact .observeLeft event ih
  | observeRight event _ ih => exact .observeRight event ih
  | sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded _ ih =>
      exact .sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded ih
  | sendRight site schema peer payload _ ih => exact .sendRight site schema peer payload ih
  | query history origin supported _ ih => exact .query history origin supported ih

/-- Exact proof-prefix consumption under one deterministic keyed table. Both
full executions return, with every final environment and observation exposed.
Any supplied suffix survives unchanged, so complete runs take suffix `[]`. -/
theorem run {Post : A → B → Prop}
    {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process (Domain.effects carriers) B}
    (aligned : Readback Post left right)
    (answers : QueryImpl (HonestCompiled.Spec carriers) Id)
    (leftEnvironment rightEnvironment : Domain.Environment carriers)
    (preceding suffix : Domain.Proof carriers) :
    ∃ leftValue rightValue leftFinal rightFinal leftEvents rightEvents emitted,
      left.run (Domain.handler .producer (HonestCompiled.tableOracle answers))
        ⟨leftEnvironment, preceding, ()⟩ =
          ⟨.returned leftValue, ⟨leftFinal, preceding ++ emitted, ()⟩, leftEvents⟩ ∧
      right.run (Domain.handler .validator (HonestCompiled.tableOracle answers))
        ⟨rightEnvironment, emitted ++ suffix, ()⟩ =
          ⟨.returned rightValue, ⟨rightFinal, suffix, ()⟩, rightEvents⟩ ∧
      Post leftValue rightValue := by
  induction aligned generalizing leftEnvironment rightEnvironment preceding suffix with
  | done holds =>
      exact ⟨_, _, leftEnvironment, rightEnvironment, [], [], [], by simp [PIR.Process.run],
        rfl, holds⟩
  | checkpointLeft environment aligned ih =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        ih environment rightEnvironment preceding suffix
      exact ⟨a, b, l, r, le, re, emitted,
        by
          simp only [PIR.Process.run, Domain.handler]
          dsimp only [Bind.bind, Pure.pure]
          simpa only [PIR.Execution.follow, List.nil_append] using lp,
        rp, post⟩
  | checkpointRight environment aligned ih =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        ih leftEnvironment environment preceding suffix
      exact ⟨a, b, l, r, le, re, emitted, lp,
        by
          simp only [PIR.Process.run, Domain.handler]
          dsimp only [Bind.bind, Pure.pure]
          simpa only [PIR.Execution.follow, List.nil_append] using rp,
        post⟩
  | observeLeft event aligned ih =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        ih leftEnvironment rightEnvironment preceding suffix
      exact ⟨a, b, l, r, event :: le, re, emitted,
        by
          simp only [PIR.Process.run, Domain.handler]
          dsimp only [Bind.bind, Pure.pure]
          simp only [PIR.Execution.follow, lp, List.singleton_append], rp, post⟩
  | observeRight event aligned ih =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        ih leftEnvironment rightEnvironment preceding suffix
      exact ⟨a, b, l, r, le, event :: re, emitted, lp,
        by
          simp only [PIR.Process.run, Domain.handler]
          dsimp only [Bind.bind, Pure.pure]
          simp only [PIR.Execution.follow, rp, List.singleton_append], post⟩
  | sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded aligned ih =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        ih leftEnvironment rightEnvironment (preceding ++ [payload]) suffix
      refine ⟨a, b, l, r, le, re, payload :: emitted, ?_, ?_, post⟩
      · simp only [PIR.Process.run, Domain.handler]
        dsimp only [Bind.bind, Pure.pure]
        simpa only [PIR.Execution.follow, List.nil_append, List.append_assoc,
          List.singleton_append] using lp
      · simp only [List.cons_append, PIR.Process.run, Domain.handler, decoded]
        dsimp only [Bind.bind, Pure.pure]
        simpa only [PIR.Execution.follow, List.nil_append] using rp
  | sendRight site schema peer payload aligned ih =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        ih leftEnvironment rightEnvironment preceding suffix
      exact ⟨a, b, l, r, le, re, emitted, lp,
        by
          simp only [PIR.Process.run, Domain.handler]
          dsimp only [Bind.bind, Pure.pure]
          simpa only [PIR.Execution.follow, List.nil_append] using rp,
        post⟩
  | query history origin supported aligned ih =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        ih (Typed.readTable (R := Typed.ByLast Domain.Raw) (fun key => answers key) history
          (.challenge origin)) leftEnvironment rightEnvironment preceding suffix
      exact ⟨a, b, l, r, .challenge origin :: le, .challenge origin :: re, emitted,
        by
          simp only [PIR.Process.run, Domain.handler, supported, ite_true, HonestCompiled.tableOracle]
          dsimp only [Bind.bind, Pure.pure]
          simp only [PIR.Execution.follow, lp, List.singleton_append],
        by
          simp only [PIR.Process.run, Domain.handler, supported, ite_true, HonestCompiled.tableOracle]
          dsimp only [Bind.bind, Pure.pure]
          simp only [PIR.Execution.follow, rp, List.singleton_append], post⟩

end Readback

/-- Successful read-back is a full compiled pair execution on one keyed
answer table. The producer starts with empty output and the validator consumes
exactly that output; the result retains both actual final frames and events. -/
theorem Readback.pair_success (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat)
    (aligned : Readback
      (fun _ result => HonestCompiled.acceptanceAt position result.values = some true)
      (Domain.participant model program context producer producerInputs)
      (Domain.participant model program context validator validatorInputs))
    (answers : QueryImpl (HonestCompiled.Spec model.toCarriers) Id) :
    HonestCompiled.Success position
      (Domain.executePair model program context producer validator producerInputs validatorInputs
        (HonestCompiled.tableOracle answers) ()) := by
  obtain ⟨left, right, leftFinal, rightFinal, leftEvents, rightEvents, proof,
    produced, validated, accepted⟩ := aligned.run answers producerInputs validatorInputs [] []
  simp only [List.nil_append, List.append_nil] at produced validated
  have produceLaw : Domain.produce model program context producer producerInputs
      (HonestCompiled.tableOracle answers) () =
      ⟨.returned left, ⟨leftFinal, proof, ()⟩, leftEvents⟩ := by
    exact (PIR.runM_pure (m := Id)
      (Domain.handler .producer (HonestCompiled.tableOracle answers))
      (Domain.participant model program context producer producerInputs)
      ⟨producerInputs, [], ()⟩).trans produced
  have validateLaw : Domain.validate model program context validator validatorInputs proof
      (HonestCompiled.tableOracle answers) () =
      ⟨.returned right, ⟨rightFinal, [], ()⟩, rightEvents⟩ := by
    exact (PIR.runM_pure (m := Id)
      (Domain.handler .validator (HonestCompiled.tableOracle answers))
      (Domain.participant model program context validator validatorInputs)
      ⟨validatorInputs, proof, ()⟩).trans validated
  simp only [Domain.executePair, produceLaw, Bind.bind, Pure.pure]
  rw [validateLaw]
  exact ⟨left, _, right, rfl, rfl, rfl, rfl, accepted⟩

end ZkcSecurity.FiatShamir
