module

public import Zkc.Construction.Uniform.SourceProcess
public import Zkc.Construction.OriginProjection
public import Zkc.Executable.DomainParticipant

@[expose] public section
/-! Handler transport for actual finite source views. Agreement is checked on
source message/query origins and on the reached nominal history, never on
arbitrary origins. The caller's initial scalar history stays opaque. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Executable.StaticSourceTransport
open Zkc.Construction Zkc.Source
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.SourceProcess
variable {F G A R : Type} {m : Type → Type} [Monad m]

theorem readback_append_message (key : Origin → Origin)
    (history : Domain.History (Structured.uniformCarriers F G))
    (origin : Origin) (payload : Payload F G) :
    readbackHistory key (history ++ [.message origin (embedPayload payload)]) =
      (readbackHistory key history).map (· ++ [.message (key origin) payload]) := by
  rw [readbackHistory_append]
  cases mapped : readbackHistory key history <;> cases payload <;> rfl

theorem readback_append_challenge (key : Origin → Origin)
    (history : Domain.History (Structured.uniformCarriers F G)) (origin : Origin) :
    readbackHistory key (history ++ [.challenge origin]) =
      (readbackHistory key history).map (· ++ [.challenge (key origin)]) := by
  rw [readbackHistory_append]
  cases readbackHistory key history <;> rfl

/-- Every source-generated suffix has scalar readback, for every reply. -/
theorem sourceView_readable (context : Context) (key : Origin → Origin)
    (process : PIR.Process (Actions F G) A)
    (history : Domain.History (Structured.uniformCarriers F G))
    (readable : (readbackHistory key history).isSome = true) :
    PIR.Yields (fun result => (readbackHistory key result.2).isSome = true)
      (sourceView context process history) := by
  induction process generalizing history with
  | done => exact readable
  | halt => trivial
  | call operation next ih =>
    cases operation with
    | receive ty site sender =>
      simp only [sourceView]
      cases ty <;> simp only [receive, PIR.Process.bind, PIR.Yields]
      all_goals intro value reply; apply ih; rw [readbackHistory_append]; cases mapped : readbackHistory key history <;> simp [mapped] at readable ⊢; simp [readbackHistory, readbackEvent, readbackPayload, embedPayload]
    | send site receiver value =>
      rename_i ty
      cases ty <;> simp only [sourceView, send, Payload.ofValue, PIR.Process.bind, PIR.Yields]
      all_goals intro reply; apply ih; rw [readbackHistory_append]; cases mapped : readbackHistory key history <;> simp [mapped] at readable ⊢; simp [readbackHistory, readbackEvent, readbackPayload, embedPayload]
    | query site field arguments =>
      simp only [sourceView, Uniform.SourceProcess.query, PIR.Process.bind, PIR.Yields]
      intro answer
      apply ih
      simpa only [readback_append_challenge, Option.isSome_map] using readable

/-- Key equality only on the source's actual static message/query constructors. -/
theorem sourceView_keys (context : Context) (first second : Origin → Origin)
    (messages : ∀ site sender receiver,
      first (context.message site sender receiver) = second (context.message site sender receiver))
    (queries : ∀ site field, first (context.query site (.draw field)) = second (context.query site (.draw field)))
    (initial : History F G) (challenge : History F G → m F)
    (process : PIR.Process (Actions F G) A)
    (history : Domain.History (Structured.uniformCarriers F G))
    (same : readbackHistory first history = readbackHistory second history)
    (proof : Proof F G)
    (next : (A × Domain.History (Structured.uniformCarriers F G)) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK first initial challenge (sourceView context process history) proof next =
      runK second initial challenge (sourceView context process history) proof next := by
  induction process generalizing history proof with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
    cases operation with
    | receive ty site sender =>
      simp only [sourceView, runK_bind]
      cases ty <;> cases proof with
      | nil => rfl
      | cons payload unread =>
        cases payload <;> simp only [receive, runK, Value.decode, Payload.value]
        all_goals try (split_ifs <;> subst_vars <;> simp_all only)
        all_goals apply ih; rw [readbackHistory_append, readbackHistory_append, same]; simp [readbackHistory, readbackEvent, readbackPayload, messages]
    | send site receiver value =>
      rename_i ty
      cases ty <;> simp only [sourceView, runK_bind, send, Payload.ofValue, runK]
      all_goals apply ih; rw [readbackHistory_append, readbackHistory_append, same]; simp [readbackHistory, readbackEvent, readbackPayload, messages]
    | query site field arguments =>
      simp only [sourceView, runK_bind, Uniform.SourceProcess.query, runK]
      have queried : Zkc.Construction.Uniform.DomainAdapter.query first initial challenge history (context.query site (.draw field)) =
          Zkc.Construction.Uniform.DomainAdapter.query second initial challenge history (context.query site (.draw field)) := by
        simp only [Zkc.Construction.Uniform.DomainAdapter.query, Context.query, Origin.query, Request.draw]
        have keys := queries site field
        simp only [Context.query, Origin.query, Request.draw] at keys
        rw [same, keys]
      rw [queried]
      split
      · congr 1
        funext answer
        cases answer with
        | stopped => rfl
        | returned answer =>
          apply ih
          simp only [readback_append_challenge, same, queries]
      · rfl

end Zkc.Executable.StaticSourceTransport
