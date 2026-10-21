module

public import ZkcSecurity.VCVio.Execution
public import Zkc.Source.Structured.Participant

@[expose] public section

/-! A concrete uniform service at the structured participant boundary.

The existing network handler owns receive/send effects. Its query branch is
never used. Configured queries execute the existing `freshQuery`, retaining
every callback state, event and stop without conditioning or retrying.
-/

namespace ZkcSecurity.VCVio.StructuredUniform

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.VCVio.Execution

variable {F G S E : Type}

/-- Exact qualified site, nominal field domain, and actual service handle. -/
abbrev Key := String × String × Nat

/-- Install fresh uniform queries without restricting the network's actions or
private state. All nominal field domains have the existing assignment `F`.
Unconfigured queries refuse; they never fall back to the network handler. -/
def withUniformQueries [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (ports : List Key) (before : Key → Phase S E Unit)
    (after : Key → F → Phase S E Unit) :
    PIR.MonadHandler ProbComp (participantInterface F G) S E
  | .receive ty site peer, s => network (.receive ty site peer) s
  | .send (ty := ty) site peer value, s => network (.send (ty := ty) site peer value) s
  | .query site field (.cons handle .nil), s =>
      let key : Key := (site, field, handle)
      if key ∈ ports then
        freshQuery (F := F) (before key) (after key) s
      else pure ⟨.stopped .refused, s, []⟩

private theorem follow_result_identity {A : Type} (e : PIR.Execution S E A) :
    e.followM (m := ProbComp) (fun a s => pure (result a s)) = pure e := by
  cases e with
  | mk outcome state events => cases outcome <;> simp [PIR.Execution.followM, result]

/-- The identity action interpretation retains the complete handler record. -/
theorem participantActions_runM
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (action : (participantInterface F G).Op) (s : S) :
    (participantActions F G action).runM handler s = handler action s := by
  change (do let e ← handler action s
             e.followM fun a s => pure (result a s)) = _
  simp only [follow_result_identity, bind_pure]

variable [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (ports : List Key) (before : Key → Phase S E Unit)
    (after : Key → F → Phase S E Unit)

@[simp] theorem withUniformQueries_receive (ty : Ty) (site : String) (peer : Nat) (s : S) :
    withUniformQueries network ports before after (.receive ty site peer) s =
      network (.receive ty site peer) s := rfl

@[simp] theorem withUniformQueries_send {ty : Ty} (site : String) (peer : Nat)
    (value : assignment F G ty) (s : S) :
    withUniformQueries network ports before after (.send site peer value) s =
      network (.send site peer value) s := rfl

/-- Equality of complete probabilistic executions at every state and for every
network. No honesty, reachability, or successful-callback premise is required. -/
theorem withUniformQueries_query (site field : String) (handle : Nat)
    (member : (site, field, handle) ∈ ports) (s : S) :
    (participantActions F G (.query site field (.cons handle .nil))).runM
        (withUniformQueries network ports before after) s =
      freshQuery (before (site, field, handle)) (after (site, field, handle)) s := by
  rw [participantActions_runM]
  change (if (site, field, handle) ∈ ports then
    freshQuery (before (site, field, handle)) (after (site, field, handle)) s
    else pure ⟨.stopped .refused, s, []⟩) = _
  simp only [member, ite_true]

/-- Wrong site, field, or handle refuses without changing the state or emitting
events, even if the wrapped network would answer that query. -/
theorem withUniformQueries_unconfigured (site field : String) (handle : Nat)
    (missing : (site, field, handle) ∉ ports) (s : S) :
    (participantActions F G (.query site field (.cons handle .nil))).runM
        (withUniformQueries network ports before after) s =
      pure ⟨.stopped .refused, s, []⟩ := by
  rw [participantActions_runM]
  change (if (site, field, handle) ∈ ports then
    freshQuery (before (site, field, handle)) (after (site, field, handle)) s
    else pure ⟨.stopped .refused, s, []⟩) = _
  simp only [missing, ite_false]
  rfl

end ZkcSecurity.VCVio.StructuredUniform
