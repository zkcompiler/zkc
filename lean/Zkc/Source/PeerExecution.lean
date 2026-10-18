module

public import Zkc.Source.Participant

@[expose] public section

/-! Honest delivery between two role-local participant processes.

A role-local process only states which actions it performs: a receive obtains
an arbitrary typed reply and a send obtains an acknowledgement. `peerHandler`
instead answers one endpoint's actions from the other endpoint's actual
residual process. A receive is answered by the peer's next send when that send
has the same type and site and is addressed to this endpoint; a send is
consumed by the peer's next receive at that site. The endpoint's own service
queries are answered by a separate service handler. The handler state is the
peer's residual process together with that service state, so at the end of a
run the state holds what remains of the peer.

Every mismatch refuses and leaves the state unchanged: another site, type or
endpoint, a peer that waits on a different action, has stopped, or has
returned. No reply is invented. The peer may not query a service of its own;
a peer query is a mismatch. This is a deterministic routing model for honest
delivery between exactly two endpoints. It is not a scheduler for arbitrary
networks, and it does not model loss, reordering or an adversarial network.
-/

set_option autoImplicit false

namespace Zkc.Source.Participant

variable {Role Ty : Type} [DecidableEq Role] [DecidableEq Ty]
  {services : Services Ty} {Value : Ty → Type} {A S E : Type}

/-- The peer endpoint's residual process and the endpoint's service state. -/
structure Peer (Role Ty : Type) (services : Services Ty) (Value : Ty → Type) (A S : Type) where
  process : PIR.Proc (interface Role Ty services Value) A
  service : S

/-- Answer the actions of endpoint `self` from the actual process of endpoint
`other`; queries of `self` go to `service`. -/
def peerHandler (self other : Role)
    (service : PIR.Handler (interface Role Ty services Value) S E) :
    PIR.Handler (interface Role Ty services Value) (Peer Role Ty services Value A S) E
  | .receive ty site sender, state =>
    match state.process with
    | .call (.send (ty := sent) peerSite receiver value) next =>
      if same : sent = ty ∧ peerSite = site ∧ sender = other ∧ receiver = self then
        ⟨.returned (same.1 ▸ value), ⟨next (), state.service⟩, []⟩
      else ⟨.stopped .refused, state, []⟩
    | _ => ⟨.stopped .refused, state, []⟩
  | .send (ty := ty) site receiver value, state =>
    match state.process with
    | .call (.receive expected peerSite sender) next =>
      if same : ty = expected ∧ peerSite = site ∧ receiver = other ∧ sender = self then
        ⟨.returned (), ⟨next (same.1 ▸ value), state.service⟩, []⟩
      else ⟨.stopped .refused, state, []⟩
    | _ => ⟨.stopped .refused, state, []⟩
  | .query site op args, state =>
    let result := service (.query site op args) state.service
    ⟨result.outcome, ⟨state.process, result.state⟩, result.events⟩

variable (self other : Role) (service : PIR.Handler (interface Role Ty services Value) S E)

/-- A receive takes exactly the value of the peer's matching send. -/
theorem peer_receive {ty : Ty} (site : String) (value : Value ty)
    (next : Unit → PIR.Proc (interface Role Ty services Value) A) (state : S)
    {B : Type} (continuation : Value ty → PIR.Proc (interface Role Ty services Value) B) :
    (PIR.Proc.call (Action.receive ty site other) continuation).run (peerHandler self other service)
        ⟨.call (Action.send site self value) next, state⟩ =
      (continuation value).run (peerHandler self other service) ⟨next (), state⟩ := by
  simp only [PIR.Proc.run, peerHandler, and_self, ↓reduceDIte, PIR.Execution.follow, List.nil_append]

/-- A send is consumed by the peer's matching receive, which obtains the value. -/
theorem peer_send {ty : Ty} (site : String) (value : Value ty)
    (next : Value ty → PIR.Proc (interface Role Ty services Value) A) (state : S)
    {B : Type} (continuation : Unit → PIR.Proc (interface Role Ty services Value) B) :
    (PIR.Proc.call (Action.send site other value) continuation).run (peerHandler self other service)
        ⟨.call (Action.receive ty site self) next, state⟩ =
      (continuation ()).run (peerHandler self other service) ⟨next value, state⟩ := by
  simp only [PIR.Proc.run, peerHandler, and_self, ↓reduceDIte, PIR.Execution.follow, List.nil_append]

/-- Queries leave the peer untouched and use the endpoint's own service. -/
theorem peer_query (site : String) (op : services.Op) (args : Values Value (services.arguments op))
    (peer : PIR.Proc (interface Role Ty services Value) A) (state : S) :
    peerHandler self other service (.query site op args) ⟨peer, state⟩ =
      let result := service (.query site op args) state
      ⟨result.outcome, ⟨peer, result.state⟩, result.events⟩ := rfl

/-- A receive refuses when the peer has already returned; nothing is invented. -/
theorem peer_receive_finished (ty : Ty) (site : String) (sender : Role) (result : A) (state : S) :
    peerHandler self other service (.receive ty site sender) ⟨.done result, state⟩ =
      ⟨.stopped .refused, ⟨.done result, state⟩, []⟩ := rfl

/-- A receive refuses when the peer's next send names another site. -/
theorem peer_receive_other_site {ty : Ty} (site peerSite : String) (value : Value ty)
    (next : Unit → PIR.Proc (interface Role Ty services Value) A) (state : S)
    (different : peerSite ≠ site) :
    peerHandler self other service (.receive ty site other)
        ⟨.call (.send peerSite self value) next, state⟩ =
      ⟨.stopped .refused, ⟨.call (.send peerSite self value) next, state⟩, []⟩ := by
  simp only [peerHandler, different, false_and, and_false, ↓reduceDIte]

/-- A send refuses when the peer's next action is a send rather than a receive. -/
theorem peer_send_unexpected {ty : Ty} (site : String) (value : Value ty)
    (peerSite : String) (peerValue : Value ty)
    (next : Unit → PIR.Proc (interface Role Ty services Value) A) (state : S) :
    peerHandler self other service (.send site other value)
        ⟨.call (.send peerSite self peerValue) next, state⟩ =
      ⟨.stopped .refused, ⟨.call (.send peerSite self peerValue) next, state⟩, []⟩ := rfl

end Zkc.Source.Participant
