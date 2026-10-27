module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckSampling

@[expose] public section

/-! Successful execution from the actual emitted endpoint proof, with consumed
coins and retained observations. The operational handler reads only packets
and coins. Reference tables occur solely in its proved invariant. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Domains.KoalaBearModel (model octicIdentity)
open ZkcSecurity.Domains.KoalaBear (Base Octic embed)
open ZkcSecurity.Families.Sumcheck

abbrev Packet := Domain.Payload model.toCarriers
abbrev Event := Domain.Event model.toCarriers
abbrev HonestState := List Packet × List Octic

/-- Nominal decoding refuses a base payload at an octic receive. A challenge is
consumed exactly once; missing messages or coins stop the execution. -/
def handler : PIR.Handler I HonestState Event
  | .receive ty site peer, (proof, coins) =>
    match proof with
    | [] => ⟨.stopped .refused, (proof, coins), []⟩
    | packet :: rest =>
      match packet.value ty with
      | none => ⟨.stopped .refused, (proof, coins), []⟩
      | some value => ⟨.returned value, (rest, coins),
          [.message (context.message site peer 1) packet]⟩
  | .send (ty := ty) site peer value, state =>
    match Domain.Payload.ofValue ty value with
    | none => ⟨.stopped .refused, state, []⟩
    | some packet => ⟨.returned (), state, [.message (context.message site 1 peer) packet]⟩
  | .query site field _, (proof, coins) => by
    change String at field
    exact if same : field = octicIdentity then by
      subst field
      exact match coins with
      | [] => ⟨.stopped .exhausted, (proof, coins), []⟩
      | challenge :: rest => ⟨.returned challenge, (proof, rest),
          [.challenge (context.query site (.draw octicIdentity))]⟩
    else ⟨.stopped .refused, (proof, coins), []⟩

variable {Frame : Type}

def endpoints {n : Nat} (state : State Frame (n + 1)) : Octic × Octic :=
  (((layout.entries state).take ((layout.entries state).length / 2)).sum,
    ((layout.entries state).drop ((layout.entries state).length / 2)).sum)

def packets (message : Octic × Octic) : List Packet :=
  [.field octicIdentity message.1, .field octicIdentity message.2]

/-- A one-round invariant can be stated directly at the successor dimension,
while the terminal invariant needs no additional messages. -/
def runInvariant (count : Nat) {n : Nat} (_handle : Nat) (state : State Frame n)
    (execution : HonestState) : Prop :=
  (count = 0 ∧ execution = ([], [])) ∨ (count = 1 ∧ ∃ (message : Octic × Octic) (r : Octic),
    execution = (packets message, [r]) ∧
    message = (((layout.entries state).take ((layout.entries state).length / 2)).sum,
      ((layout.entries state).drop ((layout.entries state).length / 2)).sum))

def ready (count : Nat) {n : Nat} (_handle : Nat) (state : State Frame (n + 1))
    (message : Octic × Octic) (execution : HonestState) : Prop :=
  count = 0 ∧ message = endpoints state ∧ ∃ r : Octic, execution = ([], [r])

theorem execution : HonestRunLaws (program (Frame := Frame)) handler runInvariant ready where
  receive count {_n} handle state execution supplied := by
    rcases supplied with impossible | ⟨one, message, r, same, messageEq⟩
    · omega
    have zero : count = 0 := by omega
    subst count
    subst execution
    subst message
    refine ⟨endpoints state, ([], [r]),
      [.message (context.message (KoalaBearSumcheckSource.site "label_6c6f77_0") 0 1) (.field octicIdentity (endpoints state).1),
       .message (context.message (KoalaBearSumcheckSource.site "label_68696768_0") 0 1) (.field octicIdentity (endpoints state).2)],
      ?_, rfl, rfl, r, rfl⟩
    rfl
  query count {_n} handle state message execution supplied := by
    rcases supplied with ⟨rfl, rfl, r, rfl⟩
    exact ⟨r, ([], []), [.challenge (context.query (KoalaBearSumcheckSource.site "label_6368616c6c656e6765") (.draw octicIdentity))],
      ([], []), [.message (context.message (KoalaBearSumcheckSource.site "label_64656c6976657279_0") 1 0) (.field octicIdentity r)],
      rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem honest_messages : HonestMessageLaw (representation (Frame := Frame)) ready := by
  intro count n handle state message execution supplied
  rw [supplied.2.1, endpoints, layout.honest_endpoints]
  exact TableReference.honest_polynomial _

/-- The actual source verifier succeeds on the emitted honest endpoint proof.
Its poststate has consumed both messages and the one supplied challenge. -/
theorem honest_run {n : Nat} (handle : Nat) (state : State Frame (n + 1)) (r : Octic)
    (yes : representation.Yes state) :
    ∃ result events,
      (actual (handle, state)).run handler (packets (endpoints state), [r]) =
        ⟨.returned result, ([], []), events⟩ ∧ representation.Yes result := by
  obtain ⟨result, final, events, ran, valid, finished⟩ :=
    honest handler runInvariant ready execution honest_messages n (handle, state)
      (packets (endpoints state), [r]) yes
      (Or.inr ⟨rfl, endpoints state, r, rfl, rfl⟩)
  have consumed : final = ([], []) := by
    rcases finished with finished | impossible
    · exact finished.2
    · exact False.elim (by omega)
  exact ⟨result, events, consumed ▸ ran, valid⟩

/-- This endpoint handler emits precisely the source producer's sends. It has
no table input or polynomial oracle. The receive supplies V's delivered coin. -/
def producerHandler (r : Octic) : PIR.Handler I Unit Packet
  | .send (ty := ty) _ _ value, state =>
    match Domain.Payload.ofValue ty value with
    | none => ⟨.stopped .refused, state, []⟩
    | some packet => ⟨.returned (), state, [packet]⟩
  | .receive ty _ _, state =>
    if same : ty = .field octicIdentity then by
      subst ty
      exact ⟨.returned r, state, []⟩
    else ⟨.stopped .refused, state, []⟩
  | .query .., state => ⟨.stopped .refused, state, []⟩

theorem producer_run (a b : Base) (r : Octic) :
    (KoalaBearSumcheckSource.producer a b).run (producerHandler r) () =
      ⟨.returned (.cons none (.cons none .nil)), (), packets (embed a, embed b)⟩ := by
  rw [KoalaBearSumcheckSource.producer_equation]
  rfl

def initial (a b : Base) (frame : Frame) : State Frame 1 :=
  EmbeddingPrefix.State.initial [a, b] 1 (embed (a + b)) frame rfl

theorem initial_endpoints (a b : Base) (frame : Frame) :
    endpoints (initial a b frame) = (embed a, embed b) := by
  have entries : layout.entries (initial a b frame) = [embed a, embed b] := rfl
  unfold endpoints
  rw [entries]
  simp

/-- One genuine mixed-domain client: proof packets are read from the actual
checked producer's run; the unchanged Contract.honest consumes the very same
whole-body verifier equation as Contract.soundness. -/
theorem source_honest (a b : Base) (frame : Frame) (handle : Nat) (r : Octic) :
    ∃ result events,
      (actual (handle, initial a b frame)).run handler
        (((KoalaBearSumcheckSource.producer a b).run (producerHandler r) ()).events, [r]) =
          ⟨.returned result, ([], []), events⟩ ∧ representation.Yes result := by
  rw [producer_run]
  rw [← initial_endpoints a b frame]
  apply honest_run
  simpa only [initial, List.sum_cons, List.sum_nil, add_zero] using
    (initial_yes [a, b] 1 frame rfl)

end ZkcSecurity.Examples.Components.KoalaBearSumcheck
