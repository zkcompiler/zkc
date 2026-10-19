module

public import Zkc.Semantics.Execution

@[expose] public section

/-! # Transcript interfaces and the Fiat–Shamir transform

A validator is a process over any operation signature `I`. A transcript
interface (`Interface`) states, for each operation, how the Fiat–Shamir
transform treats it (`Absorption`):

- a receive reads the next proof message, absorbs an event carrying it and
  continues with the reply that the absorbed event determines;
- a send absorbs an event and continues with a fixed reply;
- a query absorbs its challenge occurrence, asks the transcript oracle at the
  absorbed history followed by that occurrence and continues with its own
  decoding of the raw answer, or stops with `exhausted` when the decoder
  refuses;
- any other operation refuses.

**Keys and answers.** The transcript oracle is asked at the whole history that
ends with the query's occurrence, presented as the history before the
occurrence and the occurrence itself. The raw answer's type `Raw event` depends
only on the occurrence: in the history class of transcript queries the request
is the last event of the key, so the answer type factors through it. Decoders
read the raw answer alone (`Raw event → Option Reply`); a decoder's method,
operands, result sort and authority come from the request carried in the
occurrence and from authenticated configuration, never from proof data or from
the history before the occurrence. The history still matters elsewhere: it
identifies the oracle cell, and replay and certificates are indexed by it.

`transform` is the transform with a transcript oracle in any monad. It returns
the outcome and the unread proof suffix. `Accepted` is acceptance of an
outcome; `AcceptedComplete` additionally requires that the whole proof was
read. Soundness is stated for `Accepted`, the larger event, so it bounds
complete acceptance too (`AcceptedComplete.accepted`).

`Interface.mapRaw` precomposes every decoder with a map of raw answers; the
transform over the mapped interface is the transform over the original one
with the map applied to the oracle's answers (`transform_mapRaw`).

`Determined` is statement determination: initial histories followed by any
events identify the statement.
-/

set_option autoImplicit false

namespace Zkc.Transcript

/-- A returned value satisfying the acceptance predicate. Stops never accept. -/
def Accepted {A : Type} (accepts : A → Prop) : PIR.Outcome A → Prop
  | .returned value => accepts value
  | .stopped _ => False

/-- Complete acceptance of a transform's result: the outcome is accepted and the
unread proof suffix is empty. -/
def AcceptedComplete {A P : Type} (accepts : A → Prop) (result : PIR.Outcome A × List P) : Prop :=
  Accepted accepts result.1 ∧ result.2 = []

/-- Complete acceptance is acceptance: a bound on `Accepted` bounds it. -/
theorem AcceptedComplete.accepted {A P : Type} {accepts : A → Prop}
    {result : PIR.Outcome A × List P} (complete : AcceptedComplete accepts result) :
    Accepted accepts result.1 :=
  complete.1

/-- Acceptance is monotone in the acceptance predicate. -/
theorem Accepted.mono {A : Type} {accepts accepts' : A → Prop}
    (weaker : ∀ value, accepts value → accepts' value) :
    ∀ {outcome : PIR.Outcome A}, Accepted accepts outcome → Accepted accepts' outcome
  | .returned value, accepted => weaker value accepted
  | .stopped _, accepted => accepted

/-- How the transform treats one validator operation whose reply has type
`Reply`. Transcript events have type `E`, proof messages `P`, and the oracle
answers a query occurrence `event` in `Raw event`. -/
inductive Absorption (E P : Type) (Raw : E → Type) (Reply : Type) where
  /-- Read the next proof message, absorb `event message` and continue with the
  reply `recover` reads from that event. A message whose event recovers no reply
  refuses without being consumed. -/
  | receive (event : P → E) (recover : E → Option Reply)
  /-- Absorb `event` and continue with `value`. Produces no proof data. -/
  | send (event : E) (value : Reply)
  /-- Absorb the challenge occurrence `event`, ask the oracle at the history
  ending with it and continue with `decode` of its raw answer; a refused
  decoding stops with `exhausted`. -/
  | query (event : E) (decode : Raw event → Option Reply)
  /-- Refuse without consuming proof data. -/
  | refuse

/-- A transcript interface: the absorption of every operation of `I`. -/
abbrev Interface (I : PIR.Signature) (E P : Type) (Raw : E → Type) :=
  (operation : I.Op) → Absorption E P Raw (I.Reply operation)

/-- Precompose a query's decoder with a map of raw answers. -/
def Absorption.mapRaw {E P Reply : Type} {Raw Raw' : E → Type}
    (map : (event : E) → Raw' event → Raw event) :
    Absorption E P Raw Reply → Absorption E P Raw' Reply
  | .receive event recover => .receive event recover
  | .send event value => .send event value
  | .query event decode => .query event fun raw => decode (map event raw)
  | .refuse => .refuse

/-- An interface whose decoders read raw answers of another type through `map`. -/
def Interface.mapRaw {I : PIR.Signature} {E P : Type} {Raw Raw' : E → Type}
    (map : (event : E) → Raw' event → Raw event) (absorb : Interface I E P Raw) :
    Interface I E P Raw' :=
  fun operation => (absorb operation).mapRaw map

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type}

section Transform
variable {m : Type → Type} [Monad m]

/-- The Fiat–Shamir transform of `process` over the interface `absorb`, from the
absorbed `history`, reading proof messages from `proof` and asking `oracle` at
the absorbed history before each query and the query's occurrence. Returns the
outcome and the unread proof suffix. -/
def transform (absorb : Interface I E P Raw)
    (oracle : (preceding : List E) → (event : E) → m (Raw event)) :
    PIR.Proc I A → List E → List P → m (PIR.Outcome A × List P)
  | .done value, _, proof => pure (.returned value, proof)
  | .halt stop, _, proof => pure (.stopped stop, proof)
  | .call operation next, history, proof =>
      match absorb operation with
      | .receive event recover =>
          match proof with
          | [] => pure (.stopped .refused, [])
          | message :: rest =>
              match recover (event message) with
              | some value =>
                  transform absorb oracle (next value) (history ++ [event message]) rest
              | none => pure (.stopped .refused, message :: rest)
      | .send event value => transform absorb oracle (next value) (history ++ [event]) proof
      | .query event decode => do
          let raw ← oracle history event
          match decode raw with
          | some value => transform absorb oracle (next value) (history ++ [event]) proof
          | none => pure (.stopped .exhausted, proof)
      | .refuse => pure (.stopped .refused, proof)

variable (absorb : Interface I E P Raw) (oracle : (preceding : List E) → (event : E) → m (Raw event))

@[simp] theorem transform_done (value : A) (history : List E) (proof : List P) :
    transform absorb oracle (.done value) history proof = pure (.returned value, proof) := rfl

@[simp] theorem transform_halt (stop : PIR.Stop) (history : List E) (proof : List P) :
    transform (A := A) absorb oracle (.halt stop) history proof = pure (.stopped stop, proof) := rfl

theorem transform_receive {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E) (message : P)
    (rest : List P) :
    transform absorb oracle (.call operation next) history (message :: rest) =
      match recover (event message) with
      | some value => transform absorb oracle (next value) (history ++ [event message]) rest
      | none => pure (.stopped .refused, message :: rest) := by
  simp only [transform, absorbed]

theorem transform_receive_nil {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E) :
    transform absorb oracle (.call operation next) history [] = pure (.stopped .refused, []) := by
  simp only [transform, absorbed]

theorem transform_send {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : E} {value : I.Reply operation} (absorbed : absorb operation = .send event value)
    (history : List E) (proof : List P) :
    transform absorb oracle (.call operation next) history proof =
      transform absorb oracle (next value) (history ++ [event]) proof := by
  simp only [transform, absorbed]

theorem transform_query {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : E} {decode : Raw event → Option (I.Reply operation)}
    (absorbed : absorb operation = .query event decode) (history : List E) (proof : List P) :
    transform absorb oracle (.call operation next) history proof =
      oracle history event >>= fun raw =>
        match decode raw with
        | some value => transform absorb oracle (next value) (history ++ [event]) proof
        | none => pure (.stopped .exhausted, proof) := by
  simp only [transform, absorbed]

theorem transform_refuse {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    (absorbed : absorb operation = .refuse) (history : List E) (proof : List P) :
    transform absorb oracle (.call operation next) history proof =
      pure (.stopped .refused, proof) := by
  simp only [transform, absorbed]

/-- The transform over an interface whose decoders read raw answers through `map`
is the transform over the original interface with `map` applied to the oracle's
answers. -/
theorem transform_mapRaw [LawfulMonad m] {Raw' : E → Type} (map : (event : E) → Raw' event → Raw event)
    (oracle' : (preceding : List E) → (event : E) → m (Raw' event)) :
    ∀ (process : PIR.Proc I A) (history : List E) (proof : List P),
      transform (absorb.mapRaw map) oracle' process history proof =
        transform absorb (fun preceding event => map event <$> oracle' preceding event) process
          history proof := by
  intro process
  induction process with
  | done value => intro history proof; rfl
  | halt stop => intro history proof; rfl
  | call operation next ih =>
      intro history proof
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · have mapped : absorb.mapRaw map operation = .receive event recover := by
          simp [Interface.mapRaw, absorbed, Absorption.mapRaw]
        cases proof with
        | nil => rw [transform_receive_nil _ _ mapped, transform_receive_nil _ _ absorbed]
        | cons message rest =>
            rw [transform_receive _ _ mapped, transform_receive _ _ absorbed]
            cases recover (event message) with
            | none => rfl
            | some value => exact ih value _ _
      · have mapped : absorb.mapRaw map operation = .send event value := by
          simp [Interface.mapRaw, absorbed, Absorption.mapRaw]
        rw [transform_send _ _ mapped, transform_send _ _ absorbed]
        exact ih value _ _
      · have mapped : absorb.mapRaw map operation = .query event fun raw => decode (map event raw) := by
          simp [Interface.mapRaw, absorbed, Absorption.mapRaw]
        rw [transform_query _ _ mapped, transform_query _ _ absorbed, bind_map_left]
        congr 1
        funext raw
        cases decode (map event raw) with
        | none => rfl
        | some value => exact ih value _ _
      · have mapped : absorb.mapRaw map operation = .refuse := by
          simp [Interface.mapRaw, absorbed, Absorption.mapRaw]
        rw [transform_refuse _ _ mapped, transform_refuse _ _ absorbed]

/-- Apply a function to a returned value; stops are unchanged. -/
def mapOutcome {A B : Type} (f : A → B) : PIR.Outcome A → PIR.Outcome B
  | .returned value => .returned (f value)
  | .stopped stop => .stopped stop

/-- An outcome image accepts exactly when the outcome accepts the pulled-back
predicate. -/
theorem accepted_mapOutcome {A B : Type} (f : A → B) (accepts : B → Prop) :
    ∀ outcome : PIR.Outcome A, Accepted accepts (mapOutcome f outcome) ↔
      Accepted (fun value => accepts (f value)) outcome
  | .returned _ => Iff.rfl
  | .stopped _ => Iff.rfl

/-- A pure final projection commutes with the transform. -/
theorem transform_bind_done [LawfulMonad m] {B : Type} (f : A → B) :
    ∀ (process : PIR.Proc I A) (history : List E) (proof : List P),
      transform absorb oracle (process.bind fun value => .done (f value)) history proof =
        (fun result => (mapOutcome f result.1, result.2)) <$>
          transform absorb oracle process history proof := by
  intro process
  induction process with
  | done value => intro history proof; simp [PIR.Proc.bind, mapOutcome]
  | halt stop => intro history proof; simp [PIR.Proc.bind, mapOutcome]
  | call operation next ih =>
      intro history proof
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · cases proof with
        | nil =>
            simp only [PIR.Proc.bind]
            rw [transform_receive_nil _ _ absorbed, transform_receive_nil _ _ absorbed]
            simp [mapOutcome]
        | cons message rest =>
            simp only [PIR.Proc.bind]
            rw [transform_receive _ _ absorbed, transform_receive _ _ absorbed]
            cases recover (event message) with
            | none => simp [mapOutcome]
            | some value => exact ih value _ _
      · simp only [PIR.Proc.bind]
        rw [transform_send _ _ absorbed, transform_send _ _ absorbed]
        exact ih value _ _
      · simp only [PIR.Proc.bind]
        rw [transform_query _ _ absorbed, transform_query _ _ absorbed, map_bind]
        congr 1
        funext raw
        cases decode raw with
        | none => simp [mapOutcome]
        | some value => exact ih value _ _
      · simp only [PIR.Proc.bind]
        rw [transform_refuse _ _ absorbed, transform_refuse _ _ absorbed]
        simp [mapOutcome]

end Transform

/-- The initial histories determine the statements: when two statements' initial
histories, each followed by some events, are equal, the statements are equal.
Injective initial histories of which none is a proper prefix of another satisfy
this. -/
def Determined {E Stmt : Type} (initial : Stmt → List E) : Prop :=
  ∀ statement other (rest otherRest : List E),
    initial statement ++ rest = initial other ++ otherRest → statement = other

end Zkc.Transcript
