module

public import Zkc.Core.EveryRun
public import Zkc.Core.ThreadFits
public import Zkc.Core.LayoutLaws

public section

/-! The replay relation of the serialize step.

The serialize step turns every exchange from the prover to the verifier into a `put` at the
prover and a `take` at the verifier, and nothing connects the two: the prover's program
runs alone and returns a proof, and the verifier's program runs alone on a proof. This
module has the relation that says, of one region of the program that is serialized, that
the two runs agree with the grouped run, and the lemmas that close it under sequencing and
iteration. The proof over the operations of a region is in the modules that follow.

- `RunsTo`: a run of one process that neither sends nor receives returns a value and
  leaves the counters of the sampler (`ReturnsAlone` with the counters after the run), so
  runs compose along sequencing (`RunsTo.bind`).
- `EverySend`: every `send` of a process, along every reply, carries a value of which a
  condition holds, and the process returns values of which another condition holds. It is
  taken apart along sequencing (`everySend_bind`), like `EveryRun`. A process without an
  effect sends nothing (`EverySend.of_quiet`). The condition is kept by a handler that
  itself sends only such values, at a `send` of such a value and at every other effect
  (`Resends`, `EverySend.interpretWith`).
- `Channel`: what the two handlers' states say of the messages between the two sides: the
  messages that the prover's state gains (`Written`), the messages that the verifier's
  state gives (`Takes`), and the messages that can be carried (`Sendable`).
- `PartsReplay`: three processes, the grouped one, the prover's part and the verifier's part,
  with a handler for each part. Whenever every run of the grouped process returns a value
  of which a condition holds, and every `send` of the prover's part carries a value that can
  be carried, then for every sampler and all counters of the two parts there are a grouped
  value of which the condition holds and messages such that the prover's part under its
  handler returns its share of the value and has written the messages, and the verifier's
  part under its handler, from every state that gives the messages, returns its share of
  the value. Each part runs alone from its own counters. A draw or a sample of the grouped
  process is performed by one of the two parts, and the reply of the grouped process is the
  coin that this part is given.
- The relation is closed under sequencing (`PartsReplay.bind`, the messages are appended) and
  the iterations of a loop (`PartsReplay.iterations`). A part that performs what the grouped
  process performs while the other does nothing is related to it when its handler passes
  it (`PartsReplay.proverMirrors`, `PartsReplay.verifierMirrors`), and handlers that pass the two
  parts may replace handlers that perform every effect as it is (`PartsReplay.ofPasses`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Zkc.Core

open Zkc.Source

section Runs

variable {model : Model}

/-- A run of one process that neither sends nor receives returns a value and leaves the
counters of the sampler. -/
inductive RunsTo (sampler : Sampler model) {α : Type} :
    PIR.Process (Effects model) α → Asked → α → Asked → Prop where
  | done (value : α) (asked : Asked) : RunsTo sampler (.done value) asked value asked
  | draw (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (asked : Asked) (value : α)
      (final : Asked) :
      RunsTo sampler (next (sampler.answer site (asked site) law)) (asked.next site) value final →
        RunsTo sampler (.call (.draw site law inputs) next) asked value final
  | sample (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (asked : Asked) (value : α)
      (final : Asked) :
      RunsTo sampler (next (sampler.answer site (asked site) law)) (asked.next site) value final →
        RunsTo sampler (.call (.sample site law inputs) next) asked value final

variable {sampler : Sampler model}

/-- A run that returns a value and leaves counters returns the value. -/
theorem RunsTo.returnsAlone {α : Type} {process : PIR.Process (Effects model) α} {asked final : Asked}
    {value : α} (runs : RunsTo sampler process asked value final) :
    ReturnsAlone sampler process asked value := by
  induction runs with
  | done value asked => exact .done value asked
  | draw site law inputs next asked value final _ ih => exact .draw site law inputs next asked value ih
  | sample site law inputs next asked value final _ ih =>
      exact .sample site law inputs next asked value ih

/-- Runs compose: a process, then a continuation from the counters that it left. -/
theorem RunsTo.bind {α β : Type} {process : PIR.Process (Effects model) α}
    {next : α → PIR.Process (Effects model) β} {asked middle final : Asked} {value : α} {result : β}
    (before : RunsTo sampler process asked value middle)
    (after : RunsTo sampler (next value) middle result final) :
    RunsTo sampler (process.bind next) asked result final := by
  induction before with
  | done value asked => exact after
  | draw site law inputs tail asked value middle _ ih =>
      exact .draw site law inputs (fun reply => (tail reply).bind next) asked result final (ih after)
  | sample site law inputs tail asked value middle _ ih =>
      exact .sample site law inputs (fun reply => (tail reply).bind next) asked result final
        (ih after)

/-- Every `send` of the process, along every reply to its other effects, carries a value
of which `Sendable` holds, and the process returns values of which `after` holds. -/
@[expose] def EverySend (Sendable : (type : Ty) → model.Value type → Prop) {α : Type}
    (after : α → Prop) : PIR.Process (Effects model) α → Prop
  | .done value => after value
  | .halt _ => True
  | .call (.send _ type value) next => Sendable type value ∧ EverySend Sendable after (next PUnit.unit)
  | .call (.receive _ _) next => ∀ reply, EverySend Sendable after (next reply)
  | .call (.draw _ _ _) next => ∀ reply, EverySend Sendable after (next reply)
  | .call (.sample _ _ _) next => ∀ reply, EverySend Sendable after (next reply)
  | .call (.read _ _ _) next => ∀ reply, EverySend Sendable after (next reply)

/-- The condition on the sends of a process followed by a continuation: the sends of the
process, and from every value it returns the sends of the continuation. -/
theorem everySend_bind {α β : Type} (Sendable : (type : Ty) → model.Value type → Prop)
    (after : β → Prop) (next : α → PIR.Process (Effects model) β) :
    ∀ (process : PIR.Process (Effects model) α),
      EverySend Sendable after (process.bind next) ↔
        EverySend Sendable (fun value => EverySend Sendable after (next value)) process
  | .done _ => Iff.rfl
  | .halt _ => Iff.rfl
  | .call (.send _ _ _) tail =>
      and_congr Iff.rfl (everySend_bind Sendable after next (tail PUnit.unit))
  | .call (.receive _ _) tail =>
      forall_congr' fun reply => everySend_bind Sendable after next (tail reply)
  | .call (.draw _ _ _) tail =>
      forall_congr' fun reply => everySend_bind Sendable after next (tail reply)
  | .call (.sample _ _ _) tail =>
      forall_congr' fun reply => everySend_bind Sendable after next (tail reply)
  | .call (.read _ _ _) tail =>
      forall_congr' fun reply => everySend_bind Sendable after next (tail reply)

/-- Weaker conditions hold of the sends and of the values. -/
theorem EverySend.mono {Sendable Weaker : (type : Ty) → model.Value type → Prop} {α : Type}
    {after weaker : α → Prop} (carried : ∀ type value, Sendable type value → Weaker type value)
    (weakens : ∀ value, after value → weaker value) :
    ∀ {process : PIR.Process (Effects model) α},
      EverySend Sendable after process → EverySend Weaker weaker process
  | .done value, sent => weakens value sent
  | .halt _, _ => trivial
  | .call (.send _ type value) _, sent => ⟨carried type value sent.1, EverySend.mono carried weakens sent.2⟩
  | .call (.receive _ _) _, sent => fun reply => EverySend.mono carried weakens (sent reply)
  | .call (.draw _ _ _) _, sent => fun reply => EverySend.mono carried weakens (sent reply)
  | .call (.sample _ _ _) _, sent => fun reply => EverySend.mono carried weakens (sent reply)
  | .call (.read _ _ _) _, sent => fun reply => EverySend.mono carried weakens (sent reply)

/-- The condition that asks nothing holds of every process. -/
theorem EverySend.trivial {α : Type} :
    ∀ (process : PIR.Process (Effects model) α),
      EverySend (fun _ _ => True) (fun _ => True) process
  | .done _ => True.intro
  | .halt _ => True.intro
  | .call (.send _ _ _) next => ⟨True.intro, EverySend.trivial (next PUnit.unit)⟩
  | .call (.receive _ _) next => fun reply => EverySend.trivial (next reply)
  | .call (.draw _ _ _) next => fun reply => EverySend.trivial (next reply)
  | .call (.sample _ _ _) next => fun reply => EverySend.trivial (next reply)
  | .call (.read _ _ _) next => fun reply => EverySend.trivial (next reply)

/-- A process without an effect sends nothing. -/
theorem EverySend.of_quiet {Sendable : (type : Ty) → model.Value type → Prop} {α : Type}
    {after : α → Prop} :
    ∀ {process : PIR.Process (Effects model) α}, process.Quiet → (∀ value, after value) →
      EverySend Sendable after process
  | .done value, _, holds => holds value
  | .halt _, _, _ => True.intro
  | .call _ _, quiet, _ => quiet.elim

/-- A process without an effect, followed by a continuation, sends what the continuation
sends. -/
theorem EverySend.after_quiet {Sendable : (type : Ty) → model.Value type → Prop} {α β : Type}
    {after : β → Prop} {process : PIR.Process (Effects model) α}
    {next : α → PIR.Process (Effects model) β} (quiet : process.Quiet)
    (sent : ∀ value, EverySend Sendable after (next value)) :
    EverySend Sendable after (process.bind next) :=
  (everySend_bind Sendable after next process).mpr (EverySend.of_quiet quiet sent)

/-- The condition holds of the value of an effect that is a `send`. -/
@[expose] def Effect.Sends (Sendable : (type : Ty) → model.Value type → Prop) :
    Effect model.Value → Prop
  | .send _ type value => Sendable type value
  | .receive .. | .draw .. | .sample .. | .read .. => True

/-- An effect performed as it is sends the value of the effect, when the effect is a
`send`, and nothing otherwise. -/
theorem passEffect_sends {Sendable : (type : Ty) → model.Value type → Prop} {State : Type} :
    ∀ (effect : Effect model.Value) (state : State), effect.Sends Sendable →
      EverySend Sendable (fun _ => True) (passEffect effect state)
  | .send _ _ _, _, sends => ⟨sends, True.intro⟩
  | .receive _ _, _, _ => fun _ => True.intro
  | .draw _ _ _, _, _ => fun _ => True.intro
  | .sample _ _ _, _, _ => fun _ => True.intro
  | .read _ _ _, _, _ => fun _ => True.intro

/-- A handler sends only values of which the condition holds: at a `send` of such a value,
and at every other effect. -/
@[expose] def Resends (Sendable : (type : Ty) → model.Value type → Prop) {State : Type}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) State) : Prop :=
  ∀ (effect : Effect model.Value) (state : State), effect.Sends Sendable →
    EverySend Sendable (fun _ => True) (handler effect state)

/-- A process interpreted by a handler that sends only values of which the condition holds
sends only such values, when the process does. -/
theorem EverySend.interpretWith {Sendable : (type : Ty) → model.Value type → Prop}
    {State α : Type}
    {handler : PIR.StatefulInterpretation (Effects model) (Effects model) State}
    (resends : Resends Sendable handler) {after : α → Prop} :
    ∀ (process : PIR.Process (Effects model) α) (state : State),
      EverySend Sendable after process →
        EverySend Sendable (fun result => after result.1) (process.interpretWith handler state)
  | .done _, _, sent => sent
  | .halt _, _, _ => True.intro
  | .call (.send site type value) next, state, sent =>
      (everySend_bind Sendable _ _ _).mpr
        (EverySend.mono (fun _ _ carried => carried)
          (fun reply _ => EverySend.interpretWith resends (next reply.1) reply.2 sent.2)
          (resends (.send site type value) state sent.1))
  | .call (.receive site type) next, state, sent =>
      (everySend_bind Sendable _ _ _).mpr
        (EverySend.mono (fun _ _ carried => carried)
          (fun reply _ => EverySend.interpretWith resends (next reply.1) reply.2 (sent reply.1))
          (resends (.receive site type) state True.intro))
  | .call (.draw site law inputs) next, state, sent =>
      (everySend_bind Sendable _ _ _).mpr
        (EverySend.mono (fun _ _ carried => carried)
          (fun reply _ => EverySend.interpretWith resends (next reply.1) reply.2 (sent reply.1))
          (resends (.draw site law inputs) state True.intro))
  | .call (.sample site law inputs) next, state, sent =>
      (everySend_bind Sendable _ _ _).mpr
        (EverySend.mono (fun _ _ carried => carried)
          (fun reply _ => EverySend.interpretWith resends (next reply.1) reply.2 (sent reply.1))
          (resends (.sample site law inputs) state True.intro))
  | .call (.read site type position) next, state, sent =>
      (everySend_bind Sendable _ _ _).mpr
        (EverySend.mono (fun _ _ carried => carried)
          (fun reply _ => EverySend.interpretWith resends (next reply.1) reply.2 (sent reply.1))
          (resends (.read site type position) state True.intro))

/-- A process of which every run returns runs, under every sampler and from all counters,
to a value of which the two conditions hold. -/
theorem EveryRun.runs {α : Type} {holds sends : α → Prop}
    {Sendable : (type : Ty) → model.Value type → Prop} (sampler : Sampler model) :
    ∀ (process : PIR.Process (Effects model) α), EveryRun holds process →
      EverySend Sendable sends process → ∀ asked : Asked,
        ∃ value final, holds value ∧ sends value ∧ RunsTo sampler process asked value final
  | .done value, every, sent, asked => ⟨value, asked, every, sent, .done value asked⟩
  | .halt _, every, _, _ => every.elim
  | .call (.draw site law inputs) next, every, sent, asked => by
      obtain ⟨value, final, held, carried, runs⟩ :=
        EveryRun.runs sampler (next (sampler.answer site (asked site) law)) (every _) (sent _)
          (asked.next site)
      exact ⟨value, final, held, carried, .draw site law inputs next asked value final runs⟩
  | .call (.sample site law inputs) next, every, sent, asked => by
      obtain ⟨value, final, held, carried, runs⟩ :=
        EveryRun.runs sampler (next (sampler.answer site (asked site) law)) (every _) (sent _)
          (asked.next site)
      exact ⟨value, final, held, carried, .sample site law inputs next asked value final runs⟩
  | .call (.send _ _ _) _, every, _, _ => every.elim
  | .call (.receive _ _) _, every, _, _ => every.elim
  | .call (.read _ _ _) _, every, _, _ => every.elim

end Runs

/-! ## The channel between the two parts -/

/-- What the states of the two handlers say of the messages between the two parts: the
messages that can be carried, the messages that a state of the prover's handler gains, and
the messages that a state of the verifier's handler gives. -/
structure Channel (model : Model) (Writer Reader : Type) where
  /-- The messages that can be carried. -/
  Sendable : (type : Ty) → model.Value type → Prop
  /-- The prover's state after the messages were written from a state. -/
  Written : Writer → List (Message model) → Writer → Prop
  /-- The verifier's state after the messages were taken from a state. -/
  Takes : Reader → List (Message model) → Reader → Prop
  written_nil : ∀ writer, Written writer [] writer
  written_append : ∀ {writer middle final : Writer} {first second : List (Message model)},
    Written writer first middle → Written middle second final → Written writer (first ++ second) final
  takes_nil : ∀ {reader final : Reader}, Takes reader [] final → final = reader
  takes_append : ∀ {reader final : Reader} {first second : List (Message model)},
    Takes reader (first ++ second) final →
      ∃ middle, Takes reader first middle ∧ Takes middle second final

/-- The handler that performs every effect as it is. -/
@[expose] def passHandler (model : Model) (State : Type) :
    PIR.StatefulInterpretation (Effects model) (Effects model) State :=
  fun effect state => passEffect effect state

/-- The handler that performs every effect as it is passes every process. -/
theorem passHandler_passes {model : Model} {State α : Type} :
    ∀ (process : PIR.Process (Effects model) α), PIR.Passes (passHandler model State) process
  | .done value => PIR.Passes.done _ value
  | .halt reason => PIR.Passes.halt _ reason
  | .call effect next => call_passes (fun _ => rfl) fun reply => passHandler_passes (next reply)

/-! ## The relation -/

section Relation

variable {model : Model} {Writer Reader : Type} (channel : Channel model Writer Reader)
  (proverHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Writer)
  (verifierHandler : PIR.StatefulInterpretation (Effects model) (Effects model) Reader)

/-- A grouped process, the prover's part and the verifier's part, with the handlers of the
two parts. `left` and `right` restrict a value of the grouped process to the two parts.
Whenever every run of the grouped process returns a value of which `holds` holds and every
`send` of the prover's part carries a value that the channel carries, then under every
sampler and from all counters of the two parts: the prover's part under its handler
returns its share of such a value and has written some messages, and the verifier's part
under its handler, from every state that gives these messages, returns its share of the
value. -/
structure PartsReplay {grouped first second : Type} (left : grouped → first)
    (right : grouped → second) (whole : PIR.Process (Effects model) grouped)
    (proverPart : PIR.Process (Effects model) first)
    (verifierPart : PIR.Process (Effects model) second) : Prop where
  run : ∀ (holds : grouped → Prop) (sends : first → Prop), EveryRun holds whole →
    EverySend channel.Sendable sends proverPart →
    ∀ (sampler : Sampler model) (askedProver askedVerifier : Asked) (writer : Writer),
      ∃ (value : grouped) (messages : List (Message model)) (written : Writer)
        (finalProver finalVerifier : Asked),
        holds value ∧ sends (left value) ∧ channel.Written writer messages written ∧
        RunsTo sampler (proverPart.interpretWith proverHandler writer) askedProver
          (left value, written) finalProver ∧
        ∀ (reader taken : Reader), channel.Takes reader messages taken →
          RunsTo sampler (verifierPart.interpretWith verifierHandler reader) askedVerifier
            (right value, taken) finalVerifier

variable {channel} {proverHandler} {verifierHandler} {grouped first second : Type}
  {left : grouped → first} {right : grouped → second}

/-- The relation holds of processes equal to related ones. -/
theorem PartsReplay.congr {whole : PIR.Process (Effects model) grouped}
    {proverPart proverPart' : PIR.Process (Effects model) first}
    {verifierPart verifierPart' : PIR.Process (Effects model) second}
    (sameProver : proverPart' = proverPart) (sameVerifier : verifierPart' = verifierPart)
    (replays : PartsReplay channel proverHandler verifierHandler left right whole proverPart
      verifierPart) :
    PartsReplay channel proverHandler verifierHandler left right whole proverPart' verifierPart' := by
  subst sameProver sameVerifier
  exact replays

/-- Three processes that have returned, the parts with the shares of the grouped value. -/
theorem PartsReplay.done {value : grouped} {proverValue : first} {verifierValue : second}
    (sameProver : proverValue = left value) (sameVerifier : verifierValue = right value) :
    PartsReplay channel proverHandler verifierHandler left right (.done value) (.done proverValue)
      (.done verifierValue) := by
  subst sameProver sameVerifier
  refine ⟨fun holds sends every sent sampler askedProver askedVerifier writer => ?_⟩
  refine ⟨value, [], writer, askedProver, askedVerifier, every, sent, channel.written_nil writer,
    .done _ _, ?_⟩
  intro reader taken takes
  rw [channel.takes_nil takes]
  exact .done _ _

/-- A grouped process of which no run returns is related to every two parts. -/
theorem PartsReplay.never {whole : PIR.Process (Effects model) grouped}
    {proverPart : PIR.Process (Effects model) first}
    {verifierPart : PIR.Process (Effects model) second}
    (stuck : ∀ holds : grouped → Prop, ¬EveryRun holds whole) :
    PartsReplay channel proverHandler verifierHandler left right whole proverPart verifierPart :=
  ⟨fun holds _ every => (stuck holds every).elim⟩

/-- A grouped process that stops does not return. -/
theorem PartsReplay.halt {reason : PIR.Stop} {proverPart : PIR.Process (Effects model) first}
    {verifierPart : PIR.Process (Effects model) second} :
    PartsReplay channel proverHandler verifierHandler left right (.halt reason) proverPart
      verifierPart :=
  PartsReplay.never fun _ every => every

/-- A grouped process that sends to a role outside it does not return alone. -/
theorem PartsReplay.send {site : Site} {type : Ty} {value : model.Value type}
    {next : PUnit → PIR.Process (Effects model) grouped}
    {proverPart : PIR.Process (Effects model) first}
    {verifierPart : PIR.Process (Effects model) second} :
    PartsReplay channel proverHandler verifierHandler left right (.call (.send site type value) next)
      proverPart verifierPart :=
  PartsReplay.never fun _ every => every

/-- A grouped process that receives from a role outside it does not return alone. -/
theorem PartsReplay.receive {site : Site} {type : Ty}
    {next : model.Value type → PIR.Process (Effects model) grouped}
    {proverPart : PIR.Process (Effects model) first}
    {verifierPart : PIR.Process (Effects model) second} :
    PartsReplay channel proverHandler verifierHandler left right (.call (.receive site type) next)
      proverPart verifierPart :=
  PartsReplay.never fun _ every => every

/-- Sequencing: the parts of a sequence are the sequences of the parts, and the messages
of the sequence are the messages of its parts, in order. -/
theorem PartsReplay.bind {grouped' first' second' : Type} {left' : grouped' → first'}
    {right' : grouped' → second'} {whole : PIR.Process (Effects model) grouped}
    {proverPart : PIR.Process (Effects model) first}
    {verifierPart : PIR.Process (Effects model) second}
    {wholeNext : grouped → PIR.Process (Effects model) grouped'}
    {proverNext : first → PIR.Process (Effects model) first'}
    {verifierNext : second → PIR.Process (Effects model) second'}
    (before : PartsReplay channel proverHandler verifierHandler left right whole proverPart
      verifierPart)
    (after : ∀ value, PartsReplay channel proverHandler verifierHandler left' right' (wholeNext value)
      (proverNext (left value)) (verifierNext (right value))) :
    PartsReplay channel proverHandler verifierHandler left' right' (whole.bind wholeNext)
      (proverPart.bind proverNext) (verifierPart.bind verifierNext) := by
  refine ⟨fun holds sends every sent sampler askedProver askedVerifier writer => ?_⟩
  obtain ⟨value, messages, written, middleProver, middleVerifier, held, carried, wrote, runsProver,
      runsVerifier⟩ :=
    before.run _ _ ((everyRun_bind holds wholeNext whole).mp every)
      ((everySend_bind channel.Sendable sends proverNext proverPart).mp sent) sampler askedProver
      askedVerifier writer
  obtain ⟨result, later, final, finalProver, finalVerifier, heldResult, carriedResult, wroteLater,
      runsProverNext, runsVerifierNext⟩ :=
    (after value).run holds sends held carried sampler middleProver middleVerifier written
  refine ⟨result, messages ++ later, final, finalProver, finalVerifier, heldResult, carriedResult,
    channel.written_append wrote wroteLater, ?_, ?_⟩
  · rw [PIR.Process.interpretWith_bind]
    exact runsProver.bind runsProverNext
  · intro reader taken takes
    obtain ⟨middle, takesFirst, takesLater⟩ := channel.takes_append takes
    rw [PIR.Process.interpretWith_bind]
    exact (runsVerifier reader middle takesFirst).bind (runsVerifierNext middle taken takesLater)

/-- Iterations: the parts of a loop are the loops of the parts, when what a step produces
carries and collects in the parts as its shares. -/
theorem PartsReplay.iterations {produced firstProduced secondProduced : Type}
    {collected firstCollected secondCollected : Nat → Type}
    {left : grouped → first} {right : grouped → second}
    (leftProduced : produced → firstProduced) (rightProduced : produced → secondProduced)
    (leftCollected : (done : Nat) → collected done → firstCollected done)
    (rightCollected : (done : Nat) → collected done → secondCollected done)
    {wholeStep : Nat → grouped → PIR.Process (Effects model) produced}
    {firstStep : Nat → first → PIR.Process (Effects model) firstProduced}
    {secondStep : Nat → second → PIR.Process (Effects model) secondProduced}
    {carry : produced → grouped} {carryFirst : firstProduced → first}
    {carrySecond : secondProduced → second}
    {push : (done : Nat) → produced → collected done → collected (done + 1)}
    {pushFirst : (done : Nat) → firstProduced → firstCollected done → firstCollected (done + 1)}
    {pushSecond : (done : Nat) → secondProduced → secondCollected done →
      secondCollected (done + 1)}
    (step : ∀ iteration value, PartsReplay channel proverHandler verifierHandler leftProduced
      rightProduced (wholeStep iteration value) (firstStep iteration (left value))
      (secondStep iteration (right value)))
    (carriesFirst : ∀ made, carryFirst (leftProduced made) = left (carry made))
    (carriesSecond : ∀ made, carrySecond (rightProduced made) = right (carry made))
    (pushesFirst : ∀ done made earlier,
      pushFirst done (leftProduced made) (leftCollected done earlier) =
        leftCollected (done + 1) (push done made earlier))
    (pushesSecond : ∀ done made earlier,
      pushSecond done (rightProduced made) (rightCollected done earlier) =
        rightCollected (done + 1) (push done made earlier)) :
    ∀ (remaining done : Nat) (value : grouped) (earlier : collected done),
      PartsReplay channel proverHandler verifierHandler
        (fun final : grouped × collected (iterationsAfter remaining done) =>
          (left final.1, leftCollected _ final.2))
        (fun final : grouped × collected (iterationsAfter remaining done) =>
          (right final.1, rightCollected _ final.2))
        (Core.iterations wholeStep carry push remaining done value earlier)
        (Core.iterations firstStep carryFirst pushFirst remaining done (left value)
          (leftCollected done earlier))
        (Core.iterations secondStep carrySecond pushSecond remaining done (right value)
          (rightCollected done earlier))
  | 0, _, _, _ => PartsReplay.done rfl rfl
  | remaining + 1, done, value, earlier =>
      PartsReplay.bind (step done value) fun made => by
        rw [carriesFirst, carriesSecond, pushesFirst, pushesSecond]
        exact PartsReplay.iterations leftProduced rightProduced leftCollected rightCollected step
          carriesFirst carriesSecond pushesFirst pushesSecond remaining (done + 1) (carry made)
          (push done made earlier)

/-! ## A part that performs what the grouped process performs -/

/-- A part of a grouped process that draws and samples where the grouped process does, at
the same sites and with the same laws, and returns its share of what the grouped process
returns. A grouped process of which no run returns is mirrored by every process. -/
inductive Mirrors {grouped part : Type} (share : grouped → part) :
    PIR.Process (Effects model) grouped → PIR.Process (Effects model) part → Prop where
  | done {value : grouped} {partValue : part} (same : partValue = share value) :
      Mirrors share (.done value) (.done partValue)
  | never {whole : PIR.Process (Effects model) grouped} {process : PIR.Process (Effects model) part}
      (stuck : ∀ holds : grouped → Prop, ¬EveryRun holds whole) : Mirrors share whole process
  | draw {site : Site} {law : SamplingRow} {inputs partInputs : Values model.Value law.inputs}
      {next : model.Value law.output → PIR.Process (Effects model) grouped}
      {partNext : model.Value law.output → PIR.Process (Effects model) part} :
      (∀ reply, Mirrors share (next reply) (partNext reply)) →
        Mirrors share (.call (.draw site law inputs) next) (.call (.draw site law partInputs) partNext)
  | sample {site : Site} {law : SamplingRow} {inputs partInputs : Values model.Value law.inputs}
      {next : model.Value law.output → PIR.Process (Effects model) grouped}
      {partNext : model.Value law.output → PIR.Process (Effects model) part} :
      (∀ reply, Mirrors share (next reply) (partNext reply)) →
        Mirrors share (.call (.sample site law inputs) next)
          (.call (.sample site law partInputs) partNext)

/-- A process mirrors itself, for a share that is the value. -/
theorem Mirrors.refl {share : grouped → grouped} (sameValue : ∀ value, share value = value) :
    ∀ (process : PIR.Process (Effects model) grouped), Mirrors share process process
  | .done value => .done (sameValue value).symm
  | .halt _ => .never fun _ every => every
  | .call (.draw _ _ _) next => .draw fun reply => Mirrors.refl sameValue (next reply)
  | .call (.sample _ _ _) next => .sample fun reply => Mirrors.refl sameValue (next reply)
  | .call (.send _ _ _) _ => .never fun _ every => every
  | .call (.receive _ _) _ => .never fun _ every => every
  | .call (.read _ _ _) _ => .never fun _ every => every

/-- A part that mirrors a grouped process of which every run returns runs, under every
sampler and from all counters, to its share of a value that the grouped process returns. -/
theorem Mirrors.runs {part : Type} {share : grouped → part} {holds : grouped → Prop}
    {sends : part → Prop} {Sendable : (type : Ty) → model.Value type → Prop}
    (sampler : Sampler model) {whole : PIR.Process (Effects model) grouped}
    {process : PIR.Process (Effects model) part} (mirrors : Mirrors share whole process) :
    EveryRun holds whole → EverySend Sendable sends process → ∀ asked : Asked,
      ∃ value final, holds value ∧ sends (share value) ∧
        RunsTo sampler process asked (share value) final := by
  induction mirrors with
  | done same =>
      intro every sent asked
      subst same
      exact ⟨_, asked, every, sent, .done _ asked⟩
  | never stuck => exact fun every => (stuck _ every).elim
  | @draw site law inputs partInputs next partNext _ ih =>
      intro every sent asked
      obtain ⟨value, final, held, carried, runs⟩ :=
        ih (sampler.answer site (asked site) law) (every _) (sent _) (asked.next site)
      exact ⟨value, final, held, carried, .draw site law partInputs partNext asked _ final runs⟩
  | @sample site law inputs partInputs next partNext _ ih =>
      intro every sent asked
      obtain ⟨value, final, held, carried, runs⟩ :=
        ih (sampler.answer site (asked site) law) (every _) (sent _) (asked.next site)
      exact ⟨value, final, held, carried, .sample site law partInputs partNext asked _ final runs⟩

/-- The prover's part performs what the grouped process performs, its handler passes it,
and the verifier's part does nothing. -/
theorem PartsReplay.proverMirrors {idle : second} {whole : PIR.Process (Effects model) grouped}
    {proverPart : PIR.Process (Effects model) first} (mirrors : Mirrors left whole proverPart)
    (passes : PIR.Passes proverHandler proverPart) (absent : ∀ value, right value = idle) :
    PartsReplay channel proverHandler verifierHandler left right whole proverPart (.done idle) := by
  refine ⟨fun holds sends every sent sampler askedProver askedVerifier writer => ?_⟩
  obtain ⟨value, final, held, carried, runs⟩ := mirrors.runs sampler every sent askedProver
  refine ⟨value, [], writer, final, askedVerifier, held, carried, channel.written_nil writer, ?_, ?_⟩
  · rw [passes writer]
    exact runs.bind (.done _ _)
  · intro reader taken takes
    rw [channel.takes_nil takes, absent value]
    exact .done _ _

/-- The verifier's part performs what the grouped process performs, its handler passes it,
and the prover's part does nothing. -/
theorem PartsReplay.verifierMirrors {idle : first} {whole : PIR.Process (Effects model) grouped}
    {verifierPart : PIR.Process (Effects model) second} (mirrors : Mirrors right whole verifierPart)
    (passes : PIR.Passes verifierHandler verifierPart) (absent : ∀ value, left value = idle) :
    PartsReplay channel proverHandler verifierHandler left right whole (.done idle) verifierPart := by
  refine ⟨fun holds sends every sent sampler askedProver askedVerifier writer => ?_⟩
  obtain ⟨value, final, held, _, runs⟩ :=
    mirrors.runs sampler every (EverySend.trivial verifierPart) askedVerifier
  refine ⟨value, [], writer, askedProver, final, held, ?_, channel.written_nil writer, ?_, ?_⟩
  · rw [absent value]
    exact sent
  · rw [absent value]
    exact .done _ _
  · intro reader taken takes
    rw [channel.takes_nil takes, passes reader]
    exact runs.bind (.done _ _)

/-- Handlers that pass the two parts may replace the handlers that perform every effect as
it is. -/
theorem PartsReplay.ofPasses {whole : PIR.Process (Effects model) grouped}
    {proverPart : PIR.Process (Effects model) first}
    {verifierPart : PIR.Process (Effects model) second}
    (replays : PartsReplay channel (passHandler model Writer) (passHandler model Reader) left right
      whole proverPart verifierPart)
    (passesProver : PIR.Passes proverHandler proverPart)
    (passesVerifier : PIR.Passes verifierHandler verifierPart) :
    PartsReplay channel proverHandler verifierHandler left right whole proverPart verifierPart := by
  refine ⟨fun holds sends every sent sampler askedProver askedVerifier writer => ?_⟩
  obtain ⟨value, messages, written, finalProver, finalVerifier, held, carried, wrote, runsProver,
      runsVerifier⟩ := replays.run holds sends every sent sampler askedProver askedVerifier writer
  refine ⟨value, messages, written, finalProver, finalVerifier, held, carried, wrote, ?_, ?_⟩
  · rw [passesProver writer, ← passHandler_passes proverPart writer]
    exact runsProver
  · intro reader taken takes
    rw [passesVerifier reader, ← passHandler_passes verifierPart reader]
    exact runsVerifier reader taken takes

end Relation

end Zkc.Core
