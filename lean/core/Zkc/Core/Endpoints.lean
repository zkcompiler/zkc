module

public import Zkc.Core.Labelled

public section

/-! Processes run against each other, and the relation between a grouped run and the run
of its two parts.

The model has the meaning of a protocol for a side. It has no composition of processes.
This file gives one, as a relation: `ReturnTogether` holds of two processes, the messages
in transit, the coins announced so far, the number of coins that each of the two has heard
at each site, the counters of the sampler, and the values that the two return.

- **Messages.** A `send` puts its value in the mail of its site; a `receive` takes the
  oldest message of its site.
- **Public coins.** A `draw` is a broadcast, in order. It announces its coin on a board, at
  its site: the board holds, for every site, every coin announced there, in the order
  announced. Each of the two processes has a count of the coins it has heard at each site. A
  `receive` at a site without a message in transit hears the coin of the board at the count
  of its process, and the count goes up by one. This is how the meaning of `draw` for a side
  without the owner reads the coin: one `receive` per receiver, at the draw's site. A coin
  is not consumed, so both processes can hear it, and a coin that nobody hears leaves nothing
  in transit. A process hears every coin of a site once and in the order announced, whatever
  the order in which the two take their steps: a receiver that hears after a later coin was
  announced at the site hears the earlier one first.
- **Shared coins.** Draws and samples are answered by a sampler: the `k`-th one at a site
  by the sampler's `k`-th coin of that site, at the output type of its law. The output
  type of a law has a value, so a sampler has a coin for every request; it has none at a
  type without a value, and every model has a sampler (`Sampler.constant`). A site is the
  path of applications, the definition and the site number, so two applications of one
  protocol ask at different sites. The run of a grouped process (`ReturnsAlone`) and the
  run of two processes against each other use one sampler and count per site in the same
  way, so both see the same coins.

`Together` is the relation that the restriction law is stated with: a grouped process and
the processes of two parts of it, such that whenever the grouped process, followed by
anything, returns, the two parts, followed by continuations that return together on the
restricted values, return together. It is closed under sequencing (`Together.bind`) and
the iterations of a loop (`Together.iterations`).

The run of the two parts that `Together` builds is in step: a part draws, and the other part
hears the coin at once when it has a receiver. For the hearing to take the coin just
announced, the hearer must have heard every earlier coin of the site. That is not so of
every site: a draw none of whose receivers is in the other part announces a coin that the
other part never hears. `Together` is therefore stated for given `Listeners`, which say of
each site which of the two parts hears there, and for boards and counts at which each part
has heard every coin of the sites where it hears (`Listeners.HeardAll`). A part that does
not hear at a site may be behind there, which is harmless because it never hears there.
`Together.draw` is the one place where the board grows: it asks that the owner's part does
not hear at the draw's site and that the other part hears there exactly when its process
does.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The answers to draws and samples: the `k`-th coin of every site, at every type that
has a value. A draw or a sample asks at the output type of its law, which is populated,
so a sampler answers every request of a process. A type without a value has no coin, and
nothing asks for one. -/
structure Sampler (model : Model) where
  coin : Site → Nat → (type : Ty) → type.populated = true → model.Value type

/-- A sampler of every model: each coin is the value of its type that `Ty.inhabitant`
builds from the values the model reads from literals without data. A statement quantified
over samplers is therefore not vacuous. -/
def Sampler.constant (model : Model) : Sampler model where
  coin _ _ type populated := Ty.inhabitant (fun row => model.literal row []) type populated

instance {model : Model} : Inhabited (Sampler model) := ⟨.constant model⟩

/-- The answer of a sampler to the `count`-th request of a law at a site. -/
@[expose, reducible] def Sampler.answer {model : Model} (sampler : Sampler model) (site : Site)
    (count : Nat) (law : SamplingRow) : model.Value law.output :=
  sampler.coin site count law.output law.populated

/-- How often each site was asked. -/
abbrev Asked := Site → Nat

/-- One more answer at a site. -/
@[expose] def Asked.next (asked : Asked) (site : Site) : Asked :=
  fun other => if other = site then asked other + 1 else asked other

/-- A run of one process that neither sends nor receives returns a value. -/
inductive ReturnsAlone {model : Model} (sampler : Sampler model) {α : Type} :
    PIR.Process (Effects model) α → Asked → α → Prop where
  | done (value : α) (asked : Asked) : ReturnsAlone sampler (.done value) asked value
  | draw (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (asked : Asked) (value : α) :
      ReturnsAlone sampler (next (sampler.answer site (asked site) law)) (asked.next site) value →
        ReturnsAlone sampler (.call (.draw site law inputs) next) asked value
  | sample (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (asked : Asked) (value : α) :
      ReturnsAlone sampler (next (sampler.answer site (asked site) law)) (asked.next site) value →
        ReturnsAlone sampler (.call (.sample site law inputs) next) asked value

/-- The messages in transit: at every site, the oldest first. -/
abbrev Mail (model : Model) := Site → List ((type : Ty) × model.Value type)

/-- No message in transit. -/
@[expose] def Mail.empty {model : Model} : Mail model := fun _ => []

/-- One more message at a site, after those in transit. -/
@[expose] def Mail.put {model : Model} (mail : Mail model) (site : Site) (type : Ty)
    (value : model.Value type) : Mail model :=
  fun other => if other = site then mail other ++ [⟨type, value⟩] else mail other

/-- The mail with other messages at one site. -/
@[expose] def Mail.set {model : Model} (mail : Mail model) (site : Site)
    (messages : List ((type : Ty) × model.Value type)) : Mail model :=
  fun other => if other = site then messages else mail other

theorem Mail.put_empty_self {model : Model} (site : Site) (type : Ty) (value : model.Value type) :
    (Mail.empty.put site type value) site = [⟨type, value⟩] := by
  simp [Mail.put, Mail.empty]

theorem Mail.set_put_empty {model : Model} (site : Site) (type : Ty) (value : model.Value type) :
    (Mail.empty.put site type value).set site [] = Mail.empty := by
  funext other
  by_cases same : other = site <;> simp [Mail.set, Mail.put, Mail.empty, same]

/-- The public coins announced so far: at every site, every coin announced there, in the
order announced. A coin stays on the board. -/
abbrev Board (model : Model) := Site → List ((type : Ty) × model.Value type)

/-- No coin announced. -/
@[expose] def Board.empty {model : Model} : Board model := fun _ => []

/-- The board after a coin is announced at a site: the coin comes after those announced
there before. -/
@[expose] def Board.announce {model : Model} (board : Board model) (site : Site) (type : Ty)
    (value : model.Value type) : Board model :=
  fun other => if other = site then board other ++ [⟨type, value⟩] else board other

theorem Board.announce_self {model : Model} (board : Board model) (site : Site) (type : Ty)
    (value : model.Value type) :
    (board.announce site type value) site = board site ++ [⟨type, value⟩] := by
  simp [Board.announce]

theorem Board.announce_other {model : Model} (board : Board model) {site other : Site} (type : Ty)
    (value : model.Value type) (different : other ≠ site) :
    (board.announce site type value) other = board other := by
  simp [Board.announce, different]

/-- The coin announced at a site is the one after the coins announced there before. -/
theorem Board.announce_latest {model : Model} (board : Board model) (site : Site) (type : Ty)
    (value : model.Value type) :
    ((board.announce site type value) site)[(board site).length]? = some ⟨type, value⟩ := by
  rw [Board.announce_self]
  simp

/-- How many coins of each site a process has heard. -/
abbrev Heard := Site → Nat

/-- No coin heard. -/
abbrev Heard.start : Heard := fun _ => 0

/-- One more coin heard at a site. -/
@[expose] def Heard.next (heard : Heard) (site : Site) : Heard :=
  fun other => if other = site then heard other + 1 else heard other

theorem Heard.next_self (heard : Heard) (site : Site) :
    (heard.next site) site = heard site + 1 := by
  simp [Heard.next]

theorem Heard.next_other (heard : Heard) {site other : Site} (different : other ≠ site) :
    (heard.next site) other = heard other := by
  simp [Heard.next, different]

/-- Two processes run against each other return two values. Either process may take the
next step. A `send` puts its value in the mail of its site. A `receive` takes the oldest
message at its site, or, when no message is in transit there, hears a coin of its site: the
first one on the board that its process has not heard, after which the process has heard
one more. A `draw` announces its coin after those of its site. Each process has its own
count of the coins it has heard at each site, so each hears every coin of a site once, in
the order announced, whatever the order of the steps. -/
inductive ReturnTogether {model : Model} (sampler : Sampler model) {α β : Type} :
    PIR.Process (Effects model) α → PIR.Process (Effects model) β → Mail model → Board model →
      Heard → Heard → Asked → α → β → Prop where
  | done (first : α) (second : β) (mail : Mail model) (board : Board model)
      (heardLeft heardRight : Heard) (asked : Asked) :
      ReturnTogether sampler (.done first) (.done second) mail board heardLeft heardRight asked
        first second
  | sendLeft {site : Site} {type : Ty} {value : model.Value type}
      {next : PUnit → PIR.Process (Effects model) α} {other : PIR.Process (Effects model) β}
      {mail : Mail model} {board : Board model} {heardLeft heardRight : Heard} {asked : Asked}
      {first : α} {second : β} :
      ReturnTogether sampler (next PUnit.unit) other (mail.put site type value) board heardLeft
          heardRight asked first second →
        ReturnTogether sampler (.call (.send site type value) next) other mail board heardLeft
          heardRight asked first second
  | receiveLeft {site : Site} {type : Ty} {value : model.Value type}
      {rest : List ((type : Ty) × model.Value type)}
      {next : model.Value type → PIR.Process (Effects model) α}
      {other : PIR.Process (Effects model) β} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      mail site = ⟨type, value⟩ :: rest →
        ReturnTogether sampler (next value) other (mail.set site rest) board heardLeft heardRight
            asked first second →
          ReturnTogether sampler (.call (.receive site type) next) other mail board heardLeft
            heardRight asked first second
  | hearLeft {site : Site} {type : Ty} {value : model.Value type}
      {next : model.Value type → PIR.Process (Effects model) α}
      {other : PIR.Process (Effects model) β} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      mail site = [] → (board site)[heardLeft site]? = some ⟨type, value⟩ →
        ReturnTogether sampler (next value) other mail board (heardLeft.next site) heardRight
            asked first second →
          ReturnTogether sampler (.call (.receive site type) next) other mail board heardLeft
            heardRight asked first second
  | drawLeft {site : Site} {law : SamplingRow} {inputs : Values model.Value law.inputs}
      {next : model.Value law.output → PIR.Process (Effects model) α}
      {other : PIR.Process (Effects model) β} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      ReturnTogether sampler (next (sampler.answer site (asked site) law)) other mail
          (board.announce site law.output (sampler.answer site (asked site) law)) heardLeft
          heardRight (asked.next site) first second →
        ReturnTogether sampler (.call (.draw site law inputs) next) other mail board heardLeft
          heardRight asked first second
  | sampleLeft {site : Site} {law : SamplingRow} {inputs : Values model.Value law.inputs}
      {next : model.Value law.output → PIR.Process (Effects model) α}
      {other : PIR.Process (Effects model) β} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      ReturnTogether sampler (next (sampler.answer site (asked site) law)) other mail board
          heardLeft heardRight (asked.next site) first second →
        ReturnTogether sampler (.call (.sample site law inputs) next) other mail board heardLeft
          heardRight asked first second
  | sendRight {site : Site} {type : Ty} {value : model.Value type}
      {next : PUnit → PIR.Process (Effects model) β} {other : PIR.Process (Effects model) α}
      {mail : Mail model} {board : Board model} {heardLeft heardRight : Heard} {asked : Asked}
      {first : α} {second : β} :
      ReturnTogether sampler other (next PUnit.unit) (mail.put site type value) board heardLeft
          heardRight asked first second →
        ReturnTogether sampler other (.call (.send site type value) next) mail board heardLeft
          heardRight asked first second
  | receiveRight {site : Site} {type : Ty} {value : model.Value type}
      {rest : List ((type : Ty) × model.Value type)}
      {next : model.Value type → PIR.Process (Effects model) β}
      {other : PIR.Process (Effects model) α} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      mail site = ⟨type, value⟩ :: rest →
        ReturnTogether sampler other (next value) (mail.set site rest) board heardLeft heardRight
            asked first second →
          ReturnTogether sampler other (.call (.receive site type) next) mail board heardLeft
            heardRight asked first second
  | hearRight {site : Site} {type : Ty} {value : model.Value type}
      {next : model.Value type → PIR.Process (Effects model) β}
      {other : PIR.Process (Effects model) α} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      mail site = [] → (board site)[heardRight site]? = some ⟨type, value⟩ →
        ReturnTogether sampler other (next value) mail board heardLeft (heardRight.next site)
            asked first second →
          ReturnTogether sampler other (.call (.receive site type) next) mail board heardLeft
            heardRight asked first second
  | drawRight {site : Site} {law : SamplingRow} {inputs : Values model.Value law.inputs}
      {next : model.Value law.output → PIR.Process (Effects model) β}
      {other : PIR.Process (Effects model) α} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      ReturnTogether sampler other (next (sampler.answer site (asked site) law)) mail
          (board.announce site law.output (sampler.answer site (asked site) law)) heardLeft
          heardRight (asked.next site) first second →
        ReturnTogether sampler other (.call (.draw site law inputs) next) mail board heardLeft
          heardRight asked first second
  | sampleRight {site : Site} {law : SamplingRow} {inputs : Values model.Value law.inputs}
      {next : model.Value law.output → PIR.Process (Effects model) β}
      {other : PIR.Process (Effects model) α} {mail : Mail model} {board : Board model}
      {heardLeft heardRight : Heard} {asked : Asked} {first : α} {second : β} :
      ReturnTogether sampler other (next (sampler.answer site (asked site) law)) mail board
          heardLeft heardRight (asked.next site) first second →
        ReturnTogether sampler other (.call (.sample site law inputs) next) mail board heardLeft
          heardRight asked first second

/-- Two processes that have both returned return together. -/
theorem ReturnTogether.of_done {model : Model} (sampler : Sampler model) {α β : Type}
    (first : α) (second : β) :
    ReturnTogether sampler (.done first : PIR.Process (Effects model) α) (.done second)
      Mail.empty Board.empty Heard.start Heard.start (fun _ => 0) first second :=
  .done first second _ _ _ _ _

/-- The relation does not depend on which process is named first. -/
theorem ReturnTogether.swap {model : Model} {sampler : Sampler model} {α β : Type}
    {first : PIR.Process (Effects model) α} {second : PIR.Process (Effects model) β}
    {mail : Mail model} {board : Board model} {heardFirst heardSecond : Heard} {asked : Asked}
    {firstValue : α} {secondValue : β}
    (returns : ReturnTogether sampler first second mail board heardFirst heardSecond asked
      firstValue secondValue) :
    ReturnTogether sampler second first mail board heardSecond heardFirst asked secondValue
      firstValue := by
  induction returns with
  | done first second mail board heardLeft heardRight asked =>
      exact .done second first mail board heardRight heardLeft asked
  | sendLeft _ ih => exact .sendRight ih
  | receiveLeft found _ ih => exact .receiveRight found ih
  | hearLeft none announced _ ih => exact .hearRight none announced ih
  | drawLeft _ ih => exact .drawRight ih
  | sampleLeft _ ih => exact .sampleRight ih
  | sendRight _ ih => exact .sendLeft ih
  | receiveRight found _ ih => exact .receiveLeft found ih
  | hearRight none announced _ ih => exact .hearLeft none announced ih
  | drawRight _ ih => exact .drawLeft ih
  | sampleRight _ ih => exact .sampleLeft ih

/-! ## A grouped process and its two parts -/

/-- Which of two processes run against each other hears the coins of each site. A site is one
operation of one definition under one path of applications, so the processes of the two parts
of a protocol have, at every site, a fixed answer: a part hears at the site of a `draw` when
the other part has the owner and it has a receiver, and nowhere else. -/
structure Listeners where
  first : Site → Bool
  second : Site → Bool

/-- The listeners with the two processes named in the other order. -/
@[expose] def Listeners.swap (listeners : Listeners) : Listeners :=
  ⟨listeners.second, listeners.first⟩

/-- Every coin announced so far has been heard by each process that hears at its site. A
process that does not hear at a site may be behind there: it never hears there. -/
structure Listeners.HeardAll {model : Model} (listeners : Listeners) (board : Board model)
    (heardFirst heardSecond : Heard) : Prop where
  first : ∀ site, listeners.first site = true → heardFirst site = (board site).length
  second : ∀ site, listeners.second site = true → heardSecond site = (board site).length

/-- With no coin announced and none heard, every coin has been heard. -/
theorem Listeners.heardAll_start {model : Model} (listeners : Listeners) :
    listeners.HeardAll (Board.empty : Board model) Heard.start Heard.start :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Listeners.HeardAll.swap {model : Model} {listeners : Listeners} {board : Board model}
    {heardFirst heardSecond : Heard} (heardAll : listeners.HeardAll board heardFirst heardSecond) :
    listeners.swap.HeardAll board heardSecond heardFirst :=
  ⟨heardAll.second, heardAll.first⟩

section Together

variable {model : Model} (sampler : Sampler model) (listeners : Listeners)

/-- A grouped process and the processes of two parts of it. `left` and `right` restrict a
value of the grouped process to the two parts. Whenever the grouped process, followed by
anything, returns, the two parts, followed by continuations that return together on the
restricted values, return together: with the same coins, from an empty mail to an empty
mail, from a board and counts at which each part has heard every coin of the sites where it
hears (`Listeners.HeardAll`) to a board and counts at which it has again. -/
structure Together {grouped first second : Type} (left : grouped → first)
    (right : grouped → second) (whole : PIR.Process (Effects model) grouped)
    (firstPart : PIR.Process (Effects model) first)
    (secondPart : PIR.Process (Effects model) second) : Prop where
  run : ∀ {γ α β : Type} (afterWhole : grouped → PIR.Process (Effects model) γ)
    (afterFirst : first → PIR.Process (Effects model) α)
    (afterSecond : second → PIR.Process (Effects model) β) (board : Board model)
    (heardFirst heardSecond : Heard) (asked : Asked)
    (result : γ) (firstResult : α) (secondResult : β),
    listeners.HeardAll board heardFirst heardSecond →
    (∀ (value : grouped) (later : Board model) (laterFirst laterSecond : Heard) (counted : Asked),
      listeners.HeardAll later laterFirst laterSecond →
      ReturnsAlone sampler (afterWhole value) counted result →
        ReturnTogether sampler (afterFirst (left value)) (afterSecond (right value)) Mail.empty
          later laterFirst laterSecond counted firstResult secondResult) →
    ReturnsAlone sampler (whole.bind afterWhole) asked result →
      ReturnTogether sampler (firstPart.bind afterFirst) (secondPart.bind afterSecond) Mail.empty
        board heardFirst heardSecond asked firstResult secondResult

variable {sampler} {listeners} {grouped first second : Type} {left : grouped → first}
  {right : grouped → second}

/-- Three processes that have returned, the parts with the restrictions of the grouped
value. -/
theorem Together.done {value : grouped} {firstValue : first} {secondValue : second}
    (sameFirst : firstValue = left value) (sameSecond : secondValue = right value) :
    Together sampler listeners left right (.done value) (.done firstValue) (.done secondValue) := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  subst sameFirst sameSecond
  exact continues value board heardFirst heardSecond asked heardAll returns

/-- A grouped process that stops does not return. -/
theorem Together.halt {reason : PIR.Stop} {firstPart : PIR.Process (Effects model) first}
    {secondPart : PIR.Process (Effects model) second} :
    Together sampler listeners left right (.halt reason) firstPart secondPart := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  have stopped : ReturnsAlone sampler (.halt reason : PIR.Process (Effects model) γ) asked result :=
    returns
  cases stopped

/-- A grouped process that sends to a role outside it does not return alone. -/
theorem Together.send {site : Site} {type : Ty} {value : model.Value type}
    {next : PUnit → PIR.Process (Effects model) grouped}
    {firstPart : PIR.Process (Effects model) first}
    {secondPart : PIR.Process (Effects model) second} :
    Together sampler listeners left right (.call (.send site type value) next) firstPart
      secondPart := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  have waits : ReturnsAlone sampler
      (.call (.send site type value) fun reply => (next reply).bind afterWhole) asked result :=
    returns
  cases waits

/-- A grouped process that receives from a role outside it does not return alone. -/
theorem Together.receive {site : Site} {type : Ty}
    {next : model.Value type → PIR.Process (Effects model) grouped}
    {firstPart : PIR.Process (Effects model) first}
    {secondPart : PIR.Process (Effects model) second} :
    Together sampler listeners left right (.call (.receive site type) next) firstPart
      secondPart := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  have waits : ReturnsAlone sampler
      (.call (.receive site type) fun reply => (next reply).bind afterWhole) asked result :=
    returns
  cases waits

/-- Sequencing: the parts of a sequence are the sequences of the parts. -/
theorem Together.bind {grouped' first' second' : Type} {left' : grouped' → first'}
    {right' : grouped' → second'} {whole : PIR.Process (Effects model) grouped}
    {firstPart : PIR.Process (Effects model) first}
    {secondPart : PIR.Process (Effects model) second}
    {wholeNext : grouped → PIR.Process (Effects model) grouped'}
    {firstNext : first → PIR.Process (Effects model) first'}
    {secondNext : second → PIR.Process (Effects model) second'}
    (before : Together sampler listeners left right whole firstPart secondPart)
    (after : ∀ value, Together sampler listeners left' right' (wholeNext value)
      (firstNext (left value)) (secondNext (right value))) :
    Together sampler listeners left' right' (whole.bind wholeNext) (firstPart.bind firstNext)
      (secondPart.bind secondNext) := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  rw [PIR.Process.bind_assoc] at returns ⊢
  rw [PIR.Process.bind_assoc]
  exact before.run _ _ _ board heardFirst heardSecond asked result firstResult secondResult heardAll
    (fun value later laterFirst laterSecond counted caught returned =>
      (after value).run afterWhole afterFirst afterSecond later laterFirst laterSecond counted
        result firstResult secondResult caught continues returned)
    returns

/-- The relation does not depend on which part is named first. -/
theorem Together.swap {whole : PIR.Process (Effects model) grouped}
    {firstPart : PIR.Process (Effects model) first}
    {secondPart : PIR.Process (Effects model) second}
    (together : Together sampler listeners left right whole firstPart secondPart) :
    Together sampler listeners.swap right left whole secondPart firstPart := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterSecond afterFirst board heardSecond heardFirst asked result
    secondResult firstResult heardAll continues returns
  exact (together.run afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult ⟨heardAll.second, heardAll.first⟩
    (fun value later laterFirst laterSecond counted caught returned =>
      (continues value later laterSecond laterFirst counted caught.swap returned).swap)
    returns).swap

/-- A sample by the first part: the grouped process samples at the same site, and the second
part does nothing. -/
theorem Together.sample {site : Site} {law : SamplingRow}
    {wholeInputs firstInputs : Values model.Value law.inputs}
    {wholeValue : model.Value law.output → grouped} {firstValue : model.Value law.output → first}
    {secondValue : second}
    (sameFirst : ∀ reply, firstValue reply = left (wholeValue reply))
    (sameSecond : ∀ reply, secondValue = right (wholeValue reply)) :
    Together sampler listeners left right
      (.call (.sample site law wholeInputs) fun reply => .done (wholeValue reply))
      (.call (.sample site law firstInputs) fun reply => .done (firstValue reply))
      (.done secondValue) := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  have running : ReturnsAlone sampler
      (.call (.sample site law wholeInputs) fun reply => afterWhole (wholeValue reply)) asked
      result := returns
  cases running with
  | sample _ _ _ _ _ _ returned =>
      refine .sampleLeft ?_
      have continued := continues _ board heardFirst heardSecond _ heardAll returned
      rw [← sameFirst, ← sameSecond] at continued
      exact continued

/-- A message from the first part to the second: the grouped process has it at once. -/
theorem Together.message {site : Site} {type : Ty} {value : model.Value type}
    {wholeValue : grouped} {firstValue : first} {secondValue : model.Value type → second}
    (sameFirst : firstValue = left wholeValue) (sameSecond : secondValue value = right wholeValue) :
    Together sampler listeners left right (.done wholeValue)
      (.call (.send site type value) fun _ => .done firstValue)
      (.call (.receive site type) fun reply => .done (secondValue reply)) := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  refine .sendLeft (.receiveRight (value := value) (rest := [])
    (Mail.put_empty_self site type value) ?_)
  rw [Mail.set_put_empty]
  have continued := continues wholeValue board heardFirst heardSecond asked heardAll returns
  rw [← sameFirst, ← sameSecond] at continued
  exact continued

/-- Iterations: the parts of a loop are the loops of the parts, when what a step produces
carries and collects in the parts as its restrictions. -/
theorem Together.iterations {produced firstProduced secondProduced : Type}
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
    (step : ∀ iteration value, Together sampler listeners leftProduced rightProduced
      (wholeStep iteration value) (firstStep iteration (left value))
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
      Together sampler listeners
        (fun final : grouped × collected (iterationsAfter remaining done) =>
          (left final.1, leftCollected _ final.2))
        (fun final : grouped × collected (iterationsAfter remaining done) =>
          (right final.1, rightCollected _ final.2))
        (Core.iterations wholeStep carry push remaining done value earlier)
        (Core.iterations firstStep carryFirst pushFirst remaining done (left value)
          (leftCollected done earlier))
        (Core.iterations secondStep carrySecond pushSecond remaining done (right value)
          (rightCollected done earlier))
  | 0, _, _, _ => Together.done rfl rfl
  | remaining + 1, done, value, earlier =>
      Together.bind (step done value) fun made => by
        rw [carriesFirst, carriesSecond, pushesFirst, pushesSecond]
        exact Together.iterations leftProduced rightProduced leftCollected rightCollected step
          carriesFirst carriesSecond pushesFirst pushesSecond remaining (done + 1) (carry made)
          (push done made earlier)

/-- Steps that return without an effect: the iterations return. -/
theorem iterations_idle {I : PIR.Signature} {State Produced : Type} {Collected : Nat → Type}
    {step : Nat → State → PIR.Process I Produced} {carry : Produced → State}
    {push : (done : Nat) → Produced → Collected done → Collected (done + 1)}
    (idle : ∀ iteration state, ∃ produced, step iteration state = .done produced) :
    ∀ (remaining done : Nat) (state : State) (earlier : Collected done),
      ∃ final, Core.iterations step carry push remaining done state earlier = .done final
  | 0, _, state, earlier => ⟨(state, earlier), rfl⟩
  | remaining + 1, done, state, earlier => by
      obtain ⟨produced, returns⟩ := idle done state
      obtain ⟨final, rest⟩ := iterations_idle idle remaining (done + 1) (carry produced)
        (push done produced earlier)
      refine ⟨final, ?_⟩
      show (step done state).bind _ = _
      rw [returns]
      exact rest

end Together

/-! ## Hearing a public coin -/

section Hears

variable {model : Model} (sampler : Sampler model)

/-- A process that, run against any other, hears at most one coin of a site and returns a
value. When it listens, it hears the coin once: the coin is the one at its count of the site,
and it has then heard one more. When it does not listen, it performs nothing. -/
structure Hears (site : Site) (type : Ty) (coin : model.Value type) (listening : Bool)
    {X : Type} (process : PIR.Process (Effects model) X) (value : X) : Prop where
  run : ∀ {α β : Type} (other : PIR.Process (Effects model) α)
    (after : X → PIR.Process (Effects model) β) (board : Board model) (heardOther heard : Heard)
    (asked : Asked) (otherResult : α) (result : β),
    (listening = true → (board site)[heard site]? = some ⟨type, coin⟩) →
      ReturnTogether sampler other (after value) Mail.empty board heardOther
          (cond listening (heard.next site) heard) asked otherResult result →
        ReturnTogether sampler other (process.bind after) Mail.empty board heardOther heard asked
          otherResult result

variable {sampler} {site : Site} {type : Ty} {coin : model.Value type}

/-- A process that has returned hears nothing. -/
theorem Hears.done {X : Type} (value : X) :
    Hears sampler site type coin false (.done value : PIR.Process (Effects model) X) value :=
  ⟨fun _ _ _ _ _ _ _ _ _ returns => returns⟩

/-- One `receive` at the site hears the coin. -/
theorem Hears.receive {X : Type} (result : model.Value type → X) :
    Hears sampler site type coin true
      (.call (.receive site type) fun reply => .done (result reply)) (result coin) :=
  ⟨fun _ _ _ _ _ _ _ _ announced returns => .hearRight rfl (announced rfl) returns⟩

/-- A process that hears and one that follows it, of which at most one listens. -/
theorem Hears.bind {X Y : Type} {process : PIR.Process (Effects model) X} {value : X}
    {next : X → PIR.Process (Effects model) Y} {result : Y} {listensBefore listensAfter : Bool}
    (before : Hears sampler site type coin listensBefore process value)
    (after : Hears sampler site type coin listensAfter (next value) result)
    (once : (listensBefore && listensAfter) = false) :
    Hears sampler site type coin (listensBefore || listensAfter) (process.bind next) result := by
  refine ⟨?_⟩
  intro α β other continuation board heardOther heard asked otherResult final announced returns
  rw [PIR.Process.bind_assoc]
  cases listensBefore <;> cases listensAfter
  · exact before.run other _ board heardOther heard asked otherResult final
      (fun listens => nomatch listens)
      (after.run other continuation board heardOther heard asked otherResult final
        (fun listens => nomatch listens) returns)
  · exact before.run other _ board heardOther heard asked otherResult final
      (fun listens => nomatch listens)
      (after.run other continuation board heardOther heard asked otherResult final announced
        returns)
  · exact before.run other _ board heardOther heard asked otherResult final announced
      (after.run other continuation board heardOther (heard.next site) asked otherResult final
        (fun listens => nomatch listens) returns)
  · cases once

/-- A draw by the first part: it announces the coin, the second part hears it when it listens
at the site, and the grouped process has it at once. The first part does not hear at the site
of its own draw, and the second part hears there exactly when it listens. -/
theorem Together.draw {listeners : Listeners} {grouped first second : Type}
    {left : grouped → first} {right : grouped → second} {site : Site} {law : SamplingRow}
    {wholeInputs firstInputs : Values model.Value law.inputs}
    {wholeValue : model.Value law.output → grouped} {firstValue : model.Value law.output → first}
    {hearing : PIR.Process (Effects model) second} {heard : model.Value law.output → second}
    {listening : Bool} (ownerSilent : listeners.first site = false)
    (hearer : listeners.second site = listening)
    (sameFirst : ∀ reply, firstValue reply = left (wholeValue reply))
    (hears : ∀ reply, Hears sampler site law.output reply listening hearing (heard reply))
    (sameSecond : ∀ reply, heard reply = right (wholeValue reply)) :
    Together sampler listeners left right
      (.call (.draw site law wholeInputs) fun reply => .done (wholeValue reply))
      (.call (.draw site law firstInputs) fun reply => .done (firstValue reply)) hearing := by
  refine ⟨?_⟩
  intro γ α β afterWhole afterFirst afterSecond board heardFirst heardSecond asked result
    firstResult secondResult heardAll continues returns
  have running : ReturnsAlone sampler
      (.call (.draw site law wholeInputs) fun reply => afterWhole (wholeValue reply)) asked
      result := returns
  cases running with
  | draw _ _ _ _ _ _ returned =>
      refine .drawLeft ?_
      refine (hears (sampler.answer site (asked site) law)).run _ afterSecond _ heardFirst
        heardSecond _ firstResult secondResult ?_ ?_
      · intro listens
        rw [heardAll.second site (hearer.trans listens)]
        exact Board.announce_latest board site law.output _
      · have caught : listeners.HeardAll
            (board.announce site law.output (sampler.answer site (asked site) law)) heardFirst
            (cond listening (heardSecond.next site) heardSecond) := by
          refine ⟨fun other listens => ?_, fun other listens => ?_⟩
          · by_cases same : other = site
            · subst same
              rw [ownerSilent] at listens
              cases listens
            · rw [Board.announce_other board _ _ same]
              exact heardAll.first other listens
          · by_cases same : other = site
            · subst same
              have listens' : listening = true := hearer.symm.trans listens
              subst listens'
              show (heardSecond.next other) other = _
              rw [Heard.next_self, Board.announce_self, heardAll.second other listens]
              simp
            · rw [Board.announce_other board _ _ same]
              cases listening
              · exact heardAll.second other listens
              · show (heardSecond.next site) other = _
                rw [Heard.next_other heardSecond same]
                exact heardAll.second other listens
        have continued := continues _ _ _ _ _ caught returned
        rw [← sameFirst, ← sameSecond] at continued
        exact continued

end Hears

end Zkc.Core
