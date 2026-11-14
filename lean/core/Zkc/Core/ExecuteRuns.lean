module

public import Zkc.Core.Execute
public import Zkc.Core.EndpointsCompleteness

@[expose] public section

/-! The executor's runs are runs of the relations that the endpoint statements are about.

The sampler of a run is the one that its source of coins gives (`Coins.sampler`): a run that
ends took only coins that the source has.

- One process. A run that returns values: the process returns alone with those values under
  that sampler (`runAlone_returned`, `ReturnsAlone`). A run that stops: the process stops
  alone with that reason (`runAlone_stopped`, `StopsAlone`, the relation `ReturnsAlone` with a
  stop in the place of the return).
- Two processes against each other. A run in which both return: the two return together with
  those values (`run_together`, `ReturnTogether`), without a condition on the run. Every effect
  that the executor performs is a step of the relation (`move_performs`, `Performs`): the mail
  and the board of the run are the relation's, and the count of the coins that a process has
  heard is the relation's count. A process that hears a coin of a site after a later one was
  announced there hears the earlier one first, in both.
- Under a limit. A process that is another one cut where a row reaches the limit returns alone,
  stops alone or returns together only as the whole one does (`ReturnsAlone.of_within`,
  `Execute.StopsAlone.of_within`, `ReturnTogether.of_within`): a run under the limit that returns or
  stops is a run of the meaning without the limit.
-/

set_option autoImplicit false

namespace Zkc.Core.Execute

open Zkc.Source

variable {model : Model}

/-- The sampler of a source of coins answers with the coin that the source has. -/
theorem Coins.sampler_answer (coins : Coins model) {site : Site} {count : Nat}
    {law : SamplingRow} {reply : model.Value law.output}
    (given : coins site count law.output = some reply) :
    coins.sampler.answer site count law = reply := by
  simp [Sampler.answer, Coins.sampler, given]

/-! ## One process -/

/-- A run of one process that neither sends nor receives stops with a reason. -/
inductive StopsAlone (sampler : Sampler model) {α : Type} :
    PIR.Process (Effects model) α → Zkc.Core.Asked → PIR.Stop → Prop where
  | halt (reason : PIR.Stop) (asked : Zkc.Core.Asked) :
      StopsAlone sampler (.halt reason) asked reason
  | draw (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (asked : Zkc.Core.Asked)
      (reason : PIR.Stop) :
      StopsAlone sampler (next (sampler.answer site (asked site) law)) (asked.next site) reason →
        StopsAlone sampler (.call (.draw site law inputs) next) asked reason
  | sample (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (asked : Zkc.Core.Asked)
      (reason : PIR.Stop) :
      StopsAlone sampler (next (sampler.answer site (asked site) law)) (asked.next site) reason →
        StopsAlone sampler (.call (.sample site law inputs) next) asked reason

/-- A run of one process that returns values: the process returns alone with those values,
under the sampler of the source of coins. -/
theorem runAlone_returned (coins : Coins model) (reserved : Option Nat) {α : Type} :
    ∀ (process : PIR.Process (Effects model) α) (asked : Zkc.Core.Asked) (value : α),
      runAlone model coins process asked reserved = .returned value →
        ReturnsAlone coins.sampler process asked value
  | .done found, asked, value, ran => by
    unfold runAlone at ran
    split at ran
    · cases ran
    · cases ran
      exact .done _ _
  | .halt reason, asked, value, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran
  | .call (.draw site law inputs) next, asked, value, ran => by
    unfold runAlone at ran
    split at ran
    · cases ran
    · cases given : coins site (asked site) law.output with
      | none => simp [given] at ran
      | some reply =>
        simp only [given] at ran
        have later := runAlone_returned coins reserved (next reply) (asked.next site) value ran
        rw [← Coins.sampler_answer coins given] at later
        exact .draw site law inputs next asked value later
  | .call (.sample site law inputs) next, asked, value, ran => by
    unfold runAlone at ran
    split at ran
    · cases ran
    · cases given : coins site (asked site) law.output with
      | none => simp [given] at ran
      | some reply =>
        simp only [given] at ran
        have later := runAlone_returned coins reserved (next reply) (asked.next site) value ran
        rw [← Coins.sampler_answer coins given] at later
        exact .sample site law inputs next asked value later
  | .call (.send ..) _, asked, value, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran
  | .call (.receive ..) _, asked, value, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran
  | .call (.read ..) _, asked, value, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran

/-- A run of one process that stops: the process stops alone with that reason, under the
sampler of the source of coins. -/
theorem runAlone_stopped (coins : Coins model) (reserved : Option Nat) {α : Type} :
    ∀ (process : PIR.Process (Effects model) α) (asked : Zkc.Core.Asked) (reason : PIR.Stop),
      runAlone model coins process asked reserved = .stopped reason →
        StopsAlone coins.sampler process asked reason
  | .done found, asked, reason, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran
  | .halt found, asked, reason, ran => by
    unfold runAlone at ran
    split at ran
    · cases ran
    · cases ran
      exact .halt _ _
  | .call (.draw site law inputs) next, asked, reason, ran => by
    unfold runAlone at ran
    split at ran
    · cases ran
    · cases given : coins site (asked site) law.output with
      | none => simp [given] at ran
      | some reply =>
        simp only [given] at ran
        have later := runAlone_stopped coins reserved (next reply) (asked.next site) reason ran
        rw [← Coins.sampler_answer coins given] at later
        exact .draw site law inputs next asked reason later
  | .call (.sample site law inputs) next, asked, reason, ran => by
    unfold runAlone at ran
    split at ran
    · cases ran
    · cases given : coins site (asked site) law.output with
      | none => simp [given] at ran
      | some reply =>
        simp only [given] at ran
        have later := runAlone_stopped coins reserved (next reply) (asked.next site) reason ran
        rw [← Coins.sampler_answer coins given] at later
        exact .sample site law inputs next asked reason later
  | .call (.send ..) _, asked, reason, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran
  | .call (.receive ..) _, asked, reason, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran
  | .call (.read ..) _, asked, reason, ran => by
    unfold runAlone at ran
    split at ran <;> cases ran

/-! ## Two processes against each other -/

/-- One effect of a process as the relation `ReturnTogether` performs it: the process, the
mail, the board, the count of the coins that the process has heard and the counters before it
and after it. -/
inductive Performs (sampler : Sampler model) {α : Type} :
    PIR.Process (Effects model) α → Zkc.Core.Mail model → Zkc.Core.Board model → Heard →
      Zkc.Core.Asked → PIR.Process (Effects model) α → Zkc.Core.Mail model →
      Zkc.Core.Board model → Heard → Zkc.Core.Asked → Prop where
  | send (site : Site) (type : Ty) (value : model.Value type)
      (next : PUnit → PIR.Process (Effects model) α) (mail : Zkc.Core.Mail model)
      (board : Zkc.Core.Board model) (heard : Heard) (asked : Zkc.Core.Asked) :
      Performs sampler (.call (.send site type value) next) mail board heard asked
        (next PUnit.unit) (mail.put site type value) board heard asked
  | receive (site : Site) (type : Ty) (value : model.Value type)
      (rest : List ((type : Ty) × model.Value type))
      (next : model.Value type → PIR.Process (Effects model) α) (mail : Zkc.Core.Mail model)
      (board : Zkc.Core.Board model) (heard : Heard) (asked : Zkc.Core.Asked) :
      mail site = ⟨type, value⟩ :: rest →
        Performs sampler (.call (.receive site type) next) mail board heard asked (next value)
          (mail.set site rest) board heard asked
  | hear (site : Site) (type : Ty) (value : model.Value type)
      (next : model.Value type → PIR.Process (Effects model) α) (mail : Zkc.Core.Mail model)
      (board : Zkc.Core.Board model) (heard : Heard) (asked : Zkc.Core.Asked) :
      mail site = [] → (board site)[heard site]? = some ⟨type, value⟩ →
        Performs sampler (.call (.receive site type) next) mail board heard asked (next value)
          mail board (heard.next site) asked
  | draw (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (mail : Zkc.Core.Mail model)
      (board : Zkc.Core.Board model) (heard : Heard) (asked : Zkc.Core.Asked) :
      Performs sampler (.call (.draw site law inputs) next) mail board heard asked
        (next (sampler.answer site (asked site) law)) mail
        (board.announce site law.output (sampler.answer site (asked site) law)) heard
        (asked.next site)
  | sample (site : Site) (law : SamplingRow) (inputs : Values model.Value law.inputs)
      (next : model.Value law.output → PIR.Process (Effects model) α) (mail : Zkc.Core.Mail model)
      (board : Zkc.Core.Board model) (heard : Heard) (asked : Zkc.Core.Asked) :
      Performs sampler (.call (.sample site law inputs) next) mail board heard asked
        (next (sampler.answer site (asked site) law)) mail board heard (asked.next site)

/-- An effect of the first process, and then the two return together. -/
theorem Performs.left {sampler : Sampler model} {α β : Type}
    {process later : PIR.Process (Effects model) α} {other : PIR.Process (Effects model) β}
    {mail mail' : Zkc.Core.Mail model} {board board' : Zkc.Core.Board model}
    {heard heard' heardOther : Heard} {asked asked' : Zkc.Core.Asked} {first : α} {second : β}
    (performs : Performs sampler process mail board heard asked later mail' board' heard' asked')
    (together : ReturnTogether sampler later other mail' board' heard' heardOther asked' first
      second) :
    ReturnTogether sampler process other mail board heard heardOther asked first second := by
  cases performs with
  | send => exact .sendLeft together
  | receive _ _ _ _ _ _ _ _ _ oldest => exact .receiveLeft oldest together
  | hear _ _ _ _ _ _ _ _ empty announced => exact .hearLeft empty announced together
  | draw => exact .drawLeft together
  | sample => exact .sampleLeft together

/-- An effect of the second process, and then the two return together. -/
theorem Performs.right {sampler : Sampler model} {α β : Type}
    {process later : PIR.Process (Effects model) β} {other : PIR.Process (Effects model) α}
    {mail mail' : Zkc.Core.Mail model} {board board' : Zkc.Core.Board model}
    {heard heard' heardOther : Heard} {asked asked' : Zkc.Core.Asked} {first : α} {second : β}
    (performs : Performs sampler process mail board heard asked later mail' board' heard' asked')
    (together : ReturnTogether sampler other later mail' board' heardOther heard' asked' first
      second) :
    ReturnTogether sampler other process mail board heardOther heard asked first second := by
  cases performs with
  | send => exact .sendRight together
  | receive _ _ _ _ _ _ _ _ _ oldest => exact .receiveRight oldest together
  | hear _ _ _ _ _ _ _ _ empty announced => exact .hearRight empty announced together
  | draw => exact .drawRight together
  | sample => exact .sampleRight together

/-- The oldest message that a receive takes is the oldest message of its site, at its type. -/
theorem message?_spec {shared : Shared model} {site : Site} {type : Ty}
    {value : model.Value type} {rest : List ((type : Ty) × model.Value type)}
    (found : message? model shared site type = some (value, rest)) :
    shared.mail site = ⟨type, value⟩ :: rest := by
  unfold message? at found
  split at found
  · rename_i sent sentValue later oldest
    by_cases same : sent = type
    · subst same
      simp only [↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact oldest
    · simp [same] at found
  · cases found

/-- The coin that a role which has heard `count` coins of a site hears next is the coin of the
board at that count, at its type. -/
theorem coin?_spec {shared : Shared model} {site : Site} {count : Nat} {type : Ty}
    {value : model.Value type} (found : coin? model shared site count type = some value) :
    (shared.board site)[count]? = some ⟨type, value⟩ := by
  unfold coin? at found
  split at found
  · cases found
  · rename_i announced coin onBoard
    by_cases same : announced = type
    · subst same
      simp only [↓reduceDIte, Option.some.injEq] at found
      subst found
      exact onBoard
    · simp [same] at found

/-- An effect that the executor performs is an effect of the relation: on the mail, the board
and the counters of the run and the count of the coins that the role has heard. -/
theorem move_performs {α : Type} {coins : Coins model} {role moved : Role model α}
    {shared after : Shared model} {drew : Bool}
    (performed : move model coins role shared = .to moved after drew) :
    Performs coins.sampler role.process shared.mail shared.board role.heard shared.asked
      moved.process after.mail after.board moved.heard after.asked := by
  obtain ⟨process, heard⟩ := role
  cases process with
  | done value => simp [move] at performed
  | halt reason => simp [move] at performed
  | call effect next =>
    cases effect with
    | send site type value =>
      simp only [move, Moved.to.injEq] at performed
      obtain ⟨rfl, rfl, _⟩ := performed
      exact .send site type value next _ _ _ _
    | receive site type =>
      simp only [move] at performed
      cases oldest : message? model shared site type with
      | some found =>
        obtain ⟨value, rest⟩ := found
        simp only [oldest, Moved.to.injEq] at performed
        obtain ⟨rfl, rfl, _⟩ := performed
        exact .receive site type value rest next _ _ _ _ (message?_spec oldest)
      | none =>
        simp only [oldest] at performed
        cases empty : shared.mail site with
        | cons head later => simp [empty] at performed
        | nil =>
          simp only [empty] at performed
          cases hears : coin? model shared site (heard site) type with
          | none => simp [hears] at performed
          | some value =>
            simp only [hears, Moved.to.injEq] at performed
            obtain ⟨rfl, rfl, _⟩ := performed
            exact .hear site type value next _ _ _ _ empty (coin?_spec hears)
    | draw site law inputs =>
      simp only [move] at performed
      cases given : coins site (shared.asked site) law.output with
      | none => simp [given] at performed
      | some reply =>
        simp only [given, Moved.to.injEq] at performed
        obtain ⟨rfl, rfl, _⟩ := performed
        have step := Performs.draw (sampler := coins.sampler) site law inputs next shared.mail
          shared.board heard shared.asked
        rw [Coins.sampler_answer coins given] at step
        exact step
    | sample site law inputs =>
      simp only [move] at performed
      cases given : coins site (shared.asked site) law.output with
      | none => simp [given] at performed
      | some reply =>
        simp only [given, Moved.to.injEq] at performed
        obtain ⟨rfl, rfl, _⟩ := performed
        have step := Performs.sample (sampler := coins.sampler) site law inputs next shared.mail
          shared.board heard shared.asked
        rw [Coins.sampler_answer coins given] at step
        exact step
    | read site type position => simp [move] at performed

/-- A run from two roles in which both have returned at its end: the two processes return
together, from the mail, the board and the counters of the run and the counts of the coins
that the two have heard. -/
theorem Run.finish_together {α : Type} (coins : Coins model) {first second : α} :
    ∀ (processes : List (PIR.Process (Effects model) α)) (run : Run model α)
      (left right : Role model α), run.roles.map (·.process) = processes →
      run.roles = [left, right] →
      ((run.finish model coins).roles.map (·.process) = [.done first, .done second]) →
        ReturnTogether coins.sampler left.process right.process run.shared.mail run.shared.board
          left.heard right.heard run.shared.asked first second := by
  intro processes
  induction processes using (oneContinues_wellFounded (I := Effects model) (A := α)).induction with
  | _ processes hypothesis =>
    intro run left right same roles returned
    cases stepped : run.next? model coins with
    | none =>
      rw [Run.finish_end model stepped] at returned
      rw [roles] at returned
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at returned
      rw [returned.1, returned.2]
      exact .done first second _ _ _ _ _
    | some next =>
      rw [Run.finish_step model stepped] at returned
      obtain ⟨index, role, moved, drew, at_, performed, later⟩ := Run.next?_spec model stepped
      have continued := Run.next?_continues model stepped
      rw [same] at continued
      rw [roles] at at_ later
      match index, at_, later with
      | 0, at_, later =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
        subst at_
        simp only [List.set_cons_zero] at later
        exact (move_performs performed).left
          (hypothesis _ continued next moved right rfl later returned)
      | 1, at_, later =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at at_
        subst at_
        simp only [List.set_cons_succ, List.set_cons_zero] at later
        exact (move_performs performed).right
          (hypothesis _ continued next left moved rfl later returned)
      | index + 2, at_, _ => simp at at_

/-- A role that has ended returned: its process has returned that value. -/
theorem ended_returned {α : Type} {reserved : Option Nat} {shared : Shared model}
    {role : Role model α} {value : α}
    (ended_ : ended model reserved shared role = .returned value) :
    role.process = .done value := by
  unfold ended at ended_
  split at ended_
  · cases ended_
  · split at ended_
    · rename_i same
      cases ended_
      exact same
    all_goals (try (repeat' split at ended_)); all_goals cases ended_

/-- Two roles that have ended returned: their processes have returned those values. -/
theorem ended_returned_all {α : Type} {reserved : Option Nat} {shared : Shared model}
    {roles : List (Role model α)} {first second : α}
    (returned : roles.map (ended model reserved shared) = [.returned first, .returned second]) :
    roles.map (·.process) = [.done first, .done second] := by
  match roles, returned with
  | [left, right], returned =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at returned ⊢
    exact ⟨ended_returned returned.1, ended_returned returned.2⟩
  | [], returned => simp at returned
  | [_], returned => simp at returned
  | _ :: _ :: _ :: _, returned => simp at returned

/-- A run of two processes against each other in which both return: the two return together
with those values, under the sampler of the source of coins. The run is any run of the
executor: no condition on the order of its effects. -/
theorem run_together {α : Type} (coins : Coins model)
    (left right : PIR.Process (Effects model) α) {first second : α}
    (returned : (run model coins [left, right]).roles.map (·.process) =
      [.done first, .done second]) :
    ReturnTogether coins.sampler left right Zkc.Core.Mail.empty Zkc.Core.Board.empty Heard.start
      Heard.start Zkc.Core.Asked.start first second :=
  Run.finish_together coins _ _ ⟨left, Heard.start⟩ ⟨right, Heard.start⟩ rfl rfl returned

end Zkc.Core.Execute

namespace Zkc.Core

open Zkc.Source Execute

variable {model : Model}

/-! ## Under a limit -/

/-- A process whose first effect is not a receive is not the process of a limit. -/
theorem Within.call_inv {α : Type} {effect : (Effects model).Op}
    {limited : (Effects model).Reply effect → PIR.Process (Effects model) α}
    {whole : PIR.Process (Effects model) α} (within : Within (.call effect limited) whole) :
    (∃ next, whole = .call effect next ∧ ∀ reply, Within (limited reply) (next reply)) ∨
      ∃ site, effect = .receive site (.fin 0) := by
  generalize same : PIR.Process.call effect limited = process at within
  cases within with
  | done value => cases same
  | halt reason => cases same
  | call found limitedNext wholeNext replies =>
    cases same
    exact .inl ⟨wholeNext, rfl, replies⟩
  | cut reserved limit whole =>
    simp only [limitReached, PIR.Process.call.injEq] at same
    exact .inr ⟨_, same.1⟩

/-- A process cut at the limit that returns alone: the whole one returns alone the same
value. -/
theorem ReturnsAlone.of_within {sampler : Sampler model} {α : Type}
    {limited : PIR.Process (Effects model) α} {asked : Zkc.Core.Asked} {value : α}
    (returns : ReturnsAlone sampler limited asked value) :
    ∀ {whole : PIR.Process (Effects model) α}, Within limited whole →
      ReturnsAlone sampler whole asked value := by
  induction returns with
  | done value asked =>
    intro whole within
    rw [within.returned]
    exact .done _ _
  | draw site law inputs next asked value _ hypothesis =>
    intro whole within
    rcases within.call_inv with ⟨wholeNext, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .draw site law inputs wholeNext asked value (hypothesis (replies _))
    · cases impossible
  | sample site law inputs next asked value _ hypothesis =>
    intro whole within
    rcases within.call_inv with ⟨wholeNext, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .sample site law inputs wholeNext asked value (hypothesis (replies _))
    · cases impossible

/-- A process cut at the limit that stops alone: the whole one stops alone with the same
reason. -/
theorem Execute.StopsAlone.of_within {sampler : Sampler model} {α : Type}
    {limited : PIR.Process (Effects model) α} {asked : Zkc.Core.Asked} {reason : PIR.Stop}
    (stops : StopsAlone sampler limited asked reason) :
    ∀ {whole : PIR.Process (Effects model) α}, Within limited whole →
      StopsAlone sampler whole asked reason := by
  induction stops with
  | halt reason asked =>
    intro whole within
    rw [within.stopped]
    exact .halt _ _
  | draw site law inputs next asked reason _ hypothesis =>
    intro whole within
    rcases within.call_inv with ⟨wholeNext, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .draw site law inputs wholeNext asked reason (hypothesis (replies _))
    · cases impossible
  | sample site law inputs next asked reason _ hypothesis =>
    intro whole within
    rcases within.call_inv with ⟨wholeNext, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .sample site law inputs wholeNext asked reason (hypothesis (replies _))
    · cases impossible

/-- Two processes cut at the limit that return together: the whole ones return together the
same values. -/
theorem ReturnTogether.of_within {sampler : Sampler model} {α β : Type}
    {limitedLeft : PIR.Process (Effects model) α} {limitedRight : PIR.Process (Effects model) β}
    {mail : Zkc.Core.Mail model} {board : Zkc.Core.Board model} {heardLeft heardRight : Heard}
    {asked : Zkc.Core.Asked} {first : α} {second : β}
    (together : ReturnTogether sampler limitedLeft limitedRight mail board heardLeft heardRight
      asked first second) :
    ∀ {wholeLeft : PIR.Process (Effects model) α} {wholeRight : PIR.Process (Effects model) β},
      Within limitedLeft wholeLeft → Within limitedRight wholeRight →
        ReturnTogether sampler wholeLeft wholeRight mail board heardLeft heardRight asked first
          second := by
  induction together with
  | done first second mail board heardLeft heardRight asked =>
    intro wholeLeft wholeRight left right
    rw [left.returned, right.returned]
    exact .done _ _ _ _ _ _ _
  | sendLeft _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases left.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .sendLeft (hypothesis (replies _) right)
    · cases impossible
  | receiveLeft oldest _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases left.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .receiveLeft oldest (hypothesis (replies _) right)
    · cases impossible
      exact Fin.elim0 (by assumption)
  | hearLeft empty announced _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases left.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .hearLeft empty announced (hypothesis (replies _) right)
    · cases impossible
      exact Fin.elim0 (by assumption)
  | drawLeft _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases left.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .drawLeft (hypothesis (replies _) right)
    · cases impossible
  | sampleLeft _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases left.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .sampleLeft (hypothesis (replies _) right)
    · cases impossible
  | sendRight _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases right.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .sendRight (hypothesis left (replies _))
    · cases impossible
  | receiveRight oldest _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases right.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .receiveRight oldest (hypothesis left (replies _))
    · cases impossible
      exact Fin.elim0 (by assumption)
  | hearRight empty announced _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases right.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .hearRight empty announced (hypothesis left (replies _))
    · cases impossible
      exact Fin.elim0 (by assumption)
  | drawRight _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases right.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .drawRight (hypothesis left (replies _))
    · cases impossible
  | sampleRight _ hypothesis =>
    intro wholeLeft wholeRight left right
    rcases right.call_inv with ⟨next, rfl, replies⟩ | ⟨_, impossible⟩
    · exact .sampleRight (hypothesis left (replies _))
    · cases impossible

end Zkc.Core
