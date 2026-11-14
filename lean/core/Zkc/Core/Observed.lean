module

public import Zkc.Core.Execute

@[expose] public section

/-! What each role of a run does, read beside the executor.

The executor says how each role ended. A comparison of two programs needs more: what each role
sent, received and heard, and what it drew and sampled, in the order in which it did so. That is
read here without a change of the executor.

- `Event`: what a role does in one move, with the site, the type and the value.
- `event?` reads the mail, the board and the source of coins as the executor's `move` does, and
  a role has an event exactly when it moves (`event?_isSome`).
- `Run.observe?` is the executor's `Run.next?` with the role that moved and its event
  (`Run.observe?_next`), and `Run.finishObserved` is a run to its end with the events of its
  roles in the order of the run. It ends as the executor's run does (`finishObserved_fst`), so
  the ends that the statements about the executor are about are the ends of the observed run.
- `observeAlone` is `runAlone` with the draws and the samples of the process
  (`observeAlone_fst`).
-/

set_option autoImplicit false

namespace Zkc.Core.Execute

open Zkc.Source PIR

/-- The kinds of what a role does in one move. -/
inductive Event.Kind where
  | sent
  | received
  /-- A coin that another role drew, heard at the site of the draw. -/
  | heard
  | drew
  | sampled
  deriving Repr, DecidableEq, Inhabited

def Event.Kind.describe : Event.Kind → String
  | .sent => "sent" | .received => "received" | .heard => "heard" | .drew => "drew"
  | .sampled => "sampled"

variable (model : Model)

/-- What a role does in one move. -/
structure Event where
  kind : Event.Kind
  site : Site
  type : Ty
  value : model.Value type

/-- The event of the first effect of a role, when the effect can be performed now. -/
def event? {α : Type} (coins : Coins model) (role : Role model α) (shared : Shared model) :
    Option (Event model) :=
  match role.process with
  | .done _ => none
  | .halt _ => none
  | .call (.send site type value) _ => some ⟨.sent, site, type, value⟩
  | .call (.receive site type) _ =>
      match message? model shared site type with
      | some (value, _) => some ⟨.received, site, type, value⟩
      | none =>
        match shared.mail site with
        | _ :: _ => none
        | [] => (coin? model shared site (role.heard site) type).map (⟨.heard, site, type, ·⟩)
  | .call (.draw site law _) _ =>
      (coins site (shared.asked site) law.output).map (⟨.drew, site, law.output, ·⟩)
  | .call (.sample site law _) _ =>
      (coins site (shared.asked site) law.output).map (⟨.sampled, site, law.output, ·⟩)
  | .call (.read ..) _ => none

/-- A role has an event exactly when it moves. -/
theorem event?_isSome {α : Type} (coins : Coins model) (role : Role model α)
    (shared : Shared model) :
    (event? model coins role shared).isSome =
      (match move model coins role shared with | .to .. => true | .stays => false) := by
  obtain ⟨process, heard⟩ := role
  cases process with
  | done _ => rfl
  | halt _ => rfl
  | call op next =>
    cases op with
    | send site type value => rfl
    | receive site type =>
        simp only [event?, move]
        cases message? model shared site type with
        | some found => rfl
        | none =>
          simp only
          cases shared.mail site with
          | cons _ _ => rfl
          | nil =>
            simp only
            cases coin? model shared site (heard site) type <;> rfl
    | draw site law inputs =>
        simp only [event?, move]
        cases coins site (shared.asked site) law.output <;> rfl
    | sample site law inputs =>
        simp only [event?, move]
        cases coins site (shared.asked site) law.output <;> rfl
    | read site type position => rfl

/-- One effect of a run, with the role that performed it and its event. -/
def Run.observe? {α : Type} (coins : Coins model) (run : Run model α) :
    Option (Run model α × Nat × Option (Event model)) :=
  match firstMove model coins run.roles run.shared run.order with
  | none => none
  | some (index, moved, after, drew) =>
      some ({ roles := run.roles.set index moved, shared := after
              order := if drew then run.order.erase index ++ [index] else run.order },
        index, (run.roles[index]?).bind fun role => event? model coins role run.shared)

/-- The run after an observed effect is the run after the executor's effect. -/
theorem Run.observe?_next {α : Type} (coins : Coins model) (run : Run model α) :
    (Run.observe? model coins run).map (·.1) = run.next? model coins := by
  unfold Run.observe? Run.next?
  cases firstMove model coins run.roles run.shared run.order with
  | none => rfl
  | some found => rfl

/-- A run to its end, with the events of its roles in the order of the run, each with the
number of its role. -/
def Run.finishObserved {α : Type} (coins : Coins model) (run : Run model α)
    (log : Array (Nat × Event model)) : Run model α × Array (Nat × Event model) :=
  match _stepped : Run.observe? model coins run with
  | some (next, index, event) =>
      Run.finishObserved coins next
        (match event with
          | some event => log.push (index, event)
          | none => log)
  | none => (run, log)
termination_by run.roles.map (·.process)
decreasing_by
  have next_ : run.next? model coins = some next := by
    rw [← Run.observe?_next, _stepped]
    rfl
  exact Run.next?_continues model next_

/-- The observed run ends as the executor's run does. -/
theorem finishObserved_fst {α : Type} (coins : Coins model) (run : Run model α)
    (log : Array (Nat × Event model)) :
    (Run.finishObserved model coins run log).1 = run.finish model coins := by
  rw [Run.finishObserved]
  split
  · rename_i next index event stepped
    have next_ : run.next? model coins = some next := by
      rw [← Run.observe?_next, stepped]
      rfl
    rw [Run.finish_step model next_]
    exact finishObserved_fst coins next _
  · rename_i stopped
    have none_ : run.next? model coins = none := by
      rw [← Run.observe?_next, stopped]
      rfl
    rw [Run.finish_end model none_]
termination_by run.roles.map (·.process)
decreasing_by
  exact Run.next?_continues model next_

/-- The run of processes against each other, as `run`, with the events of its roles in the
order of the run. -/
def runObserved {α : Type} (coins : Coins model)
    (processes : List (PIR.Process (Effects model) α))
    (shared : Shared model := Shared.start model) : Run model α × Array (Nat × Event model) :=
  Run.finishObserved model coins
    { roles := processes.map fun process => { process, heard := Heard.start }, shared
      order := List.range processes.length } #[]

/-- The observed run of processes ends as their run does. -/
theorem runObserved_fst {α : Type} (coins : Coins model)
    (processes : List (PIR.Process (Effects model) α)) (shared : Shared model) :
    (runObserved model coins processes shared).1 = run model coins processes shared :=
  finishObserved_fst model coins _ _

/-- One process alone, as `runAlone`, with its draws and its samples in order. -/
def observeAlone {α : Type} (coins : Coins model) (process : PIR.Process (Effects model) α)
    (asked : Zkc.Core.Asked := fun _ => 0) (reserved : Option Nat := none)
    (log : Array (Event model) := #[]) : Outcome α × Array (Event model) :=
  match reached model reserved process with
  | some elements => (.limit elements, log)
  | none =>
    match process with
    | .done value => (.returned value, log)
    | .halt reason => (.stopped reason, log)
    | .call (.draw site law _) next =>
        match coins site (asked site) law.output with
        | some reply =>
            observeAlone coins (next reply) (asked.next site) reserved
              (log.push ⟨.drew, site, law.output, reply⟩)
        | none => (.failed (notValue site), log)
    | .call (.sample site law _) next =>
        match coins site (asked site) law.output with
        | some reply =>
            observeAlone coins (next reply) (asked.next site) reserved
              (log.push ⟨.sampled, site, law.output, reply⟩)
        | none => (.failed (notValue site), log)
    | .call (.send site ..) _ =>
        (.failed s!"a send at site {site.definition}.{site.number} in a run of one process", log)
    | .call (.receive site _) _ =>
        (.failed s!"a receive at site {site.definition}.{site.number} in a run of one process", log)
    | .call (.read site ..) _ => (.failed s!"a read at site {site.definition}.{site.number}", log)

/-- The observed run of one process ends as its run does. -/
theorem observeAlone_fst {α : Type} (coins : Coins model) (reserved : Option Nat) :
    ∀ (process : PIR.Process (Effects model) α) (asked : Zkc.Core.Asked)
      (log : Array (Event model)),
      (observeAlone model coins process asked reserved log).1 =
        runAlone model coins process asked reserved
  | .done value, asked, log => by
    unfold observeAlone runAlone
    cases reached model reserved (Process.done value : PIR.Process (Effects model) α) <;> rfl
  | .halt reason, asked, log => by
    unfold observeAlone runAlone
    cases reached model reserved (Process.halt reason : PIR.Process (Effects model) α) <;> rfl
  | .call (.draw site law inputs) next, asked, log => by
    unfold observeAlone runAlone
    cases reached model reserved (Process.call (Effect.draw site law inputs) next) with
    | some elements => rfl
    | none =>
      simp only
      cases coins site (asked site) law.output with
      | none => rfl
      | some reply => exact observeAlone_fst coins reserved (next reply) _ _
  | .call (.sample site law inputs) next, asked, log => by
    unfold observeAlone runAlone
    cases reached model reserved (Process.call (Effect.sample site law inputs) next) with
    | some elements => rfl
    | none =>
      simp only
      cases coins site (asked site) law.output with
      | none => rfl
      | some reply => exact observeAlone_fst coins reserved (next reply) _ _
  | .call (.send site type value) next, asked, log => by
    unfold observeAlone runAlone
    cases reached model reserved (Process.call (Effect.send site type value) next) <;> rfl
  | .call (.receive site type) next, asked, log => by
    unfold observeAlone runAlone
    cases reached model reserved (Process.call (Effect.receive site type) next) <;> rfl
  | .call (.read site type position) next, asked, log => by
    unfold observeAlone runAlone
    cases reached model reserved (Process.call (Effect.read site type position) next) <;> rfl

end Zkc.Core.Execute
