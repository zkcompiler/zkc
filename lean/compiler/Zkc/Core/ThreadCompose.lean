module

public import Zkc.Core.ThreadProgram

public section

/-! Two threading steps, one after the other, are one interpretation of the entry.

A derived scheme is the result of two steps: the second runs on the result of the first,
with the newest protocol as its entry and the identities that the first step left
(`Stepped.identities`), as `serializeProtocols` calls it. The whole-program theorem of one
step (`stepProtocols_entry`) says that the image of the entry is the entry interpreted by
the step's handler, between what the rule's entry does before and after. This module
composes two applications of it.

- `PIR.Process.interpretWith_threadedProcess`: a process that makes a state, interprets a
  source by a handler and finishes, interpreted by a second handler that passes the start
  and the finish, is the source interpreted by the composed handler
  (`PIR.composeHandlers`) between the same start and finish.
- `composedArguments`, `composedStart`, `composedFinish`: what the entries of two rules do
  together around the body. The second rule's entry is the outer one: its start runs
  first and its finish last. Both are without an effect when the two entries are
  (`composedStart_quiet`, `composedFinish_quiet`).
- `Stepped.rewroteEntry`: whether a step rewrote the entry, read from where the newest
  protocol of its result comes from. A step that has a result has a newest protocol
  (`stepProtocols_has_newest`), which comes from the declared entry; a step of a rule that
  rewrites an entry whose body has no rewritten operation rewrote it
  (`stepProtocols_idle_rewroteEntry`, and `stepProtocols_idle_after` for such a step after
  another); otherwise the flag decides between the image of the entry
  (`stepProtocols_entry_rewritten`) and its copy (`stepProtocols_entry_copied`).
- `stepProtocols_twice_entry`: when both steps rewrote the entry, the newest protocol of
  the second result, for a side with exactly one transcript role, is the declared entry
  interpreted by the composed handler from the composed start, followed by the composed
  finish. It is stated for two arbitrary rules with sound entries.
- `stepProtocols_plain_then_entry`: when the first step copied the entry, the newest
  protocol of the second result is the declared entry interpreted by the second step's
  handler alone.
- `stepProtocols_roles_differ`: a step that has a result was given two different roles,
  which is why the side of either role alone holds exactly one transcript role.

What remains a premise: the soundness of the two rules and of their entries and that the
functions perform no effect, which the statements about the image of a rewritten entry
take; the equations of the two steps and the position of the declared entry; and, for a
rule that copies an entry whose body has no rewritten operation, whether the step rewrote
the entry (`Stepped.rewroteEntry`), which depends on the body of the entry.
-/

set_option autoImplicit false

namespace PIR

variable {I : Signature} {A B S T : Type}

/-- A process that makes a state, interprets a source by a handler and finishes,
interpreted by a second handler that passes the start and the finish: the source
interpreted by the composed handler, between the same start and finish. -/
theorem Process.interpretWith_threadedProcess (first : StatefulInterpretation I I S)
    (second : StatefulInterpretation I I T) (start : Process I S) (source : Process I A)
    (finish : A × S → Process I B) (passesStart : Passes second start)
    (passesFinish : ∀ result, Passes second (finish result)) (other : T) :
    (start.bind fun state => (source.interpretWith first state).bind finish).interpretWith second
        other =
      start.bind fun state =>
        (source.interpretWith (composeHandlers first second) (state, other)).bind fun result =>
          (finish (result.1, result.2.1)).bind fun value => .done (value, result.2.2) := by
  rw [Process.interpretWith_bind, passesStart other, Process.bind_assoc]
  congr 1
  funext state
  rw [Process.done_bind, Process.interpretWith_bind, Process.interpretWith_interpretWith,
    Process.bind_assoc]
  congr 1
  funext result
  rw [Process.done_bind]
  exact passesFinish _ _

end PIR

namespace Zkc.Core

open Zkc.Source

section Compose

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {first second : Threads}
  {firstRule : Rule first operations functions} {secondRule : Rule second operations functions}
  {firstMeaning : RuleMeaning model first operations}
  {secondMeaning : RuleMeaning model second operations}
  {functionTable : FunctionTable model functions}

/-- The header of the entry after a step: the ports are the rule's. -/
@[expose, reducible] def Rule.entryHeader {t : Threads} (rule : Rule t operations functions)
    (roles : TranscriptRoles) (header : ProtocolHeader) : ProtocolHeader :=
  (rule.entryPorts roles header).header header

/-- The two threaded values of each of two steps, as a side holds them. -/
abbrev ComposedState (model : Model) (first second : Threads) (prover verifier : Bool) : Type :=
  ThreadState model first prover verifier × ThreadState model second prover verifier

/-- The inputs of the entry before two steps, from the inputs of the entry after them. -/
@[expose] def composedArguments (firstEntry : EntryMeaning model first firstRule)
    (secondEntry : EntryMeaning model second secondRule) (side : Side) (roles : TranscriptRoles)
    (header : ProtocolHeader)
    (arguments : Values (SideValue model side)
      (secondRule.entryPorts roles (firstRule.entryHeader roles header)).inputs) :
    Values (SideValue model side) header.inputs :=
  firstEntry.arguments side roles header
    (secondEntry.arguments side roles (firstRule.entryHeader roles header) arguments)

/-- The states that the body starts from after two steps. The entry of the second step is
the outer one: its start runs first. -/
@[expose] def composedStart (firstEntry : EntryMeaning model first firstRule)
    (secondEntry : EntryMeaning model second secondRule) (side : Side) (roles : TranscriptRoles)
    (header : ProtocolHeader)
    (arguments : Values (SideValue model side)
      (secondRule.entryPorts roles (firstRule.entryHeader roles header)).inputs) :
    PIR.Process (Effects model)
      (ComposedState model first second (side roles.prover) (side roles.verifier)) :=
  (secondEntry.start side roles (firstRule.entryHeader roles header) arguments).bind fun later =>
    (firstEntry.start side roles header
        (secondEntry.arguments side roles (firstRule.entryHeader roles header) arguments)).bind
      fun earlier => .done (earlier, later)

/-- The outputs of the entry after two steps, from the outputs of the entry before them and
the final states. The entry of the first step is the inner one: its finish runs first. -/
@[expose] def composedFinish (firstEntry : EntryMeaning model first firstRule)
    (secondEntry : EntryMeaning model second secondRule) (side : Side) (roles : TranscriptRoles)
    (header : ProtocolHeader)
    (result : Values (SideValue model side) header.outputs ×
      ComposedState model first second (side roles.prover) (side roles.verifier)) :
    PIR.Process (Effects model)
      (Values (SideValue model side)
        (secondRule.entryPorts roles (firstRule.entryHeader roles header)).outputs) :=
  (firstEntry.finish side roles header (result.1, result.2.1)).bind fun outputs =>
    secondEntry.finish side roles (firstRule.entryHeader roles header) (outputs, result.2.2)

/-- Making the states of two steps performs no effect. -/
theorem composedStart_quiet (quiet : QuietTable functionTable)
    {firstEntry : EntryMeaning model first firstRule}
    (firstSound : EntrySound firstRule firstEntry functionTable)
    {secondEntry : EntryMeaning model second secondRule}
    (secondSound : EntrySound secondRule secondEntry functionTable) (side : Side)
    (roles : TranscriptRoles) (header : ProtocolHeader)
    (arguments : Values (SideValue model side)
      (secondRule.entryPorts roles (firstRule.entryHeader roles header)).inputs) :
    (composedStart firstEntry secondEntry side roles header arguments).Quiet :=
  PIR.Process.Quiet.bind (secondSound.startQuiet quiet side roles _ arguments) fun later =>
    PIR.Process.Quiet.bind (firstSound.startQuiet quiet side roles header _) fun earlier =>
      partialProcess_quiet (model := model) (.ok (earlier, later))

/-- Consuming the states of two steps performs no effect. -/
theorem composedFinish_quiet (quiet : QuietTable functionTable)
    {firstEntry : EntryMeaning model first firstRule}
    (firstSound : EntrySound firstRule firstEntry functionTable)
    {secondEntry : EntryMeaning model second secondRule}
    (secondSound : EntrySound secondRule secondEntry functionTable) (side : Side)
    (roles : TranscriptRoles) (header : ProtocolHeader)
    (result : Values (SideValue model side) header.outputs ×
      ComposedState model first second (side roles.prover) (side roles.verifier)) :
    (composedFinish firstEntry secondEntry side roles header result).Quiet :=
  PIR.Process.Quiet.bind (firstSound.finishQuiet quiet side roles header _) fun _ =>
    secondSound.finishQuiet quiet side roles _ _

/-! ## Whether a step rewrote the entry -/

/-- Whether a step rewrote the entry: where the newest protocol of its result comes from
says so (`Origin.entry`). A caller decides it on the result. -/
@[expose] def Stepped.rewroteEntry (stepped : Stepped typeTable operations functions) : Bool :=
  match stepped.origins with
  | origin :: _ => origin.entry
  | [] => false

/-- A result whose flag says that the entry was rewritten has a newest protocol that comes
from the entry, rewritten. -/
theorem Stepped.rewroteEntry_newest {stepped : Stepped typeTable operations functions}
    (rewrote : stepped.rewroteEntry = true) :
    ∃ origin earlier, stepped.origins = origin :: earlier ∧ origin.entry = true := by
  unfold Stepped.rewroteEntry at rewrote
  split at rewrote
  · rename_i origin earlier newest
    exact ⟨origin, earlier, newest, rewrote⟩
  · cases rewrote

/-- The flag of a result is the flag of where its newest protocol comes from. -/
theorem Stepped.rewroteEntry_of_newest {stepped : Stepped typeTable operations functions}
    {origin : Origin} {earlier : List Origin} (newest : stepped.origins = origin :: earlier) :
    stepped.rewroteEntry = origin.entry := by
  unfold Stepped.rewroteEntry
  rw [newest]

/-- A step whose flag says that the entry was not rewritten copied it: the result has a
newest protocol, which comes from the entry, copied. -/
theorem stepProtocols_copied_newest {t : Threads} {rule : Rule t operations functions}
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) (copied : stepped.rewroteEntry = false) :
    ∃ origin earlier, stepped.origins = origin :: earlier ∧ origin.entry = false := by
  obtain ⟨origin, earlier, newest, _⟩ :=
    stepProtocols_newest identities number roles protocols stepped steps declared isEntry
  refine ⟨origin, earlier, newest, ?_⟩
  unfold Stepped.rewroteEntry at copied
  rw [newest] at copied
  exact copied

/-- A step of a rule that rewrites an entry whose body has no rewritten operation
(`Rule.idleEntry`) rewrote the entry. -/
theorem stepProtocols_idle_rewroteEntry {t : Threads} {rule : Rule t operations functions}
    (idle : rule.idleEntry = true) (identities : Identities) (number : Nat)
    (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    stepped.rewroteEntry = true := by
  obtain ⟨origin, earlier, newest, rewritten⟩ :=
    stepProtocols_newest identities number roles protocols stepped steps declared isEntry
  unfold Stepped.rewroteEntry
  rw [newest]
  exact rewritten idle

/-- The result of a step has a newest protocol. -/
theorem stepProtocols_has_newest {t : Threads} {rule : Rule t operations functions}
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ (newestHeader : ProtocolHeader) (newest : Var stepped.headers newestHeader),
      newest.index = 0 := by
  obtain ⟨origin, earlier, newest, _⟩ :=
    stepProtocols_newest identities number roles protocols stepped steps declared isEntry
  have counted := stepped.counted
  rw [newest] at counted
  cases shape : stepped.headers with
  | nil => rw [shape] at counted; cases counted
  | cons newestHeader rest => exact ⟨newestHeader, ⟨0, rfl⟩, rfl⟩

/-- A step of a rule that rewrites an entry whose body has no rewritten operation, run on
the result of another step with the newest protocol as its entry, rewrote the entry. -/
theorem stepProtocols_idle_after (secondIdle : secondRule.idleEntry = true)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (stepsOnce : stepProtocols first firstRule identities number roles protocols = .ok once)
    (twice : Stepped typeTable operations functions)
    (stepsTwice : stepProtocols second secondRule once.identities (once.headers.length - 1) roles
      once.protocols = .ok twice)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    twice.rewroteEntry = true := by
  obtain ⟨newestHeader, inner, innerNewest⟩ :=
    stepProtocols_has_newest identities number roles protocols once stepsOnce declared isEntry
  exact stepProtocols_idle_rewroteEntry secondIdle once.identities (once.headers.length - 1) roles
    once.protocols twice stepsTwice inner (by rw [innerNewest]; omega)

/-- The image of an entry that the step rewrote (`Stepped.rewroteEntry`): the newest
protocol of the result is the entry interpreted by the handler of the step's marks, between
what the rule's entry does before and after it. -/
theorem stepProtocols_entry_rewritten {t : Threads} {rule : Rule t operations functions}
    {sem : RuleMeaning model t operations} (quiet : QuietTable functionTable)
    (sound : RuleSound rule sem functionTable) {entryMeaning : EntryMeaning model t rule}
    (entrySound : EntrySound rule entryMeaning functionTable) (identities : Identities)
    (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number)
    (rewrote : stepped.rewroteEntry = true) :
    ∃ image : Var stepped.headers (rule.entryHeader roles header),
      image.index = 0 ∧
      ∀ (path : List Nat) (side : Side),
        OneTranscriptRole (side roles.prover) (side roles.verifier) →
        ∀ arguments : Values (SideValue model side) (rule.entryPorts roles header).inputs,
          (stepped.protocols.table model functionTable stepped.identities).get image path side
              arguments =
            (entryMeaning.start side roles header arguments).bind fun state =>
              (((protocols.table model functionTable identities).get declared path side
                  (entryMeaning.arguments side roles header arguments)).interpretWith
                (threadHandler sem
                  (marksBelow path (stepMarks t rule identities number roles protocols))
                  (side roles.prover) (side roles.verifier)) state).bind fun result =>
                entryMeaning.finish side roles header result := by
  obtain ⟨origin, earlier, newest, rewritten⟩ := Stepped.rewroteEntry_newest rewrote
  exact stepProtocols_entry quiet sound entrySound identities number roles protocols stepped steps
    declared isEntry origin earlier newest rewritten

/-- The image of an entry that the step copied: the newest protocol of the result has the
entry's meaning. -/
theorem stepProtocols_entry_copied {t : Threads} {rule : Rule t operations functions}
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number)
    (copied : stepped.rewroteEntry = false) :
    ∃ image : Var stepped.headers header, image.index = 0 ∧
      (stepped.protocols.table model functionTable stepped.identities).get image =
        (protocols.table model functionTable identities).get declared := by
  obtain ⟨origin, earlier, newest, plain⟩ :=
    stepProtocols_copied_newest identities number roles protocols stepped steps declared isEntry
      copied
  exact stepProtocols_plain_entry identities number roles protocols stepped steps declared isEntry
    origin earlier newest plain

/-! ## Two steps -/

/-- The second step runs on the result of the first with the newest protocol as its entry
and the identities that the first step left. When both steps rewrote the entry, the newest
protocol of the second result, for a side with exactly one transcript role, is the
declared entry interpreted by the composed handler from the composed start, followed by
the composed finish. -/
theorem stepProtocols_twice_entry (quiet : QuietTable functionTable)
    (firstSound : RuleSound firstRule firstMeaning functionTable)
    {firstEntry : EntryMeaning model first firstRule}
    (firstEntrySound : EntrySound firstRule firstEntry functionTable)
    (secondSound : RuleSound secondRule secondMeaning functionTable)
    {secondEntry : EntryMeaning model second secondRule}
    (secondEntrySound : EntrySound secondRule secondEntry functionTable) (identities : Identities)
    (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (stepsOnce : stepProtocols first firstRule identities number roles protocols = .ok once)
    (twice : Stepped typeTable operations functions)
    (stepsTwice : stepProtocols second secondRule once.identities (once.headers.length - 1) roles
      once.protocols = .ok twice)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number)
    (firstRewrote : once.rewroteEntry = true) (secondRewrote : twice.rewroteEntry = true) :
    ∃ image : Var twice.headers
        (secondRule.entryHeader roles (firstRule.entryHeader roles header)),
      image.index = 0 ∧
      ∀ (path : List Nat) (side : Side),
        OneTranscriptRole (side roles.prover) (side roles.verifier) →
        ∀ arguments : Values (SideValue model side)
            (secondRule.entryPorts roles (firstRule.entryHeader roles header)).inputs,
          (twice.protocols.table model functionTable twice.identities).get image path side
              arguments =
            (composedStart firstEntry secondEntry side roles header arguments).bind fun states =>
              (((protocols.table model functionTable identities).get declared path side
                  (composedArguments firstEntry secondEntry side roles header
                    arguments)).interpretWith
                (PIR.composeHandlers
                  (threadHandler firstMeaning
                    (marksBelow path (stepMarks first firstRule identities number roles protocols))
                    (side roles.prover) (side roles.verifier))
                  (threadHandler secondMeaning
                    (marksBelow path
                      (stepMarks second secondRule once.identities (once.headers.length - 1) roles
                        once.protocols))
                    (side roles.prover) (side roles.verifier))) states).bind fun result =>
                composedFinish firstEntry secondEntry side roles header result := by
  obtain ⟨inner, innerNewest, innerThreads⟩ := stepProtocols_entry_rewritten quiet firstSound
    firstEntrySound identities number roles protocols once stepsOnce declared isEntry firstRewrote
  obtain ⟨image, newest, threads⟩ := stepProtocols_entry_rewritten quiet secondSound
    secondEntrySound once.identities (once.headers.length - 1) roles once.protocols twice stepsTwice
    inner (by rw [innerNewest]; omega) secondRewrote
  refine ⟨image, newest, fun path side one arguments => ?_⟩
  rw [threads path side one arguments, innerThreads path side one]
  unfold composedStart composedFinish composedArguments
  rw [PIR.Process.bind_assoc]
  congr 1
  funext later
  rw [PIR.Process.interpretWith_threadedProcess _ _ _ _ _
      ((firstEntrySound.startQuiet quiet side roles header _).passes _)
      (fun result => (firstEntrySound.finishQuiet quiet side roles header result).passes _),
    PIR.Process.bind_assoc, PIR.Process.bind_assoc]
  congr 1
  funext earlier
  rw [PIR.Process.done_bind, PIR.Process.bind_assoc]
  congr 1
  funext result
  rw [PIR.Process.bind_assoc]
  rfl

/-- When the first step copied the entry and the second rewrote it, the newest protocol of
the second result, for a side with exactly one transcript role, is the declared entry
interpreted by the second step's handler, between what the second rule's entry does before
and after it. -/
theorem stepProtocols_plain_then_entry (quiet : QuietTable functionTable)
    (secondSound : RuleSound secondRule secondMeaning functionTable)
    {secondEntry : EntryMeaning model second secondRule}
    (secondEntrySound : EntrySound secondRule secondEntry functionTable) (identities : Identities)
    (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (stepsOnce : stepProtocols first firstRule identities number roles protocols = .ok once)
    (twice : Stepped typeTable operations functions)
    (stepsTwice : stepProtocols second secondRule once.identities (once.headers.length - 1) roles
      once.protocols = .ok twice)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number)
    (firstCopied : once.rewroteEntry = false) (secondRewrote : twice.rewroteEntry = true) :
    ∃ image : Var twice.headers (secondRule.entryHeader roles header),
      image.index = 0 ∧
      ∀ (path : List Nat) (side : Side),
        OneTranscriptRole (side roles.prover) (side roles.verifier) →
        ∀ arguments : Values (SideValue model side) (secondRule.entryPorts roles header).inputs,
          (twice.protocols.table model functionTable twice.identities).get image path side
              arguments =
            (secondEntry.start side roles header arguments).bind fun state =>
              (((protocols.table model functionTable identities).get declared path side
                  (secondEntry.arguments side roles header arguments)).interpretWith
                (threadHandler secondMeaning
                  (marksBelow path
                    (stepMarks second secondRule once.identities (once.headers.length - 1) roles
                      once.protocols))
                  (side roles.prover) (side roles.verifier)) state).bind fun result =>
                secondEntry.finish side roles header result := by
  obtain ⟨inner, innerNewest, innerMeaning⟩ := stepProtocols_entry_copied
    (model := model) (functionTable := functionTable) identities number roles protocols once
    stepsOnce declared isEntry firstCopied
  obtain ⟨image, newest, threads⟩ := stepProtocols_entry_rewritten quiet secondSound
    secondEntrySound once.identities (once.headers.length - 1) roles once.protocols twice stepsTwice
    inner (by rw [innerNewest]; omega) secondRewrote
  refine ⟨image, newest, fun path side one arguments => ?_⟩
  rw [threads path side one arguments, innerMeaning]

/-- A step that has a result was given two different roles. -/
theorem stepProtocols_roles_differ {t : Threads} {rule : Rule t operations functions}
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped) :
    roles.prover ≠ roles.verifier := by
  intro same
  unfold stepProtocols at steps
  rw [same, Nat.beq_refl] at steps
  simp at steps

end Compose

end Zkc.Core
