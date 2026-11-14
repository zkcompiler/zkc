module

public import Zkc.Core.ThreadPlain

public section

/-! The structural theorem of a threading step: what it is stated with.

A threading step rewrites a definition into an image that takes and returns two values,
one held by the prover and one by the verifier. The structural theorem says, for one
side: the image's process is the definition's process interpreted by a handler that
carries the two values the side holds (`PIR.Process.interpretWith`), and it returns the
final two values before the definition's.

This file has the vocabulary of that statement.

- `ThreadState`, `ThreadHandler`: the two threaded values of a side, each absent when its
  role is outside the side, and a handler over them.
- `RuleMeaning`: what a rule does at the operations it rewrites, as processes of the
  side: an exchange from the prover to the verifier, and a draw between the two.
  `RuleSound` says that what the rule emits runs as those processes.
- `Fits`: what the theorem requires of the handler, operation by operation. At a
  rewritten exchange or draw the handler turns the operation's process into the rule's
  action; it passes every other operation and every region and callee that the step
  copies; at an application of an image that threads it fits the callee.
- `CalleesThread`: the statement for the callees, which the case of `apply` uses.
- The laws of `repeat` and `choose` under a handler, for regions that the step threads
  and for regions that it copies. A threaded `repeat` returns the two values after the
  sequences of what it collects (`threadedAfter`), which are those of the old loop
  (`repeat_threads`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace PIR

variable {I : Signature} {A B C D S : Type}

/-- One step of a threaded region whose image is read back: the handler turns the old
operation's process into the image's, from which the old results and the next state are
read. -/
theorem thread_step_read (handler : StatefulInterpretation I I S) (source : Process I A)
    (next : A → Process I B) (state : S) (image : Process I C) (imageNext : C → Process I D)
    (pack : B × S → D) (read : C → A × S)
    (acts : source.interpretWith handler state = image.bind fun result => .done (read result))
    (rest : ∀ result, imageNext result =
      ((next (read result).1).interpretWith handler (read result).2).bind fun final =>
        .done (pack final)) :
    image.bind imageNext =
      ((source.bind next).interpretWith handler state).bind fun final => .done (pack final) := by
  rw [Process.interpretWith_bind, acts, Process.bind_assoc, Process.bind_assoc]
  congr 1
  funext result
  exact rest result

/-- One step of a threaded region whose image is made from the old one: the image's
process is the old operation's process under the handler, with its results and the next
state packed. -/
theorem thread_step_made (handler : StatefulInterpretation I I S) (source : Process I A)
    (next : A → Process I B) (state : S) (image : Process I C) (imageNext : C → Process I D)
    (pack : B × S → D) (make : A × S → C)
    (acts : image = (source.interpretWith handler state).bind fun result => .done (make result))
    (rest : ∀ result, imageNext (make result) =
      ((next result.1).interpretWith handler result.2).bind fun final => .done (pack final)) :
    image.bind imageNext =
      ((source.bind next).interpretWith handler state).bind fun final => .done (pack final) := by
  subst acts
  rw [Process.interpretWith_bind, Process.bind_assoc, Process.bind_assoc]
  congr 1
  funext result
  exact rest result

end PIR

namespace Zkc.Core

open Zkc.Source

/-- The two threaded values as a side holds them: the prover's and the verifier's, each
the unit value when its role is outside the side. -/
abbrev ThreadState (model : Model) (t : Threads) (prover verifier : Bool) : Type :=
  Held (model.Value t.prover) prover × Held (model.Value t.verifier) verifier

/-- A handler of a side's effects that carries the side's threaded values. -/
abbrev ThreadHandler (model : Model) (t : Threads) (prover verifier : Bool) : Type :=
  PIR.StatefulInterpretation (Effects model) (Effects model) (ThreadState model t prover verifier)

/-- The values an image returns: the two final threaded values, then the definition's. -/
@[expose] def threadedValues {model : Model} {t : Threads} {side : Side} {roles : TranscriptRoles}
    {out : List Located}
    (result : Values (SideValue model side) out ×
      ThreadState model t (side roles.prover) (side roles.verifier)) :
    Values (SideValue model side) (t.states roles ++ out) :=
  .cons result.2.1 (.cons result.2.2 result.1)

/-- What a rule does at the operations it rewrites, for the memberships of the prover and
of the verifier in the side: a threaded value, a message and a coin of a role exist when
the role is in the side. The site is the site of the rewritten operation's effects. -/
structure RuleMeaning (model : Model) (t : Threads) (operations : List OperationSignature) where
  /-- An exchange from the prover to the verifier: from the prover's value and the two
  threaded values, the verifier's value and the next two. -/
  exchange : (prover verifier : Bool) → (place : Place) → (site : Nat) → (effects : Site) →
    (type : Ty) → Held (model.Value type) prover → ThreadState model t prover verifier →
      PIR.Process (Effects model)
        (Held (model.Value type) verifier × ThreadState model t prover verifier)
  /-- A draw between the two: the prover's coin, the verifier's coin and the next two
  threaded values. -/
  draw : (prover verifier : Bool) → (place : Place) → (site : Nat) → (effects : Site) →
    {inputs : List Ty} → {output : Ty} → Var operations ⟨inputs, [output], .sampling⟩ →
      ThreadState model t prover verifier →
        PIR.Process (Effects model)
          ((Held (model.Value output) prover × Held (model.Value output) verifier) ×
            ThreadState model t prover verifier)

section Sound

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {t : Threads}

/-- What a rule emits runs as the rule's meaning: the emitted operations are the action's
process, after which the environment holds the action's results at the produced values
and every earlier value where it was. -/
structure RuleSound (rule : Rule t operations functions) (sem : RuleMeaning model t operations)
    (functionTable : FunctionTable model functions) : Prop where
  exchange : ∀ {protocols : List ProtocolHeader} {deployed : Bool}
    (table : ProtocolTable model protocols) (label : Nat → Site) (side : Side) (place : Place)
    (site : Nat) (type : Ty) {Δ : List Located} (value : Var Δ ⟨type, place.roles.prover⟩)
    (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨type, place.roles.verifier⟩, t.first place.roles, t.second place.roles]),
    rule.exchange place site type value first second = .ok emitted →
    ∀ env : Environment (SideValue model side) Δ,
      ∃ later : SideValue model side ⟨type, place.roles.verifier⟩ ×
          ThreadState model t (side place.roles.prover) (side place.roles.verifier) →
            Environment (SideValue model side) emitted.context,
        emitted.Runs (labelledMeaning model label functionTable table side) env
          ((sem.exchange (side place.roles.prover) (side place.roles.verifier) place site (label site) type (env value) (env first, env second)).bind
            fun result => .done (later result)) ∧
        ∀ result, later result (emitted.values.get .here) = result.1 ∧
          later result (emitted.values.get (.there .here)) = result.2.1 ∧
          later result (emitted.values.get (.there (.there .here))) = result.2.2 ∧
          ∀ {ty : Located} (reference : Var Δ ty),
            later result (reference.extend emitted.grows) = env reference
  draw : ∀ {protocols : List ProtocolHeader} {deployed : Bool}
    (table : ProtocolTable model protocols) (label : Nat → Site) (side : Side) (place : Place)
    (site : Nat) {inputs : List Ty} {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    {Δ : List Located} (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩, t.first place.roles,
        t.second place.roles]),
    rule.draw place site law first second = .ok emitted →
    ∀ env : Environment (SideValue model side) Δ,
      ∃ later : (SideValue model side ⟨output, place.roles.prover⟩ ×
            SideValue model side ⟨output, place.roles.verifier⟩) ×
          ThreadState model t (side place.roles.prover) (side place.roles.verifier) →
            Environment (SideValue model side) emitted.context,
        emitted.Runs (labelledMeaning model label functionTable table side) env
          ((sem.draw (side place.roles.prover) (side place.roles.verifier) place site (label site) law (env first, env second)).bind
            fun result => .done (later result)) ∧
        ∀ result, later result (emitted.values.get .here) = result.1.1 ∧
          later result (emitted.values.get (.there .here)) = result.1.2 ∧
          later result (emitted.values.get (.there (.there .here))) = result.2.1 ∧
          later result (emitted.values.get (.there (.there (.there .here)))) = result.2.2 ∧
          ∀ {ty : Located} (reference : Var Δ ty),
            later result (reference.extend emitted.grows) = env reference

end Sound

/-! ## What the step does at an exchange and at a draw -/

section Rewritten

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {new : List ProtocolHeader} {deployed : Bool} {t : Threads} {rule : Rule t operations functions}

/-- An emitted sequence is determined by its parts. -/
theorem Emitted.eta {dialect : Dialect} {Δ : List dialect.Ty} {head : dialect.Ty}
    {rest : List dialect.Ty} (emitted : Emitted dialect Δ (head :: rest)) :
    ({ emitted with values := .cons (emitted.values.get .here) emitted.values.tail } :
      Emitted dialect Δ (head :: rest)) = emitted := by
  cases emitted with
  | mk context grows wrap values => cases values; rfl

/-- An exchange is rewritten only when it is from the prover to the verifier. -/
theorem rewrittenExchange_between {place : Place} {sender receiver site : Nat} {type : Ty}
    {Δ : List Located} {value : Var Δ ⟨type, sender⟩} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)}
    {result : Except StepRefusal (Emitted (ProtocolDialect operations functions new deployed) Δ
      [⟨type, receiver⟩, t.first place.roles, t.second place.roles])}
    (rewritten : rewrittenExchange t rule place sender receiver site type value first second =
      some result) :
    sender = place.roles.prover ∧ receiver = place.roles.verifier := by
  unfold rewrittenExchange at rewritten
  split at rewritten
  · assumption
  · cases rewritten

/-- An exchange from the prover to the verifier is rewritten or refused. -/
theorem rewrittenExchange_some {place : Place} {site : Nat} {type : Ty} {Δ : List Located}
    {value : Var Δ ⟨type, place.roles.prover⟩} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)} :
    rewrittenExchange (new := new) (deployed := deployed) t rule place place.roles.prover
      place.roles.verifier site type value first second ≠ none := by
  unfold rewrittenExchange
  rw [dif_pos ⟨rfl, rfl⟩]
  split <;> exact Option.some_ne_none _

/-- What an exchange from the prover to the verifier becomes is what the rule emits. -/
theorem rewrittenExchange_ok {place : Place} {site : Nat} {type : Ty} {Δ : List Located}
    {value : Var Δ ⟨type, place.roles.prover⟩} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)}
    {emitted : Emitted (ProtocolDialect operations functions new deployed) Δ
      [⟨type, place.roles.verifier⟩, t.first place.roles, t.second place.roles]}
    (rewritten : rewrittenExchange t rule place place.roles.prover place.roles.verifier site type
      value first second = some (.ok emitted)) :
    rule.exchange place site type value first second = .ok emitted := by
  unfold rewrittenExchange at rewritten
  rw [dif_pos ⟨rfl, rfl⟩] at rewritten
  split at rewritten
  · rename_i raw emits
    simp only [Option.some.injEq, Except.ok.injEq] at rewritten
    rw [← rewritten]
    exact emits.trans (congrArg Except.ok (Emitted.eta raw).symm)
  · simp only [Option.some.injEq] at rewritten
    cases rewritten

/-- A draw is rewritten only when it is between the two transcript roles. -/
theorem rewrittenDraw_between {place : Place} {owner receiver site : Nat} {inputs : List Ty}
    {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩} {Δ : List Located}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    {result : Except StepRefusal (Emitted (ProtocolDialect operations functions new deployed) Δ
      [⟨output, owner⟩, ⟨output, receiver⟩, t.first place.roles, t.second place.roles])}
    (rewritten : rewrittenDraw t rule place owner receiver site law first second = some result) :
    (owner = place.roles.verifier ∧ receiver = place.roles.prover) ∨
      (owner = place.roles.prover ∧ receiver = place.roles.verifier) := by
  unfold rewrittenDraw at rewritten
  split at rewritten
  · exact .inl (by assumption)
  · split at rewritten
    · exact .inr (by assumption)
    · cases rewritten

/-- A draw by the verifier for the prover is rewritten or refused. -/
theorem rewrittenDraw_verifier_some {place : Place} {site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {Δ : List Located}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)} :
    rewrittenDraw (new := new) (deployed := deployed) t rule place place.roles.verifier
      place.roles.prover site law first second ≠ none := by
  unfold rewrittenDraw
  rw [dif_pos ⟨rfl, rfl⟩]
  split <;> exact Option.some_ne_none _

/-- A draw by the prover for the verifier is rewritten or refused. -/
theorem rewrittenDraw_prover_some {place : Place} {site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {Δ : List Located}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)} :
    rewrittenDraw (new := new) (deployed := deployed) t rule place place.roles.prover
      place.roles.verifier site law first second ≠ none := by
  unfold rewrittenDraw
  split
  · split <;> exact Option.some_ne_none _
  · rw [dif_pos ⟨rfl, rfl⟩]
    split <;> exact Option.some_ne_none _

/-- What a draw by the verifier for the prover becomes: what the rule emits, with the
owner's coin, the verifier's, bound first. -/
theorem rewrittenDraw_verifier_ok {place : Place} {site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {Δ : List Located}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    {emitted : Emitted (ProtocolDialect operations functions new deployed) Δ
      [⟨output, place.roles.verifier⟩, ⟨output, place.roles.prover⟩, t.first place.roles,
        t.second place.roles]}
    (rewritten : rewrittenDraw t rule place place.roles.verifier place.roles.prover site law first
      second = some (.ok emitted)) :
    ∃ raw, rule.draw place site law first second = .ok raw ∧
      emitted = ⟨raw.context, raw.grows, raw.wrap,
        .cons (raw.values.get (.there .here)) (.cons (raw.values.get .here) raw.values.tail.tail)⟩ := by
  unfold rewrittenDraw at rewritten
  rw [dif_pos ⟨rfl, rfl⟩] at rewritten
  split at rewritten
  · rename_i raw emits
    simp only [Option.some.injEq, Except.ok.injEq] at rewritten
    exact ⟨raw, emits, rewritten.symm⟩
  · simp only [Option.some.injEq] at rewritten
    cases rewritten

/-- What a draw by the prover for the verifier becomes: what the rule emits. -/
theorem rewrittenDraw_prover_ok {place : Place} {site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {Δ : List Located}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    {emitted : Emitted (ProtocolDialect operations functions new deployed) Δ
      [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩, t.first place.roles,
        t.second place.roles]}
    (other : ¬(place.roles.prover = place.roles.verifier ∧
      place.roles.verifier = place.roles.prover))
    (rewritten : rewrittenDraw t rule place place.roles.prover place.roles.verifier site law first
      second = some (.ok emitted)) :
    ∃ raw, rule.draw place site law first second = .ok raw ∧
      emitted = ⟨raw.context, raw.grows, raw.wrap,
        .cons (raw.values.get .here) (.cons (raw.values.get (.there .here)) raw.values.tail.tail)⟩ := by
  unfold rewrittenDraw at rewritten
  rw [dif_neg other, dif_pos ⟨rfl, rfl⟩] at rewritten
  split at rewritten
  · rename_i raw emits
    simp only [Option.some.injEq, Except.ok.injEq] at rewritten
    exact ⟨raw, emits, rewritten.symm⟩
  · simp only [Option.some.injEq] at rewritten
    cases rewritten

end Rewritten

/-! ## Values of a holder across an equation of memberships -/

/-- A held value at an equal membership. -/
@[expose] def Held.along {X : Type} {present other : Bool} (same : present = other) (held : Held X other) :
    Held X present :=
  same ▸ held

/-- The inverse of `Held.along`. -/
@[expose] def Held.back {X : Type} {present other : Bool} (same : present = other) (held : Held X present) :
    Held X other :=
  same ▸ held

@[simp] theorem Held.back_along {X : Type} {present other : Bool} (same : present = other)
    (held : Held X other) : Held.back same (Held.along same held) = held := by
  subst same; rfl

@[simp] theorem Held.along_back {X : Type} {present other : Bool} (same : present = other)
    (held : Held X present) : Held.along same (Held.back same held) = held := by
  subst same; rfl

/-- The value of a reference re-typed at the holder that runs it. -/
theorem retype_along {model : Model} {side : Side} {Δ : List Located} {type : Ty}
    {inner outer : Nat} (same : inner = outer) (env : Environment (SideValue model side) Δ)
    (reference : Var Δ ⟨type, outer⟩) :
    env (reference.retype (congrArg (Located.mk type) same.symm)) =
      Held.along (congrArg side same) (env reference) := by
  subst same; rfl

theorem retype_back {model : Model} {side : Side} {Δ : List Located} {type : Ty}
    {inner outer : Nat} (same : inner = outer) (env : Environment (SideValue model side) Δ)
    (reference : Var Δ ⟨type, inner⟩) :
    env (reference.retype (congrArg (Located.mk type) same)) =
      Held.back (congrArg side same) (env reference) := by
  subst same; rfl

/-! ## What the theorem requires of a handler -/

/-- What fits an image of a callee: a predicate on the handlers of every side, at every
path, for the callee's transcript roles. The two memberships are parameters with their
equations, so that a caller's handler is a handler of the callee's side without a cast. -/
abbrev CalleeFit (model : Model) (t : Threads) (_header : ProtocolHeader) : Type :=
  (inner : TranscriptRoles) → (path : List Nat) → (side : Side) → (prover verifier : Bool) →
    side inner.prover = prover → side inner.verifier = verifier →
      ThreadHandler model t prover verifier → Prop

section Fits

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} (t : Threads)
  (rule : Rule t operations functions) (sem : RuleMeaning model t operations)
  (functionTable : FunctionTable model functions) (oldTable : ProtocolTable model old)
  (table : CalleeTable t.header old new) (fits : Values (CalleeFit model t) old)
  (place : Place) (side : Side) (label : Nat → Site)
  (handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier))

/-- The handler passes an operation: every process of the operation. -/
@[expose] def OperationPasses (op : ProtocolOp operations functions old deployed) : Prop :=
  ∀ (arguments : Values (SideValue model side) op.arguments)
    (regions : Values (RegionFunction (SideValue model side) (Effects model)) op.regions),
    PIR.Passes handler (labelledOperation model label functionTable oldTable side op arguments regions)

/-- The handler acts as the rule at an exchange from the prover to the verifier. -/
@[expose] def ExchangeActs (site : Nat) (type : Ty) : Prop :=
  ∀ (arguments : Values (SideValue model side) [⟨type, place.roles.prover⟩])
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
    (labelledOperation model label functionTable oldTable side (operations := operations)
        (deployed := deployed) (.exchange place.roles.prover place.roles.verifier site type)
        arguments .nil).interpretWith handler state =
      (sem.exchange (side place.roles.prover) (side place.roles.verifier) place site (label site) type (arguments.get .here) state).bind fun result =>
        .done (Values.cons (Value := SideValue model side) (ty := Located.mk type place.roles.verifier)
          result.1 .nil, result.2)

/-- The handler acts as the rule at a draw by the verifier for the prover. -/
@[expose] def DrawByVerifierActs (site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true) :
    Prop :=
  ∀ (arguments : Values (SideValue model side) (Located.atRole place.roles.verifier inputs))
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
    (labelledOperation model label functionTable oldTable side (deployed := deployed)
        (.draw place.roles.verifier [place.roles.prover] site law populated) arguments .nil).interpretWith
        handler state =
      (sem.draw (side place.roles.prover) (side place.roles.verifier) place site (label site) law state).bind fun result =>
        .done (Values.cons (Value := SideValue model side) (ty := Located.mk output place.roles.verifier)
          result.1.2 (.cons (ty := Located.mk output place.roles.prover) result.1.1 .nil), result.2)

/-- The handler acts as the rule at a draw by the prover for the verifier. -/
@[expose] def DrawByProverActs (site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true) :
    Prop :=
  ∀ (arguments : Values (SideValue model side) (Located.atRole place.roles.prover inputs))
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
    (labelledOperation model label functionTable oldTable side (deployed := deployed)
        (.draw place.roles.prover [place.roles.verifier] site law populated) arguments .nil).interpretWith
        handler state =
      (sem.draw (side place.roles.prover) (side place.roles.verifier) place site (label site) law state).bind fun result =>
        .done (Values.cons (Value := SideValue model side) (ty := Located.mk output place.roles.prover)
          result.1.1 (.cons (ty := Located.mk output place.roles.verifier) result.1.2 .nil), result.2)

/-- What the handler does at a draw: the rule's action when the draw is between the two
transcript roles, and nothing otherwise. -/
@[expose] def DrawFits (owner : Nat) (receivers : List Nat) (site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true) :
    Prop :=
  match receivers with
  | [receiver] =>
      (owner = place.roles.verifier → receiver = place.roles.prover →
        DrawByVerifierActs (deployed := deployed) t sem functionTable oldTable place side label
          handler site law populated) ∧
      (¬(owner = place.roles.verifier ∧ receiver = place.roles.prover) →
        owner = place.roles.prover → receiver = place.roles.verifier →
          DrawByProverActs (deployed := deployed) t sem functionTable oldTable place side label
            handler site law populated) ∧
      (¬(owner = place.roles.verifier ∧ receiver = place.roles.prover) →
        ¬(owner = place.roles.prover ∧ receiver = place.roles.verifier) →
          OperationPasses (deployed := deployed) t functionTable oldTable place side label handler
            (.draw owner [receiver] site law populated))
  | receivers =>
      OperationPasses (deployed := deployed) t functionTable oldTable place side label handler
        (.draw owner receivers site law populated)

/-- The handler passes every process of every region function. -/
@[expose] def PassRegions : {signatures : List (List Located × List Located)} →
    Values (RegionFunction (SideValue model side) (Effects model)) signatures → Prop
  | [], _ => True
  | _ :: _, regions =>
      (∀ values, PIR.Passes handler ((regions.get .here) values)) ∧ PassRegions regions.tail

mutual
  /-- What the theorem requires of the handler for a region of a definition, operation by
  operation, as the step treats it. -/
  @[expose] def Fits {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out → Prop
    | .ret _ => True
    | .stop _ => True
    | .bind body rest => Fits body ∧ Fits rest
    | .letOp (.at ..) _ _ rest => Fits rest
    | .letOp (.sample owner site law populated) _ _ rest =>
        OperationPasses (operations := operations) (deployed := deployed) t functionTable oldTable place
          side label handler
          (.sample owner site law populated) ∧ Fits rest
    | .letOp (.exchange sender receiver site type) _ _ rest =>
        (sender = place.roles.prover → receiver = place.roles.verifier →
          ExchangeActs (operations := operations) (deployed := deployed) t sem functionTable
            oldTable place side label handler site type) ∧
        (¬(sender = place.roles.prover ∧ receiver = place.roles.verifier) →
          OperationPasses (operations := operations) (deployed := deployed) t functionTable oldTable place
          side label handler
            (.exchange sender receiver site type)) ∧ Fits rest
    | .letOp (.draw owner receivers site law populated) _ _ rest =>
        DrawFits (deployed := deployed) t sem functionTable oldTable place side label handler owner
          receivers site law populated ∧ Fits rest
    | .letOp (.repeat ..) _ bodies rest =>
        (touchesRegions t rule.derives table place.definition (some place.roles.prover)
            (some place.roles.verifier) bodies = .ok true → FitsAll bodies) ∧
        (touchesRegions t rule.derives table place.definition (some place.roles.prover)
            (some place.roles.verifier) bodies = .ok false →
          PassRegions t place side handler
            (bodies.denote (labelledMeaning model label functionTable oldTable side))) ∧ Fits rest
    | .letOp (.choose ..) _ bodies rest =>
        (touchesRegions t rule.derives table place.definition (some place.roles.prover)
            (some place.roles.verifier) bodies = .ok true → FitsAll bodies) ∧
        (touchesRegions t rule.derives table place.definition (some place.roles.prover)
            (some place.roles.verifier) bodies = .ok false →
          PassRegions t place side handler
            (bodies.denote (labelledMeaning model label functionTable oldTable side))) ∧ Fits rest
    | .letOp (.apply (header := header) callee roleMap site _) _ _ rest =>
        (∀ threaded : ThreadedCallee t new place.roles roleMap header,
          threadedCallee t table place.roles roleMap callee = some threaded →
            (fits.get callee) threaded.inner (label site).below (Side.preimage roleMap side)
              (side place.roles.prover) (side place.roles.verifier)
              (congrArg side threaded.prover) (congrArg side threaded.verifier) handler) ∧
        (threadedCallee t table place.roles roleMap callee = none →
          ∀ arguments : Values (SideValue model (Side.preimage roleMap side)) header.inputs,
            PIR.Passes handler
              ((oldTable.get callee) (label site).below (Side.preimage roleMap side) arguments)) ∧
        Fits rest

  /-- The handler fits every one of several closed regions. -/
  @[expose] def FitsAll {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures → Prop
    | .nil => True
    | .cons body tail => Fits body ∧ FitsAll tail
end

end Fits

/-! ## Agreement, iteration and selection under a handler -/

section Control

variable {X α : Type} (holds : α → Prop) (same : X → X → Bool) (side : Side) (onValue : X → α)
  (onDisagree : α)

theorem agreeWith_holds (holdsValue : ∀ value, holds (onValue value)) (holdsDisagree : holds onDisagree)
    (value : X) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles),
      holds (agreeWith same side onValue onDisagree value roles values)
  | [], _ => holdsValue value
  | role :: rest, values => by
      cases present : side role with
      | true =>
          rw [agreeWith_present present]
          cases same value (Held.value (side role) present (values.get .here)) with
          | true => exact agreeWith_holds holdsValue holdsDisagree value rest values.tail
          | false => exact holdsDisagree
      | false =>
          rw [agreeWith_absent present]
          exact agreeWith_holds holdsValue holdsDisagree value rest values.tail

/-- A property of every outcome of an agreement holds of the agreement. -/
theorem agreed_holds (holdsValue : ∀ value, holds (onValue value)) (holdsDisagree : holds onDisagree) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles)
      (onNone : roles.any side = false → α), (∀ none, holds (onNone none)) →
      holds (agreed same side onValue onDisagree roles values onNone)
  | [], _, onNone, holdsNone => holdsNone rfl
  | role :: rest, values, onNone, holdsNone => by
      cases present : side role with
      | true =>
          rw [agreed_present present]
          exact agreeWith_holds holds same side onValue onDisagree holdsValue holdsDisagree _ rest
            values.tail
      | false =>
          rw [agreed_absent present]
          exact agreed_holds holdsValue holdsDisagree rest values.tail _ fun _ => holdsNone _

end Control

/-- The value of a holder outside the side is the absent one. -/
theorem Held.eq_absent {X : Type} :
    ∀ (present : Bool) (absent : present = false) (held : Held X present),
      held = Held.absent present absent
  | false, _, _ => rfl

section Laws

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {functionTable : FunctionTable model functions} {oldTable : ProtocolTable model old}
  {newTable : ProtocolTable model new} {place : Place} {side : Side} {label : Nat → Site}
  {handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier)}

/-- A handler passes the loop of a `repeat` whose step it passes. -/
theorem repeatProcess_passes {S : Type}
    {handler : PIR.StatefulInterpretation (Effects model) (Effects model) S} (side : Side)
    (count : RepeatCount) (carried collected : List Located)
    {step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried))}
    (passes : ∀ iteration values, PIR.Passes handler (step iteration values))
    (agreed : Nat) (initial : Values (SideValue model side) carried) :
    PIR.Passes handler (repeatProcess model side count carried collected step agreed initial) := by
  cases count with
  | static number =>
      exact (iterations_passes passes number 0 initial _).bind fun _ => PIR.Passes.done handler _
  | runtime maximum =>
      show PIR.Passes handler
        (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined)
      split
      · exact (iterations_passes passes agreed 0 initial _).bind fun _ =>
          PIR.Passes.done handler _
      · exact PIR.Passes.halt handler _

/-- A handler passes a `repeat` whose region it passes. -/
theorem repeat_passes {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    (arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures)))
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)])
    (passes : PassRegions t place side handler regions) :
    PIR.Passes handler
      (labelledOperation model label functionTable oldTable side (operations := operations)
        (deployed := deployed) (.repeat participants count carried collected captures covered)
        arguments regions) := by
  show PIR.Passes handler (agreed Nat.beq side _ _ participants _ _)
  refine agreed_holds (PIR.Passes handler) Nat.beq side _ _ ?_ (PIR.Passes.halt handler _) participants
    _ _ fun _ => PIR.Passes.done handler _
  intro agreed
  exact repeatProcess_passes side count carried collected (fun _ _ => passes.1 _) agreed _

/-- The regions of a list that a handler passes: every selection is passed. -/
theorem passRegions_select (signature : List Located × List Located) :
    ∀ (count : Nat)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count signature)),
      PassRegions t place side handler regions →
      ∀ (number : Fin count) values,
        PIR.Passes handler (selectArm signature count regions number values)
  | 0, _, _, number, _ => number.elim0
  | _ + 1, _, passes, ⟨0, _⟩, values => passes.1 values
  | count + 1, regions, passes, ⟨number + 1, below⟩, values =>
      passRegions_select signature count regions.tail passes.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ values

/-- The regions of a choice on a variant that a handler passes: the region of every
alternative is passed, on whatever payloads. -/
theorem alternativeProcess_passes {participants : List Nat} {captures outputs : List Located} :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))),
      PassRegions t place side handler regions →
      ∀ (number : Nat)
        (copies : Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role))
          participants)
        (values : Values (SideValue model side) captures),
        PIR.Passes handler
          (alternativeProcess model side participants captures outputs alternatives regions number
            copies values)
  | [], _, _, _, _, _ => PIR.Passes.halt handler _
  | payload :: rest, regions, passes, 0, copies, values => by
      cases found : firstPayloads model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact PIR.Passes.halt handler _
      | some payloads =>
          rw [alternativeProcess_first found]
          exact passes.1 _
  | payload :: rest, regions, passes, number + 1, copies, values => by
      cases found : laterCopies model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact PIR.Passes.halt handler _
      | some later =>
          rw [alternativeProcess_later number found]
          exact alternativeProcess_passes rest regions.tail passes.2 number later values

/-- The regions of a `choose` that a handler passes: the region that a tag selects is
passed. -/
theorem chosenRegion_passes {participants : List Nat} {captures outputs : List Located} :
    ∀ (tag : ChoiceTag)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants captures outputs)),
      PassRegions t place side handler regions →
      ∀ (copies : Values (fun role => Held (model.Value tag.type) (side role)) participants)
        (values : Values (SideValue model side) captures) (value : model.Value tag.type),
        PIR.Passes handler
          (chosenRegion model side participants captures outputs tag regions copies values value)
  | .condition, regions, passes, _, values, _ =>
      passRegions_select (captures, outputs) 2 regions passes _ values
  | .arm count, regions, passes, _, values, _ =>
      passRegions_select (captures, outputs) count regions passes _ values
  | .alternative _ alternatives, regions, passes, copies, values, _ =>
      alternativeProcess_passes alternatives regions passes _ copies values

/-- A handler passes a `choose` whose regions it passes. -/
theorem choose_passes {participants : List Nat} {tag : ChoiceTag} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    (arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures))
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      (tag.regions participants captures outputs))
    (passes : PassRegions t place side handler regions) :
    PIR.Passes handler
      (labelledOperation model label functionTable oldTable side (operations := operations)
        (deployed := deployed) (.choose participants tag captures outputs covered) arguments
        regions) := by
  show PIR.Passes handler (agreed (tag.same model.Carrier) side _ _ participants _ _)
  refine agreed_holds (PIR.Passes handler) (tag.same model.Carrier) side _ _ ?_
    (PIR.Passes.halt handler _) participants _ _ fun _ => PIR.Passes.done handler _
  intro value
  exact chosenRegion_passes tag regions passes _ _ value

/-- An agreement under a handler is the agreement on the handled outcomes. -/
theorem agreed_threads {X A B S : Type}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) S) (pack : A × S → B)
    (same : X → X → Bool) (side : Side) (onValue : X → PIR.Process (Effects model) A)
    (onDisagree : PIR.Process (Effects model) A) (roles : List Nat)
    (values : Values (fun role => Held X (side role)) roles)
    (onNone : roles.any side = false → PIR.Process (Effects model) A) (state : S) :
    ((agreed same side onValue onDisagree roles values onNone).interpretWith handler state).bind
        (fun result => .done (pack result)) =
      agreed same side
        (fun value => ((onValue value).interpretWith handler state).bind fun result =>
          .done (pack result))
        ((onDisagree.interpretWith handler state).bind fun result => .done (pack result)) roles values
        fun none => ((onNone none).interpretWith handler state).bind fun result =>
          .done (pack result) :=
  agreed_map same side onValue onDisagree
    (fun process : PIR.Process (Effects model) A =>
      (process.interpretWith handler state).bind fun result => .done (pack result)) roles values
    onNone

/-- The values bound last are the values of the references to them. -/
theorem eval_newest {Ty : Type} {Value : Ty → Type} :
    ∀ (added : List Ty) {Γ : List Ty} (env : Environment Value Γ) (values : Values Value added),
      Operands.eval (Environment.bindAll env values) (Operands.newest added) = values
  | [], _, _, .nil => rfl
  | _ :: rest, _, env, .cons value values =>
      cons_congr (Environment.bindAll_weaken (env.push value) values Var.here)
        (eval_newest rest (env.push value) values)

/-- References put between others name the values put between the others' values. -/
theorem eval_between {Ty : Type} {Value : Ty → Type} {Γ states : List Ty} (leading : List Ty)
    {trailing : List Ty} (env : Environment Value Γ)
    (operands : Operands Γ (states ++ (leading ++ trailing))) :
    Operands.eval env (Values.between leading operands) =
      Values.between leading (Operands.eval env operands) := by
  simp only [Values.between, eval_append, eval_split]

/-- A region whose first values are returned after the next ones returns the values of the
region, in that order. -/
theorem Region.returnAfter_denote {dialect : Dialect} {interface : PIR.Signature}
    (meaning : RegionMeaning dialect interface) {Δ : List dialect.Ty} (states : List dialect.Ty) :
    ∀ (leading : List dialect.Ty) {trailing : List dialect.Ty}
      (region : Region dialect Δ (states ++ (leading ++ trailing)))
      (env : Environment meaning.Value Δ),
      (Region.returnAfter states leading region).denote meaning env =
        (region.denote meaning env).bind fun values => .done (Values.between leading values)
  | [], trailing, region, env => by
      have same : (fun values : Values meaning.Value (states ++ trailing) =>
          (PIR.Process.done (Values.between [] values) :
            PIR.Process interface (Values meaning.Value (states ++ trailing)))) =
            PIR.Process.done :=
        funext fun values => congrArg PIR.Process.done (Values.append_split states values)
      exact ((congrArg (PIR.Process.bind (region.denote meaning env)) same).trans
        (PIR.Process.bind_done _)).symm
  | head :: rest, _, region, env => by
      show (region.denote meaning env).bind _ = _
      congr 1
      funext values
      show PIR.Process.done (Operands.eval _ (Values.between (head :: rest) (Operands.newest _))) = _
      rw [eval_between, eval_newest]

/-- The values a threaded loop or its region returns: the final two threaded values after
the first of the old ones, `leading`, which are what the loop or the region collects. -/
@[expose] def threadedAfter {model : Model} {t : Threads} {side : Side} {roles : TranscriptRoles}
    (leading : List Located) {out : List Located}
    (result : Values (SideValue model side) (leading ++ out) ×
      ThreadState model t (side roles.prover) (side roles.verifier)) :
    Values (SideValue model side) (leading ++ (t.states roles ++ out)) :=
  (result.1.split leading).1.append
    (.cons result.2.1 (.cons result.2.2 (result.1.split leading).2))

/-- With nothing before them, the two values are returned first. -/
theorem threadedAfter_nil {model : Model} {t : Threads} {side : Side} {roles : TranscriptRoles}
    {out : List Located}
    (result : Values (SideValue model side) out ×
      ThreadState model t (side roles.prover) (side roles.verifier)) :
    threadedAfter [] result = threadedValues result := rfl

/-- The two values returned first, put after the first of the others. -/
theorem between_threadedValues {model : Model} {t : Threads} {side : Side}
    {roles : TranscriptRoles} (leading : List Located) {out : List Located}
    (result : Values (SideValue model side) (leading ++ out) ×
      ThreadState model t (side roles.prover) (side roles.verifier)) :
    Values.between leading (threadedValues result) = threadedAfter leading result := rfl

/-- The values after the two threaded values of a result of a threaded loop are what the
loop carries on, and the values before them what it collected. -/
theorem split_threadedAfter {model : Model} {t : Threads} {side : Side} {roles : TranscriptRoles}
    (leading : List Located) {out : List Located}
    (result : Values (SideValue model side) (leading ++ out) ×
      ThreadState model t (side roles.prover) (side roles.verifier)) :
    Values.split leading (threadedAfter leading result) =
      ((result.1.split leading).1,
        Values.cons (Value := SideValue model side) (ty := t.first roles) result.2.1
          (Values.cons (ty := t.second roles) result.2.2 (result.1.split leading).2)) :=
  Values.split_append _ _

/-- The iterations of a threaded loop: the loop that carries the two values before its own
runs the iterations of the old loop under the handler and collects what they collect, when
its step, which returns the two values after the collected ones, is the old step under the
handler. -/
theorem repeatIterations_threads (carried collected : List Located)
    {step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried))}
    {image : Nat → Values (SideValue model side) (t.states place.roles ++ carried) →
      PIR.Process (Effects model)
        (Values (SideValue model side) (collected ++ (t.states place.roles ++ carried)))}
    (related : ∀ (iteration : Nat) (values : Values (SideValue model side) carried)
      (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
      image iteration (.cons state.1 (.cons state.2 values)) =
        ((step iteration values).interpretWith handler state).bind fun result =>
          .done (threadedAfter collected result)) :
    ∀ (remaining done : Nat) (initial : Values (SideValue model side) carried)
      (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
      (earlier : Values (SideValue model side) (collectedSequencesAt (some done) collected)),
      repeatIterations model side (t.states place.roles ++ carried) collected image remaining done
          (.cons state.1 (.cons state.2 initial)) earlier =
        ((repeatIterations model side carried collected step remaining done initial
            earlier).interpretWith handler state).bind fun final =>
          .done (Values.cons (Value := SideValue model side) (ty := t.first place.roles) final.2.1
            (Values.cons (ty := t.second place.roles) final.2.2 final.1.1), final.1.2)
  | 0, _, _, _, _ => rfl
  | remaining + 1, done, initial, state, earlier => by
      rw [repeatIterations_succ, repeatIterations_succ, related, PIR.Process.interpretWith_bind,
        PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      congr 1
      funext result
      show repeatIterations model side (t.states place.roles ++ carried) collected image remaining
          (done + 1) (Values.split collected (threadedAfter collected result)).2
          (sideCollectedPush model side collected
            (Values.split collected (threadedAfter collected result)).1 earlier) = _
      rw [split_threadedAfter]
      exact repeatIterations_threads carried collected related remaining (done + 1) _ result.2 _

/-- The loop of a threaded `repeat` once its count is agreed: it is the old loop under the
handler, and it returns the two values between the sequences of the collected values,
which are the old loop's, and the carried values. -/
theorem repeatProcess_threads (count : RepeatCount) (carried collected : List Located)
    {step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried))}
    {image : Nat → Values (SideValue model side) (t.states place.roles ++ carried) →
      PIR.Process (Effects model)
        (Values (SideValue model side) (collected ++ (t.states place.roles ++ carried)))}
    (related : ∀ (iteration : Nat) (values : Values (SideValue model side) carried)
      (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
      image iteration (.cons state.1 (.cons state.2 values)) =
        ((step iteration values).interpretWith handler state).bind fun result =>
          .done (threadedAfter collected result))
    (agreed : Nat) (initial : Values (SideValue model side) carried)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)) :
    repeatProcess model side count (t.states place.roles ++ carried) collected image agreed
        (.cons state.1 (.cons state.2 initial)) =
      ((repeatProcess model side count carried collected step agreed initial).interpretWith
          handler state).bind fun result =>
        .done (threadedAfter (collectedSequencesAt count.size collected) result) := by
  cases count with
  | static number =>
      rw [repeatProcess_static, repeatProcess_static,
        repeatIterations_threads carried collected related, PIR.Process.interpretWith_bind,
        PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      congr 1
      funext final
      show PIR.Process.done _ = PIR.Process.done (threadedAfter _ (Values.append _ _, _))
      simp only [threadedAfter, Values.split_append]
  | runtime maximum =>
      by_cases within : agreed ≤ maximum
      · rw [repeatProcess_within model side within, repeatProcess_within model side within,
          repeatIterations_threads carried collected related, PIR.Process.interpretWith_bind,
          PIR.Process.bind_assoc, PIR.Process.bind_assoc]
        congr 1
        funext final
        show PIR.Process.done _ = PIR.Process.done (threadedAfter _ (Values.append _ _, _))
        simp only [threadedAfter, Values.split_append]
      · rw [repeatProcess_beyond model side (Nat.lt_of_not_le within),
          repeatProcess_beyond model side (Nat.lt_of_not_le within)]
        rfl

/-- A threaded `repeat`: the loop that carries the two values before its own is the old
loop under the handler, with the sequences of the collected values unchanged and the two
values returned after them, when its region, which takes the two values after the
iteration numbers and returns them after the values it collects, is the old region under
the handler. -/
theorem repeat_threads {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)])
    (images : Values (RegionFunction (SideValue model side) (Effects model))
      [(Located.ofRoles .nat participants ++ (t.states place.roles ++ (carried ++ captures)),
        collected ++ (t.states place.roles ++ carried))])
    (threads : ∀ (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
      (numbers : Values (SideValue model side) (Located.ofRoles .nat participants))
      (values : Values (SideValue model side) (carried ++ captures)),
      (images.get .here) (numbers.append (.cons state.1 (.cons state.2 values))) =
        (((regions.get .here) (numbers.append values)).interpretWith handler state).bind
          fun result => .done (threadedAfter collected result))
    (counts : Values (SideValue model side) (count.operands participants))
    (rest : Values (SideValue model side) (carried ++ captures))
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)) :
    labelledOperation model label functionTable newTable side (operations := operations)
        (deployed := deployed)
        (.repeat participants count (t.states place.roles ++ carried) collected captures covered)
        (counts.append (.cons state.1 (.cons state.2 rest))) images =
      ((labelledOperation model label functionTable oldTable side (operations := operations)
          (deployed := deployed) (.repeat participants count carried collected captures covered)
          (counts.append rest) regions).interpretWith handler state).bind fun result =>
        .done (threadedAfter (collectedSequencesAt count.size collected) result) := by
  simp only [labelledOperation, repeatOperation, Values.split_append]
  rw [agreed_threads]
  refine agreed_congr Nat.beq side ?_ rfl fun _ => ?_
  · intro agreed
    exact repeatProcess_threads count carried collected (fun _ _ state => threads state _ _)
      agreed _ state
  · show PIR.Process.done _ = PIR.Process.done (threadedAfter _ (Values.append _ _, _))
    simp only [threadedAfter, Values.split_append]
    rfl

/-- The regions of a threaded operation are the old regions under the handler: each takes
the two threaded values after the values that lead its inputs. -/
@[expose] def RegionsThread (handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier)) :
    {signatures targets : List (List Located × List Located)} →
      ThreadedRegions t place.roles signatures targets →
      Values (RegionFunction (SideValue model side) (Effects model)) signatures →
      Values (RegionFunction (SideValue model side) (Effects model)) targets → Prop
  | _, _, .nil, _, _ => True
  | _, _, .cons leading added tail, olds, images =>
      (∀ (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
          (before : Values (SideValue model side) leading)
          (values : Values (SideValue model side) added),
        (images.get .here) (before.append (.cons state.1 (.cons state.2 values))) =
          (((olds.get .here) (before.append values)).interpretWith handler state).bind fun result =>
            .done (threadedValues result)) ∧
      RegionsThread handler tail olds.tail images.tail

/-- The selected arm of a threaded choice is the selected arm of the old choice under the
handler. -/
theorem selectArm_threads (captures outputs : List Located) :
    ∀ (count : Nat)
      (olds : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count (captures, outputs)))
      (images : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count
          (t.states place.roles ++ captures, t.states place.roles ++ outputs))),
      RegionsThread handler (t.arms place.roles captures outputs count) olds images →
      ∀ (number : Fin count)
        (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
        (values : Values (SideValue model side) captures),
        selectArm (t.states place.roles ++ captures, t.states place.roles ++ outputs) count
            images number (.cons state.1 (.cons state.2 values)) =
          ((selectArm (captures, outputs) count olds number values).interpretWith handler state).bind
            fun result => .done (threadedValues result)
  | 0, _, _, _, number, _, _ => number.elim0
  | _ + 1, _, _, threads, ⟨0, _⟩, state, values => threads.1 state .nil values
  | count + 1, olds, images, threads, ⟨number + 1, below⟩, state, values =>
      selectArm_threads captures outputs count olds.tail images.tail threads.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ state values

/-- The region of an alternative of a threaded choice, which takes the two values after
the payloads, is the region of that alternative of the old choice under the handler. -/
theorem alternativeProcess_threads {participants : List Nat} (captures outputs : List Located) :
    ∀ (alternatives : List Ty)
      (olds : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (images : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ (t.states place.roles ++ captures),
            t.states place.roles ++ outputs))),
      RegionsThread handler (t.alternatives place.roles participants captures outputs alternatives)
        olds images →
      ∀ (number : Nat)
        (copies : Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role))
          participants)
        (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
        (values : Values (SideValue model side) captures),
        alternativeProcess model side participants (t.states place.roles ++ captures)
            (t.states place.roles ++ outputs) alternatives images number copies
            (.cons state.1 (.cons state.2 values)) =
          ((alternativeProcess model side participants captures outputs alternatives olds number
            copies values).interpretWith handler state).bind fun result =>
            .done (threadedValues result)
  | [], _, _, _, _, _, _, _ => rfl
  | payload :: rest, olds, images, threads, 0, copies, state, values => by
      cases found : firstPayloads model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found, alternativeProcess_first_other found]
          rfl
      | some payloads =>
          rw [alternativeProcess_first found, alternativeProcess_first found]
          exact threads.1 state _ values
  | payload :: rest, olds, images, threads, number + 1, copies, state, values => by
      cases found : laterCopies model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found,
            alternativeProcess_later_other number found]
          rfl
      | some later =>
          rw [alternativeProcess_later number found, alternativeProcess_later number found]
          exact alternativeProcess_threads captures outputs rest olds.tail images.tail threads.2
            number later state values

/-- The region that a tag selects of a threaded choice is the region that it selects of
the old choice under the handler. -/
theorem chosenRegion_threads {participants : List Nat} (captures outputs : List Located) :
    ∀ (tag : ChoiceTag)
      (olds : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants captures outputs))
      (images : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants (t.states place.roles ++ captures)
          (t.states place.roles ++ outputs))),
      RegionsThread handler (t.choice place.roles participants captures outputs tag) olds images →
      ∀ (copies : Values (fun role => Held (model.Value tag.type) (side role)) participants)
        (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
        (values : Values (SideValue model side) captures) (value : model.Value tag.type),
        chosenRegion model side participants (t.states place.roles ++ captures)
            (t.states place.roles ++ outputs) tag images copies
            (.cons state.1 (.cons state.2 values)) value =
          ((chosenRegion model side participants captures outputs tag olds copies values
            value).interpretWith handler state).bind fun result => .done (threadedValues result)
  | .condition, olds, images, threads, _, state, values, _ =>
      selectArm_threads captures outputs 2 olds images threads _ state values
  | .arm count, olds, images, threads, _, state, values, _ =>
      selectArm_threads captures outputs count olds images threads _ state values
  | .alternative _ alternatives, olds, images, threads, copies, state, values, _ =>
      alternativeProcess_threads captures outputs alternatives olds images threads _ copies state
        values

/-- A threaded `choose`: the choice whose arms capture and return the two values is the
old choice under the handler, when its arms are the old arms under the handler. -/
theorem choose_threads {participants : List Nat} {tag : ChoiceTag} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    {held : Located.heldBy participants (t.states place.roles ++ outputs) = true}
    (arms : Values (RegionFunction (SideValue model side) (Effects model))
      (tag.regions participants captures outputs))
    (images : Values (RegionFunction (SideValue model side) (Effects model))
      (tag.regions participants (t.states place.roles ++ captures)
        (t.states place.roles ++ outputs)))
    (threads : RegionsThread handler (t.choice place.roles participants captures outputs tag) arms
      images)
    (tags : Values (SideValue model side) (Located.ofRoles tag.type participants))
    (rest : Values (SideValue model side) captures)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)) :
    labelledOperation model label functionTable newTable side (operations := operations)
        (deployed := deployed)
        (.choose participants tag (t.states place.roles ++ captures)
          (t.states place.roles ++ outputs) held)
        (tags.append (.cons state.1 (.cons state.2 rest))) images =
      ((labelledOperation model label functionTable oldTable side (operations := operations)
          (deployed := deployed) (.choose participants tag captures outputs covered)
          (tags.append rest) arms).interpretWith handler state).bind fun result =>
        .done (threadedValues result) := by
  simp only [labelledOperation, Values.split_append]
  rw [agreed_threads]
  refine agreed_congr (tag.same model.Carrier) side
    (fun value => chosenRegion_threads captures outputs tag arms images threads _ state rest value)
    rfl ?_
  intro none
  have absentFirst : side place.roles.prover = false :=
    not_held_of_heldBy (located := t.first place.roles) held none List.mem_cons_self
  have absentSecond : side place.roles.verifier = false :=
    not_held_of_heldBy (located := t.second place.roles) held none
      (List.mem_cons_of_mem _ List.mem_cons_self)
  show PIR.Process.done (Values.cons _ (Values.cons _ _)) = PIR.Process.done (Values.cons _ (Values.cons _ _))
  exact congrArg PIR.Process.done
    (cons_congr (Held.eq_absent _ absentFirst state.1).symm
      (cons_congr (Held.eq_absent _ absentSecond state.2).symm rfl))

/-! ## The statement for the callees -/

/-- What the case of `apply` uses. An image that threads is the callee under every
handler that fits it, for every side; the image with the callee's own header has the
callee's meaning. `fits` gives, per callee, what fits its images. -/
structure CalleesThread (table : CalleeTable t.header old new) (oldTable : ProtocolTable model old)
    (newTable : ProtocolTable model new) (fits : Values (CalleeFit model t) old) : Prop where
  threaded : ∀ {header : ProtocolHeader} (callee : Var old header) (inner : TranscriptRoles)
    (image : Var new (t.header (some inner) header)), table.find callee (some inner) = some image →
    ∀ (path : List Nat) (side : Side) (prover verifier : Bool)
      (isProver : side inner.prover = prover) (isVerifier : side inner.verifier = verifier)
      (handler : ThreadHandler model t prover verifier),
      (fits.get callee) inner path side prover verifier isProver isVerifier handler →
      ∀ (first : Held (model.Value t.prover) prover) (second : Held (model.Value t.verifier) verifier)
        (arguments : Values (SideValue model side) header.inputs),
        (newTable.get image) path side
            (.cons (Held.along isProver first) (.cons (Held.along isVerifier second) arguments)) =
          (((oldTable.get callee) path side arguments).interpretWith handler (first, second)).bind
            fun result =>
              .done (.cons (Held.along isProver result.2.1)
                (.cons (Held.along isVerifier result.2.2) result.1))
  plain : PlainCallees table oldTable newTable

end Laws

/-! ## Environments after the two threaded values -/

/-- One more new value, which no old value is renamed to. -/
theorem Renaming.Agrees.weakenOne {Ty : Type} {Value : Ty → Type} {Γ Δ : List Ty}
    {rename : Renaming Γ Δ} {old : Environment Value Γ} {new : Environment Value Δ}
    (agrees : rename.Agrees old new) {head : Ty} (value : Value head) :
    Renaming.Agrees (rename.weakenOne head) old (new.push value) := by
  intro ty reference
  show (new.push value) ((Mapping.weakenOne rename head).apply reference rfl) = _
  rw [Mapping.apply_weakenOne]
  exact agrees reference

/-- After the two threaded values and the results of an operation: the environments agree
across the renaming, and the two references name the two values. -/
theorem afterTwo_agrees {Value : Located → Type} {Γ Δ : List Located} {rename : Renaming Γ Δ}
    {old : Environment Value Γ} {new : Environment Value Δ} (agrees : rename.Agrees old new)
    (first second : Located) (firstValue : Value first) (secondValue : Value second)
    {added : List Located} (values : Values Value added) :
    (afterTwo first second rename added).1.Agrees (Environment.bindAll old values)
        (Environment.bindAll (Environment.push (Environment.push new firstValue) secondValue)
          values) ∧
      (Environment.bindAll (Environment.push (Environment.push new firstValue) secondValue) values)
          (afterTwo first second rename added).2.1 = firstValue ∧
      (Environment.bindAll (Environment.push (Environment.push new firstValue) secondValue) values)
          (afterTwo first second rename added).2.2 = secondValue :=
  ⟨Renaming.Agrees.keepAll
      (Renaming.Agrees.weakenOne (Renaming.Agrees.weakenOne agrees firstValue) secondValue) values,
    Environment.bindAll_weaken _ values _, Environment.bindAll_weaken _ values _⟩

/-- At the start of the region of a loop that carries the two values: after the values
before them, the two values and the values after them, the environments agree across the
renaming, and the two references name the two values. -/
theorem afterLeading_agrees {Value : Located → Type} (first second : Located)
    (firstValue : Value first) (secondValue : Value second) {added : List Located}
    (values : Values Value added) :
    ∀ (leading : List Located) {Γ Δ : List Located} {rename : Renaming Γ Δ}
      {old : Environment Value Γ} {new : Environment Value Δ}, rename.Agrees old new →
      ∀ (numbers : Values Value leading),
        (afterLeading first second rename leading added).1.Agrees
            (Environment.bindAll old (numbers.append values))
            (Environment.bindAll new
              (numbers.append (.cons firstValue (.cons secondValue values)))) ∧
          (Environment.bindAll new (numbers.append (.cons firstValue (.cons secondValue values))))
              (afterLeading first second rename leading added).2.1 = firstValue ∧
          (Environment.bindAll new (numbers.append (.cons firstValue (.cons secondValue values))))
              (afterLeading first second rename leading added).2.2 = secondValue
  | [], _, _, _, _, _, agrees, .nil => afterTwo_agrees agrees first second firstValue secondValue values
  | _ :: rest, _, _, _, _, _, agrees, .cons number numbers =>
      afterLeading_agrees first second firstValue secondValue values rest (agrees.keep number)
        numbers

end Zkc.Core
