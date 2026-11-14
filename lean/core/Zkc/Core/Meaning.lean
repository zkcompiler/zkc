module

public import Zkc.Core.WellFormed

public section

/-! The meaning of core programs.

A function denotes a process that returns its outputs or stops; it performs no
effect. A protocol denotes, for every side, the process of the side's roles acting
together over the one effect signature `Effects model`. Every presence decision is a
match on a `Bool` membership: the step functions below take the membership of the
roles involved as explicit `Bool` arguments, so a literal side reduces each of them
to one case.

Nothing assumes a broadcast channel: a `draw` announced from outside the side is one
`receive` per receiver in the side. At a `repeat` or a `choose`, the participants in
the side must hold equal copies of the count or tag; otherwise the side stops
with the reserved reason `incomplete`, before the count is compared with the maximum.
Two copies of a variant that is the tag of a `choose` agree when they are the same
alternative, whatever their payloads, and the region of that alternative takes the payload
of each participant in the side.
A count of the operation is a count of which every participant holds the same copy.
Each participant of a `repeat` in the side holds the number of the iteration that runs,
and a value that the iterations collect is kept by its holder when the holder is in the
side.
A stop by any role of the side ends the side's process.

No other construct names `incomplete`: a `guard` and a function known by its header stop
with a `Reason`, and a `stop` of a well-formed definition names an authored reason. A
restricted row applied outside its domain stops with the reserved reason `undefined`.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable (model : Model)

/-- The meaning of a function with the given signature. -/
abbrev FunctionMeaning (inputs outputs : List Ty) : Type :=
  Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs)

/-- The meaning of a protocol: for the sites of the applications that reached it and for
every side, the side's process. -/
abbrev ProtocolMeaning (inputs outputs : List Located) : Type :=
  (path : List Nat) → (side : Side) → Values (SideValue model side) inputs →
    PIR.Process (Effects model) (Values (SideValue model side) outputs)

@[expose, reducible] def FunctionHeader.Meaning (header : FunctionHeader) : Type :=
  FunctionMeaning model header.inputs header.outputs

@[expose, reducible] def ProtocolHeader.Meaning (header : ProtocolHeader) : Type :=
  ProtocolMeaning model header.inputs header.outputs

/-- The meanings of the functions, most recent first. -/
abbrev FunctionTable (functions : List FunctionHeader) : Type :=
  Values (FunctionHeader.Meaning model) functions

/-- The meanings of the protocols, most recent first. -/
abbrev ProtocolTable (protocols : List ProtocolHeader) : Type :=
  Values (ProtocolHeader.Meaning model) protocols

/-- The result of a function known by its header as a process: its outputs, or a stop
with its authored reason. -/
@[expose] def partialProcess {A : Type} : Except Reason A → PIR.Process (Effects model) A
  | .ok value => .done value
  | .error reason => .halt reason.stop

/-- The value of a restricted row as a process: its outputs where the row is defined, and
the stop `undefined` outside its domain. -/
@[expose] def definedProcess {A : Type} : Option A → PIR.Process (Effects model) A
  | some value => .done value
  | none => .halt .undefined

/-- A pure or restricted row applied to its inputs. -/
@[expose] def rowProcess (row : OperationRow) :
    (kind : OperationKind) →
      OperationSignature.applies ⟨row.inputs, row.outputs, kind⟩ = true →
        Values model.Value row.inputs →
          PIR.Process (Effects model) (Values model.Value row.outputs)
  | .pure, applies, arguments => .done (model.pure row applies arguments)
  | .restricted _, _, arguments => definedProcess model (model.restricted row arguments)
  | .sampling, applies, _ => absurd applies Bool.false_ne_true

/-- The number of iterations of a loop that has `remaining` to run after `done`. It is
`remaining + done`, by a recursion that follows the loop's own, so that the number of the
collected values of each iteration is the type's by computation. -/
@[expose, reducible] def iterationsAfter : (remaining done : Nat) → Nat
  | 0, done => done
  | remaining + 1, done => iterationsAfter remaining (done + 1)

theorem iterationsAfter_eq :
    ∀ (remaining done : Nat), iterationsAfter remaining done = remaining + done
  | 0, done => (Nat.zero_add done).symm
  | remaining + 1, done =>
      (iterationsAfter_eq remaining (done + 1)).trans (Nat.succ_add remaining done).symm

/-- What no iteration collects: the empty sequence of every collected type. -/
@[expose] def collectedNone :
    (collected : List Ty) → Values model.Value (collectedSequences (some 0) collected)
  | [] => .nil
  | _ :: rest => .cons ⟨[], rfl⟩ (collectedNone rest)

/-- The values that one more iteration collects, put before those of the iterations so
far: the collected values are kept latest first while the loop runs. -/
@[expose] def collectedPush {done : Nat} :
    (collected : List Ty) → Values model.Value collected →
      Values model.Value (collectedSequences (some done) collected) →
        Values model.Value (collectedSequences (some (done + 1)) collected)
  | [], _, _ => .nil
  | _ :: rest, values, earlier =>
      .cons ⟨values.get .here :: (earlier.get .here).val,
          congrArg (· + 1) (earlier.get .here).property⟩
        (collectedPush rest values.tail earlier.tail)

/-- The collected values of a finished loop in the order of the iterations, as lists. -/
@[expose] def collectedLists {total : Nat} :
    (collected : List Ty) → Values model.Value (collectedSequences (some total) collected) →
      Values model.Value (collectedSequences none collected)
  | [], _ => .nil
  | _ :: rest, values =>
      .cons (values.get .here).val.reverse (collectedLists rest values.tail)

/-- The collected values of a finished loop in the order of the iterations, at the size
that is the loop's count. -/
@[expose] def collectedSized {total count : Nat} (same : total = count) :
    (collected : List Ty) → Values model.Value (collectedSequences (some total) collected) →
      Values model.Value (collectedSequences (some count) collected)
  | [], _ => .nil
  | _ :: rest, values =>
      .cons ⟨(values.get .here).val.reverse,
          List.length_reverse.trans ((values.get .here).property.trans same)⟩
        (collectedSized same rest values.tail)

/-- Iterations after `done` of them: the step run `remaining` times on the iteration number
and the state. What a step produces gives the next state and is pushed onto what the
earlier iterations collected, which is indexed by their number. It returns the last state
and what all iterations collected; the index is the number of iterations by construction.
A stop of an iteration is the stop of the iterations. -/
@[expose] def iterations {I : PIR.Signature} {State Produced : Type} {Collected : Nat → Type}
    (step : Nat → State → PIR.Process I Produced) (carry : Produced → State)
    (push : (done : Nat) → Produced → Collected done → Collected (done + 1)) :
    (remaining done : Nat) → State → Collected done →
      PIR.Process I (State × Collected (iterationsAfter remaining done))
  | 0, _, state, earlier => .done (state, earlier)
  | remaining + 1, done, state, earlier =>
      (step done state).bind fun produced =>
        iterations step carry push remaining (done + 1) (carry produced)
          (push done produced earlier)

/-- The iterations of a loop after `done` of them: the step run `remaining` times on the
iteration number, threading the carried values. It returns the carried values after the
last iteration and, per collected type, the values of all iterations, the latest first;
their number is the number of iterations by construction. A stop of an iteration is the
stop of the iterations. -/
@[expose, reducible] def loopIterations (carried collected : List Ty)
    (step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))) :
    (remaining done : Nat) → Values model.Value carried →
      Values model.Value (collectedSequences (some done) collected) →
        PIR.Process (Effects model)
          (Values model.Value carried ×
            Values model.Value (collectedSequences (some (iterationsAfter remaining done)) collected)) :=
  iterations step (fun produced => (produced.split collected).2)
    fun _ produced earlier => collectedPush model collected (produced.split collected).1 earlier

/-- One iteration of a loop: its region on the iteration number, the carried values and
the captures. -/
@[expose, reducible] def loopStep (carried collected captures : List Ty)
    (body : RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried))
    (captured : Values model.Value captures) (iteration : Nat)
    (state : Values model.Value carried) :
    PIR.Process (Effects model) (Values model.Value (collected ++ carried)) :=
  body (.cons iteration (state.append captured))

/-- A count is within an optional maximum. -/
@[expose] def withinMaximum (count : Nat) : Option Nat → Bool
  | none => true
  | some maximum => Nat.ble count maximum

/-- `loop` with a count of the operation: the region run once per iteration number below
the count, threading the carried values; the results are the sized sequences of the
collected values and then the carried values. -/
@[expose] def staticLoopProcess (count : Nat) (carried collected captures : List Ty)
    (body : RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried))
    (initial : Values model.Value carried) (captured : Values model.Value captures) :
    PIR.Process (Effects model)
      (Values model.Value (collectedSequences (some count) collected ++ carried)) :=
  (loopIterations model carried collected (loopStep model carried collected captures body captured)
    count 0 initial (collectedNone model collected)).bind fun final =>
      .done ((collectedSized model (iterationsAfter_eq count 0) collected final.2).append
        final.1)

/-- `loop` with a count that is a value: the region run once per iteration number below
the count, threading the carried values; the results are the unsized sequences of the
collected values and then the carried values. A count above the maximum, if there is one, is
outside the domain of the operation: it stops `undefined`, and the check of facts requires that
the count is known to be within the maximum. -/
@[expose] def loopProcess (maximum : Option Nat) (carried collected captures : List Ty)
    (body : RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried))
    (count : Nat) (initial : Values model.Value carried) (captured : Values model.Value captures) :
    PIR.Process (Effects model)
      (Values model.Value (collectedSequences none collected ++ carried)) :=
  cond (withinMaximum count maximum)
    ((loopIterations model carried collected
        (loopStep model carried collected captures body captured) count 0 initial
        (collectedNone model collected)).bind
      fun final => .done ((collectedLists model collected final.2).append final.1))
    (.halt .undefined)

/-- `match`: the region of the alternative that the value is, on its payload and the
captures. A variant without alternatives has no value, so nothing runs. -/
@[expose] def matchProcess (captures outputs : List Ty) :
    (alternatives : List Ty) →
      Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: captures, outputs)) →
      Ty.Variant model.Carrier alternatives → Values model.Value captures →
        PIR.Process (Effects model) (Values model.Value outputs)
  | [], _, value, _ => nomatch value
  | _ :: _, regions, .inl payload, captured => (regions.get .here) (.cons payload captured)
  | _ :: rest, regions, .inr later, captured =>
      matchProcess captures outputs rest regions.tail later captured

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- The meaning of a local operation, given the meanings of the earlier functions. -/
@[expose] def localOperation (table : FunctionTable model functions) :
    (op : LocalOp operations functions deployed) → Values model.Value op.arguments →
      Values (RegionFunction model.Value (Effects model)) op.regions →
        PIR.Process (Effects model) (Values model.Value op.results)
  | .op (kind := kind) row applies => fun arguments _ =>
      rowProcess model (.of row) kind applies arguments
  | .call callee _ => fun arguments _ => table.get callee arguments
  | .conditional .. => fun arguments regions =>
      cond (arguments.get .here) ((regions.get .here) arguments.tail)
        ((regions.get (Var.there .here)) arguments.tail)
  | .match _ alternatives captures outputs => fun arguments regions =>
      matchProcess model captures outputs alternatives regions (arguments.get .here)
        arguments.tail
  | .loop (.static count) carried collected captures => fun arguments regions =>
      staticLoopProcess model count carried collected captures (regions.get .here)
        (arguments.split carried).1 (arguments.split carried).2
  | .loop (.runtime maximum) carried collected captures => fun arguments regions =>
      loopProcess model maximum carried collected captures (regions.get .here)
        (arguments.get .here) (arguments.tail.split carried).1 (arguments.tail.split carried).2
  | .guard reason => fun arguments _ => cond (arguments.get .here) (.done .nil) (.halt reason.stop)
  | .literal value => fun _ _ => .done (.cons (value.value model) .nil)
  | .builtin operation => fun arguments _ => definedProcess model (operation.eval arguments)

@[expose, reducible] def localMeaning (table : FunctionTable model functions) :
    RegionMeaning (LocalDialect operations functions deployed) (Effects model) :=
  ⟨model.Value, localOperation model table⟩

end Local

/-! ## Presence steps

Each step takes the membership of the roles it concerns as `Bool` arguments. -/

/-- `at(r, ℓ)`: the local operation when `r` is present; otherwise nothing. -/
@[expose] def performStep {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs)) :
    (present : Bool) → Values (fun type => Held (model.Value type) present) inputs →
      PIR.Process (Effects model) (Values (fun type => Held (model.Value type) present) outputs)
  | true, arguments => run arguments
  | false, _ => .done (absentValues outputs)

/-- `exchange(s, r, site)` for the memberships of `s` and of `r`. -/
@[expose] def exchangeStep (site : Site) (type : Ty) :
    (sender receiver : Bool) → Held (model.Value type) sender →
      PIR.Process (Effects model) (Held (model.Value type) receiver)
  | true, true, value => .done value
  | true, false, value => .call (.send site type value) fun _ => .done PUnit.unit
  | false, true, _ => .call (.receive site type) fun reply => .done reply
  | false, false, _ => .done PUnit.unit

/-- The owner's part of `draw(o, R, site, law)`: draw when the owner is present,
otherwise continue without a coin. -/
@[expose] def drawStep {α : Type} (site : Site) (law : SamplingRow)
    (onDraw : model.Value law.output → PIR.Process (Effects model) α) :
    (owner : Bool) → Values (fun type => Held (model.Value type) owner) law.inputs →
      (owner = false → PIR.Process (Effects model) α) → PIR.Process (Effects model) α
  | true, inputs, _ => .call (.draw site law inputs) onDraw
  | false, _, onOutside => onOutside rfl

/-- One receiver's announcement from outside the side: its own `receive`. -/
@[expose] def receiveStep (site : Site) (type : Ty) :
    (receiver : Bool) → PIR.Process (Effects model) (Held (model.Value type) receiver)
  | true => .call (.receive site type) fun reply => .done reply
  | false => .done PUnit.unit

/-- `sample(o, site, law)` for the membership of the owner. -/
@[expose] def sampleStep (site : Site) (law : SamplingRow) :
    (owner : Bool) → Values (fun type => Held (model.Value type) owner) law.inputs →
      PIR.Process (Effects model) (Held (model.Value law.output) owner)
  | true, inputs => .call (.sample site law inputs) fun reply => .done reply
  | false, _ => .done PUnit.unit

/-- One public coin held by every role of a list that is in the side. -/
@[expose] def heldCopies (side : Side) (type : Ty) (reply : model.Value type) :
    (roles : List Nat) → Values (SideValue model side) (Located.ofRoles type roles)
  | [] => .nil
  | role :: rest => .cons (Held.of (side role) reply) (heldCopies side type reply rest)

/-- The results of a draw whose owner is in the side: every copy held in the side is
the coin. -/
@[expose] def broadcast (side : Side) (owner : Nat) (receivers : List Nat) (type : Ty)
    (reply : model.Value type) :
    Values (SideValue model side) (⟨type, owner⟩ :: Located.ofRoles type receivers) :=
  .cons (Held.of (side owner) reply) (heldCopies model side type reply receivers)

/-- The announcements of a draw whose owner is outside the side: each receiver in the
side, in order, performs its own `receive` and holds its own reply. -/
@[expose] def receiverReplies (side : Side) (site : Site) (type : Ty) :
    (receivers : List Nat) →
      PIR.Process (Effects model) (Values (SideValue model side) (Located.ofRoles type receivers))
  | [] => .done .nil
  | role :: rest =>
      (receiveStep model site type (side role)).bind fun reply =>
        (receiverReplies side site type rest).bind fun replies => .done (.cons reply replies)

/-- No role of a list is in the side when its first role and the later ones are not. -/
theorem Side.absent_cons {side : Side} {role : Nat} {rest : List Nat}
    (absent : side role = false) (restAbsent : rest.any side = false) :
    (role :: rest).any side = false := by
  simp only [List.any_cons, absent, restAbsent, Bool.or_self]

/-- Two copies of a Boolean control value agree. -/
@[expose] def agreeBool : Bool → Bool → Bool
  | true, true | false, false => true
  | true, false | false, true => false

/-- Continue with `value` when every later copy held in the side equals it. -/
@[expose] def agreeWith {X α : Type} (same : X → X → Bool) (side : Side) (onValue : X → α)
    (onDisagree : α) (value : X) :
    (roles : List Nat) → Values (fun role => Held X (side role)) roles → α
  | [], _ => onValue value
  | role :: rest, values =>
      Held.elim (side role) (values.get .here)
        (fun other => cond (same value other)
          (agreeWith same side onValue onDisagree value rest values.tail) onDisagree)
        fun _ => agreeWith same side onValue onDisagree value rest values.tail

/-- The control value the participants in the side hold: continue with it when all
their copies agree, with `onDisagree` when two differ, and with `onNone` when no
participant is in the side. -/
@[expose] def agreed {X α : Type} (same : X → X → Bool) (side : Side) (onValue : X → α) (onDisagree : α) :
    (roles : List Nat) → Values (fun role => Held X (side role)) roles →
      (roles.any side = false → α) → α
  | [], _, onNone => onNone rfl
  | role :: rest, values, onNone =>
      Held.elim (side role) (values.get .here)
        (fun value => agreeWith same side onValue onDisagree value rest values.tail)
        fun absent => agreed same side onValue onDisagree rest values.tail fun restAbsent =>
          onNone (Side.absent_cons absent restAbsent)

theorem not_held_of_heldBy {side : Side} {participants : List Nat} {located : Located}
    {outputs : List Located} (covered : Located.heldBy participants outputs = true)
    (none : participants.any side = false) (member : located ∈ outputs) :
    side located.holder = false := by
  simp only [Located.heldBy, occursIn, List.all_eq_true, List.any_eq_true] at covered
  obtain ⟨role, inside, same⟩ := covered located member
  simp only [List.any_eq_false] at none
  rw [Nat.eq_of_beq_eq_true same]
  simpa using none _ inside

/-- The unit values of outputs held by roles none of which is in the side. -/
@[expose] def absentOutputs (side : Side) :
    (outputs : List Located) → (∀ located ∈ outputs, side located.holder = false) →
      Values (SideValue model side) outputs
  | [], _ => .nil
  | located :: rest, absent =>
      .cons (Held.absent _ (absent located (List.mem_cons_self ..)))
        (absentOutputs side rest fun other member => absent other (List.mem_cons_of_mem _ member))

/-- The number of the alternative that a value of a variant is. -/
@[expose] def alternativeNumber {Carrier : Nat → Type} :
    (alternatives : List Ty) → Ty.Variant Carrier alternatives → Nat
  | [], value => nomatch value
  | _ :: _, .inl _ => 0
  | _ :: rest, .inr later => alternativeNumber rest later + 1

theorem alternativeNumber_lt {Carrier : Nat → Type} :
    ∀ (alternatives : List Ty) (value : Ty.Variant Carrier alternatives),
      alternativeNumber alternatives value < alternatives.length
  | [], value => nomatch value
  | _ :: _, .inl _ => Nat.zero_lt_succ _
  | _ :: rest, .inr later => Nat.succ_lt_succ (alternativeNumber_lt rest later)

/-- Two copies of the tag of a choice agree: equal conditions, equal arm numbers, or the
same alternative of a variant. The payloads of two copies of a variant are not compared. -/
@[expose] def ChoiceTag.same (Carrier : Nat → Type) :
    (tag : ChoiceTag) → Ty.Value Carrier tag.type → Ty.Value Carrier tag.type → Bool
  | .condition => agreeBool
  | .arm _ => fun first second => Nat.beq first.val second.val
  | .alternative _ alternatives => fun first second =>
      Nat.beq (alternativeNumber alternatives first) (alternativeNumber alternatives second)

/-- What two copies of a tag that agree have in common: they are equal conditions or equal
arm numbers, or the same alternative of a variant. -/
@[expose, reducible] def ChoiceTag.Same (Carrier : Nat → Type) :
    (tag : ChoiceTag) → Ty.Value Carrier tag.type → Ty.Value Carrier tag.type → Prop
  | .condition => fun first second => first = second
  | .arm _ => fun first second => first = second
  | .alternative _ alternatives => fun first second =>
      alternativeNumber alternatives first = alternativeNumber alternatives second

/-- The number of the region that a tag selects. Regions are ordered by tag value: for a
condition the first when it does not hold and the second when it holds, and for a variant
the region of the alternative that the value is. Every tag selects a region. -/
def ChoiceTag.select (Carrier : Nat → Type) :
    (tag : ChoiceTag) → Ty.Value Carrier tag.type → Fin tag.arms
  | .condition => fun condition => (cond condition 1 0 : Fin 2)
  | .arm _ => fun number => number
  | .alternative _ alternatives => fun value =>
      ⟨alternativeNumber alternatives value, alternativeNumber_lt alternatives value⟩

/-- A condition selects the first of its two regions when it does not hold and the second
when it holds. -/
theorem ChoiceTag.select_condition (Carrier : Nat → Type) (condition : Bool) :
    ChoiceTag.select Carrier .condition condition = (cond condition 1 0 : Fin 2) := by
  cases condition <;> rfl

/-- The region with a number among equal regions. -/
@[expose] def selectArm {I : PIR.Signature} {Ty : Type} {Value : Ty → Type}
    (signature : List Ty × List Ty) :
    (count : Nat) → Values (RegionFunction Value I) (List.replicate count signature) →
      Fin count → RegionFunction Value I signature
  | 0, _, number => number.elim0
  | _ + 1, regions, ⟨0, _⟩ => regions.get .here
  | count + 1, regions, ⟨number + 1, below⟩ =>
      selectArm signature count regions.tail ⟨number, Nat.lt_of_succ_lt_succ below⟩

/-- A copy of a variant as its payload of the first alternative: the payload of a holder
in the side whose copy is that alternative, and the unit value of a holder outside the
side. Nothing for a copy that is a later alternative. -/
@[expose] def firstPayload {First Later : Type} :
    (present : Bool) → Held (First ⊕ Later) present → Option (Held First present)
  | true, .inl payload => some payload
  | true, .inr _ => none
  | false, _ => some PUnit.unit

/-- A copy of a variant as a copy of the variant of the later alternatives. Nothing for a
copy that is the first alternative. -/
@[expose] def laterCopy {First Later : Type} :
    (present : Bool) → Held (First ⊕ Later) present → Option (Held Later present)
  | true, .inl _ => none
  | true, .inr later => some later
  | false, _ => some PUnit.unit

/-- One more copy before the copies of the later roles, when both are found. -/
@[expose] def consFound {F : Nat → Type} {role : Nat} {rest : List Nat} :
    Option (F role) → Option (Values F rest) → Option (Values F (role :: rest))
  | some first, some later => some (.cons first later)
  | none, _ => none
  | _, none => none

/-- The payloads of the first alternative of a variant that the roles of a list hold, one
per role and each held by its role, when every copy held in the side is that alternative. -/
@[expose] def firstPayloads (side : Side) (payload : Ty) (rest : List Ty) :
    (roles : List Nat) →
      Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role)) roles →
        Option (Values (fun role => Held (model.Value payload) (side role)) roles)
  | [], _ => some .nil
  | role :: roles, copies =>
      consFound (firstPayload (side role) (copies.get .here))
        (firstPayloads side payload rest roles copies.tail)

/-- The copies of a variant as copies of the variant of its later alternatives, when no
copy held in the side is the first alternative. -/
@[expose] def laterCopies (side : Side) (payload : Ty) (rest : List Ty) :
    (roles : List Nat) →
      Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role)) roles →
        Option (Values (fun role => Held (Ty.Variant model.Carrier rest) (side role)) roles)
  | [], _ => some .nil
  | role :: roles, copies =>
      consFound (laterCopy (side role) (copies.get .here))
        (laterCopies side payload rest roles copies.tail)

/-- The region of the alternative with a number, for a side: it runs on the payload of that
alternative of each participant in the side, then the captures. A copy held in the side
that is another alternative stops the side `incomplete`, as does a number beyond the
alternatives; neither arises for the number of an alternative that the participants in the
side agree on. -/
@[expose] def alternativeProcess (side : Side) (participants : List Nat)
    (captures outputs : List Located) :
    (alternatives : List Ty) →
      Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)) →
      Nat →
      Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role)) participants →
      Values (SideValue model side) captures →
        PIR.Process (Effects model) (Values (SideValue model side) outputs)
  | [], _, _, _, _ => .halt .incomplete
  | payload :: rest, regions, 0, copies, captured =>
      match firstPayloads model side payload rest participants copies with
      | some payloads =>
          (regions.get .here)
            ((remapValues (F := SideValue model side) (fun role => ⟨payload, role⟩) participants
              payloads).append captured)
      | none => .halt .incomplete
  | payload :: rest, regions, number + 1, copies, captured =>
      match laterCopies model side payload rest participants copies with
      | some later =>
          alternativeProcess side participants captures outputs rest regions.tail number later
            captured
      | none => .halt .incomplete

/-- The region of a `choose` that an agreed tag selects, for a side: the region with the
number of a condition or of an arm, on the captures, or the region of the alternative of a
variant, on the payloads of the participants in the side and the captures. -/
@[expose] def chosenRegion (side : Side) (participants : List Nat)
    (captures outputs : List Located) :
    (tag : ChoiceTag) →
      Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants captures outputs) →
      Values (fun role => Held (model.Value tag.type) (side role)) participants →
      Values (SideValue model side) captures → model.Value tag.type →
        PIR.Process (Effects model) (Values (SideValue model side) outputs)
  | .condition, regions, _, captured, value =>
      selectArm (captures, outputs) ChoiceTag.condition.arms regions
        (ChoiceTag.select model.Carrier .condition value) captured
  | .arm count, regions, _, captured, value =>
      selectArm (captures, outputs) (ChoiceTag.arm count).arms regions
        (ChoiceTag.select model.Carrier (.arm count) value) captured
  | .alternative _ alternatives, regions, copies, captured, value =>
      alternativeProcess model side participants captures outputs alternatives regions
        (alternativeNumber alternatives value) copies captured

/-- What no iteration collects for a side: the empty sequence at every holder in the side. -/
@[expose] def sideCollectedNone (side : Side) :
    (collected : List Located) →
      Values (SideValue model side) (collectedSequencesAt (some 0) collected)
  | [] => .nil
  | ⟨_, holder⟩ :: rest =>
      .cons (Held.of (side holder) ⟨[], rfl⟩) (sideCollectedNone side rest)

/-- The values that one more iteration collects for a side, put before those of the
iterations so far at every holder in the side. -/
@[expose] def sideCollectedPush (side : Side) {done : Nat} :
    (collected : List Located) → Values (SideValue model side) collected →
      Values (SideValue model side) (collectedSequencesAt (some done) collected) →
        Values (SideValue model side) (collectedSequencesAt (some (done + 1)) collected)
  | [], _, _ => .nil
  | ⟨type, holder⟩ :: rest, values, earlier =>
      .cons
        (Held.map₂
          (fun (value : model.Value type) (sequence : model.Value (.seq type (some done))) =>
            (⟨value :: sequence.val, congrArg (· + 1) sequence.property⟩ :
              model.Value (.seq type (some (done + 1)))))
          (side holder) (values.get .here) (earlier.get .here))
        (sideCollectedPush side rest values.tail earlier.tail)

/-- The collected values of a finished `repeat` in the order of the iterations, as lists. -/
@[expose] def sideCollectedLists (side : Side) {total : Nat} :
    (collected : List Located) →
      Values (SideValue model side) (collectedSequencesAt (some total) collected) →
        Values (SideValue model side) (collectedSequencesAt none collected)
  | [], _ => .nil
  | ⟨type, holder⟩ :: rest, values =>
      .cons
        (Held.map
          (fun (sequence : model.Value (.seq type (some total))) =>
            (sequence.val.reverse : model.Value (.seq type none)))
          (side holder) (values.get .here))
        (sideCollectedLists side rest values.tail)

/-- The collected values of a finished `repeat` in the order of the iterations, at the size
that is the count. -/
@[expose] def sideCollectedSized (side : Side) {total count : Nat} (same : total = count) :
    (collected : List Located) →
      Values (SideValue model side) (collectedSequencesAt (some total) collected) →
        Values (SideValue model side) (collectedSequencesAt (some count) collected)
  | [], _ => .nil
  | ⟨type, holder⟩ :: rest, values =>
      .cons
        (Held.map
          (fun (sequence : model.Value (.seq type (some total))) =>
            (⟨sequence.val.reverse,
              List.length_reverse.trans (sequence.property.trans same)⟩ :
              model.Value (.seq type (some count))))
          (side holder) (values.get .here))
        (sideCollectedSized side same rest values.tail)

/-- The sequences of collected values none of whose holders is in the side. -/
@[expose] def absentSequences (side : Side) (size : Option Nat) :
    (collected : List Located) → (∀ located ∈ collected, side located.holder = false) →
      Values (SideValue model side) (collectedSequencesAt size collected)
  | [], _ => .nil
  | located :: rest, absent =>
      .cons (Held.absent _ (absent located (List.mem_cons_self ..)))
        (absentSequences side size rest fun other member =>
          absent other (List.mem_cons_of_mem _ member))

/-- The iterations of a `repeat` for a side after `done` of them: the step run `remaining`
times on the iteration number, threading the carried values and keeping, per collected
entry, the values of all iterations at its holder, the latest first. -/
@[expose, reducible] def repeatIterations (side : Side) (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried))) :
    (remaining done : Nat) → Values (SideValue model side) carried →
      Values (SideValue model side) (collectedSequencesAt (some done) collected) →
        PIR.Process (Effects model)
          (Values (SideValue model side) carried ×
            Values (SideValue model side)
              (collectedSequencesAt (some (iterationsAfter remaining done)) collected)) :=
  iterations step (fun produced => (produced.split collected).2)
    fun _ produced earlier =>
      sideCollectedPush model side collected (produced.split collected).1 earlier

/-- `repeat(P, c)` for a side once its count is agreed: the step run once per iteration
number below the count, from 0; the results are the sequences of the collected values and
then the carried values. A count of the operation is the count, and the sequences have its
size; a count that is a value is the agreed one, the sequences are unsized, and a count above
the maximum is outside the domain of the operation: the loop stops `undefined`. -/
@[expose] def repeatProcess (side : Side) (count : RepeatCount)
    (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)))
    (agreed : Nat) (initial : Values (SideValue model side) carried) :
    PIR.Process (Effects model)
      (Values (SideValue model side) (collectedSequencesAt count.size collected ++ carried)) :=
  match count with
  | .static number =>
      (repeatIterations model side carried collected step number 0 initial
          (sideCollectedNone model side collected)).bind fun final =>
        .done ((sideCollectedSized model side (iterationsAfter_eq number 0) collected
          final.2).append final.1)
  | .runtime maximum =>
      if agreed ≤ maximum then
        (repeatIterations model side carried collected step agreed 0 initial
            (sideCollectedNone model side collected)).bind fun final =>
          .done ((sideCollectedLists model side collected final.2).append final.1)
      else .halt .undefined

/-- The loop of one role once its count is known: as the loop of a function, with a maximum
when the count is a value. -/
@[expose] def ownRepeatProcess (count : RepeatCount) (carried collected : List Ty)
    (step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried)))
    (agreed : Nat) (initial : Values model.Value carried) :
    PIR.Process (Effects model)
      (Values model.Value (collectedSequences count.size collected ++ carried)) :=
  match count with
  | .static number =>
      (loopIterations model carried collected step number 0 initial
          (collectedNone model collected)).bind fun final =>
        .done ((collectedSized model (iterationsAfter_eq number 0) collected final.2).append
          final.1)
  | .runtime maximum =>
      if agreed ≤ maximum then
        (loopIterations model carried collected step agreed 0 initial
            (collectedNone model collected)).bind fun final =>
          .done ((collectedLists model collected final.2).append final.1)
      else .halt .undefined

/-- The copies of the count of a `repeat` that the participants hold: its count operands,
or, for a count of the operation, the count itself held by every participant in the side. -/
@[expose] def repeatCopies (side : Side) (participants : List Nat) :
    (count : RepeatCount) → Values (SideValue model side) (count.operands participants) →
      Values (fun role => Held Nat (side role)) participants
  | .static number, _ =>
      unmapValues (F := SideValue model side) (fun role => ⟨.nat, role⟩) participants
        (heldCopies model side .nat number participants)
  | .runtime _, copies =>
      unmapValues (F := SideValue model side) (fun role => ⟨.nat, role⟩) participants copies

/-- `repeat(P, c)` for a side, on the copies of the count that the participants hold: the
participants in the side agree on the count and run the iterations, each holding the
iteration number, and the holders in the side collect; with no participant in the side the
carried values are the operands, and no collected sequence is held in the side. -/
@[expose] def repeatOperation (side : Side) (participants : List Nat) (count : RepeatCount)
    (carried collected captures : List Located)
    (covered : Located.heldBy participants collected = true)
    (region : RegionFunction (SideValue model side) (Effects model)
      (Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried))
    (counts : Values (fun role => Held Nat (side role)) participants)
    (initial : Values (SideValue model side) carried)
    (captured : Values (SideValue model side) captures) :
    PIR.Process (Effects model)
      (Values (SideValue model side) (collectedSequencesAt count.size collected ++ carried)) :=
  agreed Nat.beq side
    (fun agreed => repeatProcess model side count carried collected
      (fun iteration values => region
        ((heldCopies model side .nat iteration participants).append (values.append captured)))
      agreed initial)
    (.halt .incomplete) participants counts fun none =>
      .done ((absentSequences model side count.size collected fun _ member =>
        not_held_of_heldBy covered none member).append initial)

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The meaning of a protocol operation for a side. The site of an effect is the label of
the operation's site number. An applied protocol runs under the path of the application's
site, so its effects report the applications that reached them. -/
@[expose] def labelledOperation (label : Nat → Site) (functionTable : FunctionTable model functions)
    (table : ProtocolTable model protocols) (side : Side) :
    (op : ProtocolOp operations functions protocols deployed) →
      Values (SideValue model side) op.arguments →
      Values (RegionFunction (SideValue model side) (Effects model)) op.regions →
        PIR.Process (Effects model) (Values (SideValue model side) op.results)
  | .at role op bodies => fun arguments _ =>
      (performStep model
        (fun values => localOperation model functionTable op values
          (bodies.denote (localMeaning model functionTable)))
        (side role) (unmapValues _ _ arguments)).bind fun values =>
          .done (remapValues _ _ values)
  | .exchange sender receiver site type => fun arguments _ =>
      (exchangeStep model (label site) type (side sender) (side receiver)
        (arguments.get .here)).bind fun result => .done (.cons result .nil)
  | .draw owner receivers site (output := output) law populated => fun arguments _ =>
      drawStep model (label site) (.of law populated)
        (fun reply => .done (broadcast model side owner receivers output reply))
        (side owner) (unmapValues _ _ arguments) fun absent =>
          (receiverReplies model side (label site) output receivers).bind fun replies =>
            .done (.cons (Held.absent _ absent) replies)
  | .sample owner site law populated => fun arguments _ =>
      (sampleStep model (label site) (.of law populated) (side owner)
        (unmapValues _ _ arguments)).bind fun reply => .done (.cons reply .nil)
  | .repeat participants count carried collected captures covered => fun arguments regions =>
      let parts := arguments.split (count.operands participants)
      repeatOperation model side participants count carried collected captures covered
        (regions.get .here)
        (repeatCopies model side participants count parts.1)
        (parts.2.split carried).1 (parts.2.split carried).2
  | .choose participants tag captures outputs covered => fun arguments regions =>
      let parts := arguments.split (Located.ofRoles tag.type participants)
      let copies := unmapValues (F := SideValue model side) (fun role => ⟨tag.type, role⟩) _ parts.1
      agreed (tag.same model.Carrier) side
        (chosenRegion model side participants captures outputs tag regions copies parts.2)
        (.halt .incomplete) participants copies
        fun none =>
          .done (absentOutputs model side outputs fun _ member =>
            not_held_of_heldBy covered none member)
  | .apply callee roleMap site _ => fun arguments _ =>
      ((table.get callee) (label site).below (Side.preimage roleMap side)
        (unmapValues (F := SideValue model side) (Located.rename roleMap) _ arguments)).bind
        fun values => .done (remapValues (F := SideValue model side) (Located.rename roleMap) _ values)

@[expose, reducible] def labelledMeaning (label : Nat → Site) (functionTable : FunctionTable model functions)
    (table : ProtocolTable model protocols) (side : Side) :
    RegionMeaning (ProtocolDialect operations functions protocols deployed) (Effects model) :=
  ⟨SideValue model side, labelledOperation model label functionTable table side⟩

/-- The meaning of an operation of a definition as written: the site of an effect is the
definition's identity and the operation's site number, under the applications that
reached the definition. -/
@[expose, reducible] def protocolOperation (functionTable : FunctionTable model functions)
    (table : ProtocolTable model protocols) (identity : Nat) (path : List Nat) (side : Side) :
    (op : ProtocolOp operations functions protocols deployed) →
      Values (SideValue model side) op.arguments →
      Values (RegionFunction (SideValue model side) (Effects model)) op.regions →
        PIR.Process (Effects model) (Values (SideValue model side) op.results) :=
  labelledOperation model (ownSites identity path) functionTable table side

@[expose, reducible] def sideMeaning (functionTable : FunctionTable model functions)
    (table : ProtocolTable model protocols) (identity : Nat) (path : List Nat) (side : Side) :
    RegionMeaning (ProtocolDialect operations functions protocols deployed) (Effects model) :=
  labelledMeaning model (ownSites identity path) functionTable table side

end Protocol

/-- The meaning of a function, given the meanings of the earlier ones. -/
@[expose] def FunctionDefinition.meaning {operations : List OperationSignature}
    {functions : List FunctionHeader} (table : FunctionTable model functions)
    {header : FunctionHeader} (definition : FunctionDefinition operations functions header) :
    header.Meaning model :=
  fun arguments => definition.body.denote (localMeaning model table) (Environment.ofValues arguments)

/-- The meaning of a protocol with an identity, given the meanings of the functions and
of the earlier protocols. -/
@[expose] def ProtocolDefinition.meaning {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (functionTable : FunctionTable model functions) (table : ProtocolTable model protocols)
    (identity : Nat) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    header.Meaning model :=
  fun path side arguments =>
    definition.body.denote (sideMeaning model functionTable table identity path side)
      (Environment.ofValues arguments)

/-- The meanings of the functions of a program, most recent first. -/
@[expose] def Functions.table {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → Functions typeTable operations functions →
      FunctionTable model functions
  | _, .nil => .nil
  | _, .snoc earlier definition _ =>
      .cons (definition.meaning model earlier.table) earlier.table
  | _, .opaque (functions := functions) earlier header _ =>
      .cons (fun arguments =>
          partialProcess model
            (model.opaque ⟨functions.length, header.inputs, header.outputs⟩ arguments))
        earlier.table

/-- The identities of the protocols of a program: the identity of the protocol with each
number among the protocols. In a program as written a protocol's identity is its number.
A step that copies or renumbers definitions gives each image the identity of the
definition it comes from. -/
abbrev Identities := Nat → Nat

/-- The identities of a program as written. -/
abbrev Identities.written : Identities := fun number => number

/-- The meanings of the protocols of a program, most recent first. -/
@[expose] def Protocols.table {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} (functionTable : FunctionTable model functions)
    (identities : Identities) :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      ProtocolTable model protocols
  | _, .nil => .nil
  | _, .snoc (protocols := earlierHeaders) earlier definition _ =>
      .cons (definition.meaning model functionTable (earlier.table functionTable identities)
          (identities earlierHeaders.length))
        (earlier.table functionTable identities)

/-- The meaning of every function of a program. -/
@[expose] def Program.functionTable {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (program : Program typeTable operations functions protocols) : FunctionTable model functions :=
  program.functions.table model

/-- The meaning of every protocol of a program. -/
@[expose] def Program.protocolTable {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (program : Program typeTable operations functions protocols) (identities : Identities) :
    ProtocolTable model protocols :=
  program.protocols.table model (program.functionTable model) identities

/-! ## Agreements

An agreement of a protocol's signature names copies of one source value. An honest
execution starts with equal copies; a contract assumes the proposition below of the
inputs of the side it speaks of. -/

/-- The copies of an agreement that the side holds are equal. -/
@[expose] def Agreement.Holds (side : Side) {ports : List Located} (agreement : Agreement ports)
    (values : Values (SideValue model side) ports) : Prop :=
  ∀ first ∈ agreement.copies, ∀ second ∈ agreement.copies,
    ∀ (firstMember : side first.holder = true) (secondMember : side second.holder = true),
      Held.value (side first.holder) firstMember (values.get first.port) =
        Held.value (side second.holder) secondMember (values.get second.port)

/-- For every agreement over a protocol's inputs, the copies that the side holds are
equal. -/
@[expose] def Agreements.InputsHold (side : Side) {inputs outputs : List Located}
    (agreements : Agreements inputs outputs) (values : Values (SideValue model side) inputs) : Prop :=
  ∀ agreement ∈ agreements.inputs, agreement.Holds model side values

end Zkc.Core

