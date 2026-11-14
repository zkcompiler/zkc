module

public import Zkc.Core.Meaning

@[expose] public section

/-! Running a function under a limit on the work of its rows.

The meaning of a program is over a model whose pure rows are total functions: a row that reads
a value from bytes reads as many elements as the bytes ask for. An executor bounds that work.
Rows under a limit (`LimitedRows`) give the value of a pure row, or nothing when computing it
reaches the limit; when they give a value it is the value of the model's row.

A run has then three ends, and the limit is neither of the two that the program has: it is not a
return, and it is not a stop, since no reason of the program names it. The process type has one
more form, a call that waits for a reply, and the meaning gets no constructor for an executor's
concern. A row that reaches the limit becomes the process that waits to receive a value of
`index<0>`, a type with no value, at a site that the executor reserves (`limitReached`): the
site of a definition number that no definition of the program has, with the limit as its
number. No run answers it, every operation after it is behind it, and an executor that finds it
at the head of a process reports the limit (`limitOf?`).

The executor recognises the mark by its site. An effect of a program is at a site of one of its
definitions, whose definition number is the identity of that definition; the executor reserves
a number above every identity of the program it runs. So a program that itself waits to receive
a value of a type with no value waits at a site of its own, and is reported as waiting for a
message that is never sent, not as the limit. A function performs no effect at all.

`Functions.limitedTable` is the table of the meanings of the functions of a program with every
pure row applied under the limit. It is the meaning of the program wherever no row reaches the
limit (`Within`, `Functions.limitedTable_within`): the limited process of a function is the
process of its meaning, cut where a row reaches the limit.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable (model : Model)

/-- The pure rows of a model under a limit: the value of a row, or nothing when computing it
reaches the limit. A value that they give is the value of the model's row. -/
structure LimitedRows where
  /-- The limit, which the end of a run names. -/
  limit : Nat
  /-- The definition number of the site at which a row that reaches the limit waits. The
  executor gives one that no definition of the program it runs has. -/
  reserved : Nat
  pure : (row : OperationRow) → Ty.allPopulated row.outputs = true →
    Values model.Value row.inputs → Option (Values model.Value row.outputs)
  agrees : ∀ (row : OperationRow) (populated : Ty.allPopulated row.outputs = true)
    (arguments : Values model.Value row.inputs) (values : Values model.Value row.outputs),
    pure row populated arguments = some values → values = model.pure row populated arguments

/-- The limit of a run on the number of elements of collections that one reading of a value
builds, when the run is given none: `2 ^ 20`. A value of that many elements is some tens of
megabytes of data, which a run of the executor holds, and the largest collection in a proof of
the fixtures has some hundreds. The limit bounds what a few bytes can ask of the reader, as a
length of `2 ^ 60` elements of no bytes does; it is not a bound on the bytes of a proof, and a
caller with larger values gives a larger one. -/
def defaultLimit : Nat := 2 ^ 20

/-- The site of the mark of a limit: of the definition number that the executor reserves, with
the limit as its number, under no application. -/
def limitSite (reserved limit : Nat) : Site := ⟨[], reserved, limit⟩

/-- The process of a row that reached a limit: it waits to receive a value of `index<0>`, which
has no value, at the site that the executor reserves. -/
def limitReached {α : Type} (reserved limit : Nat) : PIR.Process (Effects model) α :=
  .call (.receive (limitSite reserved limit) (.fin 0)) fun reply => reply.elim0

/-- The limit that a process has reached, when it waits at its head for a value of `index<0>`
at the site that the executor reserved. A wait at any other site is the program's own. -/
def limitOf? {α : Type} (reserved : Nat) : PIR.Process (Effects model) α → Option Nat
  | .call (.receive site (.fin 0)) _ =>
      if site.definition = reserved ∧ site.path = [] then some site.number else none
  | _ => none

theorem limitOf?_limitReached {α : Type} (reserved limit : Nat) :
    limitOf? model reserved
      (limitReached model reserved limit : PIR.Process (Effects model) α) = some limit := by
  simp [limitOf?, limitReached, limitSite]

/-- A wait for a value of `index<0>` at a site of another definition is not the mark. -/
theorem limitOf?_other {α : Type} (reserved : Nat) (site : Site)
    (next : Fin 0 → PIR.Process (Effects model) α) (other : site.definition ≠ reserved) :
    limitOf? model reserved (.call (.receive site (.fin 0)) next) = none := by
  simp [limitOf?, other]

/-- Whatever follows a row that reached a limit is behind it. -/
theorem limitReached_bind {α β : Type} (reserved limit : Nat)
    (next : α → PIR.Process (Effects model) β) :
    (limitReached model reserved limit : PIR.Process (Effects model) α).bind next =
      limitReached model reserved limit := by
  simp only [limitReached, PIR.Process.bind]
  congr 1
  funext reply
  exact reply.elim0

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- The meaning of a local operation with its pure rows under a limit: a pure row gives its
value, or the process of the limit; every other operation is as in the meaning. -/
def limitedOperation (rows : LimitedRows model) (table : FunctionTable model functions) :
    (op : LocalOp operations functions deployed) → Values model.Value op.arguments →
      Values (RegionFunction model.Value (Effects model)) op.regions →
        PIR.Process (Effects model) (Values model.Value op.results)
  | .op (kind := .pure) row applies => fun arguments _ =>
      match rows.pure (.of row) applies arguments with
      | some values => .done values
      | none => limitReached model rows.reserved rows.limit
  | op => localOperation model table op

@[reducible] def limitedMeaning (rows : LimitedRows model) (table : FunctionTable model functions) :
    RegionMeaning (LocalDialect operations functions deployed) (Effects model) :=
  ⟨model.Value, limitedOperation model rows table⟩

end Local

/-- The meanings of the functions of a program with every pure row under a limit, most recent
first. -/
def Functions.limitedTable {typeTable : TypeTable} {operations : List OperationSignature}
    (rows : LimitedRows model) :
    {functions : List FunctionHeader} → Functions typeTable operations functions →
      FunctionTable model functions
  | _, .nil => .nil
  | _, .snoc earlier definition _ =>
      .cons (fun arguments =>
          definition.body.denote (limitedMeaning model rows (earlier.limitedTable rows))
            (Environment.ofValues arguments))
        (earlier.limitedTable rows)
  | _, .opaque (functions := functions) earlier header _ =>
      .cons (fun arguments =>
          partialProcess model
            (model.opaque ⟨functions.length, header.inputs, header.outputs⟩ arguments))
        (earlier.limitedTable rows)

/-! ## The limited process is the process of the meaning, cut at the limit -/

section Within

variable {model}

/-- A process that is another one, cut wherever a row reached a limit: the same return, the
same stop, the same effect with replies that are so related, or the process of a limit in the
place of anything. -/
inductive Within {α : Type} :
    PIR.Process (Effects model) α → PIR.Process (Effects model) α → Prop
  | done (value : α) : Within (.done value) (.done value)
  | halt (reason : PIR.Stop) : Within (.halt reason) (.halt reason)
  | call (effect : (Effects model).Op)
      (limited whole : (Effects model).Reply effect → PIR.Process (Effects model) α) :
      (∀ reply, Within (limited reply) (whole reply)) →
        Within (.call effect limited) (.call effect whole)
  | cut (reserved limit : Nat) (whole : PIR.Process (Effects model) α) :
      Within (limitReached model reserved limit) whole

/-- A process is itself, cut nowhere. -/
theorem Within.refl {α : Type} : ∀ (process : PIR.Process (Effects model) α), Within process process
  | .done value => .done value
  | .halt reason => .halt reason
  | .call effect next => .call effect next next fun reply => Within.refl (next reply)

/-- A cut process and then cut processes is the whole one and then the whole ones, cut. -/
theorem Within.bind {α β : Type} {limited whole : PIR.Process (Effects model) α}
    {limitedNext wholeNext : α → PIR.Process (Effects model) β} (first : Within limited whole)
    (next : ∀ value, Within (limitedNext value) (wholeNext value)) :
    Within (limited.bind limitedNext) (whole.bind wholeNext) := by
  induction first with
  | done value => exact next value
  | halt reason => exact .halt reason
  | call effect limited whole _ hypothesis => exact .call effect _ _ hypothesis
  | cut reserved limit whole =>
    rw [limitReached_bind]
    exact .cut reserved limit _

/-- A cut process that returns: the whole one returns the same values. -/
theorem Within.returned {α : Type} {whole : PIR.Process (Effects model) α} {value : α}
    (within : Within (.done value) whole) : whole = .done value := by
  generalize same : (PIR.Process.done value : PIR.Process (Effects model) α) = limited at within
  cases within with
  | done found => rfl
  | halt reason => cases same
  | call effect limited whole _ => cases same
  | cut reserved limit whole => cases same

/-- A cut process that stops: the whole one stops with the same reason. -/
theorem Within.stopped {α : Type} {whole : PIR.Process (Effects model) α} {reason : PIR.Stop}
    (within : Within (.halt reason) whole) : whole = .halt reason := by
  generalize same : (PIR.Process.halt reason : PIR.Process (Effects model) α) = limited at within
  cases within with
  | done found => cases same
  | halt found => rfl
  | call effect limited whole _ => cases same
  | cut reserved limit whole => cases same

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- Every function of a table is the function of another, cut at the limit. -/
def TableWithin (limited whole : FunctionTable model functions) : Prop :=
  ∀ {header : FunctionHeader} (callee : Var functions header)
    (arguments : Values model.Value header.inputs),
    Within (limited.get callee arguments) (whole.get callee arguments)

/-- Every region function of a list is the region function of another, cut at the limit. -/
def RegionsWithin : {signatures : List (List Ty × List Ty)} →
    Values (RegionFunction model.Value (Effects model)) signatures →
      Values (RegionFunction model.Value (Effects model)) signatures → Prop
  | [], _, _ => True
  | _ :: _, .cons limited limitedRest, .cons whole wholeRest =>
      (∀ values, Within (limited values) (whole values)) ∧ RegionsWithin limitedRest wholeRest

theorem matchProcess_within {captures outputs : List Ty} :
    ∀ (alternatives : List Ty)
      (limited whole : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: captures, outputs)))
      (value : Ty.Variant model.Carrier alternatives) (captured : Values model.Value captures),
      RegionsWithin limited whole →
        Within (matchProcess model captures outputs alternatives limited value captured)
          (matchProcess model captures outputs alternatives whole value captured)
  | [], _, _, value, _, _ => nomatch value
  | _ :: _, .cons _ _, .cons _ _, .inl _, _, within => within.1 _
  | _ :: rest, .cons _ limitedTail, .cons _ wholeTail, .inr later, captured, within =>
      matchProcess_within rest limitedTail wholeTail later captured within.2

theorem loopIterations_within {carried collected : List Ty}
    {limited whole : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))}
    (within : ∀ iteration state, Within (limited iteration state) (whole iteration state)) :
    ∀ (remaining done : Nat) (state : Values model.Value carried)
      (earlier : Values model.Value (collectedSequences (some done) collected)),
      Within (loopIterations model carried collected limited remaining done state earlier)
        (loopIterations model carried collected whole remaining done state earlier)
  | 0, _, state, earlier => .done (state, earlier)
  | remaining + 1, done, state, _ =>
      Within.bind (within done state) fun _ =>
        loopIterations_within within remaining (done + 1) _ _

/-- A local operation under limited rows, over cut functions and cut regions, is the operation
of the meaning, cut. -/
theorem limitedOperation_within (rows : LimitedRows model)
    {limited whole : FunctionTable model functions} (tables : TableWithin limited whole) :
    ∀ (op : LocalOp operations functions deployed) (arguments : Values model.Value op.arguments)
      (limitedRegions wholeRegions :
        Values (RegionFunction model.Value (Effects model)) op.regions),
      RegionsWithin limitedRegions wholeRegions →
        Within (limitedOperation model rows limited op arguments limitedRegions)
          (localOperation model whole op arguments wholeRegions)
  | .op (kind := .pure) row applies, arguments, _, _, _ => by
      show Within
        (match rows.pure (.of row) applies arguments with
          | some values => .done values
          | none => limitReached model rows.reserved rows.limit)
        (.done (model.pure (.of row) applies arguments))
      cases given : rows.pure (.of row) applies arguments with
      | none => exact .cut rows.reserved rows.limit _
      | some values =>
        rw [rows.agrees (.of row) applies arguments values given]
        exact .done _
  | .op (kind := .restricted _) row applies, arguments, _, _, _ => Within.refl _
  | .op (kind := .sampling) row applies, _, _, _, _ => absurd applies Bool.false_ne_true
  | .call callee _, arguments, _, _, _ => tables callee arguments
  | .conditional .., arguments, .cons limitedTrue (.cons limitedFalse .nil),
      .cons wholeTrue (.cons wholeFalse .nil), within => by
      show Within (cond (arguments.get .here) (limitedTrue arguments.tail)
          (limitedFalse arguments.tail))
        (cond (arguments.get .here) (wholeTrue arguments.tail) (wholeFalse arguments.tail))
      cases arguments.get .here
      · exact within.2.1 _
      · exact within.1 _
  | .match _ alternatives captures outputs, arguments, limitedRegions, wholeRegions, within =>
      matchProcess_within alternatives limitedRegions wholeRegions (arguments.get .here)
        arguments.tail within
  | .loop (.static count) carried collected captures, arguments, .cons limitedBody .nil,
      .cons wholeBody .nil, within => by
      show Within (staticLoopProcess model count carried collected captures limitedBody _ _)
        (staticLoopProcess model count carried collected captures wholeBody _ _)
      exact Within.bind (loopIterations_within (fun _ _ => within.1 _) _ _ _ _)
        fun _ => Within.refl _
  | .loop (.runtime maximum) carried collected captures, arguments, .cons limitedBody .nil,
      .cons wholeBody .nil, within => by
      show Within (loopProcess model maximum carried collected captures limitedBody _ _ _)
        (loopProcess model maximum carried collected captures wholeBody _ _ _)
      unfold loopProcess
      cases withinMaximum (arguments.get .here) maximum
      · exact Within.refl _
      · exact Within.bind (loopIterations_within (fun _ _ => within.1 _) _ _ _ _)
          fun _ => Within.refl _
  | .guard reason, arguments, _, _, _ => Within.refl _
  | .literal value, _, _, _, _ => Within.refl _
  | .builtin operation, arguments, _, _, _ => Within.refl _

mutual
  /-- A local region under limited rows, over cut functions, is the region of the meaning,
  cut. -/
  theorem limitedRegion_within (rows : LimitedRows model)
      {limited whole : FunctionTable model functions} (tables : TableWithin limited whole)
      {Γ out : List Ty} :
      ∀ (region : Region (LocalDialect operations functions deployed) Γ out)
        (env : Environment model.Value Γ),
        Within (region.denote (limitedMeaning model rows limited) env)
          (region.denote (localMeaning model whole) env)
    | .ret _, _ => .done _
    | .stop _, _ => .halt _
    | .letOp op _ bodies next, _ =>
        Within.bind
          (limitedOperation_within rows tables op _ _ _ (limitedRegions_within rows tables bodies))
          fun _ => limitedRegion_within rows tables next _
    | .bind body next, env =>
        Within.bind (limitedRegion_within rows tables body env)
          fun _ => limitedRegion_within rows tables next _

  theorem limitedRegions_within (rows : LimitedRows model)
      {limited whole : FunctionTable model functions} (tables : TableWithin limited whole)
      {signatures : List (List Ty × List Ty)} :
      ∀ (regions : Regions (LocalDialect operations functions deployed) signatures),
        RegionsWithin (regions.denote (limitedMeaning model rows limited))
          (regions.denote (localMeaning model whole))
    | .nil => trivial
    | .cons body tail =>
        ⟨fun _ => limitedRegion_within rows tables body _,
          limitedRegions_within rows tables tail⟩
end

/-- The functions of a program under limited rows are its functions, cut at the limit: a
limited function that returns or stops does what the meaning does. -/
theorem Functions.limitedTable_within {typeTable : TypeTable} (rows : LimitedRows model) :
    ∀ {functions : List FunctionHeader} (program : Functions typeTable operations functions),
      TableWithin (program.limitedTable model rows) (program.table model)
  | _, .nil => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          Within (α := Values model.Value header.outputs)
            (Values.get ((Functions.snoc earlier definition wellFormed).limitedTable model rows)
              callee arguments)
            (Values.get ((Functions.snoc earlier definition wellFormed).table model) callee
              arguments))
        (fun arguments =>
          limitedRegion_within rows (Functions.limitedTable_within rows earlier) definition.body _)
        (fun callee => Functions.limitedTable_within rows earlier callee) callee
  | _, .opaque earlier other named => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          Within (α := Values model.Value header.outputs)
            (Values.get ((Functions.opaque earlier other named).limitedTable model rows) callee
              arguments)
            (Values.get ((Functions.opaque earlier other named).table model) callee arguments))
        (fun arguments => Within.refl _)
        (fun callee => Functions.limitedTable_within rows earlier callee) callee

end Within

end Zkc.Core
