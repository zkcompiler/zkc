module

public import Zkc.Core.Stops
public import Zkc.Core.Admissible

public section

/-! A function that cannot stop returns.

`Functions.stops` says of each function whether it can stop: whether its body has a guard, a
stop, or a call of a function that can stop. A function of which it
says that it cannot stop either returns or stops `undefined`, on every arguments, in every
model: every other operation of local code returns, or stops `undefined` outside its domain.
An admissible program never stops `undefined`. So a function of an admissible program that
cannot stop returns.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {model : Model}

/-- A process returns, or stops `undefined`. -/
@[expose] def Settles {A : Type} (process : PIR.Process (Effects model) A) : Prop :=
  (∃ value, process = .done value) ∨ process = .halt .undefined

theorem Settles.done {A : Type} (value : A) :
    Settles (model := model) (PIR.Process.done value) := .inl ⟨value, rfl⟩

theorem Settles.bind {A B : Type} {source : PIR.Process (Effects model) A}
    {next : A → PIR.Process (Effects model) B} (settles : Settles source)
    (continues : ∀ value, Settles (next value)) : Settles (source.bind next) := by
  rcases settles with ⟨value, returned⟩ | stopped
  · rw [returned]
    exact continues value
  · rw [stopped]
    exact .inr rfl

/-- A process that returns or stops `undefined`, and never stops `undefined`, returns. -/
theorem Settles.returns {A : Type} {process : PIR.Process (Effects model) A}
    (settles : Settles process) (never : NeverStops .undefined process) :
    ∃ value, process = .done value := by
  rcases settles with returned | stopped
  · exact returned
  · rw [stopped] at never
    exact absurd rfl (NeverStops.halt_iff.mp never)

theorem definedProcess_settles {A : Type} (result : Option A) :
    Settles (definedProcess model result) := by
  cases result with
  | some value => exact .inl ⟨value, rfl⟩
  | none => exact .inr rfl

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

theorem rowProcess_settles (row : OperationRow) :
    ∀ (kind : OperationKind)
      (applies : OperationSignature.applies ⟨row.inputs, row.outputs, kind⟩ = true)
      (arguments : Values model.Value row.inputs),
      Settles (rowProcess model row kind applies arguments)
  | .pure, _, _ => .inl ⟨_, rfl⟩
  | .restricted _, _, _ => definedProcess_settles _
  | .sampling, applies, _ => absurd applies Bool.false_ne_true

/-- Every region function of a list returns or stops `undefined`. -/
@[expose] def SettledRegions : {signatures : List (List Ty × List Ty)} →
    Values (RegionFunction model.Value (Effects model)) signatures → Prop
  | [], _ => True
  | _ :: _, .cons body rest => (∀ values, Settles (body values)) ∧ SettledRegions rest

/-- The functions of a table of which a list says that they cannot stop return or stop
`undefined`. -/
@[expose] def SettledTable (table : FunctionTable model functions) (callees : List Bool) : Prop :=
  ∀ {header : FunctionHeader} (callee : Var functions header),
    callees.getD callee.index true = false →
      ∀ arguments : Values model.Value header.inputs, Settles (table.get callee arguments)

theorem matchProcess_settles {captures outputs : List Ty} :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: captures, outputs)))
      (value : Ty.Variant model.Carrier alternatives) (captured : Values model.Value captures),
      SettledRegions regions →
        Settles (matchProcess model captures outputs alternatives regions value captured)
  | [], _, value, _, _ => nomatch value
  | _ :: _, .cons _ _, .inl _, _, settled => settled.1 _
  | _ :: rest, .cons _ tail, .inr later, captured, settled =>
      matchProcess_settles rest tail later captured settled.2

theorem loopIterations_settles {carried collected : List Ty}
    {step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))}
    (settles : ∀ iteration state, Settles (step iteration state)) :
    ∀ (remaining done : Nat) (state : Values model.Value carried)
      (earlier : Values model.Value (collectedSequences (some done) collected)),
      Settles (loopIterations model carried collected step remaining done state earlier)
  | 0, _, _, _ => .inl ⟨_, rfl⟩
  | remaining + 1, done, state, _ =>
      Settles.bind (settles done state) fun _ =>
        loopIterations_settles settles remaining (done + 1) _ _

/-- A local operation that cannot stop by itself, over regions that return or stop
`undefined`, returns or stops `undefined`. -/
theorem localOperation_settles {table : FunctionTable model functions} {callees : List Bool}
    (settled : SettledTable table callees) :
    ∀ (op : LocalOp operations functions deployed), op.stops callees = false →
      ∀ (arguments : Values model.Value op.arguments)
        (regions : Values (RegionFunction model.Value (Effects model)) op.regions),
        SettledRegions regions → Settles (localOperation model table op arguments regions)
  | .op (kind := kind) row applies, _, arguments, _, _ => by
      show Settles (rowProcess model (.of row) kind applies arguments)
      exact rowProcess_settles (model := model) (OperationRow.of row) kind applies arguments
  | .call callee _, quiet, arguments, _, _ => settled callee quiet arguments
  | .conditional .., _, arguments, .cons onTrue (.cons onFalse .nil), regions => by
      show Settles (cond (arguments.get .here) (onTrue arguments.tail) (onFalse arguments.tail))
      cases arguments.get .here
      · exact regions.2.1 _
      · exact regions.1 _
  | .match _ alternatives captures outputs, _, arguments, regions, settledRegions =>
      matchProcess_settles alternatives regions (arguments.get .here) arguments.tail settledRegions
  | .loop (.static count) carried collected captures, _, arguments, .cons body .nil, regions => by
      show Settles (staticLoopProcess model count carried collected captures body _ _)
      exact Settles.bind (loopIterations_settles (fun _ _ => regions.1 _) _ _ _ _)
        fun _ => .inl ⟨_, rfl⟩
  | .loop (.runtime maximum) carried collected captures, _, arguments, .cons body .nil, regions => by
      show Settles (loopProcess model maximum carried collected captures body _ _ _)
      unfold loopProcess
      cases withinMaximum _ maximum
      · exact .inr rfl
      · exact Settles.bind (loopIterations_settles (fun _ _ => regions.1 _) _ _ _ _)
          fun _ => .inl ⟨_, rfl⟩
  | .guard _, stops, _, _, _ => by cases stops
  | .literal _, _, _, _, _ => .inl ⟨_, rfl⟩
  | .builtin _, _, _, _, _ => definedProcess_settles _

mutual
  /-- A local region that cannot stop returns or stops `undefined`. -/
  theorem localRegion_settles {table : FunctionTable model functions} {callees : List Bool}
      (settled : SettledTable table callees) {Γ out : List Ty} :
      ∀ (region : Region (LocalDialect operations functions deployed) Γ out),
        localRegionStops callees region = false →
          ∀ (env : Environment model.Value Γ),
            Settles (region.denote (localMeaning model table) env)
    | .ret _, _, _ => .inl ⟨_, rfl⟩
    | .stop _, stops, _ => by cases stops
    | .letOp op arguments bodies next, stops, env => by
        have parts : (op.stops callees = false ∧ localRegionsStop callees bodies = false) ∧
            localRegionStops callees next = false := by
          simpa [localRegionStops, Bool.or_eq_false_iff] using stops
        exact Settles.bind
          (localOperation_settles settled op parts.1.1 _ _
            (localRegions_settle settled bodies parts.1.2))
          fun values => localRegion_settles settled next parts.2 _
    | .bind body next, stops, env => by
        have parts : localRegionStops callees body = false ∧
            localRegionStops callees next = false := by
          simpa [localRegionStops, Bool.or_eq_false_iff] using stops
        exact Settles.bind (localRegion_settles settled body parts.1 env)
          fun values => localRegion_settles settled next parts.2 _

  theorem localRegions_settle {table : FunctionTable model functions} {callees : List Bool}
      (settled : SettledTable table callees) {signatures : List (List Ty × List Ty)} :
      ∀ (regions : Regions (LocalDialect operations functions deployed) signatures),
        localRegionsStop callees regions = false →
          SettledRegions (regions.denote (localMeaning model table))
    | .nil, _ => trivial
    | .cons body tail, stops => by
        have parts : localRegionStops callees body = false ∧
            localRegionsStop callees tail = false := by
          simpa [localRegionsStop, Bool.or_eq_false_iff] using stops
        exact ⟨fun values => localRegion_settles settled body parts.1 _,
          localRegions_settle settled tail parts.2⟩
end

end Local

/-- The functions of a program of which `Functions.stops` says that they cannot stop return or
stop `undefined`. -/
theorem Functions.table_settled {typeTable : TypeTable} {operations : List OperationSignature} :
    ∀ {functions : List FunctionHeader} (program : Functions typeTable operations functions),
      SettledTable (program.table model) program.stops
  | _, .nil => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed => by
      intro callee
      exact Var.cases
        (motive := fun header callee =>
          (Functions.snoc earlier definition wellFormed).stops.getD callee.index true = false →
            ∀ arguments : Values model.Value header.inputs,
              Settles (Values.get ((Functions.snoc earlier definition wellFormed).table model)
                callee arguments))
        (fun quiet arguments =>
          localRegion_settles (Functions.table_settled earlier) definition.body quiet _)
        (fun callee quiet => Functions.table_settled earlier callee quiet) callee
  | _, .opaque earlier other named => by
      intro callee
      exact Var.cases
        (motive := fun header callee =>
          (Functions.opaque earlier other named).stops.getD callee.index true = false →
            ∀ arguments : Values model.Value header.inputs,
              Settles (Values.get ((Functions.opaque earlier other named).table model) callee
                arguments))
        (fun quiet => by cases quiet)
        (fun callee quiet => Functions.table_settled earlier callee quiet) callee

/-- A function of an admissible program that cannot stop returns, on every arguments, for
every model that satisfies the domain laws. -/
theorem Program.returns_of_admissible {typeTable : TypeTable}
    {operations : List OperationSignature} {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} (laws : model.DomainLaws operations)
    (program : Program typeTable operations functions protocols)
    (passes : program.admissible = true) {header : FunctionHeader}
    (callee : Var functions header)
    (quiet : program.functions.stops.getD callee.index true = false)
    (arguments : Values model.Value header.inputs) :
    ∃ values, (program.functionTable model).get callee arguments = .done values :=
  (Functions.table_settled program.functions callee quiet arguments).returns
    (Program.never_undefined_of_admissible laws program passes callee arguments)

end Zkc.Core
