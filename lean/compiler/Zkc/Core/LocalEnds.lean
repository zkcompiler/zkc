module

public import Zkc.Core.RoundTrip
public import Zkc.Core.ThreadPlain

public section

/-! Local code ends: it returns, or stops with a reason that is not `incomplete`.

`incomplete` is the reason of a side whose roles disagree on a control value. Local code has
one role and performs no effect, so its process is a value or a stop, and no construct of
local code names `incomplete`: a row and a built-in operation stop `undefined` outside their
domains, a loop above its maximum stops `undefined`, a guard and a function known by its header
stop with an authored reason, and a `stop` of a well-formed region names an authored reason.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {model : Model}

/-- A process performs nothing and does not stop `incomplete`: it returns, or stops with
another reason. -/
@[expose] def Ends {A : Type} (process : PIR.Process (Effects model) A) : Prop :=
  (∃ value, process = .done value) ∨ ∃ why, why ≠ PIR.Stop.incomplete ∧ process = .halt why

theorem Ends.done {A : Type} (value : A) : Ends (model := model) (PIR.Process.done value) :=
  .inl ⟨value, rfl⟩

theorem Ends.halt {A : Type} {why : PIR.Stop} (other : why ≠ .incomplete) :
    Ends (model := model) (PIR.Process.halt why : PIR.Process (Effects model) A) :=
  .inr ⟨why, other, rfl⟩

theorem Ends.bind {A B : Type} {source : PIR.Process (Effects model) A}
    {next : A → PIR.Process (Effects model) B} (ends : Ends source)
    (continues : ∀ value, Ends (next value)) : Ends (source.bind next) := by
  rcases ends with ⟨value, returned⟩ | ⟨why, other, stopped⟩
  · rw [returned]
    exact continues value
  · rw [stopped]
    exact .inr ⟨why, other, rfl⟩

theorem partialProcess_ends {A : Type} (result : Except Reason A) :
    Ends (partialProcess model result) := by
  cases result with
  | ok value => exact Ends.done value
  | error reason => exact Ends.halt reason.stop_ne_incomplete

theorem definedProcess_ends {A : Type} (result : Option A) :
    Ends (definedProcess model result) := by
  cases result with
  | some value => exact Ends.done value
  | none => exact Ends.halt PIR.Stop.noConfusion

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- Every function of the table ends. -/
@[expose] def EndingTable (table : FunctionTable model functions) : Prop :=
  ∀ {header : FunctionHeader} (callee : Var functions header)
    (arguments : Values model.Value header.inputs), Ends (table.get callee arguments)

/-- Every region function of a list ends. -/
@[expose] def EndingRegions : {signatures : List (List Ty × List Ty)} →
    Values (RegionFunction model.Value (Effects model)) signatures → Prop
  | [], _ => True
  | _ :: _, .cons body rest => (∀ values, Ends (body values)) ∧ EndingRegions rest

theorem rowProcess_ends (row : OperationRow) :
    ∀ (kind : OperationKind)
      (applies : OperationSignature.applies ⟨row.inputs, row.outputs, kind⟩ = true)
      (arguments : Values model.Value row.inputs),
      Ends (rowProcess model row kind applies arguments)
  | .pure, _, _ => Ends.done _
  | .restricted _, _, _ => definedProcess_ends _
  | .sampling, applies, _ => absurd applies Bool.false_ne_true

theorem matchProcess_ends {captures outputs : List Ty} :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: captures, outputs)))
      (value : Ty.Variant model.Carrier alternatives) (captured : Values model.Value captures),
      EndingRegions regions →
        Ends (matchProcess model captures outputs alternatives regions value captured)
  | [], _, value, _, _ => nomatch value
  | _ :: _, .cons _ _, .inl _, _, ending => ending.1 _
  | _ :: rest, .cons _ tail, .inr later, captured, ending =>
      matchProcess_ends rest tail later captured ending.2

theorem loopIterations_ends {carried collected : List Ty}
    {step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))}
    (ends : ∀ iteration state, Ends (step iteration state)) :
    ∀ (remaining done : Nat) (state : Values model.Value carried)
      (earlier : Values model.Value (collectedSequences (some done) collected)),
      Ends (loopIterations model carried collected step remaining done state earlier)
  | 0, _, _, _ => Ends.done _
  | remaining + 1, done, state, _ =>
      Ends.bind (ends done state) fun _ => loopIterations_ends ends remaining (done + 1) _ _

/-- A local operation over functions and regions that end ends. -/
theorem localOperation_ends {table : FunctionTable model functions} (ending : EndingTable table) :
    ∀ (op : LocalOp operations functions deployed) (arguments : Values model.Value op.arguments)
      (regions : Values (RegionFunction model.Value (Effects model)) op.regions),
      EndingRegions regions → Ends (localOperation model table op arguments regions)
  | .op (kind := kind) row applies, arguments, _, _ => by
      show Ends (rowProcess model (.of row) kind applies arguments)
      exact rowProcess_ends (model := model) (OperationRow.of row) kind applies arguments
  | .call callee _, arguments, _, _ => ending callee arguments
  | .conditional .., arguments, .cons onTrue (.cons onFalse .nil), regions => by
      show Ends (cond (arguments.get .here) (onTrue arguments.tail) (onFalse arguments.tail))
      cases arguments.get .here
      · exact regions.2.1 _
      · exact regions.1 _
  | .match _ alternatives captures outputs, arguments, regions, endingRegions =>
      matchProcess_ends alternatives regions (arguments.get .here) arguments.tail endingRegions
  | .loop (.static count) carried collected captures, arguments, .cons body .nil, regions => by
      show Ends (staticLoopProcess model count carried collected captures body _ _)
      exact Ends.bind (loopIterations_ends (fun _ _ => regions.1 _) _ _ _ _) fun _ => Ends.done _
  | .loop (.runtime maximum) carried collected captures, arguments, .cons body .nil, regions => by
      show Ends (loopProcess model maximum carried collected captures body _ _ _)
      unfold loopProcess
      cases withinMaximum _ maximum
      · exact Ends.halt PIR.Stop.noConfusion
      · exact Ends.bind (loopIterations_ends (fun _ _ => regions.1 _) _ _ _ _)
          fun _ => Ends.done _
  | .guard reason, arguments, _, _ => by
      show Ends (cond (arguments.get .here) (PIR.Process.done Values.nil)
        (PIR.Process.halt reason.stop))
      cases arguments.get .here
      · exact Ends.halt reason.stop_ne_incomplete
      · exact Ends.done _
  | .literal _, _, _, _ => Ends.done _
  | .builtin _, _, _, _ => definedProcess_ends _

mutual
  /-- A well-formed local region over functions that end ends. -/
  theorem localRegion_ends {typeTable : TypeTable} {table : FunctionTable model functions}
      (ending : EndingTable table) {Γ out : List Ty} :
      ∀ (region : Region (LocalDialect operations functions deployed) Γ out),
        localRegionViolation typeTable region = none →
          ∀ (env : Environment model.Value Γ), Ends (region.denote (localMeaning model table) env)
    | .ret _, _, _ => Ends.done _
    | .stop reason, clean, _ => by
        refine Ends.halt (authoredStop_ne_incomplete ?_)
        rw [localRegionViolation] at clean
        cases authored : authoredStop reason with
        | true => rfl
        | false =>
            rw [authored] at clean
            cases clean
    | .letOp op arguments bodies next, clean, env => by
        obtain ⟨_, bodiesClean, nextClean⟩ := localRegionViolation_letOp clean
        exact Ends.bind
          (localOperation_ends ending op _ _ (localRegions_end ending bodies bodiesClean))
          fun values => localRegion_ends ending next nextClean _
    | .bind body next, clean, env => by
        obtain ⟨_, bodyClean, nextClean⟩ := localRegionViolation_bind clean
        exact Ends.bind (localRegion_ends ending body bodyClean env)
          fun values => localRegion_ends ending next nextClean _

  theorem localRegions_end {typeTable : TypeTable} {table : FunctionTable model functions}
      (ending : EndingTable table) {signatures : List (List Ty × List Ty)} :
      ∀ (regions : Regions (LocalDialect operations functions deployed) signatures),
        localRegionsViolation typeTable regions = none →
          EndingRegions (regions.denote (localMeaning model table))
    | .nil, _ => trivial
    | .cons body tail, clean => by
        rw [localRegionsViolation] at clean
        obtain ⟨bodyClean, tailClean⟩ := earlierViolation_both clean
        exact ⟨fun values => localRegion_ends ending body bodyClean _,
          localRegions_end ending tail tailClean⟩
end

end Local

/-- The functions of a program end. -/
theorem Functions.table_ends {typeTable : TypeTable} {operations : List OperationSignature} :
    ∀ {functions : List FunctionHeader} (program : Functions typeTable operations functions),
      EndingTable (program.table model)
  | _, .nil => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          Ends (Values.get ((Functions.snoc earlier definition wellFormed).table model) callee
            arguments))
        (fun arguments =>
          localRegion_ends (Functions.table_ends earlier) definition.body
            (FunctionDefinition.violation_none wellFormed).2 _)
        (fun callee => Functions.table_ends earlier callee) callee
  | _, .opaque earlier other named => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          Ends (Values.get ((Functions.opaque earlier other named).table model) callee
            arguments))
        (fun arguments => partialProcess_ends _)
        (fun callee => Functions.table_ends earlier callee) callee

end Zkc.Core
