module

public import Zkc.Core.DecodingLimit
public import Zkc.Core.ProjectProgramMeaning

@[expose] public section

/-! The programs of roles with their pure rows under a limit.

A verifier reads a proof in the program of its role: the rows that take values from the reader
are local operations of that program. `RolePrograms.limitedTable` is the table of the meanings
of the role programs with every pure row applied under the limit, as
`Functions.limitedTable` is for functions: the local operations of a role and the functions
they call are under the limit, and every effect, loop, choice and call of a role program is as
in the meaning. A row that reaches the limit becomes the process of the limit, at the site that
the executor reserves.

The limited program of a role is the program of the meaning, cut where a row reaches the limit
(`RolePrograms.limitedTable_within`): it performs the same effects with the same replies, and
where it returns or stops the meaning does the same.

The executor reserves a definition number above the identity of every definition of the
program (`reservedDefinition`, `identity_lt_reservedDefinition`). The program of a role performs
its effects at the sites of its own protocol and of the protocols it calls, whose definition
numbers are those identities (`RolePrograms.table`: `ownSites (identities definition) path`), so
no effect of the program is at the reserved site.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- A definition number above the identity of every one of the first `count` definitions of a
program: the definition of the site that an executor reserves for the mark of the limit. -/
def reservedDefinition (identities : Identities) : Nat → Nat
  | 0 => 0
  | count + 1 => max (reservedDefinition identities count) (identities count + 1)

/-- The identity of a definition of the program is below the reserved number. -/
theorem identity_lt_reservedDefinition (identities : Identities) :
    ∀ (count number : Nat), number < count →
      identities number < reservedDefinition identities count
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | count + 1, number, below => by
    simp only [reservedDefinition]
    by_cases last : number = count
    · subst last
      omega
    · have earlier := identity_lt_reservedDefinition identities count number (by omega)
      omega

variable (model : Model)

section Role

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {programs : List RoleHeader} {deployed : Bool}

/-- The meaning of a role operation with its pure rows under a limit: a local computation of the
role is under the limit, with its regions; every other operation is as in the meaning. -/
def limitedRoleOperation (rows : LimitedRows model) (table : FunctionTable model functions)
    (called : RoleTable model programs) (label : Nat → Site) :
    (op : RoleOp operations functions programs deployed) → Values model.Value op.arguments →
      Values (RegionFunction model.Value (Effects model)) op.regions →
        PIR.Process (Effects model) (Values model.Value op.results)
  | .perform op bodies => fun arguments _ =>
      limitedOperation model rows table op arguments
        (bodies.denote (limitedMeaning model rows table))
  | op => roleOperation model table called label op

@[reducible] def limitedRoleMeaning (rows : LimitedRows model)
    (table : FunctionTable model functions) (called : RoleTable model programs)
    (label : Nat → Site) :
    RegionMeaning (RoleDialect operations functions programs deployed) (Effects model) :=
  ⟨model.Value, limitedRoleOperation model rows table called label⟩

end Role

/-- The meanings of the role programs with every pure row under a limit, most recent first,
over functions that are under the limit. -/
def RolePrograms.limitedTable {operations : List OperationSignature}
    {functions : List FunctionHeader} (rows : LimitedRows model)
    (functionTable : FunctionTable model functions) (identities : Identities) :
    {programs : List RoleHeader} → RolePrograms operations functions programs →
      RoleTable model programs
  | _, .nil => .nil
  | _, .snoc earlier definition _ program =>
      .cons
        (fun path arguments =>
          program.body.denote
            (limitedRoleMeaning model rows functionTable
              (earlier.limitedTable rows functionTable identities)
              (ownSites (identities definition) path))
            (Environment.ofValues arguments))
        (earlier.limitedTable rows functionTable identities)

/-! ## The limited program of a role is its program, cut at the limit -/

section Within

variable {model}
variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {programs : List RoleHeader} {deployed : Bool}

/-- Every role program of a table is the program of another, cut at the limit. -/
def RoleTableWithin (limited whole : RoleTable model programs) : Prop :=
  ∀ {header : RoleHeader} (program : Var programs header) (path : List Nat)
    (arguments : Values model.Value header.inputs),
    Within (limited.get program path arguments) (whole.get program path arguments)

theorem selectArm_within (signature : List Ty × List Ty) :
    ∀ (count : Nat)
      (limited whole : Values (RegionFunction model.Value (Effects model))
        (List.replicate count signature))
      (number : Fin count), RegionsWithin limited whole →
        ∀ values, Within (selectArm signature count limited number values)
          (selectArm signature count whole number values)
  | 0, _, _, number, _ => number.elim0
  | _ + 1, .cons _ _, .cons _ _, ⟨0, _⟩, within => within.1
  | count + 1, .cons _ limitedTail, .cons _ wholeTail, ⟨number + 1, below⟩, within =>
      selectArm_within signature count limitedTail wholeTail
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ within.2

theorem ownChosenRegion_within (captures outputs : List Ty) :
    ∀ (tag : ChoiceTag)
      (limited whole : Values (RegionFunction model.Value (Effects model))
        (tag.ownRegions captures outputs))
      (value : model.Value tag.type) (captured : Values model.Value captures),
      RegionsWithin limited whole →
        Within (ownChosenRegion model captures outputs tag limited value captured)
          (ownChosenRegion model captures outputs tag whole value captured)
  | .condition, limited, whole, value, captured, within =>
      selectArm_within (captures, outputs) ChoiceTag.condition.arms limited whole
        (ChoiceTag.select model.Carrier .condition value) within captured
  | .arm count, limited, whole, value, captured, within =>
      selectArm_within (captures, outputs) (ChoiceTag.arm count).arms limited whole
        (ChoiceTag.select model.Carrier (.arm count) value) within captured
  | .alternative _ alternatives, limited, whole, value, captured, within =>
      matchProcess_within alternatives limited whole value captured within

theorem ownRepeatProcess_within (count : RepeatCount) (carried collected : List Ty)
    {limited whole : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))}
    (within : ∀ iteration state, Within (limited iteration state) (whole iteration state))
    (agreed : Nat) (initial : Values model.Value carried) :
    Within (ownRepeatProcess model count carried collected limited agreed initial)
      (ownRepeatProcess model count carried collected whole agreed initial) := by
  cases count with
  | «static» number =>
    exact Within.bind (loopIterations_within within _ _ _ _) fun _ => Within.refl _
  | runtime maximum =>
    simp only [ownRepeatProcess]
    by_cases fits : agreed ≤ maximum
    · simp only [fits, ↓reduceIte]
      exact Within.bind (loopIterations_within within _ _ _ _) fun _ => Within.refl _
    · simp only [fits, ↓reduceIte]
      exact Within.refl _

/-- A role operation under limited rows, over cut functions, cut role programs and cut regions,
is the operation of the meaning, cut. -/
theorem limitedRoleOperation_within (rows : LimitedRows model)
    {limitedFunctions wholeFunctions : FunctionTable model functions}
    (functionsWithin : TableWithin limitedFunctions wholeFunctions)
    {limitedCalled wholeCalled : RoleTable model programs}
    (calledWithin : RoleTableWithin limitedCalled wholeCalled) (label : Nat → Site) :
    ∀ (op : RoleOp operations functions programs deployed)
      (arguments : Values model.Value op.arguments)
      (limitedRegions wholeRegions :
        Values (RegionFunction model.Value (Effects model)) op.regions),
      RegionsWithin limitedRegions wholeRegions →
        Within
          (limitedRoleOperation model rows limitedFunctions limitedCalled label op arguments
            limitedRegions)
          (roleOperation model wholeFunctions wholeCalled label op arguments wholeRegions)
  | .perform op bodies, arguments, _, _, _ =>
      limitedOperation_within rows functionsWithin op arguments _ _
        (limitedRegions_within rows functionsWithin bodies)
  | .send _ _, _, _, _, _ => Within.refl _
  | .receive _ _, _, _, _, _ => Within.refl _
  | .draw _ _ _, _, _, _, _ => Within.refl _
  | .sample _ _ _, _, _, _, _ => Within.refl _
  | .repeat count carried collected _, _, .cons _ .nil, .cons _ .nil, within =>
      ownRepeatProcess_within count carried collected (fun _ _ => within.1 _) _ _
  | .choose tag captures outputs, arguments, limitedRegions, wholeRegions, within =>
      ownChosenRegion_within captures outputs tag limitedRegions wholeRegions
        (arguments.get .here) arguments.tail within
  | .call site callee, arguments, _, _, _ => calledWithin callee (label site).below arguments

mutual
  /-- A role region under limited rows is the region of the meaning, cut. -/
  theorem limitedRoleRegion_within (rows : LimitedRows model)
      {limitedFunctions wholeFunctions : FunctionTable model functions}
      (functionsWithin : TableWithin limitedFunctions wholeFunctions)
      {limitedCalled wholeCalled : RoleTable model programs}
      (calledWithin : RoleTableWithin limitedCalled wholeCalled) (label : Nat → Site)
      {Γ out : List Ty} :
      ∀ (region : Region (RoleDialect operations functions programs deployed) Γ out)
        (env : Environment model.Value Γ),
        Within
          (region.denote (limitedRoleMeaning model rows limitedFunctions limitedCalled label) env)
          (region.denote (roleMeaning model wholeFunctions wholeCalled label) env)
    | .ret _, _ => .done _
    | .stop _, _ => .halt _
    | .letOp op _ bodies next, _ =>
        Within.bind
          (limitedRoleOperation_within rows functionsWithin calledWithin label op _ _ _
            (limitedRoleRegions_within rows functionsWithin calledWithin label bodies))
          fun _ => limitedRoleRegion_within rows functionsWithin calledWithin label next _
    | .bind body next, env =>
        Within.bind (limitedRoleRegion_within rows functionsWithin calledWithin label body env)
          fun _ => limitedRoleRegion_within rows functionsWithin calledWithin label next _

  theorem limitedRoleRegions_within (rows : LimitedRows model)
      {limitedFunctions wholeFunctions : FunctionTable model functions}
      (functionsWithin : TableWithin limitedFunctions wholeFunctions)
      {limitedCalled wholeCalled : RoleTable model programs}
      (calledWithin : RoleTableWithin limitedCalled wholeCalled) (label : Nat → Site)
      {signatures : List (List Ty × List Ty)} :
      ∀ (regions : Regions (RoleDialect operations functions programs deployed) signatures),
        RegionsWithin
          (regions.denote (limitedRoleMeaning model rows limitedFunctions limitedCalled label))
          (regions.denote (roleMeaning model wholeFunctions wholeCalled label))
    | .nil => trivial
    | .cons body tail =>
        ⟨fun _ => limitedRoleRegion_within rows functionsWithin calledWithin label body _,
          limitedRoleRegions_within rows functionsWithin calledWithin label tail⟩
end

/-- The role programs under limited rows, over functions that are the functions of the meaning
cut at the limit, are the role programs of the meaning, cut at the limit: a limited program of a
role that returns or stops does what the meaning does, and it performs the effects of the
meaning with their replies. -/
theorem RolePrograms.limitedTable_within (rows : LimitedRows model)
    {limitedFunctions wholeFunctions : FunctionTable model functions}
    (functionsWithin : TableWithin limitedFunctions wholeFunctions) (identities : Identities) :
    ∀ {programs : List RoleHeader} (roles : RolePrograms operations functions programs),
      RoleTableWithin (roles.limitedTable model rows limitedFunctions identities)
        (roles.table model wholeFunctions identities)
  | _, .nil => fun program => program.elimNil
  | _, .snoc earlier definition role program => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ (path : List Nat)
          (arguments : Values model.Value header.inputs),
          Within (α := Values model.Value header.outputs)
            (Values.get ((RolePrograms.snoc earlier definition role program).limitedTable model
              rows limitedFunctions identities) callee path arguments)
            (Values.get ((RolePrograms.snoc earlier definition role program).table model
              wholeFunctions identities) callee path arguments))
        (fun path _ =>
          limitedRoleRegion_within rows functionsWithin
            (RolePrograms.limitedTable_within rows functionsWithin identities earlier)
            (ownSites (identities definition) path) program.body _)
        (fun callee => RolePrograms.limitedTable_within rows functionsWithin identities earlier
          callee) callee

end Within

end Zkc.Core
