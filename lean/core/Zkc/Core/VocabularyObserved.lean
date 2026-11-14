module

public import Zkc.Core.VocabularyExecute
public import Zkc.Core.Observed

@[expose] public section

/-! Runs with what each role did, as data.

`Execute.observeRoles` and `Execute.observeRole` run processes that return data, of any model
whose carrier is the concrete one, and give how each ended and what each did: what it sent,
received, heard, drew and sampled, in the order in which it did so. A comparison of runs under
any model reads them.

Under the model of the vocabulary's rows, `runRolesObserved` and `runRoleObserved` are
`Vocabulary.runRoles` and `Vocabulary.runRole` with what each role did. Their ends are the ends
of those runs (`runRolesObserved_outcomes`, `runRoleObserved_outcome`), so what is proved of a
run that returns or stops is proved of the observed run.
-/

set_option autoImplicit false

namespace Zkc.Core.Execute

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-- What a role of a run did in one move, as data. -/
structure Did where
  kind : Event.Kind
  site : Site
  value : Datum
  deriving Inhabited

/-- How a run of several roles ended, and what each did. -/
structure ObservedRoles where
  outcomes : List (Outcome (List Datum))
  /-- For each role, in the order given: what it did, in the order in which it did so. -/
  did : List (List Did)

section Model

variable (model : Model) (carrier : model.Carrier = Concrete.Carrier)

/-- An event of a run, as data. -/
def Did.ofEvent (event : Event model) : Did :=
  ⟨event.kind, event.site, datumOf model carrier event.type event.value⟩

/-- Processes that return data run against each other: how each ended, with the limit when the
run reserved a site for its mark, and what each did. -/
def observeRoles (coins : Coins model) (processes : List (PIR.Process (Effects model) (List Datum)))
    (reserved : Option Nat) : ObservedRoles :=
  let observed := runObserved model coins processes
  { outcomes := observed.1.roles.map (ended model reserved observed.1.shared)
    did := (List.range processes.length).map fun index =>
      (observed.2.toList.filter (·.1 == index)).map fun (_, event) =>
        Did.ofEvent model carrier event }

/-- The roles of the observed run end as the roles of the run. -/
theorem observeRoles_outcomes (coins : Coins model)
    (processes : List (PIR.Process (Effects model) (List Datum))) (reserved : Option Nat) :
    (observeRoles model carrier coins processes reserved).outcomes =
      (run model coins processes).roles.map
        (ended model reserved (run model coins processes).shared) := by
  simp only [observeRoles, runObserved_fst]

/-- One process alone: how it ended, and its draws and its samples. -/
def observeRole {α : Type} (coins : Coins model) (process : PIR.Process (Effects model) α)
    (reserved : Option Nat) : Outcome α × List Did :=
  let observed := observeAlone model coins process (fun _ => 0) reserved
  (observed.1, observed.2.toList.map (Did.ofEvent model carrier))

end Model

end Zkc.Core.Execute

namespace Zkc.Core.Vocabulary

open Zkc.Source
open Zkc.Core.Concrete (Datum)
open Execute (Did ObservedRoles)

section Roles

variable (table : Table) (package : Raw.Package) (typed : Typed) {headers : List ProtocolHeader}
  (protocols : Protocols typed.typeTable (typed.table.map (·.signature)) typed.functions headers)
  (identities : Identities)

/-- `runRoles`, with what each role did. -/
def runRolesObserved (roles : List Nat) (inputs : List (Option (Checked table package)))
    (coins : Execute.Coins (model table package)) (limit : Nat := defaultLimit) :
    Except String ObservedRoles :=
  match missing table package with
  | first :: _ => .error first
  | [] =>
    match roles.mapM fun role => roleProcess table package role inputs
        (limitedEntry table package typed protocols identities role limit) with
    | .error message => .error message
    | .ok processes =>
      .ok (Execute.observeRoles (model table package) rfl coins processes
        (some (reservedDefinition identities headers.length)))

/-- The roles of the observed run end as the roles of the run. -/
theorem runRolesObserved_outcomes (roles : List Nat)
    (inputs : List (Option (Checked table package))) (coins : Execute.Coins (model table package))
    (limit : Nat) :
    (runRolesObserved table package typed protocols identities roles inputs coins limit).map
        (·.outcomes) =
      (runRoles table package typed protocols identities roles inputs coins limit).map
        (·.outcomes) := by
  unfold runRolesObserved runRoles
  cases missing table package with
  | cons first rest => rfl
  | nil =>
    simp only
    cases roles.mapM fun role => roleProcess table package role inputs
        (limitedEntry table package typed protocols identities role limit) with
    | error message => rfl
    | ok processes =>
      exact congrArg Except.ok (Execute.observeRoles_outcomes (model table package) rfl coins
        processes _)

/-- `runRole`, with the draws and the samples of the role. -/
def runRoleObserved (role : Nat) (inputs : List (Option (Checked table package)))
    (coins : Execute.Coins (model table package)) (limit : Nat := defaultLimit) :
    Except String (Execute.Outcome (List Datum) × List Did) :=
  match missing table package with
  | first :: _ => .error first
  | [] =>
    match limitedEntry table package typed protocols identities role limit with
    | .error message => .error message
    | .ok entry =>
      match ownInputs role entry.1.inputs inputs with
      | none => .error "an input of the role is not given, or was validated at another type"
      | some data =>
        match Execute.roleValues (model table package) rfl (roleHeader role entry.1).inputs
            data with
        | none => .error "an input is not a value of its port's type"
        | some arguments =>
          let observed := Execute.observeRole (model table package) rfl coins
            (entry.2 [] arguments) (some (reservedDefinition identities headers.length))
          .ok (observed.1.map
              (Execute.roleData (model table package) rfl (roleHeader role entry.1).outputs),
            observed.2)

/-- The observed run of one role ends as its run. -/
theorem runRoleObserved_outcome (role : Nat) (inputs : List (Option (Checked table package)))
    (coins : Execute.Coins (model table package)) (limit : Nat) :
    (runRoleObserved table package typed protocols identities role inputs coins limit).map (·.1) =
      runRole table package typed protocols identities role inputs coins limit := by
  unfold runRoleObserved runRole
  cases missing table package with
  | cons first rest => rfl
  | nil =>
    simp only
    cases limitedEntry table package typed protocols identities role limit with
    | error message => rfl
    | ok entry =>
      simp only
      cases ownInputs role entry.1.inputs inputs with
      | none => rfl
      | some data =>
        simp only
        cases Execute.roleValues (model table package) rfl (roleHeader role entry.1).inputs
            data with
        | none => rfl
        | some arguments => simp only [Except.map, Execute.observeRole, Execute.observeAlone_fst]

end Roles

end Zkc.Core.Vocabulary
