module

public import Zkc.Core.VocabularyModel
public import Zkc.Core.ExecuteRuns

@[expose] public section

/-! Running the programs of roles under the model of the vocabulary's rows, with the limit.

`Vocabulary.run` runs a function. Here the executor runs the programs of roles of the newest
protocol of a program: one role alone (`runRole`), as a verifier that reads a proof is run, or
several against each other (`runRoles`). The program is the package's own or one that a step
made of it, with the identities of its definitions.

- **Inputs.** A run takes validated inputs (`Checked`), one per input port of the entry that a
  role of the run holds and none for the others. An input is validated once, at the type of its
  port, and run as often as a caller likes; the bytes of a proof are a validated input
  (`Checked.ofBytes`), so a statement is validated once and the proof varied.
- **Coins.** The source of coins is a parameter (`Execute.Coins`); `seededCoins` is the one of
  a seed, each coin the value of the law of its type. A source that a caller makes is read
  through `validCoins`, so that a coin is validated where it enters a run.
- **The limit.** Every pure row is under a limit on the number of elements of collections that
  one reading of a value builds, `defaultLimit` unless the caller gives one. The executor
  reserves a definition number above the identity of every definition of the program for the
  mark of the limit, and a role whose program reaches the limit ends with the limit
  (`Execute.Outcome.limit`): its program did not return, and it did not stop.

What a run says of the meaning, for the sampler of its source of coins and the role programs of
the meaning under the model of the vocabulary's rows, without a limit:

- a run of one role that returns outputs: the role's program, on the inputs given, returns alone
  with values whose data are those outputs (`runRole_returned`); one that stops: the program
  stops alone with that reason (`runRole_stopped`);
- a run of two roles in which both return: their two programs return together with those
  outputs (`runRoles_together`), without a condition on the run.
-/

set_option autoImplicit false

namespace Zkc.Core.Vocabulary

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-- The role programs that a run runs are the role programs of the meaning under the model of
the vocabulary's rows, cut where a reading reaches the limit: a role that returns or stops in a
run does so in the meaning, and it performs the effects of the meaning. -/
theorem limitedRoles_within (table : Table) (package : Raw.Package) (typed : Typed)
    (limit reserved : Nat) (identities : Identities) {programs : List RoleHeader}
    (roles : RolePrograms (typed.table.map (·.signature)) typed.functions programs) :
    RoleTableWithin
      (roles.limitedTable (model table package) (limitedRows table package limit reserved)
        (typed.program.functions.limitedTable (model table package)
          (limitedRows table package limit reserved)) identities)
      (roles.table (model table package) (typed.program.functionTable (model table package))
        identities) :=
  RolePrograms.limitedTable_within (limitedRows table package limit reserved)
    (Functions.limitedTable_within (limitedRows table package limit reserved)
      typed.program.functions) identities roles

/-- A source of coins that gives only values: a coin that validation does not accept at the
type of its law is no coin, and a run that asks for it fails there. A coin enters a run as an
input does, and a nominal type accepts any datum, so a source that a caller makes is read
through this. -/
def validCoins (table : Table) (package : Raw.Package)
    (coins : Execute.Coins (model table package)) : Execute.Coins (model table package) :=
  fun site occurrence type =>
    (coins site occurrence type).filter fun value =>
      validInput table package.types.toArray type (Execute.datumOf (model table package) rfl type value)

/-- The coins of a seed, for the model of a package: the `k`-th coin of a site is the value of
the law of its type (`lawValue`) made of the numbers of the seed, the site and `k`, with the
order of the group as the bound on the scalar of a point. A type without a law has no coin. -/
def seededCoins (table : Table) (package : Raw.Package) (seed : List Nat) :
    Execute.Coins (model table package) :=
  validCoins table package fun site occurrence type =>
    match lawValueOf table package.types.toArray Concrete.scalarModulus
        (Execute.coinNumbers seed site occurrence) type with
    | .ok datum => Execute.valueOf (model table package) rfl type datum
    | .error _ => none

/-- The data of the inputs of an entry that a role holds, in order: one validated input per
port that the role holds, validated at the type of the port. -/
def ownInputs {table : Table} {package : Raw.Package} (role : Nat) :
    List Located → List (Option (Checked table package)) → Option (List Datum)
  | [], _ => some []
  | port :: ports, inputs =>
    if port.holder == role then
      match inputs with
      | some input :: rest =>
        if input.type = port.type then (ownInputs role ports rest).map (input.datum :: ·)
        else none
      | _ => none
    else ownInputs role ports inputs.tail

section Roles

variable (table : Table) (package : Raw.Package) (typed : Typed) {headers : List ProtocolHeader}
  (protocols : Protocols typed.typeTable (typed.table.map (·.signature)) typed.functions headers)
  (identities : Identities)

/-- The program of a role of the newest protocol under the limit of a run, with the site that
the run reserves for the mark of the limit. -/
def limitedEntry (role limit : Nat) :
    Except String ((header : ProtocolHeader) ×
      RoleHeader.Meaning (model table package) (roleHeader role header)) :=
  Execute.limitedRoleEntry (model table package)
    (limitedRows table package limit (reservedDefinition identities headers.length))
    (typed.program.functions.limitedTable (model table package)
      (limitedRows table package limit (reservedDefinition identities headers.length)))
    identities role protocols

/-- The program of a role of the newest protocol in the meaning under the model of the
vocabulary's rows, without a limit. -/
def wholeEntry (role : Nat) :
    Except String ((header : ProtocolHeader) ×
      RoleHeader.Meaning (model table package) (roleHeader role header)) :=
  Execute.roleEntry (model table package) (typed.program.functionTable (model table package))
    identities role protocols

/-- The program of a role under the limit is its program of the meaning, cut where a reading
reaches the limit. -/
theorem limitedEntry_within (role limit : Nat)
    (result : (header : ProtocolHeader) ×
      RoleHeader.Meaning (model table package) (roleHeader role header))
    (found : limitedEntry table package typed protocols identities role limit = .ok result) :
    ∃ whole, wholeEntry table package typed protocols identities role = .ok ⟨result.1, whole⟩ ∧
      ∀ path arguments, Within (result.2 path arguments) (whole path arguments) :=
  Execute.limitedRoleEntry_within (model table package) _
    (Functions.limitedTable_within _ typed.program.functions) identities role protocols result
    found

/-- Runs the program of one role of the newest protocol of a program of an admitted package
alone, on the validated inputs that the role holds and a source of coins, under the model of
the vocabulary's rows with the limit. A role that reaches the limit ends with the limit. -/
def runRole (role : Nat) (inputs : List (Option (Checked table package)))
    (coins : Execute.Coins (model table package)) (limit : Nat := defaultLimit) :
    Except String (Execute.Outcome (List Datum)) :=
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
          .ok ((Execute.runAlone (model table package) coins (entry.2 [] arguments) (fun _ => 0)
              (some (reservedDefinition identities headers.length))).map
            (Execute.roleData (model table package) rfl (roleHeader role entry.1).outputs))

/-- The process of a role on the inputs given, returning its outputs as data: of the entry
given, the role's program under the limit or its program of the meaning. -/
def roleProcess (role : Nat) (inputs : List (Option (Checked table package)))
    (entry : Except String ((header : ProtocolHeader) ×
      RoleHeader.Meaning (model table package) (roleHeader role header))) :
    Except String (PIR.Process (Effects (model table package)) (List Datum)) :=
  match entry with
  | .error message => .error message
  | .ok entry =>
    match ownInputs role entry.1.inputs inputs with
    | none => .error "an input of the role is not given, or was validated at another type"
    | some data =>
      match Execute.roleValues (model table package) rfl (roleHeader role entry.1).inputs
          data with
      | none => .error "an input is not a value of its port's type"
      | some arguments =>
        .ok ((entry.2 [] arguments).bind fun values =>
          .done (Execute.roleData (model table package) rfl (roleHeader role entry.1).outputs
            values))

/-- How a run of several roles ended: the outcome of each role, in the order given. -/
structure RolesRun where
  outcomes : List (Execute.Outcome (List Datum))

/-- Runs the programs of two or more roles of the newest protocol of a program of an admitted
package against each other, on the validated inputs that they hold and a source of coins, under
the model of the vocabulary's rows with the limit. -/
def runRoles (roles : List Nat) (inputs : List (Option (Checked table package)))
    (coins : Execute.Coins (model table package)) (limit : Nat := defaultLimit) :
    Except String RolesRun :=
  match missing table package with
  | first :: _ => .error first
  | [] =>
    match roles.mapM fun role => roleProcess table package role inputs
        (limitedEntry table package typed protocols identities role limit) with
    | .error message => .error message
    | .ok processes =>
      let final := Execute.run (model table package) coins processes
      .ok { outcomes := final.roles.map
              (Execute.ended (model table package)
                (some (reservedDefinition identities headers.length)) final.shared) }

/-- A run of one role that returns outputs: the program of the role in the meaning under the
model of the vocabulary's rows, without a limit, on the inputs given, returns alone, under the
sampler of the source of coins, values whose data are the outputs. -/
theorem runRole_returned {role : Nat} {inputs : List (Option (Checked table package))}
    {coins : Execute.Coins (model table package)} {limit : Nat} {outputs : List Datum}
    (ran : runRole table package typed protocols identities role inputs coins limit =
      .ok (.returned outputs)) :
    ∃ (header : ProtocolHeader)
      (program : RoleHeader.Meaning (model table package) (roleHeader role header))
      (data : List Datum)
      (arguments : Values (model table package).Value (roleHeader role header).inputs)
      (values : Values (model table package).Value (roleHeader role header).outputs),
      wholeEntry table package typed protocols identities role = .ok ⟨header, program⟩ ∧
        ownInputs role header.inputs inputs = some data ∧
        Execute.roleValues (model table package) rfl (roleHeader role header).inputs data =
          some arguments ∧
        ReturnsAlone coins.sampler (program [] arguments) Asked.start values ∧
        outputs = Execute.roleData (model table package) rfl (roleHeader role header).outputs
          values := by
  unfold runRole at ran
  split at ran
  · cases ran
  · cases found : limitedEntry table package typed protocols identities role limit with
    | error message => simp [found] at ran
    | ok entry =>
      simp only [found] at ran
      cases own : ownInputs role entry.1.inputs inputs with
      | none => simp [own] at ran
      | some data =>
        simp only [own] at ran
        cases read : Execute.roleValues (model table package) rfl
            (roleHeader role entry.1).inputs data with
        | none => simp [read] at ran
        | some arguments =>
          simp only [read, Except.ok.injEq] at ran
          cases alone : Execute.runAlone (model table package) coins (entry.2 [] arguments)
              (fun _ => 0) (some (reservedDefinition identities headers.length)) with
          | returned values =>
            simp only [alone, Execute.Outcome.map, Execute.Outcome.returned.injEq] at ran
            obtain ⟨whole, entryWhole, within⟩ :=
              limitedEntry_within table package typed protocols identities role limit entry found
            exact ⟨entry.1, whole, data, arguments, values, entryWhole, own, read,
              (Execute.runAlone_returned coins _ _ _ _ alone).of_within (within [] arguments),
              ran.symm⟩
          | stopped reason => simp [alone, Execute.Outcome.map] at ran
          | limit elements => simp [alone, Execute.Outcome.map] at ran
          | failed message => simp [alone, Execute.Outcome.map] at ran

/-- A run of one role that stops: the program of the role in the meaning under the model of the
vocabulary's rows, without a limit, on the inputs given, stops alone with that reason, under
the sampler of the source of coins. -/
theorem runRole_stopped {role : Nat} {inputs : List (Option (Checked table package))}
    {coins : Execute.Coins (model table package)} {limit : Nat} {reason : PIR.Stop}
    (ran : runRole table package typed protocols identities role inputs coins limit =
      .ok (.stopped reason)) :
    ∃ (header : ProtocolHeader)
      (program : RoleHeader.Meaning (model table package) (roleHeader role header))
      (data : List Datum)
      (arguments : Values (model table package).Value (roleHeader role header).inputs),
      wholeEntry table package typed protocols identities role = .ok ⟨header, program⟩ ∧
        ownInputs role header.inputs inputs = some data ∧
        Execute.roleValues (model table package) rfl (roleHeader role header).inputs data =
          some arguments ∧
        Execute.StopsAlone coins.sampler (program [] arguments) Asked.start reason := by
  unfold runRole at ran
  split at ran
  · cases ran
  · cases found : limitedEntry table package typed protocols identities role limit with
    | error message => simp [found] at ran
    | ok entry =>
      simp only [found] at ran
      cases own : ownInputs role entry.1.inputs inputs with
      | none => simp [own] at ran
      | some data =>
        simp only [own] at ran
        cases read : Execute.roleValues (model table package) rfl
            (roleHeader role entry.1).inputs data with
        | none => simp [read] at ran
        | some arguments =>
          simp only [read, Except.ok.injEq] at ran
          cases alone : Execute.runAlone (model table package) coins (entry.2 [] arguments)
              (fun _ => 0) (some (reservedDefinition identities headers.length)) with
          | stopped stoppedWith =>
            simp only [alone, Execute.Outcome.map, Execute.Outcome.stopped.injEq] at ran
            subst ran
            obtain ⟨whole, entryWhole, within⟩ :=
              limitedEntry_within table package typed protocols identities role limit entry found
            exact ⟨entry.1, whole, data, arguments, entryWhole, own, read,
              (Execute.runAlone_stopped coins _ _ _ _ alone).of_within (within [] arguments)⟩
          | returned values => simp [alone, Execute.Outcome.map] at ran
          | limit elements => simp [alone, Execute.Outcome.map] at ran
          | failed message => simp [alone, Execute.Outcome.map] at ran

/-- The process of a role under the limit is its process of the meaning, cut where a reading
reaches the limit. -/
theorem roleProcess_within {role limit : Nat} {inputs : List (Option (Checked table package))}
    {limited : PIR.Process (Effects (model table package)) (List Datum)}
    (found : roleProcess table package role inputs
      (limitedEntry table package typed protocols identities role limit) = .ok limited) :
    ∃ whole, roleProcess table package role inputs
        (wholeEntry table package typed protocols identities role) = .ok whole ∧
      Within limited whole := by
  unfold roleProcess at found
  cases entered : limitedEntry table package typed protocols identities role limit with
  | error message => simp [entered] at found
  | ok entry =>
    simp only [entered] at found
    obtain ⟨whole, entryWhole, within⟩ :=
      limitedEntry_within table package typed protocols identities role limit entry entered
    cases own : ownInputs role entry.1.inputs inputs with
    | none => simp [own] at found
    | some data =>
      simp only [own] at found
      cases read : Execute.roleValues (model table package) rfl
          (roleHeader role entry.1).inputs data with
      | none => simp [read] at found
      | some arguments =>
        simp only [read, Except.ok.injEq] at found
        subst found
        refine ⟨_, ?_, Within.bind (within [] arguments) fun _ => Within.refl _⟩
        simp only [roleProcess, entryWhole, own, read]

/-- A run of two roles in which both return: the programs of the two roles in the meaning under
the model of the vocabulary's rows, without a limit, on the inputs given, return together, under
the sampler of the source of coins, the outputs of the run. The run is any run of the executor:
no condition on the order of its effects. -/
theorem runRoles_together {first second : Nat} {inputs : List (Option (Checked table package))}
    {coins : Execute.Coins (model table package)} {limit : Nat} {result : RolesRun}
    {left right : List Datum}
    (ran : runRoles table package typed protocols identities [first, second] inputs coins limit =
      .ok result)
    (returned : result.outcomes = [.returned left, .returned right]) :
    ∃ wholeFirst wholeSecond,
      roleProcess table package first inputs
          (wholeEntry table package typed protocols identities first) = .ok wholeFirst ∧
        roleProcess table package second inputs
          (wholeEntry table package typed protocols identities second) = .ok wholeSecond ∧
        ReturnTogether coins.sampler wholeFirst wholeSecond Mail.empty Board.empty Heard.start
          Heard.start Asked.start left right := by
  unfold runRoles at ran
  split at ran
  · cases ran
  · cases one : roleProcess table package first inputs
        (limitedEntry table package typed protocols identities first limit) with
    | error message => simp [List.mapM_cons, one, bind, Except.bind] at ran
    | ok limitedFirst =>
      cases other : roleProcess table package second inputs
          (limitedEntry table package typed protocols identities second limit) with
      | error message => simp [List.mapM_cons, one, other, bind, Except.bind] at ran
      | ok limitedSecond =>
        simp only [List.mapM_cons, List.mapM_nil, one, other, bind, Except.bind, pure,
          Except.pure, Except.ok.injEq] at ran
        subst ran
        simp only at returned
        obtain ⟨wholeFirst, foundFirst, withinFirst⟩ :=
          roleProcess_within table package typed protocols identities one
        obtain ⟨wholeSecond, foundSecond, withinSecond⟩ :=
          roleProcess_within table package typed protocols identities other
        have done := Execute.ended_returned_all returned
        exact ⟨wholeFirst, wholeSecond, foundFirst, foundSecond,
          (Execute.run_together coins limitedFirst limitedSecond done).of_within
            withinFirst withinSecond⟩

end Roles

/-- Validates data as inputs of the entry of a typed package, each at the type of its port: one
datum per input port, in order. A datum that is not a value of the type of its port is not an
input (`none`), and a role that holds its port does not run. Validate a statement once with
this, and vary the proof. -/
def checkedInputs (table : Table) (package : Raw.Package) (ports : List Located)
    (data : List Datum) : List (Option (Checked table package)) :=
  (ports.zip data).map fun (port, datum) => checked? table package port.type datum

/-- Validates data as the inputs of the newest protocol of an admitted package as it is written
and runs the program of one role alone on them, with the coins of a seed, under the limit. -/
def runEntryRole (table : Table) (package : Raw.Package) (role : Nat) (data : List Datum)
    (seed : List Nat) (limit : Nat := defaultLimit) :
    Except String (Execute.Outcome (List Datum)) :=
  match elaborate package with
  | .error refusal => .error s!"the core refuses the package: {reprStr refusal}"
  | .ok typed =>
    match typed.protocols.head? with
    | none => .error "the program has no protocol"
    | some header =>
      runRole table package typed typed.program.protocols Identities.written role
        (checkedInputs table package header.inputs data) (seededCoins table package seed) limit

/-- Validates data as the inputs of the newest protocol of an admitted package as it is written
and runs the programs of the given roles against each other on them, with the coins of a seed,
under the limit. -/
def runEntry (table : Table) (package : Raw.Package) (roles : List Nat) (data : List Datum)
    (seed : List Nat) (limit : Nat := defaultLimit) : Except String RolesRun :=
  match elaborate package with
  | .error refusal => .error s!"the core refuses the package: {reprStr refusal}"
  | .ok typed =>
    match typed.protocols.head? with
    | none => .error "the program has no protocol"
    | some header =>
      runRoles table package typed typed.program.protocols Identities.written roles
        (checkedInputs table package header.inputs data) (seededCoins table package seed) limit

end Zkc.Core.Vocabulary
