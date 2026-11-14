import Zkc.Tests.Core.Declare
import Zkc.Core.LegalStep

/-! The refusals of a threading step: what the kernel finds, and witnesses of what the
theorems of `Core/LegalStep.lean` assume.

- **A declared role beyond the roles of the entry.** Both steps refuse the declaration
  with `entry`, a refusal of the construction item, before any definition is rewritten;
  so does a declaration that names one role as prover and verifier. Neither step reaches
  an internal refusal on it.
- **The hypotheses of `threadRegion_returns` and `stepProtocols_returns_or_residual`.**
  `Rule.External` holds of the two rules
  and fails for a rule that refuses `image` at an exchange. `served` is `true` for the
  entry of `sumcheck` among the images that the Fiat–Shamir step makes of its callee when
  the callee is reached as the entry applies it, and `false` among the images of a callee
  that is not reached. A region with a `stop` is not legal; the body of a well-formed
  definition is. `ConstructionAccepts` and `RowsPresent` hold of a result and fail for a
  refusal of their kind.
- **The hypotheses of `stepProtocols_returns`.** `Rule.Legal` holds of the two rules over
  tables whose types are types of the package (`RowsNamed`, `FunctionsNamed`), which the
  tables of a typed package are and a table with a row of another type is not. It fails
  for a rule that has a role that the definition does not have write a literal after every
  exchange, and for one that writes a literal of a type that the package does not have:
  the kernel shows the step of each refused with `residual`, on the result of the
  Fiat–Shamir step of the fixture, where the same rule with a role of the entry and a
  literal of a type of the package returns. `EntriesBelow` holds of demands without an
  entry and fails for an entry with a role that the protocol does not have.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace StepRefusals

/-! ## A declared role beyond the roles of the entry -/

raw_package raw from file "fixtures/construction/schnorr.json"
raw_declaration declaration from file "fixtures/construction/schnorr.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

/-- The declaration with another verifier. -/
noncomputable abbrev withVerifier (verifier : Nat) : Raw.Declaration :=
  { declaration with verifier := verifier, online := [declaration.prover, verifier] }

/-- The serialize step, with a declaration, on the result of the Fiat–Shamir step with the
declaration of the fixture. -/
noncomputable def serializedWith (other : Raw.Declaration) :
    Except StepRefusal (Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :=
  match fiatShamir typed declaration with
  | .ok constructed => serializeProtocols other constructed.identities constructed.protocols
  | .error refusal => .error refusal

/-- The refusal of a step, if it refuses. -/
def refusalOf {α : Type} : Except StepRefusal α → Option StepRefusal
  | .ok _ => none
  | .error refusal => some refusal

-- The entry has the roles 0 and 1, and the fixture declares them: both steps return.
kernel_refl declared_roles : (raw.protocols.map (·.roles), declaration.prover, declaration.verifier)
  equals ([2], 0, 1)
kernel_refl fiatShamir_returns : refusalOf (fiatShamir typed declaration) equals none
kernel_refl serialize_returns : refusalOf (serializedWith declaration) equals none

-- A verifier that the entry does not have: each step refuses the declaration.
kernel_refl fiatShamir_beyond : refusalOf (fiatShamir typed (withVerifier 2)) equals
  some StepRefusal.entry
kernel_refl serialize_beyond : refusalOf (serializedWith (withVerifier 2)) equals
  some StepRefusal.entry

-- One role as prover and verifier.
kernel_refl fiatShamir_same : refusalOf (fiatShamir typed (withVerifier 0)) equals
  some StepRefusal.entry
kernel_refl serialize_same : refusalOf (serializedWith (withVerifier 0)) equals
  some StepRefusal.entry

/-- The refusal is of the construction item, not internal. -/
theorem entry_construction :
    StepRefusal.entry.construction = true ∧ StepRefusal.entry.internal = false := ⟨rfl, rfl⟩

#print axioms fiatShamir_beyond
#print axioms serialize_beyond

/-! ## The hypotheses of the theorems about refusals -/

section Witnesses

variable {operations : List OperationSignature} {functions : List FunctionHeader}

/-- The two rules never refuse internally. -/
example (suite : Suite operations functions) : (fiatShamirRule suite).External :=
  fiatShamirRule_external suite

example (layout : Layout operations) : (serializeRule (functions := functions) layout).External :=
  serializeRule_external layout

/-- A rule that refuses `image` at every exchange. -/
def imageRule : Rule ⟨.nat, .nat⟩ ([] : List OperationSignature) ([] : List FunctionHeader) where
  exchange := fun {_ _} _ _ _ {_} _ _ _ => .error StepRefusal.image
  derives := false
  draw := fun {_ _} _ _ {_ _} _ {_} _ _ => .error StepRefusal.row
  entryRefusal := fun _ _ => none
  entryPorts := fun _ header => ⟨header.inputs, header.outputs, header.agreements⟩
  entry := fun {_ _} _ _ _ => .error StepRefusal.row
  idleEntry := false

/-- It refuses internally. -/
theorem imageRule_internal : ¬ imageRule.External := by
  intro external
  have refused := external.exchange (protocols := []) (deployed := false) ⟨0, ⟨0, 1⟩, false⟩ 0 .bool
    (Δ := [⟨.nat, 1⟩, ⟨.nat, 0⟩, ⟨.bool, 0⟩]) (.there (.there .here)) (.there .here) .here
    StepRefusal.image rfl
  cases refused

/-- A result is accepted by the construction item and has its rows; a refusal of the
construction item is not accepted, and a missing row is not present. -/
example : ConstructionAccepts (.ok 0 : Except StepRefusal Nat) ∧
    RowsPresent (.ok 0 : Except StepRefusal Nat) :=
  ⟨fun _ refused => (nomatch refused), fun _ refused => (nomatch refused)⟩

example : ¬ ConstructionAccepts (.error .entry : Except StepRefusal Nat) :=
  fun accepted => nomatch accepted .entry rfl

example : ¬ RowsPresent (.error .row : Except StepRefusal Nat) :=
  fun present => nomatch present .row rfl

/-- A refusal that neither excludes is internal. -/
example : ∃ refusal, (.error .image : Except StepRefusal Nat) = .error refusal ∧
    refusal.internal = true :=
  (step_returns_or_internal (result := (.error .image : Except StepRefusal Nat))
    (fun _ refused => by cases refused; rfl) (fun _ refused => by cases refused; rfl)).resolve_left
    (fun returned => nomatch returned)

/-- The body of a well-formed definition is legal; a region with a `stop` is not. -/
example {typeTable : TypeTable} {protocols : List ProtocolHeader} {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (wellFormed : definition.violation typeTable = none) :
    Region.Legal typeTable header.roles none definition.body :=
  definition.body_legal wellFormed

example {typeTable : TypeTable} {protocols : List ProtocolHeader} {deployed : Bool} :
    ¬ Region.Legal typeTable 2 none
      (Region.stop (dialect := ProtocolDialect operations functions protocols deployed)
        (Γ := []) (out := []) .reject) :=
  Region.Legal.not_stop

/-- `stepProtocols_returns_or_residual` at the two rules: a step that the construction item
accepts and whose declaration has the rows returns, or an image violates a residual
condition. -/
example {typeTable : TypeTable} {old : List ProtocolHeader} (suite : Suite operations functions)
    (identities : Identities) (entry : Nat) (roles : TranscriptRoles)
    (protocols : Protocols typeTable operations functions old)
    (accepted : ConstructionAccepts
      (stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities entry roles
        protocols))
    (present : RowsPresent
      (stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities entry roles
        protocols)) :
    (∃ stepped, stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities entry
        roles protocols = .ok stepped) ∨
      ∃ violation, stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities
        entry roles protocols = .error (.residual violation) :=
  stepProtocols_returns_or_residual (fiatShamirRule_external suite) identities entry roles
    protocols accepted present

example {typeTable : TypeTable} {old : List ProtocolHeader} (layout : Layout operations)
    (identities : Identities) (entry : Nat) (roles : TranscriptRoles)
    (protocols : Protocols typeTable operations functions old)
    (accepted : ConstructionAccepts
      (stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities entry roles
        protocols))
    (present : RowsPresent
      (stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities entry roles
        protocols)) :
    (∃ stepped, stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities
        entry roles protocols = .ok stepped) ∨
      ∃ violation, stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities
        entry roles protocols = .error (.residual violation) :=
  stepProtocols_returns_or_residual (serializeRule_external layout) identities entry roles
    protocols accepted present

end Witnesses

#print axioms threadRegion_external
#print axioms threadRegion_returns
#print axioms stepProtocols_not_image
#print axioms stepProtocols_returns_or_residual
#print axioms fiatShamirRule_external
#print axioms serializeRule_external

/-! ## A rule emits what the check of a definition accepts -/

section Legal

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {typeTable : TypeTable}

/-- The two rules emit what the check accepts, over tables whose types are types of the
package. -/
example (rows : RowsNamed typeTable operations) (callees : FunctionsNamed typeTable functions)
    (suite : Suite operations functions) : (fiatShamirRule suite).Legal typeTable :=
  fiatShamirRule_legal rows callees suite

example (rows : RowsNamed typeTable operations) (layout : Layout operations) :
    (serializeRule (functions := functions) layout).Legal typeTable :=
  serializeRule_legal rows layout

/-- The tables of a typed package are such tables. -/
example : RowsNamed typed.typeTable (typed.table.map (·.signature)) := typed.rowsNamed

example : FunctionsNamed typed.typeTable typed.functions := typed.functionsNamed

/-- So the rule of every suite and of every layout that a declaration describes over the
tables of a typed package emits what the check accepts. -/
example (package : Typed) (suite : Raw.Suite) :
    (fiatShamirRule (Suite.ofRaw (tableScope (package.table.map (·.signature)))
      (tableScope package.functions) suite)).Legal package.typeTable :=
  fiatShamirRule_legal package.rowsNamed package.functionsNamed _

example (package : Typed) (raw : Raw.Layout) :
    ∀ layout, Layout.ofRaw (tableScope (package.table.map (·.signature))) raw = some layout →
      (serializeRule (functions := package.functions) layout).Legal package.typeTable :=
  fun layout _ => serializeRule_legal package.rowsNamed layout

/-- A table with a row of a type that the package does not have is not, and neither is a
function with such a type in its header. -/
example : ¬ RowsNamed ⟨0, [], []⟩ [⟨[], [.nominal 0], .pure⟩] :=
  fun rows => absurd (rows (signature := ⟨[], [.nominal 0], .pure⟩) .here).2 (by decide)

example : ¬ FunctionsNamed ⟨0, [], []⟩ [⟨[.nominal 0], [], false⟩] :=
  fun callees => absurd (callees (header := ⟨[.nominal 0], [], false⟩) .here).1 (by decide)

/-- `stepProtocols_returns` at the two rules: a step that the construction item accepts and
whose declaration has the rows returns. -/
example {old : List ProtocolHeader} (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) (suite : Suite operations functions)
    (identities : Identities) (entry : Nat) (roles : TranscriptRoles)
    (protocols : Protocols typeTable operations functions old)
    (accepted : ConstructionAccepts
      (stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities entry roles
        protocols))
    (present : RowsPresent
      (stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities entry roles
        protocols)) :
    ∃ stepped, stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities entry
      roles protocols = .ok stepped :=
  stepProtocols_returns (fiatShamirRule_external suite) (fiatShamirRule_legal rows callees suite)
    identities entry roles protocols accepted present

example {old : List ProtocolHeader} (rows : RowsNamed typeTable operations)
    (layout : Layout operations) (identities : Identities) (entry : Nat) (roles : TranscriptRoles)
    (protocols : Protocols typeTable operations functions old)
    (accepted : ConstructionAccepts
      (stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities entry roles
        protocols))
    (present : RowsPresent
      (stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities entry roles
        protocols)) :
    ∃ stepped, stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities
      entry roles protocols = .ok stepped :=
  stepProtocols_returns (serializeRule_external layout) (serializeRule_legal rows layout)
    identities entry roles protocols accepted present

/-- Neither step refuses the fixture's package internally, whatever the declaration. -/
example (other : Raw.Declaration) (refusal : StepRefusal)
    (refused : fiatShamir typed other = .error refusal) : refusal.internal = false :=
  fiatShamir_external typed other refused

example (other : Raw.Declaration) (refusal : StepRefusal)
    (refused : construct typed other = .error refusal) : refusal.internal = false :=
  construct_external typed other refused

/-- A rule that threads two numbers and has a given role write a given literal after every
exchange from the prover to the verifier. Its entry starts the two numbers at zero and
drops them after the body. It refuses a draw between the two transcript roles. -/
def markRule (role : Nat) (mark : Literal) : Rule ⟨.nat, .nat⟩ operations functions where
  exchange := fun {protocols deployed} place site type {_} value first second =>
    let sent : Emitted (ProtocolDialect operations functions protocols deployed) _
        [⟨type, place.roles.verifier⟩] :=
      Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
        (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil) .nil
    let marked : Emitted (ProtocolDialect operations functions protocols deployed) sent.context
        [⟨mark.type, role⟩] :=
      Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
        (.at role (.literal mark) .nil) .nil .nil
    .ok (sent.andThen marked
      (.cons ((sent.values.get .here).extend marked.grows)
        (.cons ((first.extend sent.grows).extend marked.grows)
          (.cons ((second.extend sent.grows).extend marked.grows) .nil))))
  derives := false
  draw := fun {_ _} place site {_ _} _ {_} _ _ => .error (.interactive place.definition site)
  entryRefusal := fun _ _ => none
  entryPorts := fun _ header => ⟨header.inputs, header.outputs, header.agreements⟩
  entry := fun {protocols deployed} place header body =>
    let atProver : Emitted (ProtocolDialect operations functions protocols deployed)
        (bindAll [] header.inputs) [⟨.nat, place.roles.prover⟩] :=
      Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
        (.at place.roles.prover (.literal (.nat 0)) .nil) .nil .nil
    let atVerifier : Emitted (ProtocolDialect operations functions protocols deployed)
        atProver.context [⟨.nat, place.roles.verifier⟩] :=
      Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
        (.at place.roles.verifier (.literal (.nat 0)) .nil) .nil .nil
    match body ((Renaming.identity header.inputs).extend (atProver.grows.trans atVerifier.grows))
        ((atProver.values.get .here).extend atVerifier.grows) (atVerifier.values.get .here) with
    | .ok threaded =>
        .ok (atProver.wrap (atVerifier.wrap (.bind threaded
          (.ret (Operands.newest header.outputs
            (Γ := ⟨.nat, place.roles.verifier⟩ :: ⟨.nat, place.roles.prover⟩ ::
              atVerifier.context))))))
    | .error refusal => .error refusal
  idleEntry := false

/-- A rule that has a role that the definition does not have write the literal does not
emit what the check accepts: after an exchange between the roles 0 and 1 of a definition
with two roles, the role 7 acts. -/
theorem markRule_out_of_range :
    ¬ (markRule (operations := []) (functions := []) 7 (.nat 0)).Legal ⟨0, [], []⟩ := by
  intro legal
  obtain ⟨_, passes⟩ := legal.exchange (protocols := []) (deployed := false) ⟨0, ⟨0, 1⟩, false⟩ 0
    .bool (Δ := [⟨.nat, 1⟩, ⟨.nat, 0⟩, ⟨.bool, 0⟩]) (.there (.there .here)) (.there .here) .here _
    rfl
  obtain ⟨added, _, emitted⟩ := passes 2 none rfl rfl
  have refused : (Except.error Violation.roleOutOfRange : Except Violation (List Nat)) =
      .ok (added ++ []) := emitted [] (.ret .nil) []
  cases refused

/-- A rule that writes a literal of a type that the package does not have does not emit
what the check accepts. -/
theorem markRule_unnamed :
    ¬ (markRule (operations := []) (functions := []) 0 (.nominal 0 [])).Legal ⟨0, [], []⟩ := by
  intro legal
  obtain ⟨_, passes⟩ := legal.exchange (protocols := []) (deployed := false) ⟨0, ⟨0, 1⟩, false⟩ 0
    .bool (Δ := [⟨.nat, 1⟩, ⟨.nat, 0⟩, ⟨.bool, 0⟩]) (.there (.there .here)) (.there .here) .here _
    rfl
  obtain ⟨added, _, emitted⟩ := passes 2 none rfl rfl
  have refused : (Except.error Violation.nominalRow : Except Violation (List Nat)) =
      .ok (added ++ []) := emitted [] (.ret .nil) []
  cases refused

/-- Every way a protocol is reached as the entry names two of its roles when no protocol
is reached; an entry with a role that the protocol does not have does not. -/
example (old : List ProtocolHeader) : EntriesBelow old [] :=
  fun _ _ reached => by
    obtain ⟨_, at_, _⟩ := reached
    cases at_

example : ¬ EntriesBelow [⟨2, [], [], default, false⟩] [[.entry ⟨5, 6⟩]] := by
  intro below
  obtain ⟨header, at_, prover, _⟩ := below 0 ⟨5, 6⟩ ⟨_, rfl, List.mem_singleton.mpr rfl⟩
  cases at_
  exact absurd prover (by decide)

end Legal

/-- The step of the rule that writes a literal after every exchange, on the result of the
Fiat–Shamir step with the declaration of the fixture. -/
noncomputable def markedWith (role : Nat) (mark : Literal) :
    Except StepRefusal (Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :=
  match fiatShamir typed declaration with
  | .ok constructed =>
      stepProtocols ⟨.nat, .nat⟩ (markRule role mark) constructed.identities
        (constructed.headers.length - 1) ⟨declaration.prover, declaration.verifier⟩
        constructed.protocols
  | .error refusal => .error refusal

-- A role of the entry writes a number: the step returns.
kernel_refl mark_returns : refusalOf (markedWith 0 (.nat 0)) equals none

-- A role that the entry does not have writes it: an image violates a residual condition.
kernel_refl mark_out_of_range : refusalOf (markedWith 7 (.nat 0)) equals
  some (StepRefusal.residual Violation.roleOutOfRange)

-- A role of the entry writes a literal of a type that the package does not have.
kernel_refl mark_unnamed : refusalOf (markedWith 0 (.nominal 4096 [])) equals
  some (StepRefusal.residual Violation.nominalRow)

#print axioms threadRegion_passes
#print axioms plainRegion_passes
#print axioms fiatShamirRule_legal
#print axioms serializeRule_legal
#print axioms stepProtocols_external
#print axioms stepProtocols_returns
#print axioms Zkc.Core.fiatShamir_returns
#print axioms serializeProtocols_returns
#print axioms construct_returns
#print axioms markRule_out_of_range
#print axioms markRule_unnamed
#print axioms mark_out_of_range
#print axioms mark_unnamed

/-! ## Applications that have an image to name -/

namespace Sumcheck

raw_package raw from file "fixtures/construction/sumcheck.json"
raw_declaration declaration from file "fixtures/construction/sumcheck.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

/-- Whether every application of the newest protocol has an image to name, among the
images that a step makes of the earlier protocols when they are reached as `demands` say. -/
def newestServed {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} (t : Threads) (rule : Rule t operations functions)
    (roles : TranscriptRoles) (demands : List (List Demand)) :
    {old : List ProtocolHeader} → Protocols typeTable operations functions old → Option Bool
  | _, .nil => none
  | _, .snoc earlier definition _ =>
      match rewriteProtocols t rule Identities.written earlier demands with
      | .ok rewritten =>
          some (served t rewritten.table (some roles.prover) (some roles.verifier) definition.body)
      | .error _ => none

/-- The same for the Fiat–Shamir rule of a declaration's suite and its two roles. -/
def servedBy (typed : Typed) (declaration : Raw.Declaration) (demands : List (List Demand)) :
    Option Bool :=
  match declaration.suite with
  | none => none
  | some suite =>
      let suite := Suite.ofRaw (tableScope (typed.table.map (·.signature)))
        (tableScope typed.functions) suite
      newestServed ⟨suite.state, suite.state⟩ (fiatShamirRule suite)
        ⟨declaration.prover, declaration.verifier⟩ demands typed.program.protocols

/-- For the entry of the fixture. -/
noncomputable abbrev entryServed (demands : List (List Demand)) : Option Bool :=
  servedBy typed declaration demands

-- The entry applies its callee with the roles in their order. Among the images of the
-- callee reached that way, the application has the image that threads.
kernel_refl served_reached : entryServed [[.applied (some 0) (some 1)]] equals some true

-- A callee that is not reached has no image, and the application has none to name.
kernel_refl served_unreached : entryServed [[]] equals some false

end Sumcheck

end StepRefusals
