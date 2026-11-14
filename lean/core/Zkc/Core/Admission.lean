module

public import Zkc.Core.Maxima
public import Zkc.Core.CopiesSound
public import Zkc.Core.Stops
public import Zkc.Core.Keys
public import Zkc.Core.VocabularyModel

public section

/-! Admission: one decision, and what an admitted package guarantees.

`admit` decides whether a raw package is admitted and returns the typed package with what
was checked, or every refusal found. A consumer takes an `Admitted`: it does not assemble
admission from elaboration and the checks.

A raw package is admitted when the sites of each protocol are numbered in the order of its
body, it elaborates (its residual conditions hold), the normal form of every body passes the
check of facts, and every protocol passes the check of copies. That is a program as written.
The package of what a step returns is admitted with gaps between its sites and without the
check of copies (`Claims.written`).
The check of facts includes the maximum of a loop over a value: the count is known to be
within it at every participant, and a count above it is outside the domain of the loop.

For a model that satisfies the domain laws, every function, every protocol at every side and
every role program of an admitted package never stops `undefined`, as written.

For every model, every protocol of a package admitted as written, at a side that supports the
requirements that the check of copies found for it and on arguments of which its input
agreements hold, never stops `incomplete`, and its output agreements hold of what it returns.
The side of every role supports every requirement.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

namespace Admission

/-- What of admission a raw package does not meet. -/
inductive Refusal where
  /-- It does not elaborate. -/
  | elaboration (refusal : Zkc.Core.Refusal)
  /-- The normal form of a definition does not pass the check of facts: the definition, and
  the first application of its normal form that is not justified. -/
  | facts (definition : Zkc.Core.Refusal.Definition) (unjustified : Unjustified)
  /-- A protocol does not pass the check of copies: its number, and the requirement that is
  not met. -/
  | copies (protocol : Nat) (refusal : Copies.Refusal)
  /-- The sites of a protocol are not numbered in the order of its body. -/
  | sites (protocol : Nat)
  /-- The table of keys does not give a protocol one key per site, or gives two sites one
  key. -/
  | keys (protocol : Nat)
  /-- What the producer states of which functions can stop is not what their bodies say: the
  number of the first function that differs. -/
  | stops (function : Nat)
  /-- A row is not the vocabulary's row of its name, with the reason. -/
  | row (reason : String)
  /-- The data of a literal of a nominal type are not data of that type: the definition and
  the row of the type. -/
  | literal (definition : Zkc.Core.Refusal.Definition) (row : Nat)
  deriving Repr

/-- What a producer states beside a raw package, and what the package is checked against:
the keys of the sites of each protocol; whether each function can stop, in program order;
the vocabulary whose row every row of the package under one of its names must be (a row under
another name is a row of an extension); the vocabulary of whose types the data of its
literals must be. Each is checked when it is given. -/
structure Claims where
  /-- The package is a program as written, and not what a step returned. A program as written
  has its sites numbered without gaps and passes the check of copies. What a step returns has
  its sites in the order of its body, with gaps where the step removed one, and the check of
  copies is not run on it: the Fiat–Shamir step does not declare the two transcript states
  that it threads to be copies, and after serialization the prover and the verifier do not
  interact. -/
  written : Bool := true
  keys : Option SiteKeys := none
  stops : Option (List Bool) := none
  rows : Option Vocabulary.Table := none
  literals : Option Vocabulary.Table := none

end Admission


section Sites

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

mutual
  /-- The sites of a region of a protocol body, in the order of the body. -/
  def siteOrder {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → List Nat
    | .ret _ => []
    | .stop _ => []
    | .letOp op _ bodies next => op.sites ++ siteOrders bodies ++ siteOrder next
    | .bind body next => siteOrder body ++ siteOrder next

  def siteOrders {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures → List Nat
    | .nil => []
    | .cons body tail => siteOrder body ++ siteOrders tail
end

/-- The numbers of the sites of each protocol of a program, in the order of its body, in
program order. -/
def Protocols.siteOrders {typeTable : TypeTable} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      List (List Nat)
  | _, .nil => []
  | _, .snoc earlier definition _ => earlier.siteOrders ++ [siteOrder definition.body]

end Sites

/-- Site numbers that increase. -/
def increasing : List Nat → Bool
  | first :: second :: rest => decide (first < second) && increasing (second :: rest)
  | _ => true

/-- The protocols whose sites are not numbered in the order of the body (without gaps, for a
program as written), and those that the table of keys, when one is given, does not give one
key per site and no key twice. -/
def Typed.unkeyed (typed : Typed) (keys : Option SiteKeys) (written : Bool := true) :
    List Admission.Refusal :=
  let orders := typed.program.protocols.siteOrders
  let numbered := (orders.zip (List.range orders.length)).filterMap fun (sites, number) =>
    if cond written (sites == List.range sites.length) (increasing sites) then none
    else some (Admission.Refusal.sites number)
  let keyed := match keys with
    | none => []
    | some keys =>
        if keys.length != orders.length then [Admission.Refusal.keys orders.length]
        else ((orders.zip keys).zip (List.range orders.length)).filterMap fun ((sites, given), number) =>
          if given.length == sites.length && SiteKey.distinct given then none
          else some (Admission.Refusal.keys number)
  numbered ++ keyed

/-- The first function of which the producer's statement of whether it can stop is not what
its body says. -/
def Typed.misstated (typed : Typed) (stops : Option (List Bool)) : List Admission.Refusal :=
  match stops with
  | none => []
  | some stated =>
      let computed := typed.program.functions.stops.reverse
      if stated.length != computed.length then [.stops computed.length]
      else match ((stated.zip computed).zip (List.range computed.length)).find? fun ((said, is), _) =>
          said != is with
        | some (_, number) => [.stops number]
        | none => []

namespace Raw

/-- Whether the data of a literal of a nominal type are data of that type, for a vocabulary:
one number below the order for a type computed in a field, and not zero for `nonzero`; bytes
for a type without arithmetic. No literal of a group is data: its values are made by rows. -/
def nominalLiteral (table : Vocabulary.Table) (types : Array CatalogueRow) (row : Nat)
    (data : List Nat) : Bool :=
  match Vocabulary.closedOf types (.nominal row) with
  | none => false
  | some closed =>
      let positive := match closed with
        | .nonzero _ => data.all (· != 0)
        | _ => true
      match Vocabulary.elementOf table closed with
      | some (.prime order) | some (.extension order _ _) =>
          data.length == 1 && data.all (· < order) && positive
      | some .curve => false
      | none => data.all (· < 256)

mutual
  /-- The rows of the nominal literals of a local region whose data are not data of their
  types. -/
  partial def LocalRegion.badLiterals (accepted : Nat → List Nat → Bool) : LocalRegion → List Nat
    | .ret _ | .stop _ => []
    | .block _ body next => body.badLiterals accepted ++ next.badLiterals accepted
    | .step instruction next => instruction.badLiterals accepted ++ next.badLiterals accepted

  partial def LocalStep.badLiterals (accepted : Nat → List Nat → Bool) : LocalStep → List Nat
    | .literal (.nominal row data) => if accepted row data then [] else [row]
    | .conditional _ _ _ onTrue onFalse => onTrue.badLiterals accepted ++ onFalse.badLiterals accepted
    | .match _ _ _ _ arms => arms.toList.flatMap (·.badLiterals accepted)
    | .loop _ _ _ _ body => body.badLiterals accepted
    | _ => []
end

/-- The same for a region of a protocol body. -/
partial def ProtocolRegion.badLiterals (accepted : Nat → List Nat → Bool) : ProtocolRegion → List Nat
  | .ret _ | .stop _ => []
  | .block _ body next => body.badLiterals accepted ++ next.badLiterals accepted
  | .step instruction next =>
      (match instruction with
        | .at _ performed => performed.badLiterals accepted
        | .repeat _ _ _ _ _ body => body.badLiterals accepted
        | .choose _ _ _ _ _ arms => arms.toList.flatMap (·.badLiterals accepted)
        | _ => []) ++ next.badLiterals accepted

/-- The rows of a package under a name of the vocabulary that are not the vocabulary's. A row
under another name is a row of an extension, and is not refused. -/
def Package.foreignRows (package : Package) (table : Vocabulary.Table) : List Admission.Refusal :=
  (Vocabulary.misstated table package).map Admission.Refusal.row

/-- The literals of nominal types of a package whose data are not data of their types. -/
def Package.foreignLiterals (package : Package) (table : Vocabulary.Table) :
    List Admission.Refusal :=
  let accepted := nominalLiteral table package.types.toArray
  let ofFunctions := (package.functions.zip (List.range package.functions.length)).flatMap
    fun (function, number) =>
      match function.body with
      | some body => (body.badLiterals accepted).map (Admission.Refusal.literal (.function number))
      | none => []
  let ofProtocols := (package.protocols.zip (List.range package.protocols.length)).flatMap
    fun (protocol, number) =>
      (protocol.body.badLiterals accepted).map (Admission.Refusal.literal (.protocol number))
  ofFunctions ++ ofProtocols

end Raw

/-- The definitions of a typed package whose normal form does not pass the check of facts. -/
def Typed.inadmissible (typed : Typed) (written : Bool := true) : List Admission.Refusal :=
  typed.program.functions.inadmissible.map (fun (number, unjustified) =>
      Admission.Refusal.facts (.function number) unjustified) ++
    typed.program.protocols.inadmissible.map (fun (number, unjustified) =>
      Admission.Refusal.facts (.protocol number) unjustified) ++
    cond written (typed.program.protocols.copies.2.map fun (number, refusal) =>
      Admission.Refusal.copies number refusal) []

/-- What a package does not meet of what is stated beside it: its sites in the order of its
bodies, always; and, each when it is given, the keys of its sites, which functions can stop,
the vocabulary that its rows are of, and the vocabulary of whose types the data of its literals
are. -/
def Admission.Claims.unmet (claims : Admission.Claims) (package : Raw.Package) (typed : Typed) :
    List Admission.Refusal :=
  typed.unkeyed claims.keys claims.written ++ typed.misstated claims.stops ++
    (match claims.rows with
      | some table => package.foreignRows table
      | none => []) ++
    match claims.literals with
    | some table => package.foreignLiterals table
    | none => []

/-- A package that is admitted: the package, what was stated beside it, its typed form, and
what was checked. The claims say which of the checks beside the package were made: a consumer
that needs one reads it here (`Admitted.rows_matched`). -/
structure Admitted where
  package : Raw.Package
  claims : Admission.Claims
  typed : Typed
  elaborated : elaborate package = .ok typed
  admissible : typed.program.admissible = true
  coherent : claims.written = true → typed.program.protocols.coherent = true
  stated : claims.unmet package typed = []

/-- The admission of a raw package: the admitted package, or every refusal found. What the
producer states beside the package is checked when it is given: the keys of its sites, which
functions can stop, and the vocabulary that its rows and the data of its literals are of. -/
def admit (package : Raw.Package) (claims : Admission.Claims := {}) :
    Except (List Admission.Refusal) Admitted :=
  match elaborated : elaborate package with
  | .error refusal => .error [.elaboration refusal]
  | .ok typed =>
      if admissible : typed.program.admissible = true then
        if coherent : claims.written = true → typed.program.protocols.coherent = true then
          if stated : claims.unmet package typed = [] then
            .ok ⟨package, claims, typed, elaborated, admissible, coherent, stated⟩
          else .error (claims.unmet package typed)
        else .error (typed.inadmissible claims.written ++ claims.unmet package typed)
      else .error (typed.inadmissible claims.written ++ claims.unmet package typed)

/-- What admission returns is the package that was given, with what was stated beside it. -/
theorem admit_package {package : Raw.Package} {claims : Admission.Claims} {admitted : Admitted}
    (admits : admit package claims = .ok admitted) : admitted.package = package := by
  unfold admit at admits
  split at admits
  · cases admits
  · split at admits
    · split at admits
      · split at admits
        · cases admits
          rfl
        · cases admits
      · cases admits
    · cases admits

namespace Admitted

variable {model : Model}

/-- Every function of an admitted package never stops `undefined`. -/
theorem never_undefined (admitted : Admitted)
    (laws : model.DomainLaws (admitted.typed.table.map (·.signature))) {header : FunctionHeader}
    (callee : Var admitted.typed.functions header)
    (arguments : Values model.Value header.inputs) :
    NeverStops .undefined ((admitted.typed.program.functionTable model).get callee arguments) :=
  Program.never_undefined_of_admissible laws admitted.typed.program admitted.admissible callee
    arguments

/-- Every protocol of an admitted package never stops `undefined`, with any identities, under
any path, for any side, on any values, whatever the replies of its effects. -/
theorem protocols_never_undefined (admitted : Admitted)
    (laws : model.DomainLaws (admitted.typed.table.map (·.signature))) (identities : Identities)
    {header : ProtocolHeader} (callee : Var admitted.typed.protocols header) (path : List Nat)
    (side : Side) (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      ((admitted.typed.program.protocolTable model identities).get callee path side arguments) :=
  Program.protocols_never_undefined_of_admissible laws admitted.typed.program admitted.admissible
    identities callee path side arguments

/-- The program of every role of every protocol of an admitted package never stops
`undefined`, under any path and on any arguments, whatever the replies of its effects. -/
theorem role_never_undefined (admitted : Admitted)
    (laws : model.DomainLaws (admitted.typed.table.map (·.signature))) (identities : Identities)
    (projected : Projected (admitted.typed.table.map (·.signature)) admitted.typed.functions
      admitted.typed.protocols)
    (projects : projectProtocols admitted.typed.program.protocols = .ok projected)
    {header : ProtocolHeader} (callee : Var admitted.typed.protocols header) (role : Nat)
    (calling : Var projected.headers (roleHeader role header))
    (named : projected.callees.find callee role = some calling) (path : List Nat)
    (arguments : Values model.Value (roleHeader role header).inputs) :
    NeverStops .undefined
      ((projected.programs.table model (admitted.typed.program.functionTable model)
        identities).get calling path arguments) :=
  Program.role_never_undefined_of_admissible laws admitted.typed.program admitted.admissible
    identities projected projects callee role calling named path arguments

/-- The requirements that the check of copies found for a protocol of an admitted package: the
copies that must be one value, each with its role and its support. -/
def requirements (admitted : Admitted) {header : ProtocolHeader}
    (callee : Var admitted.typed.protocols header) : List Copies.Requirement :=
  admitted.typed.program.protocols.copies.1.getD callee.index []

/-- Every protocol of a package admitted as written, for a side that supports its requirements
and on arguments of which its input agreements hold, never stops `incomplete`, whatever the
replies of its effects, and its output agreements hold of what it returns. -/
theorem protocols_cohere (admitted : Admitted) (written : admitted.claims.written = true)
    (identities : Identities)
    {header : ProtocolHeader} (callee : Var admitted.typed.protocols header) (path : List Nat)
    (side : Side) (arguments : Values (SideValue model side) header.inputs)
    (inputsHold : header.agreements.InputsHold model side arguments)
    (supported : side.supports (admitted.requirements callee) = true) :
    Coheres (fun outputs => ∀ agreement ∈ header.agreements.outputs,
        agreement.Holds model side outputs)
      ((admitted.typed.program.protocolTable model identities).get callee path side arguments) :=
  Protocols.table_agrees (Functions.table_ends admitted.typed.program.functions) identities
    admitted.typed.program.protocols (admitted.coherent written) callee path side arguments
    inputsHold
    supported

/-- Every protocol of a package admitted as written, run by all its roles together on arguments
of which its input agreements hold, never stops `incomplete`, and its output agreements hold
of what it returns. -/
theorem protocols_cohere_together (admitted : Admitted)
    (written : admitted.claims.written = true) (identities : Identities)
    {header : ProtocolHeader} (callee : Var admitted.typed.protocols header) (path : List Nat)
    (arguments : Values (SideValue model fun _ => true) header.inputs)
    (inputsHold : header.agreements.InputsHold model (fun _ => true) arguments) :
    Coheres (fun outputs => ∀ agreement ∈ header.agreements.outputs,
        agreement.Holds model (fun _ => true) outputs)
      ((admitted.typed.program.protocolTable model identities).get callee path (fun _ => true)
        arguments) :=
  admitted.protocols_cohere written identities callee path (fun _ => true) arguments inputsHold
    (Side.supports_everyone _)

/-- The rows of an admitted package under the names of the vocabulary that was stated beside it
are that vocabulary's rows. -/
theorem rows_stated (admitted : Admitted) {table : Vocabulary.Table}
    (claimed : admitted.claims.rows = some table) :
    Vocabulary.misstated table admitted.package = [] := by
  have stated := admitted.stated
  unfold Admission.Claims.unmet at stated
  rw [claimed] at stated
  have rows : admitted.package.foreignRows table = [] :=
    (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp stated).1).2
  exact List.map_eq_nil_iff.mp rows

/-- The rows of an admitted package without a row of an extension are those of the vocabulary
that was stated beside it. -/
theorem rows_matched (admitted : Admitted) {table : Vocabulary.Table}
    (claimed : admitted.claims.rows = some table)
    (closed : Vocabulary.extensions table admitted.package = []) :
    Vocabulary.mismatches table admitted.package = [] :=
  Vocabulary.mismatches_of_misstated (admitted.rows_stated claimed) closed

/-- The model that runs an admitted package whose rows were checked against the vocabulary, and
that has no row of an extension, satisfies the domain laws of its table: the statements above
hold of it. -/
theorem vocabulary_laws (admitted : Admitted)
    (claimed : admitted.claims.rows = some Vocabulary.table)
    (closed : Vocabulary.extensions Vocabulary.table admitted.package = []) :
    (Vocabulary.model Vocabulary.table admitted.package).DomainLaws
      (admitted.typed.table.map (·.signature)) :=
  Vocabulary.model_domainLaws admitted.elaborated (admitted.rows_matched claimed closed)

/-- Every function of an admitted package whose rows were checked against the vocabulary, and
that has no row of an extension, never stops `undefined` in the model that runs the package. -/
theorem never_undefined_vocabulary (admitted : Admitted)
    (claimed : admitted.claims.rows = some Vocabulary.table)
    (closed : Vocabulary.extensions Vocabulary.table admitted.package = [])
    {header : FunctionHeader}
    (callee : Var admitted.typed.functions header)
    (arguments : Values (Vocabulary.model Vocabulary.table admitted.package).Value header.inputs) :
    NeverStops .undefined
      ((admitted.typed.program.functionTable
        (Vocabulary.model Vocabulary.table admitted.package)).get callee arguments) :=
  admitted.never_undefined (admitted.vocabulary_laws claimed closed) callee arguments

end Admitted

end Zkc.Core
