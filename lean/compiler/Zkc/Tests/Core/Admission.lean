import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Tests.Core.Runs
import Zkc.Core.RoundTrip
import Zkc.Core.ProtocolFactsProject
import Zkc.Core.VocabularyModel

/-! The admission of a package by the vocabulary, and what follows from it.

- A package of `koala-bear` and its units with three rows of the vocabulary, `field.is_nonzero`,
  the restricted row `field.nonzero` that names it as its domain row, and `field.inverse`, built
  here. Its function guards `field.is_nonzero`, then applies `field.nonzero` and inverts the
  unit. Its protocol does the same between two roles: the first guards and sends the unit, the
  second inverts it. The rows of the package are the vocabulary's, which the kernel computes,
  and the vocabulary admits the package: the model implements every row.
- The model of the vocabulary satisfies the domain laws of the package's table
  (`Vocabulary.model_domainLaws`), so the statements that take the domain laws apply to the
  model that runs the package: its function and the program of each role of its protocol never
  stop `undefined`. The same holds of the model that the checks of the executor run, the one
  of the package unelaborated from the typed one.
- The laws are a condition on the model: under it the function without the guard stops
  `undefined` at 0, where `field.nonzero` has no value, and returns the inverse at 2. The check
  of facts does not pass that function.
- A row with a name of the vocabulary and another signature is reported, each with its
  reason: other inputs, other outputs, another kind, a domain row of another name, a domain row
  at other static arguments, a restricted row without the domain row that the vocabulary
  gives, and static arguments at which the vocabulary has no row of the name. The core admits
  each of these packages; the vocabulary does not.

The runs, the reports and the admission are computed by Lean's interpreter; the comparison of the
rows with the vocabulary and the conditions of the statements by the kernel.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Admission

/-! ## A package that the vocabulary admits -/

/-- A row at the one static argument `koala-bear`, the type row 0. -/
abbrev row (name : String) (inputs outputs : List Ty) (kind : OperationKind) : Operation :=
  ⟨⟨Name.ofString name, [.type (.nominal 0)]⟩, ⟨inputs, outputs, kind⟩⟩

/-- The types `koala-bear` and `nonzero<koala-bear>`. -/
abbrev types : List CatalogueRow :=
  [⟨Name.ofString "koala-bear", []⟩, ⟨Name.ofString "nonzero", [.type (.nominal 0)]⟩]

/-- `field.is_nonzero`, the restricted row `field.nonzero` with it as its domain row, and
`field.inverse`. -/
abbrev rows : List Operation :=
  [row "field.is_nonzero" [.nominal 0] [.bool] .pure,
   row "field.nonzero" [.nominal 0] [.nominal 1] (.restricted (some 0)),
   row "field.inverse" [.nominal 1] [.nominal 1] .pure]

/-- `guard is_nonzero(x); return inverse(nonzero(x))`. -/
abbrev guarded : Raw.Function :=
  ⟨false, [.nominal 0], [.nominal 1], some <|
    .step (.op 0 [0]) <|
    .step (.guard .reject 1) <|
    .step (.op 1 [0]) <|
    .step (.op 2 [2]) <|
    .ret [3]⟩

/-- The first role guards `is_nonzero(x)` and sends `nonzero(x)`; the second inverts it. -/
abbrev relayed : Raw.Protocol :=
  ⟨false, 2, [⟨.nominal 0, 0⟩], [⟨.nominal 1, 1⟩], [],
    .step (.at 0 (.op 0 [0])) <|
    .step (.at 0 (.guard .reject 1)) <|
    .step (.at 0 (.op 1 [0])) <|
    .step (.exchange 0 1 0 2) <|
    .step (.at 1 (.op 2 [3])) <|
    .ret [4]⟩

abbrev raw : Raw.Package := ⟨types, [], [], rows, [guarded], [relayed], none⟩

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

-- The package has a restricted row that names a domain row.
kernel_refl kinds :
    (typed.table.map (·.signature.kind)) equals [.pure, .restricted (some 0), .pure]

-- The rows of the package are the vocabulary's.
kernel_refl matched : Vocabulary.mismatches Vocabulary.table raw equals []

-- Every function and every protocol passes the check of facts.
kernel_refl justified : typed.program.justified equals true

/-! ## The domain laws and what they give -/

/-- The model of the vocabulary's rows of the package. -/
abbrev model : Model := Vocabulary.model Vocabulary.table raw

/-- The model satisfies the domain laws of the package's table. -/
theorem laws : model.DomainLaws (typed.table.map (·.signature)) :=
  Vocabulary.model_domainLaws elaborate_eq matched

/-- Under the model of the vocabulary, every function of the package never stops `undefined`,
on any arguments. -/
theorem function_defined {header : FunctionHeader} (callee : Var typed.functions header)
    (arguments : Values model.Value header.inputs) :
    NeverStops .undefined ((typed.program.functionTable model).get callee arguments) :=
  Program.never_undefined laws typed.program justified callee arguments

/-- The function of the package. -/
abbrev invert : Var typed.functions ⟨[.nominal 0], [.nominal 1], false⟩ := ⟨0, rfl⟩

/-- The statement at the function and the element 0, where `field.nonzero` has no value. -/
theorem invert_defined_at_zero :
    NeverStops .undefined
      ((typed.program.functionTable model).get invert (.cons (Concrete.Datum.number 0) .nil)) :=
  function_defined invert _

/-- The value of a result that is known to be one. -/
def okValue {ε α : Type} (result : Except ε α) (accepted : result.isOk = true) : α :=
  match result, accepted with
  | .ok value, _ => value

theorem okValue_eq {ε α : Type} (result : Except ε α) (accepted : result.isOk = true) :
    result = .ok (okValue result accepted) := by
  match result, accepted with
  | .ok value, _ => rfl

kernel_refl projects : (projectProtocols typed.program.protocols).isOk equals true

/-- The role programs of the package. -/
noncomputable def projected :
    Projected (typed.table.map (·.signature)) typed.functions typed.protocols :=
  okValue (projectProtocols typed.program.protocols) projects

theorem projected_eq : projectProtocols typed.program.protocols = .ok projected :=
  okValue_eq (projectProtocols typed.program.protocols) projects

/-- Under the model of the vocabulary, the program of every role of every protocol of the
package never stops `undefined`, under any path and on any arguments, whatever the replies of
its effects. -/
theorem role_defined (identities : Identities) {header : ProtocolHeader}
    (callee : Var typed.protocols header) (role : Nat)
    (program : Var projected.headers (roleHeader role header))
    (named : projected.callees.find callee role = some program) (path : List Nat)
    (arguments : Values model.Value (roleHeader role header).inputs) :
    NeverStops .undefined
      ((projected.programs.table model (typed.program.functionTable model) identities).get
        program path arguments) :=
  Program.role_never_undefined laws typed.program justified identities projected projected_eq
    callee role program named path arguments

/-- The protocol of the package. -/
abbrev relay : Var typed.protocols ⟨2, [⟨.nominal 0, 0⟩], [⟨.nominal 1, 1⟩], .none, false⟩ :=
  ⟨0, rfl⟩

-- Both roles of the protocol have a program, to which the statement applies.
kernel_refl first_named : (projected.callees.find relay 0).isSome equals true
kernel_refl second_named : (projected.callees.find relay 1).isSome equals true

/-- The model that the checks of the executor run, the one of the package unelaborated from
the typed one, satisfies the domain laws too. -/
theorem executor_laws : (Runs.modelOf typed).DomainLaws (typed.table.map (·.signature)) :=
  Vocabulary.model_domainLaws (elaborate_unelaborate typed)
    (show Vocabulary.mismatches Vocabulary.table (unelaborate typed) = [] from
      unelaborate_eq ▸ matched)

#print axioms Vocabulary.mismatches_of_admitted
#print axioms Vocabulary.model_domainLaws
#print axioms laws
#print axioms function_defined
#print axioms role_defined
#print axioms executor_laws

/-! ## The laws are a condition -/

/-- The function without the guard: `return inverse(nonzero(x))`. -/
abbrev unguarded : Raw.Function :=
  ⟨false, [.nominal 0], [.nominal 1], some <|
    .step (.op 1 [0]) <|
    .step (.op 2 [1]) <|
    .ret [2]⟩

abbrev unguardedRaw : Raw.Package := ⟨types, [], [], rows, [unguarded], [], none⟩

kernel_refl unguarded_elaborates : (elaborate unguardedRaw).isOk equals true

noncomputable def unguardedElaborated : Typed := Typed.ofRaw unguardedRaw unguarded_elaborates

typed_literal unguardedTyped := unguardedElaborated

-- The rows of the package are the vocabulary's, and the check of facts does not pass its
-- function.
kernel_refl unguarded_matched : Vocabulary.mismatches Vocabulary.table unguardedRaw equals []
kernel_refl unguarded_fails : unguardedTyped.program.justified equals false

/-! ## Runs and reports -/

open Zkc.Core.Concrete (Datum)
open Zkc.Core.Vocabulary (Run)

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"admission: {label}")

def describe : Run → String
  | .returned outputs => s!"returned {reprStr outputs}"
  | .stopped reason => s!"stopped {reprStr reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

/-- A package of the two types with the rows given and no program. -/
def tableOf (types : List CatalogueRow) (rows : List Operation) : Raw.Package :=
  ⟨types, [], [], rows, [], [], none⟩

/-- Whether the vocabulary reports exactly one row of a package, with a message that has both
texts. -/
def reports (package : Raw.Package) (name reason : String) : Bool :=
  match Vocabulary.missing Vocabulary.table package with
  | [message] => (message.splitOn name).length > 1 && (message.splitOn reason).length > 1
  | _ => false

#eval show IO Unit from do
  let inverse := (Vocabulary.koalaBearOrder + 1) / 2
  -- The guarded function: the inverse at 2, `reject` at 0.
  let returned := describe (Vocabulary.runData Vocabulary.table raw 0 [.number 2])
  check s!"the guarded function at 2: {returned}" (returned == describe (.returned [.number inverse]))
  let rejected := describe (Vocabulary.runData Vocabulary.table raw 0 [.number 0])
  check s!"the guarded function at 0: {rejected}" (rejected == describe (.stopped .reject))
  -- Without the guard the restricted row is applied outside its domain: `undefined`.
  let inside := describe (Vocabulary.runData Vocabulary.table unguardedRaw 0 [.number 2])
  check s!"the unguarded function at 2: {inside}" (inside == describe (.returned [.number inverse]))
  let outside := describe (Vocabulary.runData Vocabulary.table unguardedRaw 0 [.number 0])
  check s!"the unguarded function at 0: {outside}" (outside == describe (.stopped .undefined))
  -- The protocol: the programs of the two roles against each other.
  let typed ← match elaborateWritten raw with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  let relayed ← IO.ofExcept (Runs.joint typed [.number 2] [] [0, 1])
  check s!"the protocol at 2: {relayed.grouped.describe}"
    (relayed.agrees && relayed.grouped.same (.returned [.number inverse]))
  let stopped ← IO.ofExcept (Runs.joint typed [.number 0] [] [0, 1])
  check s!"the protocol at 0: {stopped.grouped.describe}"
    (stopped.grouped.describe == "stopped PIR.Stop.reject")
  -- The vocabulary admits both packages: every row is its own and the model implements it.
  check "the package is not admitted" (Vocabulary.missing Vocabulary.table raw).isEmpty
  check "the unguarded package is not admitted" (Vocabulary.missing Vocabulary.table unguardedRaw).isEmpty
  -- A name of the vocabulary with another signature.
  let isNonzero := row "field.is_nonzero" [.nominal 0] [.bool] .pure
  let nonzero := row "field.nonzero" [.nominal 0] [.nominal 1] (.restricted (some 0))
  check "other inputs"
    (reports (tableOf types [row "field.add" [.nominal 0] [.nominal 0] .pure]) "field.add" "inputs")
  check "other outputs"
    (reports (tableOf types [row "field.is_nonzero" [.nominal 0] [.nominal 0] .pure])
      "field.is_nonzero" "outputs")
  check "another kind"
    (reports (tableOf types [row "field.add" [.nominal 0, .nominal 0] [.nominal 0] (.restricted none)])
      "field.add" "kind")
  check "a pure row as a law"
    (reports (tableOf types [row "field.add" [.nominal 0, .nominal 0] [.nominal 0] .sampling])
      "field.add" "kind")
  check "a restricted row without its domain row"
    (reports (tableOf types [isNonzero, row "field.nonzero" [.nominal 0] [.nominal 1] (.restricted none)])
      "field.nonzero" "kind")
  check "a restricted row as a pure row"
    (reports (tableOf types [isNonzero, row "field.nonzero" [.nominal 0] [.nominal 1] .pure])
      "field.nonzero" "kind")
  check "a domain row of another name"
    (reports
      (tableOf types [row "field.from_nonzero" [.nominal 1] [.nominal 0] .pure,
        row "field.nonzero" [.nominal 0] [.nominal 1] (.restricted (some 0))])
      "field.nonzero" "kind")
  -- The domain row at another field: `field.is_nonzero` of `bls12-381.fr`, the type row 2.
  let scalarTypes := types ++ [⟨Name.ofString "bls12-381.fr", []⟩]
  let scalarIsNonzero : Operation :=
    ⟨⟨Name.ofString "field.is_nonzero", [.type (.nominal 2)]⟩, ⟨[.nominal 2], [.bool], .pure⟩⟩
  check "the domain row at the same static arguments is admitted"
    (Vocabulary.missing Vocabulary.table (tableOf scalarTypes [isNonzero, nonzero, scalarIsNonzero])).isEmpty
  check "a domain row at other static arguments"
    (reports
      (tableOf scalarTypes [isNonzero, scalarIsNonzero,
        row "field.nonzero" [.nominal 0] [.nominal 1] (.restricted (some 1))])
      "field.nonzero" "kind")
  -- A name of the vocabulary at static arguments at which it has no row: the units are not a
  -- field.
  check "static arguments without a row"
    (reports
      (tableOf types [⟨⟨Name.ofString "field.add", [.type (.nominal 1)]⟩,
        ⟨[.nominal 1, .nominal 1], [.nominal 1], .pure⟩⟩])
      "field.add" "is not a row of the vocabulary")
  -- The core admits a table with another signature: only the vocabulary compares it.
  check "the core admits another signature"
    (elaborate (tableOf types [row "field.add" [.nominal 0] [.nominal 0] .pure])).isOk

end Admission
