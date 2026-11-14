import Zkc.Tests.Core.Declare
import Zkc.Tests.Core.Runs
import Zkc.Tests.Core.Repeats
import Zkc.Tests.Core.Alternatives
import Zkc.Core.Closure
import Zkc.Core.ProofIdentity
import Zkc.Core.VocabularyModel

/-! Checks of the closure of an entry (`Zkc.Core.Closure`) and of the scheme closure
(`Zkc.Core.ProofIdentity`).

- `fixtures/closure.json` has two entries that share nothing. `tally` sums two values of
  `bls12-381.fr` with the function `sum`, sends the sum and reads a field of a record;
  `invert_and_send` inverts a value of `koala-bear` with the function `invert`, which guards
  the domain row `field.is_nonzero` of the restricted row `field.nonzero`, and sends the
  inverse. A variant declaration and a sampling row belong to neither. The kernel computes the
  closure of each entry and finds the package of that entry alone, numbered in post-order
  (`fixtures/closure-tally.json`, `fixtures/closure-invert.json`); the closure of a function
  is that package without its protocol. `fixtures/closure-shuffled.json` lists the same
  definitions and rows in another order, with a type row, a record declaration, an operation
  row and a function that neither entry reaches: its closures are the same packages.
- The closures of every protocol of `fixtures/sumcheck.json`, `fixtures/repeats.json` and
  `fixtures/alternatives.json` elaborate as written, the entry is the last protocol, and the
  closure of a closure at its last protocol is itself.
- On these fixtures an entry and its closure have the same outcomes. No theorem states it
  for every package, and these checks do not stand for one. The kernel evaluates the
  closures of `sums` (`fixtures/repeats.json`) and of `decide` (`fixtures/alternatives.json`) for an arbitrary
  model, which neither package's rows constrain, and finds the values that the checks of the
  original packages state. Lean's interpreter runs the entries and the functions of
  `fixtures/closure.json` and of the shuffled package, the entries of `fixtures/repeats.json`
  and `fixtures/alternatives.json`, and their closures, under the model of the vocabulary's
  rows, which reads a row by its catalogue identity and not by its number, and finds the same
  outcomes. `fixtures/sumcheck.json` names its rows by catalogue domains that the vocabulary
  does not read, and does not run.
- The scheme closure of `fixtures/construction/schnorr.json`, `audit-source.json` and
  `sumcheck.json` with their declarations elaborates, is its own scheme closure, and the
  construction steps succeed on it as on the original. With site rows in the declaration of
  `audit-source`, a function that only a site row names is reached when the entry reaches the
  site row's protocol and not otherwise, and the site rows are renumbered with the functions.
  `fixtures/closure-schnorr-extended.json` is the Schnorr package with a type row, an
  operation row and a function inserted before every other and a protocol after the entry,
  with its declaration renumbered to match: its scheme closure is the Schnorr package's, so
  the two scheme identities are equal, while the two proof identities differ.

A closure that several checks read is proposed by the elaborator's evaluator
(`normal_form`), and the kernel checks that it is the closure; the kernel does not share the
evaluation of a closure between the checks that read it.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ClosureChecks

/-! ## Two unrelated entries -/

namespace TwoEntries

raw_package raw from file "fixtures/closure.json"
raw_package tally from file "fixtures/closure-tally.json"
raw_package invert from file "fixtures/closure-invert.json"
raw_package shuffled from file "fixtures/closure-shuffled.json"

kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl tally_accepted : (elaborateWritten tally).isOk equals true
kernel_refl invert_accepted : (elaborateWritten invert).isOk equals true
kernel_refl shuffled_accepted : (elaborateWritten shuffled).isOk equals true

-- What each entry reaches, in post-order: the type rows of its ports, its callee after the
-- rows the callee applies, a domain row before its restricted row, a record declaration
-- where the body first names it, the entry last.
kernel_refl tally_reached : raw.reached [.protocol 0] equals
  [.typeRow 0, .operation 0, .function 0, .record 0, .protocol 0]
kernel_refl invert_reached : raw.reached [.protocol 1] equals
  [.typeRow 1, .typeRow 2, .operation 2, .operation 3, .operation 4, .function 1, .protocol 1]

-- The closure of each entry is the package of that entry alone.
kernel_refl closure_tally : raw.closure 0 equals tally
kernel_refl closure_invert : raw.closure 1 equals invert

-- The closure of a function is the package of what it reaches, without protocols.
kernel_refl function_closure : raw.functionClosure 1 equals
  ⟨invert.types, [], [], invert.operations, invert.functions, [],
    some ⟨["invert"], [], [], []⟩⟩

-- A closure is its own closure.
kernel_refl tally_closed : tally.closure 0 equals tally
kernel_refl invert_closed : invert.closure 0 equals invert

-- Definitions and rows that an entry does not reach, and the order of the package, change
-- neither its closure nor its numbering.
kernel_refl shuffled_tally : shuffled.closure 1 equals tally
kernel_refl shuffled_invert : shuffled.closure 0 equals invert

#print axioms closure_tally
#print axioms shuffled_tally

end TwoEntries

/-! ## The fixtures of the language -/

namespace Sumcheck

raw_package raw from file "fixtures/sumcheck.json"

-- From `sumcheck`: the rows of its ports, the row of its first instruction, then `round`
-- after the functions it calls and the rows they apply, then `final_check`, then the entry.
kernel_refl reached : raw.renumberingOf [.protocol 1] equals
  ⟨[1, 0], [], [], [11, 1, 2, 3, 4, 5, 6, 7, 10, 0, 8, 9, 12, 13, 14], [0, 1, 2], [0, 1]⟩
kernel_refl round_reached : raw.renumberingOf [.protocol 0] equals
  ⟨[1, 0], [], [], [1, 2, 3, 4, 5, 6, 7, 10, 0, 11, 8, 9, 12], [0, 1], [0]⟩

normal_form closed := raw.closure 1
normal_form round := raw.closure 0

kernel_refl closed_eq : raw.closure 1 equals closed
kernel_refl round_eq : raw.closure 0 equals round
kernel_refl closure_accepted : (elaborateWritten closed).isOk equals true
kernel_refl round_accepted : (elaborateWritten round).isOk equals true
kernel_refl closure_closed : closed.closure 1 equals closed
kernel_refl round_closed : round.closure 0 equals round

end Sumcheck

namespace RepeatsClosure

raw_package raw from file "fixtures/repeats.json"

normal_form sums := raw.closure 1
normal_form squares := raw.closure 0

kernel_refl sums_eq : raw.closure 1 equals sums
kernel_refl squares_eq : raw.closure 0 equals squares
kernel_refl sums_entry : (raw.renumberingOf [.protocol 1]).protocols equals [1]
kernel_refl squares_entry : (raw.renumberingOf [.protocol 0]).protocols equals [0]
kernel_refl sums_accepted : (elaborateWritten sums).isOk equals true
kernel_refl squares_accepted : (elaborateWritten squares).isOk equals true
kernel_refl sums_closed : sums.closure 0 equals sums
kernel_refl squares_closed : squares.closure 0 equals squares

kernel_refl sums_elaborates : (elaborate sums).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw sums sums_elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate sums equals Except.ok typed

abbrev entry :
    Var typed.protocols ⟨2, [⟨.nat, 0⟩, ⟨.nat, 1⟩], [⟨.nat, 0⟩, ⟨.nat, 1⟩], .none, false⟩ :=
  ⟨0, rfl⟩

noncomputable abbrev meaning (model : Model) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get entry []

/-- The closure of `sums` for the side of both roles, on the counts 4 and 4. -/
theorem both_sum (model : Model) :
    meaning model Repeats.both (.cons (4 : Nat) (.cons (4 : Nat) .nil)) =
      .done (.cons (6 : Nat) (.cons (14 : Nat) .nil)) := kernel_rfl%

/-- The closure of `sums` beyond the maximum. -/
theorem both_beyond (model : Model) :
    meaning model Repeats.both (.cons (9 : Nat) (.cons (9 : Nat) .nil)) = .halt .undefined :=
  kernel_rfl%

/-- The entry and its closure have one meaning on these inputs, for every model. -/
theorem same_sum (model : Model) :
    meaning model Repeats.both (.cons (4 : Nat) (.cons (4 : Nat) .nil)) =
      Repeats.meaning model Repeats.sums Repeats.both (.cons (4 : Nat) (.cons (4 : Nat) .nil)) :=
  (both_sum model).trans (Repeats.both_sum model).symm

theorem same_beyond (model : Model) :
    meaning model Repeats.both (.cons (9 : Nat) (.cons (9 : Nat) .nil)) =
      Repeats.meaning model Repeats.sums Repeats.both (.cons (9 : Nat) (.cons (9 : Nat) .nil)) :=
  (both_beyond model).trans (Repeats.both_beyond model).symm

#print axioms same_sum

end RepeatsClosure

namespace AlternativesClosure

raw_package raw from file "fixtures/alternatives.json"

-- `never` names the second variant declaration only: in its closure it is the first.
kernel_refl never_closure : raw.closure 1 equals
  ⟨[], [], [⟨[]⟩], [], [],
    [⟨false, 2, [⟨.variant 0 [], 0⟩, ⟨.variant 0 [], 1⟩, ⟨.nat, 0⟩], [⟨.nat, 0⟩], [],
      .step (.choose [0, 1] [0, 1] (.alternative 0 []) [2] [⟨.nat, 0⟩] .none) (.ret [3])⟩],
    some ⟨[], ["never"], [["left", "right"]], [[]]⟩⟩

normal_form decideOnly := raw.closure 0
normal_form neverOnly := raw.closure 1
normal_form swappedOnly := raw.closure 2

kernel_refl decide_eq : raw.closure 0 equals decideOnly
kernel_refl never_eq : raw.closure 1 equals neverOnly
kernel_refl swapped_eq : raw.closure 2 equals swappedOnly
kernel_refl swapped_entry : (raw.renumberingOf [.protocol 2]).protocols equals [0, 2]
kernel_refl swapped_accepted : (elaborateWritten swappedOnly).isOk equals true
kernel_refl decide_accepted : (elaborateWritten decideOnly).isOk equals true
kernel_refl never_accepted : (elaborateWritten neverOnly).isOk equals true
kernel_refl swapped_closed : swappedOnly.closure 1 equals swappedOnly
kernel_refl decide_closed : decideOnly.closure 0 equals decideOnly
kernel_refl never_closed : neverOnly.closure 0 equals neverOnly

kernel_refl decide_elaborates : (elaborate decideOnly).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw decideOnly decide_elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate decideOnly equals Except.ok typed

abbrev entry :
    Var typed.protocols
      ⟨2, [⟨Alternatives.choice, 0⟩, ⟨Alternatives.choice, 1⟩], [⟨.nat, 1⟩, ⟨.nat, 0⟩], .none,
        false⟩ :=
  ⟨0, rfl⟩

noncomputable abbrev meaning (model : Model) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get entry []

theorem both_first (model : Model) :
    meaning model Alternatives.both (.cons (.inl (3 : Nat)) (.cons (.inl (4 : Nat)) .nil)) =
      .done (.cons (10 : Nat) (.cons (6 : Nat) .nil)) := kernel_rfl%

theorem both_disagree (model : Model) :
    meaning model Alternatives.both (.cons (.inl (3 : Nat)) (.cons (.inr (.inl true)) .nil)) =
      .halt .incomplete := kernel_rfl%

/-- `decide` and its closure have one meaning on these inputs, for every model. -/
theorem same_first (model : Model) :
    meaning model Alternatives.both (.cons (.inl (3 : Nat)) (.cons (.inl (4 : Nat)) .nil)) =
      Alternatives.meaning model Alternatives.decide Alternatives.both
        (.cons (.inl (3 : Nat)) (.cons (.inl (4 : Nat)) .nil)) :=
  (both_first model).trans (Alternatives.both_first model).symm

theorem same_disagree (model : Model) :
    meaning model Alternatives.both (.cons (.inl (3 : Nat)) (.cons (.inr (.inl true)) .nil)) =
      Alternatives.meaning model Alternatives.decide Alternatives.both
        (.cons (.inl (3 : Nat)) (.cons (.inr (.inl true)) .nil)) :=
  (both_disagree model).trans (Alternatives.both_disagree model).symm

#print axioms same_first

end AlternativesClosure

/-! ## Runs under the model of the vocabulary's rows

These run in Lean's interpreter, not in the kernel. -/

namespace Runs

open Zkc.Core.Concrete Zkc.Core.Vocabulary

def readPackage (path : String) : IO Raw.Package := do
  match Raw.parsePackage (← IO.FS.readFile path) with
  | .ok raw => pure raw
  | .error message => throw (IO.userError message)

def typedOf (raw : Raw.Package) : IO Typed :=
  match elaborate raw with
  | .ok typed => pure typed
  | .error refusal => throw (IO.userError s!"refused: {repr refusal}")

def readDeclaration (path : String) : IO Raw.Declaration := do
  match Raw.parseDeclaration (← IO.FS.readFile path) with
  | .ok declaration => pure declaration
  | .error message => throw (IO.userError message)

def describe : Vocabulary.Run → String
  | .returned outputs => s!"returned {reprStr outputs}"
  | .stopped reason => s!"stopped {reprStr reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

/-- The last protocol of two packages, run on the same inputs, ends alike, as expected, and
each role's program agrees with the grouped run. -/
def sameEntry (first second : Raw.Package) (inputs : List Datum)
    (expected : Zkc.Core.Runs.Ended) : IO Unit := do
  let first ← IO.ofExcept (Zkc.Core.Runs.interactive (← typedOf first) inputs [] 0 1)
  let second ← IO.ofExcept (Zkc.Core.Runs.interactive (← typedOf second) inputs [] 0 1)
  unless first.agrees && second.agrees && first.grouped.same second.grouped &&
      first.grouped.same expected do
    throw (IO.userError
      s!"{first.grouped.describe} and {second.grouped.describe}, not {expected.describe}")

/-- A function of one package and a function of another, run on the same inputs, end alike,
as expected. -/
def sameFunction (first : Raw.Package) (firstNumber : Nat) (second : Raw.Package)
    (secondNumber : Nat) (inputs : List Datum) (expected : String) : IO Unit := do
  let first := describe (runData table first firstNumber inputs)
  let second := describe (runData table second secondNumber inputs)
  unless first == second && first == expected do
    throw (IO.userError s!"{first} and {second}, not {expected}")

#eval show IO Unit from do
  let raw ← readPackage (package_file "fixtures/closure.json")
  let shuffled ← readPackage (package_file "fixtures/closure-shuffled.json")
  let inverse := (koalaBearOrder + 1) / 2
  -- The last protocol of `fixtures/closure.json` is `invert_and_send`, that of the shuffled
  -- package is `tally`.
  sameEntry raw (raw.closure 1) [.number 2] (.returned [.number inverse])
  sameEntry raw (raw.closure 1) [.number 0] (.stopped .reject)
  sameEntry shuffled (raw.closure 0) [.number 3, .number 4] (.returned [.number 7, .number 5])
  sameEntry shuffled (shuffled.closure 1) [.number 3, .number 4]
    (.returned [.number 7, .number 5])
  sameFunction raw 1 (raw.functionClosure 1) 0 [.number 2]
    s!"returned {reprStr [Datum.number inverse]}"
  sameFunction raw 1 (raw.functionClosure 1) 0 [.number 0] "stopped PIR.Stop.reject"
  sameFunction raw 0 (raw.functionClosure 0) 0 [.number 3, .number 4]
    s!"returned {reprStr [Datum.number 7]}"
  sameFunction shuffled 0 (raw.functionClosure 1) 0 [.number 5]
    (describe (runData table raw 1 [.number 5]))

#eval show IO Unit from do
  let repeats ← readPackage (package_file "fixtures/repeats.json")
  sameEntry repeats (repeats.closure 1) [.number 4, .number 4] (.returned [.number 6, .number 14])
  sameEntry repeats (repeats.closure 1) [.number 9, .number 9] (.stopped .undefined)
  let alternatives ← readPackage (package_file "fixtures/alternatives.json")
  sameEntry alternatives (alternatives.closure 2)
    [.sequence [.number 0, .number 3], .sequence [.number 0, .number 4]]
    (.returned [.number 11, .number 8])
  sameEntry alternatives (alternatives.closure 2)
    [.sequence [.number 1, .number 0], .sequence [.number 1, .number 1]]
    (.returned [.number 21, .number 1])

end Runs

/-! ## Scheme closures -/

namespace SchemeSchnorr

raw_package raw from file "fixtures/construction/schnorr.json"
raw_declaration declaration from file "fixtures/construction/schnorr.declaration.json"
raw_package extended from file "fixtures/closure-schnorr-extended.json"
raw_declaration extendedDeclaration from file
  "fixtures/closure-schnorr-extended.declaration.json"

normal_form scheme := raw.schemeClosure declaration

kernel_refl scheme_eq : raw.schemeClosure declaration equals scheme
kernel_refl accepted : (elaborateWritten scheme.1).isOk equals true
kernel_refl elaborates : (elaborate scheme.1).isOk equals true
kernel_refl closed : scheme.1.schemeClosure scheme.2 equals scheme
kernel_refl entry_last : scheme.2.entry equals scheme.1.protocols.length - 1

noncomputable def typed : Typed := Typed.ofRaw scheme.1 elaborates

kernel_refl constructs : (steppedProtocols typed (construct typed scheme.2)).isOk equals true

kernel_refl original_elaborates : (elaborate raw).isOk equals true

noncomputable def originalTyped : Typed := Typed.ofRaw raw original_elaborates

kernel_refl original_constructs :
  (steppedProtocols originalTyped (construct originalTyped declaration)).isOk equals true

kernel_refl extended_elaborates : (elaborate extended).isOk equals true

-- The inserted definitions and rows do not change the scheme closure.
kernel_refl extended_scheme : extended.schemeClosure extendedDeclaration equals scheme

/-- So they do not change the scheme identity. -/
theorem extended_identity :
    Raw.schemeIdentity extended extendedDeclaration = Raw.schemeIdentity raw declaration :=
  Raw.schemeIdentity_eq_of_schemeClosure_eq (extended_scheme.trans scheme_eq.symm)

#print axioms extended_scheme
#print axioms extended_identity

-- The identities as bytes: the scheme identities are equal and the proof identities of the
-- two packages are not (Lean's interpreter).
#eval show IO Unit from do
  let raw ← Runs.readPackage (package_file "fixtures/construction/schnorr.json")
  let declaration ← Runs.readDeclaration (package_file "fixtures/construction/schnorr.declaration.json")
  let extended ← Runs.readPackage (package_file "fixtures/closure-schnorr-extended.json")
  let extendedDeclaration ←
    Runs.readDeclaration (package_file "fixtures/closure-schnorr-extended.declaration.json")
  unless Raw.schemeIdentity extended extendedDeclaration == Raw.schemeIdentity raw declaration do
    throw (IO.userError "the scheme identities differ")
  if Raw.proofIdentity extended extendedDeclaration == Raw.proofIdentity raw declaration then
    throw (IO.userError "the proof identities are equal")

end SchemeSchnorr

namespace SchemeAuditSource

raw_package raw from file "fixtures/construction/audit-source.json"
raw_declaration declaration from file "fixtures/construction/audit-source.declaration.json"

normal_form scheme := raw.schemeClosure declaration

kernel_refl scheme_eq : raw.schemeClosure declaration equals scheme
kernel_refl elaborates : (elaborate scheme.1).isOk equals true
kernel_refl closed : scheme.1.schemeClosure scheme.2 equals scheme
kernel_refl entry_last : scheme.2.entry equals scheme.1.protocols.length - 1

noncomputable def typed : Typed := Typed.ofRaw scheme.1 elaborates

kernel_refl constructs : (steppedProtocols typed (construct typed scheme.2)).isOk equals true

kernel_refl original_elaborates : (elaborate raw).isOk equals true

noncomputable def originalTyped : Typed := Typed.ofRaw raw original_elaborates

kernel_refl original_constructs :
  (steppedProtocols originalTyped (construct originalTyped declaration)).isOk equals true

/-- The declaration with one absorbing function, and site rows that name the function of
`bool` messages for the first site of `announce` and the function of `fin 2` messages for the
first site of `challenge`, for the image with transcript roles 0 and 1. -/
noncomputable abbrev withSites : Raw.Declaration :=
  { declaration with
    suite := match declaration.suite with
      | some (.source state start _ deriving_ _) =>
          some (.source state start [0] deriving_
            [[⟨0, 1, none⟩], [], [⟨0, 2, some (0, 1)⟩], []])
      | other => other }

/-- The functions that the suite of a declaration names: the start function, the absorbing
functions, the deriving functions and the site rows. -/
abbrev suiteFunctions (declaration : Raw.Declaration) :
    Option (Nat × List Nat × List Nat × List (List Raw.SiteRow)) :=
  match declaration.suite with
  | some (.source _ start absorbing deriving_ sites) =>
      some (start, absorbing, deriving_.map (·.2), sites)
  | _ => none

-- The entry reaches every protocol. The start function is listed after the functions it
-- calls, then the absorbing and the deriving function, then the function that only a site
-- row names; the site rows are renumbered with it.
kernel_refl site_functions :
  suiteFunctions (raw.schemeClosure withSites).2 equals
    some (2, [1], [3], [[⟨0, 4, none⟩], [], [⟨0, 0, some (0, 1)⟩], []])

-- With `challenge` as the entry, only its site rows count: the function that the site rows
-- of `announce` name is not reached.
kernel_refl site_functions_challenge :
  suiteFunctions (raw.schemeClosure { withSites with entry := 2 }).2 equals
    some (2, [1], [3], [[⟨0, 0, some (0, 1)⟩]])
kernel_refl functions_challenge :
  (raw.schemeClosure { withSites with entry := 2 }).1.functions.length equals 4

-- Both scheme closures with site rows are their own scheme closures.
normal_form siteScheme := raw.schemeClosure withSites
normal_form challengeScheme := raw.schemeClosure { withSites with entry := 2 }

kernel_refl site_scheme_eq : raw.schemeClosure withSites equals siteScheme
kernel_refl challenge_scheme_eq :
  raw.schemeClosure { withSites with entry := 2 } equals challengeScheme
kernel_refl site_scheme_closed : siteScheme.1.schemeClosure siteScheme.2 equals siteScheme
kernel_refl challenge_scheme_closed :
  challengeScheme.1.schemeClosure challengeScheme.2 equals challengeScheme

end SchemeAuditSource

namespace SchemeSumcheck

raw_package raw from file "fixtures/construction/sumcheck.json"
raw_declaration declaration from file "fixtures/construction/sumcheck.declaration.json"

normal_form scheme := raw.schemeClosure declaration

kernel_refl scheme_eq : raw.schemeClosure declaration equals scheme
kernel_refl elaborates : (elaborate scheme.1).isOk equals true
kernel_refl closed : scheme.1.schemeClosure scheme.2 equals scheme
kernel_refl entry_last : scheme.2.entry equals scheme.1.protocols.length - 1

noncomputable def typed : Typed := Typed.ofRaw scheme.1 elaborates

kernel_refl constructs : (steppedProtocols typed (construct typed scheme.2)).isOk equals true

kernel_refl original_elaborates : (elaborate raw).isOk equals true

noncomputable def originalTyped : Typed := Typed.ofRaw raw original_elaborates

kernel_refl original_constructs :
  (steppedProtocols originalTyped (construct originalTyped declaration)).isOk equals true

end SchemeSumcheck

end ClosureChecks
