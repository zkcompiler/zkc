module

public import Zkc.Core.DerivedScheme
public import Zkc.Core.CanonicalLayoutValues

public section

/-! Completeness of the scheme that the construction steps derive from a package, in the
model of the vocabulary.

`construct_complete` (`Zkc.Core.DerivedScheme`) is for an arbitrary model and takes the laws
of the layout as a premise. `Vocabulary.canonicalLaws` (`Zkc.Core.CanonicalLayoutLaws`) gives
those laws in the model of the vocabulary's rows of a package (`Vocabulary.model`), for the
layout of a declaration that names the rows of the canonical layout. This module joins the
two.

**The statements.**

- `Vocabulary.construct_complete`: the pipeline of a declaration (`construct`: the
  Fiat–Shamir step, then the serialize step) on a package.
- `Vocabulary.serializeProtocols_complete`: the serialize step of a declaration alone, on a
  package whose Fiat–Shamir step is authored. It has no suite and no condition on the
  inputs.

**What a caller supplies.** Of the package and the declaration, each decided by evaluation:

- the core elaborates the package (`elaborate package = .ok typed`);
- the rows of the package are the vocabulary's (`mismatches Vocabulary.table package = []`);
- the rows that the declaration names for its layout have the names of the rows of the
  canonical layout (`declaration.namesCanonical package = true`);
- the equations that say which programs were constructed: the result of the pipeline, the
  layout that the declaration names, the position of the declared entry, the projection of
  the result and its two role programs.

Of the model, asked only of a declaration that needs it:

- `PointCompression`, when a row that the declared layout names to put or to take a value is
  at a type with a point of G1 in it (`declaration.movesPoint`);
- that the suite returns (`Raw.Declaration.SuiteReturns`), when the suite of the declaration
  calls functions of the package (`declaration.suiteCallsFunctions`). A catalogue suite has
  rows only, and a row returns, so a declaration with a catalogue suite supplies nothing.

Of a run:

- inputs on which the prover's and the verifier's copies of the statement are equal
  (`StatementCopiesEqual`);
- that the layout writes every value that the interactive entry for the prover alone sends,
  whatever it receives and samples (`EverySend` of `Vocabulary.writes`);
- completeness of the interactive entry for the prover and the verifier together
  (`GroupedComplete`).

Nothing is assumed of the layout besides `PointCompression`: its laws are derived.

**What is not proved here.** `PointCompression`; that the values that a given protocol sends
are written (`Zkc.Core.CanonicalLayoutValues` reduces it for the rows of the arithmetic of a
prime field and for a multiple of a point); completeness of a given interactive protocol.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-! ## The suite of a declaration -/

/-- Whether the suite of a declaration calls functions of the package: a suite written in
source. A catalogue suite has rows only, and a declaration without a suite has none. -/
@[expose] def Raw.Declaration.suiteCallsFunctions (declaration : Raw.Declaration) : Bool :=
  match declaration.suite with
  | some (.source ..) => true
  | _ => false

/-- The suite that a declaration names over the rows and the functions of a typed package
returns in a model: every absorber, deriver and starter that it gives returns on every
input, with the meanings of the package's own functions. -/
@[expose] def Raw.Declaration.SuiteReturns (declaration : Raw.Declaration) (typed : Typed)
    (model : Model) : Prop :=
  ∀ suite : Zkc.Core.Suite (typed.table.map (·.signature)) typed.functions,
    declaration.suite.map
        (Zkc.Core.Suite.ofRaw (tableScope (typed.table.map (·.signature)))
          (tableScope typed.functions)) =
      some suite →
    suite.Returns (typed.program.functionTable model)

/-- The suite of a declaration that calls no function of the package returns, in every
model: a catalogue suite has rows only, and a pure row is a total function. -/
theorem Raw.Declaration.suiteReturns_of_rows {declaration : Raw.Declaration}
    (rowsOnly : declaration.suiteCallsFunctions = false) (typed : Typed) (model : Model) :
    declaration.SuiteReturns typed model := by
  intro suite isSuite
  unfold Raw.Declaration.suiteCallsFunctions at rowsOnly
  cases found : declaration.suite with
  | none =>
    rw [found] at isSuite
    cases isSuite
  | some raw =>
    rw [found] at isSuite rowsOnly
    cases raw with
    | catalogue state label start absorbing deriving_ identity =>
      cases Option.some.inj isSuite
      exact Zkc.Core.Suite.ofRaw_catalogue_returns _ _ state label start absorbing deriving_
        identity _
    | source state start absorbing deriving_ sites => cases rowsOnly

/-- The suite of a declaration returns in a model in which every function of the package
returns on every input. -/
theorem Raw.Declaration.suiteReturns_of_functions (declaration : Raw.Declaration) {typed : Typed}
    {model : Model} (returns : FunctionsReturn (typed.program.functionTable model)) :
    declaration.SuiteReturns typed model :=
  fun suite _ => returns.suite suite

namespace Vocabulary

-- The hypotheses under the quantifier of a statement are named for what they say.
set_option linter.unusedVariables false

/-! ## The scheme of a declaration, in the model of the vocabulary -/

/-- Completeness of the scheme that the pipeline of a declaration derives from a package
(`construct`: the Fiat–Shamir step, then the serialize step), in the model of the
vocabulary's rows of the package.

The premises about the package and the declaration are decided by evaluation: the core
elaborates the package, its rows are the vocabulary's, the rows that the declaration names
for its layout have the names of the rows of the canonical layout, and the equations that
say which programs were constructed (the result of the pipeline, the layout that the
declaration names, the declared entry, the projection of the result and its two role
programs; the newest protocol of the result is the constructed entry).

Two premises are about the model, each asked only of a declaration that needs it: the
compressed encoding of G1, when the declared layout puts or takes a value of a type with a
point of G1 in it; and that the suite returns, when the suite calls functions of the
package.

Then, for inputs of a run of the declared entry for the prover and the verifier together on
which their copies of the statement are equal: when the layout writes every value that the
interactive entry sends for the prover alone, and the interactive entry is complete for
every sampler with the verifier's share of its outputs accepted, then for every sampler the
constructed prover, on the prover's share of the inputs, returns a proof before its other
outputs, and the constructed verifier, on that proof before the verifier's share of the
inputs, returns outputs that are accepted, read as the outputs of the interactive verifier
(`outputsWithoutProof`: the proof is an output of the prover).

No premise is about the layout besides the compressed encoding: its laws in the model are
derived (`canonicalLaws`). -/
theorem construct_complete {package : Raw.Package} {typed : Typed}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = []) (declaration : Raw.Declaration)
    (named : declaration.namesCanonical package = true)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (constructs : construct typed declaration = .ok serialized)
    (layout : Layout (typed.table.map (·.signature)))
    (isLayout : declaration.layout.bind
        (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    {header : ProtocolHeader} (declared : Var typed.protocols header)
    (isEntry : declared.index = typed.protocols.length - 1 - declaration.entry)
    (derived : Projected (typed.table.map (·.signature)) typed.functions serialized.headers)
    (projectsDerived : projectProtocols serialized.protocols = .ok derived)
    (compression : declaration.movesPoint Vocabulary.table package = true → PointCompression)
    (returns : declaration.suiteCallsFunctions = true →
      declaration.SuiteReturns typed (model Vocabulary.table package)) :
    ∃ constructed : Var serialized.headers
        ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
          header),
      constructed.index = 0 ∧
      ∀ (derivedProver : Var derived.headers
          (roleHeader declaration.roles.prover
            ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
              header)))
        (derivedVerifier : Var derived.headers
          (roleHeader declaration.roles.verifier
            ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
              header)))
        (namedDerivedProver :
          derived.callees.find constructed declaration.roles.prover = some derivedProver)
        (namedDerivedVerifier :
          derived.callees.find constructed declaration.roles.verifier = some derivedVerifier)
        (inputs : Values
          (SideValue (model Vocabulary.table package)
            ((single declaration.roles.prover).union (single declaration.roles.verifier)))
          header.inputs)
        (agrees : StatementCopiesEqual (model Vocabulary.table package)
          ((single declaration.roles.prover).union (single declaration.roles.verifier))
          declaration.roles header inputs)
        (writable : EverySend (model := model Vocabulary.table package)
          (fun type value => writes Vocabulary.table package type value = true) (fun _ => True)
          ((typed.program.protocolTable (model Vocabulary.table package) Identities.written).get
            declared [] (single declaration.roles.prover)
            (leftValues (model Vocabulary.table package) (single declaration.roles.prover)
              (single declaration.roles.verifier) inputs)))
        (acceptedInteractive :
          Values (model Vocabulary.table package).Value
            (own declaration.roles.verifier header.outputs) → Prop)
        (complete : GroupedComplete
          ((typed.program.protocolTable (model Vocabulary.table package) Identities.written).get
            declared [] ((single declaration.roles.prover).union (single declaration.roles.verifier))
            inputs)
          fun outputs =>
            acceptedInteractive
              (verifierShare (model Vocabulary.table package) declaration.roles outputs)),
        DerivedComplete
          (((derived.programs.table (model Vocabulary.table package)
                (typed.program.functionTable (model Vocabulary.table package))
                serialized.identities).get derivedProver []
              (inputsWithoutProof (model Vocabulary.table package)
                (construct_roles_differ typed declaration serialized constructs)
                (proverShare (model Vocabulary.table package) declaration.roles inputs))).bind
            fun outputs =>
              .done (provedOutputs (model Vocabulary.table package) declaration.roles.prover
                outputs))
          (fun proof =>
            (derived.programs.table (model Vocabulary.table package)
                (typed.program.functionTable (model Vocabulary.table package))
                serialized.identities).get derivedVerifier []
              (proofInputs (model Vocabulary.table package) declaration.roles.verifier proof
                (verifierShare (model Vocabulary.table package) declaration.roles inputs)))
          (fun outputs =>
            acceptedInteractive (outputsWithoutProof (model Vocabulary.table package) outputs)) := by
  obtain ⟨suite, _, _, namesSuite, _, _, _, _⟩ :=
    construct_steps typed declaration serialized constructs
  have suiteReturns : suite.Returns (typed.program.functionTable (model Vocabulary.table package)) := by
    cases calls : declaration.suiteCallsFunctions with
    | true => exact returns calls suite namesSuite
    | false => exact Raw.Declaration.suiteReturns_of_rows calls typed _ suite namesSuite
  obtain ⟨constructed, newest, derives⟩ := Zkc.Core.construct_complete
    (model := model Vocabulary.table package) typed declaration serialized constructs suite
    namesSuite layout isLayout declared isEntry derived projectsDerived
  refine ⟨constructed, newest, ?_⟩
  intro derivedProver derivedVerifier namedDerivedProver namedDerivedVerifier inputs agrees writable
    acceptedInteractive complete
  exact derives derivedProver derivedVerifier namedDerivedProver namedDerivedVerifier suiteReturns
    (canonicalLaws elaborated matched isLayout named compression) inputs agrees writable
    acceptedInteractive complete

/-- Completeness of the scheme that the serialize step of a declaration derives from a
package whose Fiat–Shamir step is authored (`serializeProtocols`: the entry is the newest
protocol), in the model of the vocabulary's rows of the package.

The premises about the package and the declaration are decided by evaluation: the core
elaborates the package, its rows are the vocabulary's, the rows that the declaration names
for its layout have the names of the rows of the canonical layout, and the equations that
say which programs were constructed (the result of the step, the layout that the declaration
names, the entry, the projection of the result and its two role programs). The compressed
encoding of G1 is asked only when the declared layout puts or takes a value of a type with a
point of G1 in it.

Then, for the inputs of a run of the entry for the prover and the verifier together: when
the layout writes every value that the entry sends for the prover alone, and the entry is
complete for every sampler with the verifier's share of its outputs accepted, the derived
scheme is complete, with the outputs of the derived verifier accepted when they are, read as
the outputs of the interactive verifier. There is no suite and no condition on the
inputs. -/
theorem serializeProtocols_complete {package : Raw.Package} {typed : Typed}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = []) (declaration : Raw.Declaration)
    (named : declaration.namesCanonical package = true)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (serializes : serializeProtocols declaration Identities.written typed.program.protocols =
      .ok serialized)
    (layout : Layout (typed.table.map (·.signature)))
    (isLayout : declaration.layout.bind
        (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    {header : ProtocolHeader} (declared : Var typed.protocols header)
    (isEntry : declared.index = 0)
    (derived : Projected (typed.table.map (·.signature)) typed.functions serialized.headers)
    (projectsDerived : projectProtocols serialized.protocols = .ok derived)
    (compression : declaration.movesPoint Vocabulary.table package = true → PointCompression) :
    ∃ constructed : Var serialized.headers
        ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
          header),
      constructed.index = 0 ∧
      ∀ (derivedProver : Var derived.headers
          (roleHeader declaration.roles.prover
            ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
              header)))
        (derivedVerifier : Var derived.headers
          (roleHeader declaration.roles.verifier
            ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
              header)))
        (namedDerivedProver :
          derived.callees.find constructed declaration.roles.prover = some derivedProver)
        (namedDerivedVerifier :
          derived.callees.find constructed declaration.roles.verifier = some derivedVerifier)
        (inputs : Values
          (SideValue (model Vocabulary.table package)
            ((single declaration.roles.prover).union (single declaration.roles.verifier)))
          header.inputs)
        (writable : EverySend (model := model Vocabulary.table package)
          (fun type value => writes Vocabulary.table package type value = true) (fun _ => True)
          ((typed.program.protocolTable (model Vocabulary.table package) Identities.written).get
            declared [] (single declaration.roles.prover)
            (leftValues (model Vocabulary.table package) (single declaration.roles.prover)
              (single declaration.roles.verifier) inputs)))
        (acceptedInteractive :
          Values (model Vocabulary.table package).Value
            (own declaration.roles.verifier header.outputs) → Prop)
        (complete : GroupedComplete
          ((typed.program.protocolTable (model Vocabulary.table package) Identities.written).get
            declared [] ((single declaration.roles.prover).union (single declaration.roles.verifier))
            inputs)
          fun outputs =>
            acceptedInteractive
              (verifierShare (model Vocabulary.table package) declaration.roles outputs)),
        DerivedComplete
          (((derived.programs.table (model Vocabulary.table package)
                (typed.program.functionTable (model Vocabulary.table package))
                serialized.identities).get derivedProver []
              (inputsWithoutProof (model Vocabulary.table package)
                (stepProtocols_roles_differ Identities.written (typed.protocols.length - 1)
                  declaration.roles typed.program.protocols serialized
                  (serializeProtocols_steps declaration Identities.written
                    typed.program.protocols layout isLayout serialized serializes))
                (proverShare (model Vocabulary.table package) declaration.roles inputs))).bind
            fun outputs =>
              .done (provedOutputs (model Vocabulary.table package) declaration.roles.prover
                outputs))
          (fun proof =>
            (derived.programs.table (model Vocabulary.table package)
                (typed.program.functionTable (model Vocabulary.table package))
                serialized.identities).get derivedVerifier []
              (proofInputs (model Vocabulary.table package) declaration.roles.verifier proof
                (verifierShare (model Vocabulary.table package) declaration.roles inputs)))
          (fun outputs =>
            acceptedInteractive (outputsWithoutProof (model Vocabulary.table package) outputs)) := by
  obtain ⟨constructed, newest, derives⟩ := Zkc.Core.serializeProtocols_complete
    (model := model Vocabulary.table package) declaration Identities.written typed.program
    serialized serializes layout isLayout declared isEntry derived projectsDerived
  refine ⟨constructed, newest, ?_⟩
  intro derivedProver derivedVerifier namedDerivedProver namedDerivedVerifier inputs writable
    acceptedInteractive complete
  exact derives derivedProver derivedVerifier namedDerivedProver namedDerivedVerifier
    (canonicalLaws elaborated matched isLayout named compression) inputs writable
    acceptedInteractive complete

end Vocabulary

end Zkc.Core
