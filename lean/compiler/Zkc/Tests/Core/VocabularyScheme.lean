import Zkc.Tests.Core.DerivedScheme
import Zkc.Tests.Core.CanonicalLayoutLaws
import Zkc.Core.VocabularyScheme

/-! Completeness of the scheme that the construction steps derive from a package, in the model
of the vocabulary: the two statements of `Zkc.Core.VocabularyScheme` at packages.

`Vocabulary.construct_complete` joins `construct_complete` with the laws of the canonical
layout (`Vocabulary.canonicalLaws`); `Vocabulary.serializeProtocols_complete` is its variant
for the serialize step alone. At each package below the premises about the package and its
declaration are closed equations that the kernel evaluates: the core elaborates the package,
its rows are the vocabulary's, the declared rows have the names of the rows of the canonical
layout, the result of the pipeline, the layout that the declaration names, the position of
the entry, the projection of the result and its two role programs. A catalogue suite needs
no premise.

- **The frontend's scheme `Proof = Schnorr<G1>`** (`Schnorr`). The fixtures
  `fixtures/construction/schnorr-frontend-scheme.json` and
  `schnorr-frontend-scheme.declaration.json` are the files `scheme-Proof.json` and
  `scheme-Proof.declaration.json` that the frontend's tool writes for
  `examples/schnorr_example.zkc` of the repository, byte for byte. They are written from
  `lean/compiler` by

      lake exe zkc-check types --library ../../libraries --library ../../examples \
        --library ../../examples/support --packages <directory> ../../examples/schnorr_example.zkc

  The package names the vocabulary's rows of the field `bls12-381.fr`, of the group
  `bls12-381.g1`, of the suite `suite.merlin3.bls12-381.fr64be/0` and of the canonical layout
  over bytes. The prover sends a point, so the laws take the compressed encoding of G1. What
  the theorem leaves (`Schnorr.complete`) is exactly: `PointCompression`;
  `GroupClosedUnderMultiples`, that a multiple of a point of the group is of the group; the
  condition on the inputs, that the prover's and the verifier's copies of the base and of the
  point are equal and that the prover's base is a point of the group; and completeness of the
  interactive entry. The premise about the messages is discharged from these: it is exactly
  that every multiple of the prover's base is a point of the group (`Schnorr.writable_iff`);
  the response is a result of `field.add` and needs nothing. Completeness of the interactive
  entry is exactly the verifier's equation in the model's rows at every nonce and every
  challenge (`Schnorr.interactive_complete_iff`, and `Schnorr.complete_of_equation` for the
  theorem with that equation as its hypothesis); the kernel evaluates it to `true` at the
  generator, the scalar 7 and its point, and to `false` with the scalar 8, on which the
  interactive entry is not complete.
- **`fixtures/construction/collecting.json`** (`Collecting`). Its rows are the vocabulary's
  and no message has a point: there is no premise about the layout at all. The premise about
  the messages is discharged at every input (`Collecting.writable`): the prover sends results
  of `field.add` and `field.mul`, which the layout writes whatever they are given, in three
  rounds, and then receives as many coins as its count, or stops `undefined` when the count is
  above the maximum 4 of the loop; the kernel evaluates the entry for the prover alone at
  each count up to 4 and at every count above. What the theorem leaves
  (`Collecting.complete`) is the condition on the inputs, which inputs with one challenge
  and one count satisfy (`Collecting.complete_honest`), and completeness of the interactive
  entry.
- **The frontend's scheme `Proof = Doubling`** (`Doubling`): every premise at once. The
  fixtures `doubling-frontend-scheme.json` and `doubling-frontend-scheme.declaration.json`
  are what the same command writes for `fixtures/construction/doubling-frontend-scheme.zkc`
  (with `--library R/lib` alone): a protocol in which the prover sends a `bool`, the verifier
  draws a challenge of the field and the prover sends the challenge added to itself. No
  message has a point, the suite is a catalogue suite, the entry has no statement, the layout
  writes both messages, and the interactive entry returns on every run. The theorem gives
  completeness of the constructed prover and verifier without a hypothesis
  (`Doubling.complete`): its premises hold together of a package that the frontend printed.
- **The serialize step alone** (`Units`): `Vocabulary.serializeProtocols_complete` at
  `fixtures/construction/units.json`, whose declaration has no suite, with every premise
  discharged and no hypothesis: the derived verifier returns the collection that the prover
  holds (`Units.complete`).
- **The premises that are asked only of some declarations.** `suiteCallsFunctions` is `false`
  at the declarations above and `true` at `schnorr-source`, whose suite returns because its
  functions return. The executable check of `GroupClosedUnderMultiples`: multiples of
  multiples of the generator are of the group; and a point of the curve outside the group has
  a multiple outside it, so the condition that the prover's base is of the group is needed.

What is not checked here: `PointCompression` and `GroupClosedUnderMultiples` (their
executable checks are here and in `Tests/Core/CanonicalLayout.lean`); the verifier's
equation of Schnorr at every nonce and challenge; completeness of the interactive entry of
`collecting`.

The axioms of every theorem of `Zkc.Core.VocabularyScheme`, of the statements that this change
made public or restated, and of the checks are printed at the end. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core
open Zkc.Core.Concrete (Datum)

namespace VocabularyScheme

open Threading (okValue okValue_eq)
open CanonicalLayoutLaws (declared_get)

/-! ## The frontend's scheme `Proof = Schnorr<G1>` -/

namespace Schnorr

raw_package raw from file "fixtures/construction/schnorr-frontend-scheme.json"
raw_declaration declaration from file
  "fixtures/construction/schnorr-frontend-scheme.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

/-- The model of the vocabulary's rows of the package. -/
noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

-- The rows of the package are the vocabulary's; the rows that the declaration names have the
-- names of the rows of the canonical layout; a row that it names is at a type with a point of
-- G1 in it; and its suite is a catalogue suite.
kernel_refl matched : Vocabulary.mismatches Vocabulary.table raw equals []

kernel_refl named : declaration.namesCanonical raw equals true

kernel_refl moves_point : declaration.movesPoint Vocabulary.table raw equals true

kernel_refl rows_only : declaration.suiteCallsFunctions equals false

-- The entry is the protocol 0, the prover the role 0 and the verifier the role 1.
kernel_refl roles_declared : (declaration.entry, declaration.prover, declaration.verifier) equals
  (0, 0, 1)

kernel_refl layout_declared :
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome equals true

/-- The layout of the declaration, over the rows of the package. -/
noncomputable def layout : Layout operations :=
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).get layout_declared

theorem declared :
    declaration.layout.bind (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) =
      some layout :=
  declared_get declaration layout_declared

kernel_refl construct_accepts : (construct typed declaration).isOk equals true

/-- The result of the pipeline of the declaration. -/
noncomputable def serialized : Stepped typed.typeTable operations typed.functions :=
  okValue (construct typed declaration) construct_accepts

theorem constructs : construct typed declaration = .ok serialized := okValue_eq _ _

kernel_refl result_projects : (projectProtocols serialized.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def derived : Projected operations typed.functions serialized.headers :=
  okValue (projectProtocols serialized.protocols) result_projects

/-- The header of the entry `Schnorr<G = G1>`, the one protocol of the package, and the
entry. -/
noncomputable abbrev header : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev entry : Var typed.protocols header := ⟨0, kernel_rfl%⟩

-- The newest protocol of the result has the header of the constructed entry.
kernel_refl newest_header : serialized.headers[0]? equals
  some ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
    header)

/-- The constructed entry. -/
noncomputable def constructed : Var serialized.headers
    ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles header) :=
  ⟨0, newest_header⟩

kernel_refl prover_named :
  (derived.callees.find constructed declaration.roles.prover).isSome equals true
kernel_refl verifier_named :
  (derived.callees.find constructed declaration.roles.verifier).isSome equals true

/-- The constructed prover and verifier. -/
noncomputable def derivedProver : Var derived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        header)) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        header)) :=
  Option.get _ verifier_named

/-! ### The inputs

The entry has five inputs: the base as the prover and as the verifier hold it, the point as
each holds it, and the scalar, which the prover holds alone. The statement is the base and the
point. -/

/-- The side of the prover and the verifier together. -/
noncomputable abbrev both : Side :=
  (single declaration.roles.prover).union (single declaration.roles.verifier)

/-- The group and the field of the package: the nominal types 0 and 1. -/
abbrev point : Ty := .nominal 0

abbrev scalar : Ty := .nominal 1

/-- Inputs of the entry: the copies of the base and of the point, and the scalar. -/
noncomputable abbrev inputsOf (model : Model)
    (proverBase verifierBase proverPoint verifierPoint : model.Value point)
    (witness : model.Value scalar) : Values (SideValue model both) header.inputs :=
  .cons (ty := (⟨point, 0⟩ : Located)) proverBase
    (.cons (ty := (⟨point, 1⟩ : Located)) verifierBase
      (.cons (ty := (⟨point, 0⟩ : Located)) proverPoint
        (.cons (ty := (⟨point, 1⟩ : Located)) verifierPoint
          (.cons (ty := (⟨scalar, 0⟩ : Located)) witness .nil))))

/-- The prover's copy of the base: the first input. -/
noncomputable abbrev proverBase (inputs : Values (SideValue model both) header.inputs) : Datum :=
  inputs.get (ty := (⟨point, 0⟩ : Located)) ⟨0, kernel_rfl%⟩

-- The statement of the entry: the base and the point, each held by both roles.
kernel_refl statement :
  statementOf declaration.roles header equals
    [⟨point, ⟨0, ⟨0, kernel_rfl%⟩⟩, [⟨1, ⟨1, kernel_rfl%⟩⟩]⟩,
      ⟨point, ⟨0, ⟨2, kernel_rfl%⟩⟩, [⟨1, ⟨3, kernel_rfl%⟩⟩]⟩]

/-- Inputs in which the prover and the verifier hold one base and one point satisfy the
condition of the theorem on the inputs. -/
theorem honest_inputs_agree (base commitmentKey witness : Datum) :
    StatementCopiesEqual model both declaration.roles header
      (inputsOf model base base commitmentKey commitmentKey witness) := by
  intro isProver isVerifier agreement member
  rw [statement] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨⟨0, kernel_rfl%⟩, ⟨1, kernel_rfl%⟩, kernel_rfl%, kernel_rfl%, rfl⟩
  · cases List.mem_singleton.mp member
    exact ⟨⟨2, kernel_rfl%⟩, ⟨3, kernel_rfl%⟩, kernel_rfl%, kernel_rfl%, rfl⟩

/-! ### What the interactive prover sends

The entry for the prover alone samples a nonce, sends the commitment, receives the challenge
and sends the response. The commitment is the result of the row 1, `group.scale`, on the
prover's base and the nonce; the response is the result of the row 3, `field.add`, on the
nonce and the result of the row 2, `field.mul`, on the challenge and the scalar. -/

/-- The commitment: the row `group.scale` on the base and the nonce. -/
noncomputable abbrev commitment (model : Model) (base : model.Value point)
    (nonce : model.Value scalar) : model.Value point :=
  (model.pure ⟨1, [point, scalar], [point]⟩ rfl (.cons base (.cons nonce .nil))).get .here

/-- The response: the row `field.add` on the nonce and the product of the challenge and the
scalar. -/
noncomputable abbrev response (model : Model) (nonce challenge witness : model.Value scalar) :
    model.Value scalar :=
  (model.pure ⟨3, [scalar, scalar], [scalar]⟩ rfl
    (.cons nonce
      (.cons ((model.pure ⟨2, [scalar, scalar], [scalar]⟩ rfl
        (.cons challenge (.cons witness .nil))).get .here) .nil))).get .here

/-- The entry for the prover alone, in every model, as the kernel evaluates it. -/
theorem prover_shape (model : Model) (proverBase verifierBase proverPoint verifierPoint :
    model.Value point) (witness : model.Value scalar) :
    (typed.program.protocolTable model Identities.written).get entry []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover) (single declaration.roles.verifier)
          (inputsOf model proverBase verifierBase proverPoint verifierPoint witness)) =
      .call (.sample ⟨[], 0, 0⟩ ⟨0, [], scalar, rfl⟩ .nil) fun nonce =>
        .call (.send ⟨[], 0, 1⟩ point (commitment model proverBase nonce)) fun _ =>
          .call (.receive ⟨[], 0, 2⟩ scalar) fun challenge =>
            .call (.send ⟨[], 0, 3⟩ scalar (response model nonce challenge witness)) fun _ =>
              .done .nil :=
  kernel_rfl%

/-- The layout writes the commitment exactly when the multiple of the base by the nonce,
reduced modulo the order of the group, is a point of the group. -/
theorem commitment_written (base nonce : Datum) :
    Vocabulary.writes Vocabulary.table raw point (commitment model base nonce) =
      Vocabulary.inGroup
        (Concrete.scalePoint base.toPoint (nonce.toNat % Concrete.scalarModulus)) :=
  Vocabulary.model_scale_writes (package := raw) (row := 1) (output := 0)
    (operation := ⟨⟨Name.ofString "group.scale", [.type point]⟩, ⟨[point, scalar], [point], .pure⟩⟩)
    (group := "bls12-381.g1") (base := point) (scalar := scalar) kernel_rfl% kernel_rfl%
    kernel_rfl% kernel_rfl% kernel_rfl% rfl
    (.cons (ty := point) base (.cons (ty := scalar) nonce .nil))

/-- The layout writes the response, whatever the nonce, the challenge and the scalar: the row
`field.add` gives an element of the field. -/
theorem response_written (nonce challenge witness : Datum) :
    Vocabulary.writes Vocabulary.table raw scalar (response model nonce challenge witness) =
      true :=
  Vocabulary.model_arithmetic_writes (package := raw) (row := 3) (output := 1)
    (operation := ⟨⟨Name.ofString "field.add", [.type scalar]⟩, ⟨[scalar, scalar], [scalar], .pure⟩⟩)
    (name := "field.add") (field := "bls12-381.fr") (order := Vocabulary.bls12381Order)
    (width := 32) (inputs := [scalar, scalar]) kernel_rfl% kernel_rfl% (by decide) kernel_rfl%
    kernel_rfl% kernel_rfl% (by decide) rfl _

/-- The premise of the theorem about the messages, at the Schnorr prover, is exactly this:
every multiple of the prover's base by a number below the order of the group is a point of
the group. The response needs nothing. -/
theorem writable_iff (inputs : Values (SideValue model both) header.inputs) :
    EverySend (model := model)
        (fun type value => Vocabulary.writes Vocabulary.table raw type value = true)
        (fun _ => True)
        ((typed.program.protocolTable model Identities.written).get entry []
          (single declaration.roles.prover)
          (leftValues model (single declaration.roles.prover)
            (single declaration.roles.verifier) inputs)) ↔
      ∀ nonce : Datum,
        Vocabulary.inGroup
          (Concrete.scalePoint (proverBase inputs).toPoint
            (nonce.toNat % Concrete.scalarModulus)) = true := by
  match inputs with
  | .cons base (.cons verifierBase (.cons proverPoint (.cons verifierPoint (.cons witness .nil)))) =>
    rw [prover_shape model base verifierBase proverPoint verifierPoint witness]
    constructor
    · intro sends nonce
      exact (commitment_written base nonce).symm.trans (sends nonce).1
    · intro ofGroup nonce
      exact ⟨(commitment_written base nonce).trans (ofGroup nonce), fun challenge =>
        ⟨response_written nonce challenge witness, True.intro⟩⟩

/-- The messages of the prover are written when its base is a point of the group and the
multiples of a point of the group are of the group. -/
theorem writable (closed : Vocabulary.GroupClosedUnderMultiples)
    (inputs : Values (SideValue model both) header.inputs)
    (baseOfGroup : Vocabulary.inGroup (proverBase inputs).toPoint = true) :
    EverySend (model := model)
      (fun type value => Vocabulary.writes Vocabulary.table raw type value = true)
      (fun _ => True)
      ((typed.program.protocolTable model Identities.written).get entry []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover)
          (single declaration.roles.verifier) inputs)) :=
  (writable_iff inputs).mpr fun _ => closed.multiple_inGroup _ _ baseOfGroup

/-! ### What completeness of the interactive entry is

The entry for the prover and the verifier together samples the nonce, draws the challenge and
checks the verifier's equation: the base times the response is the commitment plus the point
times the challenge, with the rows 1 (`group.scale`), 4 (`group.add`) and 5 (`group.equal`). -/

/-- The verifier's check on a nonce and a challenge. -/
noncomputable abbrev verdict (model : Model)
    (proverBase verifierBase verifierPoint : model.Value point)
    (witness nonce challenge : model.Value scalar) : Bool :=
  (model.pure ⟨5, [point, point], [.bool]⟩ rfl
    (.cons (commitment model verifierBase (response model nonce challenge witness))
      (.cons ((model.pure ⟨4, [point, point], [point]⟩ rfl
        (.cons (commitment model proverBase nonce)
          (.cons (commitment model verifierPoint challenge) .nil))).get .here) .nil))).get .here

/-- The entry for the prover and the verifier together, in every model, as the kernel
evaluates it. -/
theorem grouped_shape (model : Model) (proverBase verifierBase proverPoint verifierPoint :
    model.Value point) (witness : model.Value scalar) :
    (typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model proverBase verifierBase proverPoint verifierPoint witness) =
      .call (.sample ⟨[], 0, 0⟩ ⟨0, [], scalar, rfl⟩ .nil) fun nonce =>
        .call (.draw ⟨[], 0, 2⟩ ⟨0, [], scalar, rfl⟩ .nil) fun challenge =>
          (((cond (verdict model proverBase verifierBase verifierPoint witness nonce challenge)
                (.done .nil) (.halt .reject) :
              PIR.Process (Effects model) (Values model.Value [])).bind fun _ =>
            (.done .nil : PIR.Process (Effects model) (Values (SideValue model both) []))).bind
            fun _ => .done .nil) :=
  kernel_rfl%

/-- Every run of a guard on a flag returns an accepted result exactly when the flag holds and
the result is accepted. -/
theorem guard_everyRun (flag : Bool)
    (accepted : Values (SideValue model both) header.outputs → Prop) :
    EveryRun accepted
        (((cond flag (.done .nil) (.halt .reject) :
            PIR.Process (Effects model) (Values model.Value [])).bind fun _ =>
          (.done .nil : PIR.Process (Effects model) (Values (SideValue model both) []))).bind
          fun _ => .done .nil) ↔
      flag = true ∧ accepted .nil := by
  cases flag
  · exact ⟨fun run => run.elim, fun holds => Bool.noConfusion holds.1⟩
  · exact ⟨fun run => ⟨rfl, run⟩, fun holds => holds.2⟩

/-- Completeness of the interactive entry, the premise of the theorem that stays a hypothesis,
is exactly this: the verifier's equation holds in the model's rows for every nonce and every
challenge, and the result is accepted. That the equation holds when the point is the base
times the scalar is a fact of the arithmetic of the curve, which this package does not
prove. -/
theorem interactive_complete_iff (proverBase verifierBase proverPoint verifierPoint witness : Datum)
    (accepted : Values (SideValue model both) header.outputs → Prop) :
    GroupedComplete
        ((typed.program.protocolTable model Identities.written).get entry [] both
          (inputsOf model proverBase verifierBase proverPoint verifierPoint witness))
        accepted ↔
      (∀ nonce challenge : Datum,
        verdict model proverBase verifierBase verifierPoint witness nonce challenge = true) ∧
        accepted .nil := by
  have shape := grouped_shape model proverBase verifierBase proverPoint verifierPoint witness
  rw [groupedComplete_iff_everyRun, shape]
  constructor
  · intro every
    exact ⟨fun nonce challenge => ((guard_everyRun _ accepted).mp (every nonce challenge)).1,
      ((guard_everyRun _ accepted).mp (every (Datum.number 0) (Datum.number 0))).2⟩
  · rintro ⟨holds, accepts⟩ nonce challenge
    exact (guard_everyRun _ accepted).mpr ⟨holds nonce challenge, accepts⟩

/-- The generator, seven times the generator, and the scalar seven. -/
noncomputable abbrev generator : Datum := Datum.ofPoint Concrete.generator

noncomputable abbrev sevenfold : Datum := Datum.ofPoint (Concrete.scalePoint Concrete.generator 7)

-- The verifier's equation as the kernel evaluates it in the model, at the generator as the
-- base, the nonce 5 and the challenge 3: it holds for the point that is seven times the
-- generator with the scalar 7, and fails with the scalar 8.
kernel_refl equation_holds :
  verdict model generator generator sevenfold (Datum.number 7) (Datum.number 5) (Datum.number 3)
  equals true

kernel_refl equation_fails :
  verdict model generator generator sevenfold (Datum.number 8) (Datum.number 5) (Datum.number 3)
  equals false

/-- The interactive entry is not complete on a scalar that is not the logarithm of the point:
completeness is a condition on the inputs. -/
theorem wrong_witness_incomplete
    (accepted : Values (SideValue model both) header.outputs → Prop) :
    ¬ GroupedComplete
      ((typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model generator generator sevenfold sevenfold (Datum.number 8)))
      accepted := by
  intro complete
  have holds := ((interactive_complete_iff _ _ _ _ _ accepted).mp complete).1 (Datum.number 5)
    (Datum.number 3)
  rw [equation_fails] at holds
  cases holds

/-! ### The theorem at the scheme -/

/-- The constructed prover on inputs: it returns the proof before its other outputs. -/
noncomputable def prover (inputs : Values (SideValue model both) header.inputs) :=
  ((derived.programs.table model (typed.program.functionTable model)
        serialized.identities).get derivedProver []
      (inputsWithoutProof model (proof := layout.proof) (rest := header.inputs)
        (construct_roles_differ typed declaration serialized constructs)
        (proverShare model declaration.roles inputs))).bind fun outputs =>
    .done (provedOutputs model declaration.roles.prover outputs)

/-- The constructed verifier on a proof and the verifier's share of the inputs. -/
noncomputable def verifier (inputs : Values (SideValue model both) header.inputs)
    (proof : model.Value layout.proof) :=
  (derived.programs.table model (typed.program.functionTable model)
      serialized.identities).get derivedVerifier []
    (proofInputs model declaration.roles.verifier (proof := layout.proof) (rest := header.inputs)
      proof (verifierShare model declaration.roles inputs))

/-- The condition on the outputs of the constructed verifier: the interactive condition, read
on them. The proof is an output of the prover. -/
noncomputable abbrev acceptedDerived
    (acceptedInteractive :
      Values model.Value (own declaration.roles.verifier header.outputs) → Prop) :
    Values model.Value
      (own declaration.roles.verifier (⟨layout.proof, declaration.roles.prover⟩ :: header.outputs)) →
        Prop :=
  fun outputs => acceptedInteractive (outputsWithoutProof model outputs)

/-- `Vocabulary.construct_complete` at the frontend's scheme `Proof = Schnorr<G1>`, in the
model of the vocabulary. Every premise about the package and the declaration is evaluated by
the kernel, the suite is a catalogue suite, and the laws of the layout are derived. What is
left:

- `compression`: the compressed encoding of G1, because the prover sends a point;
- `closed`: the multiples of a point of the group are of the group;
- the condition on the inputs: the prover's and the verifier's copies of the base and of the
  point are equal (`agrees`), and the prover's base is a point of the group (`baseOfGroup`);
- `complete`: completeness of the interactive entry.

Then the scheme of the constructed prover and verifier is complete. -/
theorem complete (compression : Vocabulary.PointCompression)
    (closed : Vocabulary.GroupClosedUnderMultiples)
    (inputs : Values (SideValue model both) header.inputs)
    (agrees : StatementCopiesEqual model both declaration.roles header inputs)
    (baseOfGroup : Vocabulary.inGroup (proverBase inputs).toPoint = true)
    (acceptedInteractive : Values model.Value (own declaration.roles.verifier header.outputs) → Prop)
    (complete : GroupedComplete
      ((typed.program.protocolTable model Identities.written).get entry [] both inputs)
      fun outputs => acceptedInteractive (verifierShare model declaration.roles outputs)) :
    DerivedComplete (prover inputs) (verifier inputs) (acceptedDerived acceptedInteractive) := by
  obtain ⟨found, isNewest, derives⟩ := Vocabulary.construct_complete typed_eq matched declaration
    named serialized constructs layout declared entry kernel_rfl% derived
    (okValue_eq _ result_projects) (fun _ => compression)
    (fun calls => Bool.noConfusion (rows_only.symm.trans calls))
  have same : found = constructed := Var.ext isNewest
  subst same
  exact derives derivedProver derivedVerifier (Option.some_get prover_named).symm
    (Option.some_get verifier_named).symm inputs agrees (writable closed inputs baseOfGroup)
    acceptedInteractive complete

/-- The theorem at inputs in which the prover and the verifier hold one base and one point:
the condition on the copies is discharged, and the base is a point of the group. -/
theorem complete_honest (compression : Vocabulary.PointCompression)
    (closed : Vocabulary.GroupClosedUnderMultiples) (base commitmentKey witness : Datum)
    (baseOfGroup : Vocabulary.inGroup base.toPoint = true)
    (acceptedInteractive : Values model.Value (own declaration.roles.verifier header.outputs) → Prop)
    (complete : GroupedComplete
      ((typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model base base commitmentKey commitmentKey witness))
      fun outputs => acceptedInteractive (verifierShare model declaration.roles outputs)) :
    DerivedComplete (prover (inputsOf model base base commitmentKey commitmentKey witness))
      (verifier (inputsOf model base base commitmentKey commitmentKey witness))
      (acceptedDerived acceptedInteractive) :=
  Schnorr.complete compression closed _ (honest_inputs_agree base commitmentKey witness)
    baseOfGroup acceptedInteractive complete

/-- The theorem with completeness of the interactive entry read in the model's rows: at inputs
in which the prover and the verifier hold one base, a point of the group, and one point, when
the verifier's equation holds at every nonce and every challenge, the scheme of the
constructed prover and verifier is complete. Every hypothesis is then a fact of the
arithmetic of the curve or a condition on the inputs. -/
theorem complete_of_equation (compression : Vocabulary.PointCompression)
    (closed : Vocabulary.GroupClosedUnderMultiples) (base commitmentKey witness : Datum)
    (baseOfGroup : Vocabulary.inGroup base.toPoint = true)
    (equation : ∀ nonce challenge : Datum,
      verdict model base base commitmentKey witness nonce challenge = true) :
    DerivedComplete (prover (inputsOf model base base commitmentKey commitmentKey witness))
      (verifier (inputsOf model base base commitmentKey commitmentKey witness))
      (acceptedDerived fun _ => True) :=
  complete_honest compression closed base commitmentKey witness baseOfGroup (fun _ => True)
    ((interactive_complete_iff base base commitmentKey commitmentKey witness _).mpr
      ⟨equation, True.intro⟩)

end Schnorr

/-! ## `collecting.json` -/

namespace Collecting

open Threading (raw declaration typed layout twice rounds roundsHeader)
open CanonicalLayoutLaws.Collecting (matched named no_point declared)
open DerivedScheme.Collecting (constructs derived constructed derivedProver derivedVerifier
  result_projects prover_named verifier_named)

/-- The model of the vocabulary's rows of the package. -/
noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

-- The suite of the declaration is a catalogue suite.
kernel_refl rows_only : declaration.suiteCallsFunctions equals false

/-- The side of the prover and the verifier together. -/
noncomputable abbrev both : Side :=
  (single declaration.roles.prover).union (single declaration.roles.verifier)

/-! ### What the interactive prover sends

The entry has four inputs: the challenge and the count, each as the prover and as the verifier
hold it. For the prover alone it runs three rounds, in each of which it sends the sum of a
carried value with itself (the row 1, `field.add`), receives a coin and sends the product of
the sum and the coin (the row 2, `field.mul`); then, when its count is at most 4, as many
receives as the count, and above 4 it stops `undefined`. The kernel evaluates the entry at each
count up to 4 and at every count above. -/

/-- The field of the package: the nominal type 0. -/
abbrev field : Ty := .nominal 0

/-- Inputs of the entry: the copies of the challenge and of the count. -/
noncomputable abbrev inputsOf (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (proverCount verifierCount : Nat) : Values (SideValue model both) roundsHeader.inputs :=
  .cons (ty := (⟨field, 0⟩ : Located)) proverChallenge
    (.cons (ty := (⟨field, 1⟩ : Located)) verifierChallenge
      (.cons (ty := (⟨.nat, 0⟩ : Located)) proverCount
        (.cons (ty := (⟨.nat, 1⟩ : Located)) verifierCount .nil)))

/-- The row `field.add` and the row `field.mul` of the package. -/
noncomputable abbrev sum (model : Model) (first second : model.Value field) : model.Value field :=
  (model.pure ⟨1, [field, field], [field]⟩ rfl (.cons first (.cons second .nil))).get .here

noncomputable abbrev product (model : Model) (first second : model.Value field) :
    model.Value field :=
  (model.pure ⟨2, [field, field], [field]⟩ rfl (.cons first (.cons second .nil))).get .here

/-- One round for the prover: it sends the sum of the carried value with itself, receives a
coin and sends the product of the sum and the coin. -/
noncomputable abbrev round (model : Model) (carried : model.Value field)
    (next : PIR.Process (Effects model) Unit) : PIR.Process (Effects model) Unit :=
  .call (.send ⟨[], 1, 0⟩ field (sum model carried carried)) fun _ =>
    .call (.receive ⟨[], 1, 1⟩ field) fun coin =>
      .call (.send ⟨[], 1, 2⟩ field (product model (sum model carried carried) coin)) fun _ =>
        next

/-- The three rounds: each carries the sum of the round before. -/
noncomputable abbrev threeRounds (model : Model) (challenge : model.Value field)
    (next : PIR.Process (Effects model) Unit) : PIR.Process (Effects model) Unit :=
  round model challenge
    (round model (sum model challenge challenge)
      (round model (sum model (sum model challenge challenge) (sum model challenge challenge))
        next))

/-- As many receives as a count: the coins of the applied protocol `challenge`, below the site
3 of the entry. -/
noncomputable def receives (model : Model) : Nat → PIR.Process (Effects model) Unit
  | 0 => .done ()
  | count + 1 => .call (.receive ⟨[3], 0, 0⟩ field) fun _ => receives model count

/-- The entry for the prover alone, without its outputs. -/
noncomputable abbrev proverRun (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (proverCount verifierCount : Nat) : PIR.Process (Effects model) Unit :=
  ((typed.program.protocolTable model Identities.written).get rounds []
      (single declaration.roles.prover)
      (leftValues model (single declaration.roles.prover) (single declaration.roles.verifier)
        (inputsOf model proverChallenge verifierChallenge proverCount verifierCount))).bind
    fun _ => .done ()

/-- The entry for the prover alone at a count up to 4, in every model, as the kernel evaluates
it: the three rounds, and then as many receives as the count. -/
theorem prover_shape_0 (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (verifierCount : Nat) :
    proverRun model proverChallenge verifierChallenge 0 verifierCount =
      threeRounds model proverChallenge (receives model 0) :=
  kernel_rfl%

theorem prover_shape_1 (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (verifierCount : Nat) :
    proverRun model proverChallenge verifierChallenge 1 verifierCount =
      threeRounds model proverChallenge (receives model 1) :=
  kernel_rfl%

theorem prover_shape_2 (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (verifierCount : Nat) :
    proverRun model proverChallenge verifierChallenge 2 verifierCount =
      threeRounds model proverChallenge (receives model 2) :=
  kernel_rfl%

theorem prover_shape_3 (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (verifierCount : Nat) :
    proverRun model proverChallenge verifierChallenge 3 verifierCount =
      threeRounds model proverChallenge (receives model 3) :=
  kernel_rfl%

theorem prover_shape_4 (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (verifierCount : Nat) :
    proverRun model proverChallenge verifierChallenge 4 verifierCount =
      threeRounds model proverChallenge (receives model 4) :=
  kernel_rfl%

/-- The entry for the prover alone at a count above 4: the three rounds, and then it stops
`undefined`. -/
theorem prover_shape_beyond (model : Model) (proverChallenge verifierChallenge : model.Value field)
    (verifierCount excess : Nat) :
    proverRun model proverChallenge verifierChallenge (excess + 5) verifierCount =
      threeRounds model proverChallenge (.halt .undefined) :=
  kernel_rfl%

/-- The condition that the layout writes a value. -/
abbrev Written : (type : Ty) → model.Value type → Prop :=
  fun type value => Vocabulary.writes Vocabulary.table raw type value = true

/-- The layout writes what a round sends, whatever it carries and whatever coin it receives:
its values are results of `field.add` and `field.mul`. -/
theorem round_sends (carried : Datum) {next : PIR.Process (Effects model) Unit}
    (later : EverySend Written (fun _ => True) next) :
    EverySend Written (fun _ => True) (round model carried next) :=
  ⟨CanonicalLayoutLaws.Collecting.sum_written (.cons carried (.cons carried .nil)), fun coin =>
    ⟨CanonicalLayoutLaws.Collecting.product_written
      (.cons (sum model carried carried) (.cons coin .nil)), later⟩⟩

/-- Receives send nothing. -/
theorem receives_send_nothing : ∀ count : Nat,
    EverySend Written (fun _ => True) (receives model count)
  | 0 => True.intro
  | count + 1 => fun _ => receives_send_nothing count

/-- The layout writes every value that the entry for the prover alone sends, at every count:
up to 4 the three rounds and the receives, and above 4 the three rounds. -/
theorem run_sends (proverChallenge verifierChallenge : Datum) (verifierCount : Nat) :
    ∀ count : Nat, EverySend Written (fun _ => True)
      (proverRun model proverChallenge verifierChallenge count verifierCount) := by
  have rounds_send : ∀ {next : PIR.Process (Effects model) Unit},
      EverySend Written (fun _ => True) next →
        EverySend Written (fun _ => True) (threeRounds model proverChallenge next) :=
    fun later => round_sends _ (round_sends _ (round_sends _ later))
  have at_shape : ∀ {run shape : PIR.Process (Effects model) Unit}, run = shape →
      EverySend Written (fun _ => True) shape → EverySend Written (fun _ => True) run :=
    fun same sends => same ▸ sends
  intro count
  match count with
  | 0 =>
    exact at_shape (prover_shape_0 model proverChallenge verifierChallenge verifierCount)
      (rounds_send (receives_send_nothing 0))
  | 1 =>
    exact at_shape (prover_shape_1 model proverChallenge verifierChallenge verifierCount)
      (rounds_send (receives_send_nothing 1))
  | 2 =>
    exact at_shape (prover_shape_2 model proverChallenge verifierChallenge verifierCount)
      (rounds_send (receives_send_nothing 2))
  | 3 =>
    exact at_shape (prover_shape_3 model proverChallenge verifierChallenge verifierCount)
      (rounds_send (receives_send_nothing 3))
  | 4 =>
    exact at_shape (prover_shape_4 model proverChallenge verifierChallenge verifierCount)
      (rounds_send (receives_send_nothing 4))
  | excess + 5 =>
    exact at_shape
      (prover_shape_beyond model proverChallenge verifierChallenge verifierCount excess)
      (rounds_send True.intro)

/-- The layout writes every value that the interactive prover sends, at every input: the
premise of the theorem about the messages holds of the package. -/
theorem writable (inputs : Values (SideValue model both) roundsHeader.inputs) :
    EverySend Written (fun _ => True)
      ((typed.program.protocolTable model Identities.written).get rounds []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover)
          (single declaration.roles.verifier) inputs)) := by
  match inputs with
  | .cons proverChallenge (.cons verifierChallenge (.cons proverCount (.cons verifierCount .nil))) =>
    exact EverySend.mono (fun _ _ sent => sent) (fun _ _ => True.intro)
      ((everySend_bind Written (fun _ => True) (fun _ => PIR.Process.done ()) _).mp
        (run_sends proverChallenge verifierChallenge verifierCount proverCount))

/-- The constructed prover on inputs: it returns the proof before its other outputs. -/
noncomputable def prover (inputs : Values (SideValue model both) roundsHeader.inputs) :=
  ((derived.programs.table model (typed.program.functionTable model)
        twice.identities).get derivedProver []
      (inputsWithoutProof model (proof := layout.proof) (rest := roundsHeader.inputs)
        (construct_roles_differ typed declaration twice constructs)
        (proverShare model declaration.roles inputs))).bind fun outputs =>
    .done (provedOutputs model declaration.roles.prover outputs)

/-- The constructed verifier on a proof and the verifier's share of the inputs. -/
noncomputable def verifier (inputs : Values (SideValue model both) roundsHeader.inputs)
    (proof : model.Value layout.proof) :=
  (derived.programs.table model (typed.program.functionTable model)
      twice.identities).get derivedVerifier []
    (proofInputs model declaration.roles.verifier (proof := layout.proof)
      (rest := roundsHeader.inputs) proof (verifierShare model declaration.roles inputs))

/-- The condition on the outputs of the constructed verifier: the interactive condition, read
on them. -/
noncomputable abbrev acceptedDerived
    (acceptedInteractive :
      Values model.Value (own declaration.roles.verifier roundsHeader.outputs) → Prop) :
    Values model.Value
      (own declaration.roles.verifier
        (⟨layout.proof, declaration.roles.prover⟩ :: roundsHeader.outputs)) → Prop :=
  fun outputs => acceptedInteractive (outputsWithoutProof model outputs)

/-- `Vocabulary.construct_complete` at `collecting`, in the model of the vocabulary. Every
premise about the package and the declaration is evaluated by the kernel, the suite is a
catalogue suite, and the layout moves no point, so there is no premise about the layout at
all; the layout writes the messages of the interactive prover (`writable`). What is left: the
condition on the inputs, and completeness of the interactive entry. -/
theorem complete (inputs : Values (SideValue model both) roundsHeader.inputs)
    (agrees : StatementCopiesEqual model both declaration.roles roundsHeader inputs)
    (acceptedInteractive :
      Values model.Value (own declaration.roles.verifier roundsHeader.outputs) → Prop)
    (complete : GroupedComplete
      ((typed.program.protocolTable model Identities.written).get rounds [] both inputs)
      fun outputs => acceptedInteractive (verifierShare model declaration.roles outputs)) :
    DerivedComplete (prover inputs) (verifier inputs) (acceptedDerived acceptedInteractive) := by
  obtain ⟨found, isNewest, derives⟩ := Vocabulary.construct_complete Threading.typed_eq matched
    declaration named twice constructs layout declared rounds kernel_rfl% derived
    (okValue_eq _ result_projects)
    (fun moves => Bool.noConfusion (no_point.symm.trans moves))
    (fun calls => Bool.noConfusion (rows_only.symm.trans calls))
  have same : found = constructed := Var.ext isNewest
  subst same
  exact derives derivedProver derivedVerifier (Option.some_get prover_named).symm
    (Option.some_get verifier_named).symm inputs agrees (writable inputs) acceptedInteractive
    complete

/-- The theorem at inputs in which the prover and the verifier hold one challenge and one
count: the condition on the inputs is discharged, and completeness of the interactive entry
is the one hypothesis. -/
theorem complete_honest (challenge : Datum) (count : Nat)
    (acceptedInteractive :
      Values model.Value (own declaration.roles.verifier roundsHeader.outputs) → Prop)
    (complete : GroupedComplete
      ((typed.program.protocolTable model Identities.written).get rounds [] both
        (inputsOf model challenge challenge count count))
      fun outputs => acceptedInteractive (verifierShare model declaration.roles outputs)) :
    DerivedComplete (prover (inputsOf model challenge challenge count count))
      (verifier (inputsOf model challenge challenge count count))
      (acceptedDerived acceptedInteractive) :=
  Collecting.complete _ (ThreadTogether.honest_inputs_agree model challenge count).copiesEqual
    acceptedInteractive complete

end Collecting

/-! ## The frontend's scheme `Proof = Doubling` -/

namespace Doubling

raw_package raw from file "fixtures/construction/doubling-frontend-scheme.json"
raw_declaration declaration from file
  "fixtures/construction/doubling-frontend-scheme.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

/-- The model of the vocabulary's rows of the package. -/
noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

-- The rows of the package are the vocabulary's; the rows that the declaration names have the
-- names of the rows of the canonical layout; no row that it names is at a type with a point
-- of G1 in it; and its suite is a catalogue suite.
kernel_refl matched : Vocabulary.mismatches Vocabulary.table raw equals []

kernel_refl named : declaration.namesCanonical raw equals true

kernel_refl no_point : declaration.movesPoint Vocabulary.table raw equals false

kernel_refl rows_only : declaration.suiteCallsFunctions equals false

kernel_refl layout_declared :
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome equals true

/-- The layout of the declaration, over the rows of the package. -/
noncomputable def layout : Layout operations :=
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).get layout_declared

theorem declared :
    declaration.layout.bind (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) =
      some layout :=
  declared_get declaration layout_declared

kernel_refl construct_accepts : (construct typed declaration).isOk equals true

/-- The result of the pipeline of the declaration. -/
noncomputable def serialized : Stepped typed.typeTable operations typed.functions :=
  okValue (construct typed declaration) construct_accepts

theorem constructs : construct typed declaration = .ok serialized := okValue_eq _ _

kernel_refl result_projects : (projectProtocols serialized.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def derived : Projected operations typed.functions serialized.headers :=
  okValue (projectProtocols serialized.protocols) result_projects

/-- The header of the entry `Doubling`, the one protocol of the package, and the entry. -/
noncomputable abbrev header : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev entry : Var typed.protocols header := ⟨0, kernel_rfl%⟩

kernel_refl newest_header : serialized.headers[0]? equals
  some ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
    header)

/-- The constructed entry. -/
noncomputable def constructed : Var serialized.headers
    ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles header) :=
  ⟨0, newest_header⟩

kernel_refl prover_named :
  (derived.callees.find constructed declaration.roles.prover).isSome equals true
kernel_refl verifier_named :
  (derived.callees.find constructed declaration.roles.verifier).isSome equals true

/-- The constructed prover and verifier. -/
noncomputable def derivedProver : Var derived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        header)) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        header)) :=
  Option.get _ verifier_named

/-- The side of the prover and the verifier together. -/
noncomputable abbrev both : Side :=
  (single declaration.roles.prover).union (single declaration.roles.verifier)

/-- The field of the package: the nominal type 0. -/
abbrev scalar : Ty := .nominal 0

/-- The inputs of the entry: the flag, which the prover holds. -/
noncomputable abbrev inputsOf (model : Model) (flag : Bool) :
    Values (SideValue model both) header.inputs :=
  .cons (ty := (⟨.bool, 0⟩ : Located)) flag .nil

-- The entry has no input that both roles hold, so its statement is empty.
kernel_refl no_statement : statementOf declaration.roles header equals []

/-- Every input satisfies the condition on the inputs. -/
theorem inputs_agree (inputs : Values (SideValue model both) header.inputs) :
    StatementCopiesEqual model both declaration.roles header inputs := by
  intro isProver isVerifier agreement member
  rw [no_statement] at member
  cases member

/-- The response: the row 1, `field.add`, on the challenge and the challenge. -/
noncomputable abbrev response (model : Model) (challenge : model.Value scalar) : model.Value scalar :=
  (model.pure ⟨1, [scalar, scalar], [scalar]⟩ rfl (.cons challenge (.cons challenge .nil))).get .here

/-- The entry for the prover alone, in every model, as the kernel evaluates it: it sends the
flag, receives the challenge and sends the response. -/
theorem prover_shape (model : Model) (flag : Bool) :
    (typed.program.protocolTable model Identities.written).get entry []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover) (single declaration.roles.verifier)
          (inputsOf model flag)) =
      .call (.send ⟨[], 0, 0⟩ .bool flag) fun _ =>
        .call (.receive ⟨[], 0, 1⟩ scalar) fun challenge =>
          .call (.send ⟨[], 0, 2⟩ scalar (response model challenge)) fun _ => .done .nil :=
  kernel_rfl%

/-- The entry for the prover and the verifier together, in every model, as the kernel
evaluates it: the verifier draws the challenge, and the entry returns. -/
theorem grouped_shape (model : Model) (flag : Bool) :
    (typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model flag) =
      .call (.draw ⟨[], 0, 1⟩ ⟨0, [], scalar, rfl⟩ .nil) fun _ => .done .nil :=
  kernel_rfl%

/-- The layout writes the response, whatever the challenge. -/
theorem response_written (challenge : Datum) :
    Vocabulary.writes Vocabulary.table raw scalar (response model challenge) = true :=
  Vocabulary.model_arithmetic_writes (package := raw) (row := 1) (output := 0)
    (operation := ⟨⟨Name.ofString "field.add", [.type scalar]⟩, ⟨[scalar, scalar], [scalar], .pure⟩⟩)
    (name := "field.add") (field := "bls12-381.fr") (order := Vocabulary.bls12381Order)
    (width := 32) (inputs := [scalar, scalar]) kernel_rfl% kernel_rfl% (by decide) kernel_rfl%
    kernel_rfl% kernel_rfl% (by decide) rfl _

/-- The layout writes every value that the interactive prover sends: the flag, a `bool`, and
the response, a result of the arithmetic of the field. -/
theorem writable (flag : Bool) :
    EverySend (model := model)
      (fun type value => Vocabulary.writes Vocabulary.table raw type value = true)
      (fun _ => True)
      ((typed.program.protocolTable model Identities.written).get entry []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover)
          (single declaration.roles.verifier) (inputsOf model flag))) := by
  rw [prover_shape model flag]
  exact ⟨Vocabulary.writes_bool Vocabulary.table raw flag, fun challenge =>
    ⟨response_written challenge, True.intro⟩⟩

/-- The interactive entry is complete: it returns whatever the challenge. -/
theorem interactive_complete (flag : Bool) :
    GroupedComplete
      ((typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model flag))
      fun _ => True := by
  rw [groupedComplete_iff_everyRun, grouped_shape model flag]
  exact fun _ => True.intro

/-- The constructed prover on the flag: it returns the proof before its other outputs. -/
noncomputable def prover (flag : Bool) :=
  ((derived.programs.table model (typed.program.functionTable model)
        serialized.identities).get derivedProver []
      (inputsWithoutProof model (proof := layout.proof) (rest := header.inputs)
        (construct_roles_differ typed declaration serialized constructs)
        (proverShare model declaration.roles (inputsOf model flag)))).bind fun outputs =>
    .done (provedOutputs model declaration.roles.prover outputs)

/-- The constructed verifier on a proof. -/
noncomputable def verifier (flag : Bool) (proof : model.Value layout.proof) :=
  (derived.programs.table model (typed.program.functionTable model)
      serialized.identities).get derivedVerifier []
    (proofInputs model declaration.roles.verifier (proof := layout.proof) (rest := header.inputs)
      proof (verifierShare model declaration.roles (inputsOf model flag)))

/-- `Vocabulary.construct_complete` at the frontend's scheme `Proof = Doubling`, in the model
of the vocabulary, with every premise discharged and no hypothesis: the premises about the
package and the declaration by the kernel; no compressed encoding, since no message has a
point; a catalogue suite; no statement; the messages of the prover, which the layout writes;
and completeness of the interactive entry. For every sampler the constructed prover returns a
proof on which the constructed verifier returns. -/
theorem complete (flag : Bool) :
    DerivedComplete (prover flag) (verifier flag) (fun _ => True) := by
  obtain ⟨found, isNewest, derives⟩ := Vocabulary.construct_complete typed_eq matched declaration
    named serialized constructs layout declared entry kernel_rfl% derived
    (okValue_eq _ result_projects)
    (fun moves => Bool.noConfusion (no_point.symm.trans moves))
    (fun calls => Bool.noConfusion (rows_only.symm.trans calls))
  have same : found = constructed := Var.ext isNewest
  subst same
  exact derives derivedProver derivedVerifier (Option.some_get prover_named).symm
    (Option.some_get verifier_named).symm (inputsOf model flag) (inputs_agree _) (writable flag)
    (fun _ => True) (interactive_complete flag)

end Doubling

/-! ## The serialize step alone: `units.json` -/

namespace Units

raw_package raw from file "fixtures/construction/units.json"
raw_declaration declaration from file "fixtures/construction/units.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

/-- The model of the vocabulary's rows of the package. -/
noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

-- The rows of the package are the vocabulary's; the rows that the declaration names have the
-- names of the rows of the canonical layout; no row that it names is at a type with a point
-- of G1 in it; and the declaration has no suite.
kernel_refl matched : Vocabulary.mismatches Vocabulary.table raw equals []

kernel_refl named : declaration.namesCanonical raw equals true

kernel_refl no_point : declaration.movesPoint Vocabulary.table raw equals false

kernel_refl no_suite : declaration.suite.isNone equals true

kernel_refl layout_declared :
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome equals true

/-- The layout of the declaration, over the rows of the package. -/
noncomputable def layout : Layout operations :=
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).get layout_declared

theorem declared :
    declaration.layout.bind (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) =
      some layout :=
  declared_get declaration layout_declared

kernel_refl serialize_accepts :
  (serializeProtocols declaration Identities.written typed.program.protocols).isOk equals true

/-- The result of the serialize step of the declaration. -/
noncomputable def serialized : Stepped typed.typeTable operations typed.functions :=
  okValue (serializeProtocols declaration Identities.written typed.program.protocols)
    serialize_accepts

theorem serializes :
    serializeProtocols declaration Identities.written typed.program.protocols = .ok serialized :=
  okValue_eq _ _

kernel_refl result_projects : (projectProtocols serialized.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def derived : Projected operations typed.functions serialized.headers :=
  okValue (projectProtocols serialized.protocols) result_projects

/-- The header of the entry, the one protocol of the package, and the entry. -/
noncomputable abbrev header : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev entry : Var typed.protocols header := ⟨0, kernel_rfl%⟩

kernel_refl newest_header : serialized.headers[0]? equals
  some ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
    header)

/-- The serialized entry. -/
noncomputable def constructed : Var serialized.headers
    ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles header) :=
  ⟨0, newest_header⟩

kernel_refl prover_named :
  (derived.callees.find constructed declaration.roles.prover).isSome equals true
kernel_refl verifier_named :
  (derived.callees.find constructed declaration.roles.verifier).isSome equals true

/-- The derived prover and verifier. -/
noncomputable def derivedProver : Var derived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        header)) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        header)) :=
  Option.get _ verifier_named

/-- The side of the prover and the verifier together. -/
noncomputable abbrev both : Side :=
  (single declaration.roles.prover).union (single declaration.roles.verifier)

/-- The type of the message: a collection, without a size, of values of the type with one
value. -/
abbrev units : Ty := .seq (.tuple []) none

/-- The inputs of the entry: the collection, which the prover holds. -/
noncomputable abbrev inputsOf (model : Model) (collection : List PUnit) :
    Values (SideValue model both) header.inputs :=
  .cons (ty := (⟨units, 0⟩ : Located)) collection .nil

/-- The entry for the prover alone, in every model, as the kernel evaluates it: it sends the
collection. -/
theorem prover_shape (model : Model) (collection : List PUnit) :
    (typed.program.protocolTable model Identities.written).get entry []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover) (single declaration.roles.verifier)
          (inputsOf model collection)) =
      .call (.send ⟨[], 0, 0⟩ units collection) fun _ =>
        .done (.cons (ty := (⟨units, 1⟩ : Located)) PUnit.unit .nil) :=
  kernel_rfl%

/-- The entry for the prover and the verifier together, in every model, as the kernel
evaluates it: it returns the collection as the verifier holds it. -/
theorem grouped_shape (model : Model) (collection : List PUnit) :
    (typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model collection) =
      .done (.cons (ty := (⟨units, 1⟩ : Located)) collection .nil) :=
  kernel_rfl%

/-- The layout writes every collection of values of the type with one value: as its length. -/
theorem collection_written (collection : List PUnit) :
    Vocabulary.writes Vocabulary.table raw units collection = true := by
  have closedIs : Vocabulary.closedOf raw.types.toArray units =
      some (.seq (.tuple []) none) := kernel_rfl%
  simp [Vocabulary.writes, Vocabulary.messageFormat, closedIs, Vocabulary.formatOf,
    Vocabulary.formatsOf, Vocabulary.sequences, Format.through, Format.counted, Format.each,
    Format.natural, Concrete.toDatum, Concrete.tupleData, Vocabulary.asItems]
  exact fun _ _ => rfl

/-- The layout writes the value that the interactive prover sends. -/
theorem writable (collection : List PUnit) :
    EverySend (model := model)
      (fun type value => Vocabulary.writes Vocabulary.table raw type value = true)
      (fun _ => True)
      ((typed.program.protocolTable model Identities.written).get entry []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover)
          (single declaration.roles.verifier) (inputsOf model collection))) := by
  rw [prover_shape model collection]
  exact ⟨collection_written collection, True.intro⟩

/-- The interactive condition on what the verifier holds of the outputs: its result is the
collection that the prover holds. -/
noncomputable abbrev acceptedOwn (collection : List PUnit) :
    Values model.Value (own declaration.roles.verifier header.outputs) → Prop :=
  fun outputs => outputs.get (ty := units) .here = collection

/-- The interactive entry is complete: the verifier returns the prover's collection. -/
theorem interactive_complete (collection : List PUnit) :
    GroupedComplete
      ((typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model collection))
      fun outputs => acceptedOwn collection (verifierShare model declaration.roles outputs) := by
  rw [groupedComplete_iff_everyRun, grouped_shape model collection]
  exact rfl

/-- The derived prover on a collection: it returns the proof before its other outputs. -/
noncomputable def prover (collection : List PUnit) :=
  ((derived.programs.table model (typed.program.functionTable model)
        serialized.identities).get derivedProver []
      (inputsWithoutProof model (proof := layout.proof) (rest := header.inputs)
        (stepProtocols_roles_differ Identities.written (typed.protocols.length - 1)
          declaration.roles typed.program.protocols serialized
          (serializeProtocols_steps declaration Identities.written typed.program.protocols layout
            declared serialized serializes))
        (proverShare model declaration.roles (inputsOf model collection)))).bind fun outputs =>
    .done (provedOutputs model declaration.roles.prover outputs)

/-- The derived verifier on a proof. -/
noncomputable def verifier (collection : List PUnit) (proof : model.Value layout.proof) :=
  (derived.programs.table model (typed.program.functionTable model)
      serialized.identities).get derivedVerifier []
    (proofInputs model declaration.roles.verifier (proof := layout.proof) (rest := header.inputs)
      proof (verifierShare model declaration.roles (inputsOf model collection)))

/-- The condition on the outputs of the derived verifier: the interactive condition, read on
them. -/
noncomputable abbrev acceptedDerived (collection : List PUnit) :
    Values model.Value
      (own declaration.roles.verifier (⟨layout.proof, declaration.roles.prover⟩ :: header.outputs)) →
        Prop :=
  fun outputs => acceptedOwn collection (outputsWithoutProof model outputs)

/-- `Vocabulary.serializeProtocols_complete` at `units.json`, in the model of the vocabulary,
with every premise discharged and no hypothesis: the premises about the package and the
declaration by the kernel; no compressed encoding, since the message has no point; the
message of the prover, which the layout writes; and completeness of the interactive entry.
For every sampler the derived prover returns a proof on which the derived verifier returns
the collection that the prover holds. -/
theorem complete (collection : List PUnit) :
    DerivedComplete (prover collection) (verifier collection) (acceptedDerived collection) := by
  obtain ⟨found, isNewest, derives⟩ := Vocabulary.serializeProtocols_complete typed_eq matched
    declaration named serialized serializes layout declared entry rfl derived
    (okValue_eq _ result_projects)
    (fun moves => Bool.noConfusion (no_point.symm.trans moves))
  have same : found = constructed := Var.ext isNewest
  subst same
  exact derives derivedProver derivedVerifier (Option.some_get prover_named).symm
    (Option.some_get verifier_named).symm (inputsOf model collection) (writable collection)
    (acceptedOwn collection) (interactive_complete collection)

end Units

/-! ## The premises that are asked only of some declarations -/

namespace Premises

-- The suite of `schnorr-source` is written in source: it calls functions of the package.
kernel_refl source_suite : ThreadingSchnorr.declaration.suiteCallsFunctions equals true

/-- The suite of `schnorr-source` returns in every model: each function of the package returns
on every input. This is the premise that `Vocabulary.construct_complete` asks of a declaration
whose suite calls functions. -/
theorem source_suite_returns (model : Model) :
    ThreadingSchnorr.declaration.SuiteReturns ThreadingSchnorr.typed model :=
  ThreadingSchnorr.declaration.suiteReturns_of_functions
    (ThreadTogether.schnorr_functions_return model)

/-- A catalogue suite returns in every model, without a premise. -/
theorem catalogue_suite_returns (model : Model) :
    Schnorr.declaration.SuiteReturns Schnorr.typed model :=
  Raw.Declaration.suiteReturns_of_rows Schnorr.rows_only Schnorr.typed model

open Zkc.Core.Vocabulary Zkc.Core.Concrete in
-- The executable check of the hypothesis `GroupClosedUnderMultiples`: multiples of multiples
-- of the generator are of the group. A point of the curve outside the group has a multiple
-- outside the group: of such a base the layout does not write the commitment.
#eval show IO Unit from do
  let check (label : String) (condition : Bool) : IO Unit :=
    unless condition do throw (IO.userError s!"vocabulary scheme: {label}")
  for first in [0, 1, 7, scalarModulus - 1] do
    let point := scalePoint generator first
    check s!"{first} times the generator is of the group" (inGroup point)
    for second in [0, 1, 2, 5, 1000003, scalarModulus - 1] do
      check s!"{second} times {first} times the generator is of the group"
        (inGroup (scalePoint point second))
  let outside : Concrete.Point := some (0, 2)
  check "a point of the curve outside the group" (onCurve outside && !inGroup outside)
  check "a multiple of a point outside the group is outside the group"
    (!inGroup (scalePoint outside 1))

end Premises

end VocabularyScheme

/-! ## Axioms -/

section Axioms

open Zkc.Core

-- `Zkc.Core.VocabularyScheme`
#print axioms Raw.Declaration.suiteReturns_of_rows
#print axioms Raw.Declaration.suiteReturns_of_functions
#print axioms Vocabulary.construct_complete
#print axioms Vocabulary.serializeProtocols_complete

-- The hypothesis about multiples of a point (`Zkc.Core.CanonicalLayoutValues`).
#print axioms Vocabulary.model_scale_writes_of_group

-- The lemmas of `Zkc.Core.VocabularyModel` that the laws of the canonical layout reuse.
#print axioms Vocabulary.mismatch_none
#print axioms Vocabulary.fillEach_getElem?
#print axioms Vocabulary.fill_signature
#print axioms Vocabulary.merlinSuite?_none
#print axioms Vocabulary.model_pure
#print axioms Vocabulary.applyOperation_read
#print axioms Vocabulary.elaborate_table

-- The checks of this file.
#print axioms VocabularyScheme.Schnorr.honest_inputs_agree
#print axioms VocabularyScheme.Schnorr.prover_shape
#print axioms VocabularyScheme.Schnorr.commitment_written
#print axioms VocabularyScheme.Schnorr.response_written
#print axioms VocabularyScheme.Schnorr.writable_iff
#print axioms VocabularyScheme.Schnorr.writable
#print axioms VocabularyScheme.Schnorr.grouped_shape
#print axioms VocabularyScheme.Schnorr.interactive_complete_iff
#print axioms VocabularyScheme.Schnorr.wrong_witness_incomplete
#print axioms VocabularyScheme.Schnorr.complete
#print axioms VocabularyScheme.Schnorr.complete_honest
#print axioms VocabularyScheme.Schnorr.complete_of_equation
#print axioms VocabularyScheme.Collecting.prover_shape_4
#print axioms VocabularyScheme.Collecting.prover_shape_beyond
#print axioms VocabularyScheme.Collecting.round_sends
#print axioms VocabularyScheme.Collecting.run_sends
#print axioms VocabularyScheme.Collecting.writable
#print axioms VocabularyScheme.Collecting.complete
#print axioms VocabularyScheme.Collecting.complete_honest
#print axioms VocabularyScheme.Doubling.writable
#print axioms VocabularyScheme.Doubling.interactive_complete
#print axioms VocabularyScheme.Doubling.complete
#print axioms VocabularyScheme.Units.collection_written
#print axioms VocabularyScheme.Units.writable
#print axioms VocabularyScheme.Units.interactive_complete
#print axioms VocabularyScheme.Units.complete
#print axioms VocabularyScheme.Premises.source_suite_returns
#print axioms VocabularyScheme.Premises.catalogue_suite_returns

end Axioms
