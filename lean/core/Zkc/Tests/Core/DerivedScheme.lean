import Zkc.Tests.Core.ThreadTogether
import Zkc.Tests.Core.SerializeReplay
import Zkc.Core.DerivedScheme

/-! Completeness of the scheme that the construction steps derive: the statements at
packages, and a witness and a failing example of what they are stated with.

- **The values.** The outputs of the verifier of a serialized entry, read as its outputs of
  the entry before the step, are read back; a value that the role itself holds is dropped
  by the reading, which is why the statements take the two roles to differ.
- **`StatementCopiesEqual`.** The condition of the statements on the inputs. At a protocol
  of three roles that each hold a copy of one agreed input, for the side of all three: it
  holds when the prover's and the verifier's copies are equal, whatever the third role
  holds; `StatementAgrees`, which the statements took before, fails when the third copy
  differs; and it fails when the prover's and the verifier's copies differ.
- **`Resends`.** It holds of the handler that performs every effect as it is, for every
  condition, and fails of a handler that sends a value before every effect. A process that
  only receives sends nothing, and sends nothing under the first handler
  (`EverySend.interpretWith`); under the second it sends.
- **`Layout.Carries` and `RegionCarries`.** The layout of the toy package of
  `Tests/Core/SerializeReplay.lean` carries `bool`; the same layout without a row that puts
  carries no type, a region with an exchange from the prover to the verifier has
  `RegionCarries` over the first and not over the second, and the serialize step refuses
  the package over the second: that the layout carries the messages is what the step
  checks.
- **`fiatShamir_sends`.** At the package of `Tests/Core/ThreadTogether.lean` whose entry
  returns on every run: the entry for the prover alone sends a number and receives a coin;
  its Fiat–Shamir image sends only numbers, by the theorem with every premise discharged,
  and the kernel evaluates it to the `send` of that number alone.
- **`construct_complete` at the fixtures.** At `fixtures/construction/collecting.json`,
  `sumcheck.json` and `schnorr-source.json` with their declarations, every premise that
  says which programs were constructed is a closed equation that the kernel evaluates, and
  `Suite.Returns` is discharged (two catalogue suites, and a source suite whose functions
  return). What is left (`CompleteFrom`) is the statement for an arbitrary model: from the
  laws of the layout, inputs on which the statement copies agree, messages of the
  interactive prover that are writable and completeness of the interactive entry, to
  completeness of the constructed prover and verifier.
- **Every premise at once.** At the toy package, in the model in which its layout has the
  laws, each of the four statements with every premise discharged: `serialize_complete`
  (`Toy.serialized_complete`); `fiatShamir_serialize_complete`, for a suite whose start and
  absorption are functions of the package (`Toy.constructed_complete`); `construct_complete`,
  for a declaration that names such a suite and a layout of the six rows
  (`Toy.Declared.declared_complete`); and `serializeProtocols_complete`, for the serialize
  step of that declaration alone (`Toy.Declared.authored_complete`). The conclusion of each
  is completeness of two role programs without a hypothesis. The kernel evaluates the
  programs: the prover returns the proof of `true` and the verifier returns `true` on it.
- **A law that fails.** In the model whose `take` returns another value the same role
  programs are not a complete scheme: the verifier stops on the proof that the prover
  returns (`Toy.flipped_not_complete`).

What is not checked here: the laws of the canonical layout, that the messages of the
interactive provers of the fixtures are writable, and completeness of the interactive
protocols of the fixtures. These are what `CompleteFrom` leaves at each fixture. The
statements in the model of the vocabulary, with the laws of the canonical layout derived,
are in `Tests/Core/VocabularyScheme.lean`.

The axioms of every theorem of `Zkc.Core.DerivedScheme` and of the checks are printed at the
end. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace DerivedScheme

/-! ## The values -/

/-- The outputs of a verifier, role 1, before which the proof of a prover, role 0, was put,
are read back. -/
theorem verifier_outputs_read_back (model : Model) (ports : List Located)
    (outputs : Values model.Value (own 1 ports)) :
    outputsWithoutProof model
        (inputsWithoutProof model (proof := .bool) (rest := ports) (by decide : (1 : Nat) ≠ 0)
          outputs) = outputs :=
  outputsWithoutProof_inputsWithoutProof _ outputs

/-- A role that holds the proof itself loses it in the reading: the reading is the identity
only for a verifier that is not the prover. -/
theorem own_proof_dropped (model : Model) :
    outputsWithoutProof model (prover := 0) (verifier := 0) (proof := .bool) (rest := [])
        (Values.cons (ty := Ty.bool) true .nil) = .nil :=
  rfl

/-! ## `StatementCopiesEqual`

A protocol of three roles with one agreed input, a `bool` that each role holds, for the side
of all three. The condition of the statements asks that the prover's copy and the verifier's
copy are equal and nothing of the third role's copy; `StatementAgrees` asks that all three
are equal. -/

namespace Copies

/-- The header: one agreement of the three copies. -/
abbrev threeHeader : ProtocolHeader :=
  ⟨3, [⟨.bool, 0⟩, ⟨.bool, 1⟩, ⟨.bool, 2⟩], [],
    ⟨[⟨.bool, ⟨0, .here⟩, [⟨1, .there .here⟩, ⟨2, .there (.there .here)⟩]⟩], []⟩, false⟩

/-- The side of every role. -/
abbrev everyRole : Side := fun _ => true

/-- The three copies, as the side holds them. -/
abbrev copies (model : Model) (atProver atVerifier atThird : Bool) :
    Values (SideValue model everyRole) threeHeader.inputs :=
  .cons (ty := (⟨.bool, 0⟩ : Located)) atProver
    (.cons (ty := (⟨.bool, 1⟩ : Located)) atVerifier
      (.cons (ty := (⟨.bool, 2⟩ : Located)) atThird .nil))

-- The statement of the header is its one agreement, and the copies of the prover and of the
-- verifier are its first two inputs.
kernel_refl statement :
  statementOf Threading.roles threeHeader equals
    [⟨.bool, ⟨0, .here⟩, [⟨1, .there .here⟩, ⟨2, .there (.there .here)⟩]⟩]

/-- The one agreement. -/
abbrev agreement : Agreement threeHeader.inputs :=
  ⟨.bool, ⟨0, .here⟩, [⟨1, .there .here⟩, ⟨2, .there (.there .here)⟩]⟩

kernel_refl prover_copy : agreement.copyOf 0 equals some .here

kernel_refl verifier_copy : agreement.copyOf 1 equals some (.there .here)

/-- Equal copies of the prover and the verifier satisfy the condition, whatever the third
role holds. -/
theorem two_copies_equal (model : Model) (copy third : Bool) :
    StatementCopiesEqual model everyRole Threading.roles threeHeader
      (copies model copy copy third) := by
  intro isProver isVerifier found member
  rw [statement] at member
  cases List.mem_singleton.mp member
  exact ⟨.here, .there .here, prover_copy, verifier_copy, rfl⟩

/-- A third copy that differs fails `StatementAgrees`: it is the stronger condition. -/
theorem third_copy_disagrees (model : Model) :
    ¬ StatementAgrees model everyRole Threading.roles threeHeader
      (copies model true true false) := by
  intro agrees
  have holds := agrees agreement (by rw [statement]; exact List.mem_singleton.mpr rfl)
  have equal : true = false :=
    holds ⟨0, .here⟩ List.mem_cons_self ⟨2, .there (.there .here)⟩
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) rfl rfl
  exact Bool.noConfusion equal

/-- Different copies of the prover and the verifier fail the condition: it is a condition on
the inputs. -/
theorem different_copies_unequal (model : Model) (third : Bool) :
    ¬ StatementCopiesEqual model everyRole Threading.roles threeHeader
      (copies model true false third) := by
  intro equal
  obtain ⟨atProver, atVerifier, hasProver, hasVerifier, same⟩ :=
    equal rfl rfl agreement (by rw [statement]; exact List.mem_singleton.mpr rfl)
  cases Option.some.inj (hasProver.symm.trans prover_copy)
  cases Option.some.inj (hasVerifier.symm.trans verifier_copy)
  exact Bool.noConfusion same

end Copies

/-! ## `Resends` -/

/-- The handler that performs every effect as it is sends only values of a condition, at a
`send` of such a value and at every other effect. -/
theorem passing_resends (model : Model) (Sendable : (type : Ty) → model.Value type → Prop) :
    Resends Sendable (passHandler model Unit) :=
  fun effect state sends => passEffect_sends effect state sends

/-- A handler that sends `true` before every effect. -/
def leaking (model : Model) : PIR.StatefulInterpretation (Effects model) (Effects model) Unit :=
  fun effect state => .call (.send ⟨[], 0, 0⟩ .bool true) fun _ => passEffect effect state

/-- It does not send only values of the condition that holds of no value. -/
theorem leaking_not_resends (model : Model) : ¬ Resends (fun _ _ => False) (leaking model) :=
  fun resends => (resends (.receive ⟨[], 0, 0⟩ .bool) () True.intro).1

/-- A process of one effect: it receives a value and returns it. -/
def receives (model : Model) : PIR.Process (Effects model) Bool :=
  .call (.receive ⟨[], 0, 0⟩ .bool) .done

/-- It sends nothing. -/
theorem receives_sends_nothing (model : Model) :
    EverySend (fun _ _ => False) (fun _ => True) (receives model) :=
  fun _ => True.intro

/-- Under the handler that performs every effect it sends nothing: `EverySend.interpretWith`
at that handler. -/
theorem passed_sends_nothing (model : Model) :
    EverySend (fun _ _ => False) (fun _ => True)
      ((receives model).interpretWith (passHandler model Unit) ()) :=
  EverySend.interpretWith (passing_resends model _) (receives model) ()
    (receives_sends_nothing model)

/-- Under the handler that sends before every effect it sends: the condition on the handler
is needed. -/
theorem leaked_sends (model : Model) :
    ¬ EverySend (fun _ _ => False) (fun _ => True)
      ((receives model).interpretWith (leaking model) ()) :=
  fun sent => sent.1

/-! ## `Layout.Carries` and `RegionCarries` -/

namespace Carried

open SerializeReplay.Toy (typed rows layout roles)

/-- The layout of the toy package carries `bool`. -/
theorem carries_bool : layout.Carries .bool := ⟨rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- The same layout without a row that puts a value. -/
noncomputable def bare : Layout rows := { layout with put := fun _ => none }

/-- It carries no type. -/
theorem bare_not_carries (type : Ty) : ¬ bare.Carries type := by
  rintro ⟨_, ⟨put, row⟩, _⟩
  cases row

/-- A region of one exchange of a `bool` from the prover to the verifier. -/
noncomputable def exchanging :
    Region (ProtocolDialect rows typed.functions [] true) [⟨.bool, 0⟩] [] :=
  .letOp (.exchange 0 1 0 .bool) (.cons .here .nil) .nil (.ret .nil)

/-- The layout carries its message. -/
theorem exchanging_carried : RegionCarries layout roles exchanging :=
  ⟨fun _ _ => carries_bool, trivial, trivial⟩

/-- The layout without the row does not. -/
theorem exchanging_not_carried : ¬ RegionCarries bare roles exchanging :=
  fun carried => bare_not_carries .bool (carried.1 rfl rfl)

-- The serialize step refuses the package over the layout without the row: the message of
-- its exchange has no row.
kernel_refl bare_refused :
  (stepProtocols bare.threads (serializeRule bare) Identities.written 0 roles
    typed.program.protocols).isOk equals false

end Carried

/-! ## The Fiat–Shamir image of an entry for the prover alone -/

namespace Sends

open ThreadTogether.Returning (typed suite entry entryHeader once onceEntry)

/-- The condition that a value is a number. -/
abbrev numbers (model : Model) : (type : Ty) → model.Value type → Prop :=
  fun type _ => type = .nat

/-- The entry for the prover alone. -/
noncomputable abbrev interactive (model : Model) :
    PIR.Process (Effects model) (Values (SideValue model (single 0)) entryHeader.outputs) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get entry [] (single 0) .nil

/-- Its Fiat–Shamir image for the prover alone. -/
noncomputable abbrev derived (model : Model) :
    PIR.Process (Effects model) (Values (SideValue model (single 0)) entryHeader.outputs) :=
  (once.protocols.table model (typed.program.functionTable model) once.identities).get onceEntry
    [] (single 0) .nil

/-- The entry for the prover alone sends the number 5 and receives the verifier's coin. -/
theorem interactive_shape (model : Model) :
    interactive model =
      .call (.send ⟨[], 0, 0⟩ .nat (5 : Nat)) fun _ =>
        .call (.receive ⟨[], 0, 1⟩ (.nominal 0)) fun _ =>
          .done (.cons (ty := (⟨.nat, 1⟩ : Located)) PUnit.unit .nil) :=
  kernel_rfl%

/-- Every value that it sends is a number. -/
theorem interactive_sends (model : Model) :
    EverySend (numbers model) (fun _ => True) (interactive model) := by
  rw [interactive_shape]
  exact ⟨rfl, fun _ => True.intro⟩

/-- `fiatShamir_sends` at the package, with every premise discharged: every value that the
image sends for the prover alone is a number. -/
theorem derived_sends (model : Model) :
    EverySend (numbers model) (fun _ => True) (derived model) := by
  obtain ⟨image, first, sends⟩ := fiatShamir_sends suite
    (Functions.table_quiet typed.program.functions) Identities.written 0 Threading.roles
    typed.program.protocols once (Threading.okValue_eq _ _) entry rfl
  have same : image = onceEntry := Var.ext first
  subst same
  exact sends [] (single 0) rfl rfl .nil (numbers model) (fun _ => True) (interactive_sends model)

/-- The image as the kernel evaluates it: it sends the number 5 and derives the coin
instead of receiving it. -/
theorem derived_shape (model : Model) :
    derived model =
      .call (.send ⟨[], 0, 0⟩ .nat (5 : Nat)) fun _ =>
        .done (.cons (ty := (⟨.nat, 1⟩ : Located)) PUnit.unit .nil) :=
  kernel_rfl%

end Sends

/-! ## `construct_complete` at the fixtures -/

/-- The image of a declared value under a function is the function's value at it. -/
theorem map_get {α β : Type} (function : α → β) :
    ∀ (value : Option α) (isSome : value.isSome = true),
      value.map function = some (function (value.get isSome))
  | some _, _ => rfl

/-- What is left of `construct_complete` at a package and a declaration, once the premises
that say which programs were constructed and `Suite.Returns` are discharged: for every
model, from the laws of the layout, inputs on which the prover's and the verifier's copies
of the statement are equal, messages of the interactive prover that the layout can write
and completeness of the interactive entry, completeness of the constructed prover and
verifier, with the interactive condition read on the outputs of the constructed verifier. -/
def CompleteFrom (typed : Typed) (declaration : Raw.Declaration)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (differ : declaration.roles.prover ≠ declaration.roles.verifier)
    (layout : Layout (typed.table.map (·.signature))) {header : ProtocolHeader}
    (declared : Var typed.protocols header)
    (derived : Projected (typed.table.map (·.signature)) typed.functions serialized.headers)
    (derivedProver : Var derived.headers
      (roleHeader declaration.roles.prover
        ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
          header)))
    (derivedVerifier : Var derived.headers
      (roleHeader declaration.roles.verifier
        ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
          header))) : Prop :=
  ∀ (model : Model) (laws : layout.Lawful model)
    (inputs : Values
      (SideValue model
        ((single declaration.roles.prover).union (single declaration.roles.verifier)))
      header.inputs),
    StatementCopiesEqual model
      ((single declaration.roles.prover).union (single declaration.roles.verifier))
      declaration.roles header inputs →
    EverySend laws.Writable (fun _ => True)
      ((typed.program.protocolTable model Identities.written).get declared []
        (single declaration.roles.prover)
        (leftValues model (single declaration.roles.prover) (single declaration.roles.verifier)
          inputs)) →
    ∀ acceptedInteractive :
      Values model.Value (own declaration.roles.verifier header.outputs) → Prop,
    GroupedComplete
      ((typed.program.protocolTable model Identities.written).get declared []
        ((single declaration.roles.prover).union (single declaration.roles.verifier)) inputs)
      (fun outputs => acceptedInteractive (verifierShare model declaration.roles outputs)) →
    DerivedComplete
      (((derived.programs.table model (typed.program.functionTable model)
            serialized.identities).get derivedProver []
          (inputsWithoutProof model differ (proverShare model declaration.roles inputs))).bind
        fun outputs => .done (provedOutputs model declaration.roles.prover outputs))
      (fun proof =>
        (derived.programs.table model (typed.program.functionTable model)
            serialized.identities).get derivedVerifier []
          (proofInputs model declaration.roles.verifier proof
            (verifierShare model declaration.roles inputs)))
      (fun outputs => acceptedInteractive (outputsWithoutProof model outputs))

/-- `construct_complete` at a package and a declaration, for the constructed entry and its
two role programs: what is left when the premises that say which programs were constructed
hold and the suite returns in every model. -/
theorem complete_from (typed : Typed) (declaration : Raw.Declaration)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (constructs : construct typed declaration = .ok serialized)
    (suite : Suite (typed.table.map (·.signature)) typed.functions)
    (isSuite : declaration.suite.map
        (Suite.ofRaw (tableScope (typed.table.map (·.signature))) (tableScope typed.functions)) =
      some suite)
    (returns : ∀ model : Model, suite.Returns (typed.program.functionTable model))
    (layout : Layout (typed.table.map (·.signature)))
    (isLayout : declaration.layout.bind
        (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    {header : ProtocolHeader} (declared : Var typed.protocols header)
    (isEntry : declared.index = typed.protocols.length - 1 - declaration.entry)
    (derived : Projected (typed.table.map (·.signature)) typed.functions serialized.headers)
    (projectsDerived : projectProtocols serialized.protocols = .ok derived)
    (constructed : Var serialized.headers
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        header))
    (newest : constructed.index = 0)
    (derivedProver : Var derived.headers
      (roleHeader declaration.roles.prover
        ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
          header)))
    (derivedVerifier : Var derived.headers
      (roleHeader declaration.roles.verifier
        ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
          header)))
    (namedProver : derived.callees.find constructed declaration.roles.prover = some derivedProver)
    (namedVerifier :
      derived.callees.find constructed declaration.roles.verifier = some derivedVerifier) :
    CompleteFrom typed declaration serialized
      (construct_roles_differ typed declaration serialized constructs) layout declared derived
      derivedProver derivedVerifier := by
  intro model laws inputs agrees writable acceptedInteractive complete
  obtain ⟨found, isNewest, derives⟩ := construct_complete (model := model) typed declaration
    serialized constructs suite isSuite layout isLayout declared isEntry derived projectsDerived
  have same : found = constructed := Var.ext (isNewest.trans newest.symm)
  subst same
  exact derives derivedProver derivedVerifier namedProver namedVerifier (returns model) laws
    inputs agrees writable acceptedInteractive complete

/-! ### `collecting` -/

namespace Collecting

open Threading (typed declaration suite layout twice rounds roundsHeader okValue okValue_eq)

/-- The pipeline of the declaration has the result of the two steps. -/
theorem constructs : construct typed declaration = .ok twice :=
  Threading.construct_is_step.trans Threading.serialize_steps

kernel_refl result_projects : (projectProtocols twice.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def derived :
    Projected (typed.table.map (·.signature)) typed.functions twice.headers :=
  okValue (projectProtocols twice.protocols) result_projects

-- The newest protocol of the result has the header of the constructed entry.
kernel_refl newest_header : twice.headers[0]? equals
  some ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
    roundsHeader)

/-- The constructed entry. -/
noncomputable def constructed : Var twice.headers
    ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
      roundsHeader) :=
  ⟨0, newest_header⟩

kernel_refl prover_named :
  (derived.callees.find constructed declaration.roles.prover).isSome equals true
kernel_refl verifier_named :
  (derived.callees.find constructed declaration.roles.verifier).isSome equals true

/-- The constructed prover and verifier. -/
noncomputable def derivedProver : Var derived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        roundsHeader)) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        roundsHeader)) :=
  Option.get _ verifier_named

/-- `construct_complete` at `collecting`: what is left. The result of the pipeline, the
suite and the layout of the declaration, the position of the entry, the projection of the
result and its two role programs are evaluated by the kernel; the suite returns because it
is a catalogue suite. -/
theorem complete :
    CompleteFrom typed declaration twice
      (construct_roles_differ typed declaration twice constructs) layout rounds derived
      derivedProver derivedVerifier :=
  complete_from typed declaration twice constructs suite
    (map_get _ _ Threading.suite_declared) ThreadTogether.collecting_returns layout
    (Option.some_get Threading.layout_declared).symm rounds kernel_rfl% derived
    (okValue_eq _ result_projects) constructed rfl derivedProver derivedVerifier
    (Option.some_get prover_named).symm (Option.some_get verifier_named).symm

end Collecting

/-! ### `sumcheck` -/

namespace Sumcheck

open ThreadingSumcheck (typed declaration suite layout twice sumcheck sumcheckHeader)
open Threading (okValue okValue_eq)

/-- The pipeline of the declaration has the result of the two steps. -/
theorem constructs : construct typed declaration = .ok twice :=
  ThreadingSumcheck.construct_is_step.trans ThreadingSumcheck.serialize_steps

kernel_refl result_projects : (projectProtocols twice.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def derived :
    Projected (typed.table.map (·.signature)) typed.functions twice.headers :=
  okValue (projectProtocols twice.protocols) result_projects

kernel_refl newest_header : twice.headers[0]? equals
  some ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
    sumcheckHeader)

/-- The constructed entry. -/
noncomputable def constructed : Var twice.headers
    ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
      sumcheckHeader) :=
  ⟨0, newest_header⟩

kernel_refl prover_named :
  (derived.callees.find constructed declaration.roles.prover).isSome equals true
kernel_refl verifier_named :
  (derived.callees.find constructed declaration.roles.verifier).isSome equals true

/-- The constructed prover and verifier. -/
noncomputable def derivedProver : Var derived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        sumcheckHeader)) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        sumcheckHeader)) :=
  Option.get _ verifier_named

/-- `construct_complete` at `sumcheck`, a package with an applied protocol that the
serialize step threads and with functions: what is left. -/
theorem complete :
    CompleteFrom typed declaration twice
      (construct_roles_differ typed declaration twice constructs) layout sumcheck derived
      derivedProver derivedVerifier :=
  complete_from typed declaration twice constructs suite
    (map_get _ _ ThreadingSumcheck.suite_declared) ThreadTogether.sumcheck_returns layout
    (Option.some_get ThreadingSumcheck.layout_declared).symm sumcheck kernel_rfl% derived
    (okValue_eq _ result_projects) constructed rfl derivedProver derivedVerifier
    (Option.some_get prover_named).symm (Option.some_get verifier_named).symm

end Sumcheck

/-! ### `schnorr-source` -/

namespace Schnorr

open ThreadingSchnorr (typed declaration suite layout twice schnorr schnorrHeader)
open Threading (okValue okValue_eq)

/-- The pipeline of the declaration has the result of the two steps. -/
theorem constructs : construct typed declaration = .ok twice :=
  ThreadingSchnorr.construct_is_step.trans ThreadingSchnorr.serialize_steps

kernel_refl result_projects : (projectProtocols twice.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def derived :
    Projected (typed.table.map (·.signature)) typed.functions twice.headers :=
  okValue (projectProtocols twice.protocols) result_projects

kernel_refl newest_header : twice.headers[0]? equals
  some ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
    schnorrHeader)

/-- The constructed entry. -/
noncomputable def constructed : Var twice.headers
    ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
      schnorrHeader) :=
  ⟨0, newest_header⟩

kernel_refl prover_named :
  (derived.callees.find constructed declaration.roles.prover).isSome equals true
kernel_refl verifier_named :
  (derived.callees.find constructed declaration.roles.verifier).isSome equals true

/-- The constructed prover and verifier. -/
noncomputable def derivedProver : Var derived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        schnorrHeader)) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
        schnorrHeader)) :=
  Option.get _ verifier_named

/-- `construct_complete` at `schnorr-source`, whose suite calls functions of the package:
what is left. `Suite.Returns` is discharged, because each of the six functions returns on
every input in every model. -/
theorem complete :
    CompleteFrom typed declaration twice
      (construct_roles_differ typed declaration twice constructs) layout schnorr derived
      derivedProver derivedVerifier :=
  complete_from typed declaration twice constructs suite
    (map_get _ _ ThreadingSchnorr.suite_declared) ThreadTogether.schnorr_returns layout
    (Option.some_get ThreadingSchnorr.layout_declared).symm schnorr kernel_rfl% derived
    (okValue_eq _ result_projects) constructed rfl derivedProver derivedVerifier
    (Option.some_get prover_named).symm (Option.some_get verifier_named).symm

end Schnorr

/-! ## Every premise at once

The toy package of `Tests/Core/SerializeReplay.lean`: the prover sends `true`, and the
verifier stops `reject` unless what it receives holds and returns it. In the model that
does not flip its layout has the laws. -/

namespace Toy

open SerializeReplay.Toy (typed rows layout model laws roles header entry both serialized steps
  serializedHeader serializedEntry entryMeaning writable every accepted returned stopped)
open Threading (okValue okValue_eq)

/-- The prover and the verifier are two roles. -/
theorem roles_differ : roles.prover ≠ roles.verifier := by decide

/-- The interactive condition on what the verifier holds of the outputs: its result is
`true`. -/
abbrev acceptedOwn (flip : Bool) : Values (model flip).Value (own 1 header.outputs) → Prop :=
  fun outputs => outputs.get .here = true

/-- The result of a derived verifier: its outputs, read as the outputs of the interactive
verifier, of which it holds one. The proof is an output of the prover. -/
noncomputable abbrev verifierResult (flip : Bool)
    (outputs : Values (model flip).Value (own 1 (⟨layout.proof, 0⟩ :: header.outputs))) : Bool :=
  (outputsWithoutProof (model flip) outputs).get .here

/-- The condition on the outputs of a derived verifier: the interactive condition, read on
them. -/
abbrev acceptedDerived (flip : Bool) :
    Values (model flip).Value (own 1 (⟨layout.proof, 0⟩ :: header.outputs)) → Prop :=
  fun outputs => acceptedOwn flip (outputsWithoutProof (model flip) outputs)

/-- The entry is complete for every sampler, with the verifier's result `true` accepted. -/
theorem complete (flip : Bool) :
    GroupedComplete (entryMeaning flip [] both .nil)
      (fun outputs => acceptedOwn flip (verifierShare (model flip) roles outputs)) :=
  (EveryRun.mono
    (fun outputs holds => by
      match outputs, holds with
      | .cons value .nil, holds => exact holds)
    (every flip)).groupedComplete

/-! ### The serialize step alone -/

kernel_refl result_projects : (projectProtocols serialized.protocols).isOk equals true

/-- The role programs of the serialized package. -/
noncomputable def derived : Projected rows typed.functions serialized.headers :=
  okValue (projectProtocols serialized.protocols) result_projects

kernel_refl prover_named : (derived.callees.find serializedEntry 0).isSome equals true
kernel_refl verifier_named : (derived.callees.find serializedEntry 1).isSome equals true

/-- The programs of the prover and of the verifier of the serialized entry. -/
noncomputable def derivedProver : Var derived.headers (roleHeader 0 serializedHeader) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers (roleHeader 1 serializedHeader) :=
  Option.get _ verifier_named

/-- The derived prover, in a model: the program of the prover on the prover's share of no
input; it returns the proof before its other outputs. -/
noncomputable def prover (flip : Bool) :=
  ((derived.programs.table (model flip) (typed.program.functionTable (model flip))
        serialized.identities).get derivedProver []
      (inputsWithoutProof (model flip) (proof := layout.proof) (rest := header.inputs) roles_differ
        (proverShare (model flip) roles .nil))).bind fun outputs =>
    .done (provedOutputs (model flip) roles.prover outputs)

/-- The derived verifier, in a model: the program of the verifier on a proof. -/
noncomputable def verifier (flip : Bool) (proof : List Bool) :=
  (derived.programs.table (model flip) (typed.program.functionTable (model flip))
      serialized.identities).get derivedVerifier []
    (proofInputs (model flip) roles.verifier (proof := layout.proof) (rest := header.inputs) proof
      (verifierShare (model flip) roles .nil))

/-- `serialize_complete` at the package, the layout and the model that has the laws, with
every premise discharged: the equation of the step, the position of the entry, the
projection and the two role programs by the kernel; the laws of the layout; the messages of
the prover, which are writable; and completeness of the entry. The scheme of the two role
programs is complete, with the verifier's result `true` accepted. -/
theorem serialized_complete :
    DerivedComplete (prover false) (verifier false) (acceptedDerived false) := by
  obtain ⟨found, isNewest, derives⟩ := serialize_complete (model := model false) layout
    Identities.written 0 roles typed.program serialized steps entry kernel_rfl% derived
    (okValue_eq _ result_projects)
  have same : found = serializedEntry := Var.ext isNewest
  subst same
  exact derives derivedProver derivedVerifier (Option.some_get prover_named).symm
    (Option.some_get verifier_named).symm laws .nil writable (acceptedOwn false) (complete false)

-- The two programs as the kernel evaluates them: the prover returns the proof of `true`,
-- and the verifier returns `true` on it.
kernel_refl prover_proves :
  (returned (prover false)).map (fun result => (result.1 : List Bool)) equals some [true]

kernel_refl verifier_accepts :
  (returned (verifier false [true])).map (verifierResult false) equals some true

/-! ### A law that fails -/

-- In the model that flips, the prover returns the proof of `true`, and the verifier stops
-- `reject` on it: it takes `false`.
kernel_refl flipped_prover_proves :
  (returned (prover true)).map (fun result => (result.1 : List Bool)) equals some [true]

kernel_refl flipped_verifier_rejects : stopped (verifier true [true]) equals some .reject

/-- Over the layout without the laws the same two role programs are not a complete scheme,
even when every result is accepted, although the entry is complete (`complete true`): the
verifier stops on the proof that the prover returns. -/
theorem flipped_not_complete : ¬ DerivedComplete (prover true) (verifier true) (fun _ => True) := by
  intro derives
  obtain ⟨proof, values, proves, result, verifies, _⟩ := derives (Sampler.constant (model true))
  have observed := flipped_prover_proves
  have isProof : proof = [true] := by
    generalize prover true = process at observed proves
    cases proves with
    | done value asked => exact Option.some.inj observed
    | draw site law inputs next asked value returns => cases observed
    | sample site law inputs next asked value returns => cases observed
  subst isProof
  have rejects := flipped_verifier_rejects
  generalize verifier true [true] = process at rejects verifies
  cases verifies with
  | done value asked => cases rejects
  | draw site law inputs next asked value returns => cases rejects
  | sample site law inputs next asked value returns => cases rejects

/-! ### The Fiat–Shamir step and then the serialize step

A suite over the two functions of the package: the transcript state is a `bool`, a role
starts it with the function that returns `false`, and it absorbs a `bool` with the function
that returns the absorbed value. -/

/-- The suite. -/
noncomputable def suite : Suite rows typed.functions where
  state := .bool
  start := fun statement =>
    match statement with
    | [] => some (.handler ⟨1, kernel_rfl%⟩)
    | _ :: _ => none
  absorb := fun _ type =>
    match type with
    | .bool => some (.handler ⟨0, kernel_rfl%⟩)
    | _ => none
  derive := fun _ _ _ => none

/-- Each of the two functions returns on every input, in both models. -/
theorem functions_return (flip : Bool) :
    FunctionsReturn (typed.program.functionTable (model flip)) := by
  intro header callee inputs
  obtain ⟨index, valid⟩ := callee
  match index, valid with
  | 0, valid => cases Option.some.inj valid; exact ThreadTogether.returns_done kernel_rfl%
  | 1, valid => cases Option.some.inj valid; exact ThreadTogether.returns_done kernel_rfl%
  | index + 2, valid => cases valid

/-- The suite returns. -/
theorem suite_returns (flip : Bool) : suite.Returns (typed.program.functionTable (model flip)) :=
  FunctionsReturn.suite (functions_return flip) suite

/-- The Fiat–Shamir step on the protocols of the package. -/
noncomputable abbrev fiatShamirStep :
    Except StepRefusal (Stepped typed.typeTable rows typed.functions) :=
  stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) Identities.written 0 roles
    typed.program.protocols

kernel_refl fiatShamir_returns : fiatShamirStep.isOk equals true

noncomputable def once : Stepped typed.typeTable rows typed.functions :=
  okValue fiatShamirStep fiatShamir_returns

-- The step rewrote the entry: both roles absorb the message.
kernel_refl once_rewritten : once.rewroteEntry equals true

/-- The serialize step on the result, with the newest protocol as the entry. -/
noncomputable abbrev serializeStep :
    Except StepRefusal (Stepped typed.typeTable rows typed.functions) :=
  stepProtocols layout.threads (serializeRule layout) once.identities (once.headers.length - 1)
    roles once.protocols

kernel_refl serialize_returns : serializeStep.isOk equals true

noncomputable def twice : Stepped typed.typeTable rows typed.functions :=
  okValue serializeStep serialize_returns

/-- The constructed entry: the newest protocol after both steps. -/
noncomputable abbrev constructedEntry : Var twice.headers serializedHeader := ⟨0, kernel_rfl%⟩

kernel_refl constructed_projects : (projectProtocols twice.protocols).isOk equals true

/-- The role programs of the constructed package. -/
noncomputable def constructed : Projected rows typed.functions twice.headers :=
  okValue (projectProtocols twice.protocols) constructed_projects

kernel_refl constructed_prover_named :
  (constructed.callees.find constructedEntry 0).isSome equals true
kernel_refl constructed_verifier_named :
  (constructed.callees.find constructedEntry 1).isSome equals true

/-- The programs of the prover and of the verifier of the constructed entry. -/
noncomputable def constructedProver : Var constructed.headers (roleHeader 0 serializedHeader) :=
  Option.get _ constructed_prover_named

noncomputable def constructedVerifier : Var constructed.headers (roleHeader 1 serializedHeader) :=
  Option.get _ constructed_verifier_named

-- The entry has no input, so its statement is empty.
kernel_refl no_statement : statementOf roles header equals []

/-- The inputs agree on the statement: every copy that the side holds is equal, which gives
the condition of the statements, that the prover's and the verifier's copies are
(`StatementAgrees.copiesEqual`). -/
theorem inputs_agree (flip : Bool) : StatementAgrees (model flip) both roles header .nil := by
  intro agreement member
  rw [no_statement] at member
  cases member

/-- The constructed prover, in a model. -/
noncomputable def constructedProves (flip : Bool) :=
  ((constructed.programs.table (model flip) (typed.program.functionTable (model flip))
        twice.identities).get constructedProver []
      (inputsWithoutProof (model flip) (proof := layout.proof) (rest := header.inputs) roles_differ
        (proverShare (model flip) roles .nil))).bind fun outputs =>
    .done (provedOutputs (model flip) roles.prover outputs)

/-- The constructed verifier, in a model, on a proof. -/
noncomputable def constructedVerifies (flip : Bool) (proof : List Bool) :=
  (constructed.programs.table (model flip) (typed.program.functionTable (model flip))
      twice.identities).get constructedVerifier []
    (proofInputs (model flip) roles.verifier (proof := layout.proof) (rest := header.inputs) proof
      (verifierShare (model flip) roles .nil))

/-- `fiatShamir_serialize_complete` at the package, the suite, the layout and the model that
has the laws, with every premise discharged: the equations of the two steps, the position
of the entry, the projection and the two role programs by the kernel; the suite, which
returns; the laws of the layout; the inputs, which agree on the statement; the messages of
the interactive prover, which are writable; and completeness of the interactive entry. The
scheme of the two constructed role programs is complete, with the verifier's result `true`
accepted. -/
theorem constructed_complete :
    DerivedComplete (constructedProves false) (constructedVerifies false)
      (acceptedDerived false) := by
  obtain ⟨found, isNewest, derives⟩ := fiatShamir_serialize_complete (model := model false) suite
    layout Identities.written 0 roles typed.program once (okValue_eq _ fiatShamir_returns) twice
    (okValue_eq _ serialize_returns) entry kernel_rfl% constructed
    (okValue_eq _ constructed_projects)
  have same : found = constructedEntry := Var.ext isNewest
  subst same
  exact derives constructedProver constructedVerifier
    (Option.some_get constructed_prover_named).symm
    (Option.some_get constructed_verifier_named).symm (suite_returns false) laws .nil
    (inputs_agree false).copiesEqual writable (acceptedOwn false) (complete false)

-- The two constructed programs as the kernel evaluates them: the prover returns the proof
-- of `true`, and the verifier returns `true` on it.
kernel_refl constructed_prover_proves :
  (returned (constructedProves false)).map (fun result => (result.1 : List Bool))
  equals some [true]

kernel_refl constructed_verifier_accepts :
  (returned (constructedVerifies false [true])).map (verifierResult false) equals some true

/-! ### The pipeline of a declaration

A declaration for the package: the entry, the prover and the verifier; a source suite of
the two functions; and a layout of the six rows. `construct` on it is the two steps above,
with the suite and the layout that the declaration names. -/

namespace Declared

open SerializeReplay.Toy (wire encode)

/-- The declaration. -/
abbrev declaration : Raw.Declaration :=
  ⟨0, 0, 1, [0, 1], some (.source .bool 0 [1] [] [[]]),
    some ⟨wire, wire, wire, 0, 2, 3, 5, [1], [4]⟩⟩

kernel_refl construct_accepts : (construct typed declaration).isOk equals true

/-- The result of the pipeline. -/
noncomputable def result : Stepped typed.typeTable rows typed.functions :=
  okValue (construct typed declaration) construct_accepts

/-- The suite that the declaration names. -/
noncomputable def declaredSuite : Suite rows typed.functions :=
  Suite.ofRaw (tableScope rows) (tableScope typed.functions) (.source .bool 0 [1] [] [[]])

/-- The layout that the declaration names: the rows that put and take a value of a type are
looked up among the declared ones. -/
noncomputable def declaredLayout : Layout rows where
  writer := wire
  reader := wire
  proof := wire
  writerPopulated := rfl
  readerPopulated := rfl
  proofPopulated := rfl
  start := ⟨0, kernel_rfl%⟩
  put := fun type => firstRowWith (tableScope rows) ⟨[wire, type], [wire], .pure⟩ [1]
  close := ⟨2, kernel_rfl%⟩
  read := ⟨3, kernel_rfl%⟩
  take := fun type => firstRowWith (tableScope rows) ⟨[wire], [.bool, type, wire], .pure⟩ [4]
  exhausted := ⟨5, kernel_rfl%⟩

/-- The declaration names it. -/
theorem names_layout :
    declaration.layout.bind (Layout.ofRaw (tableScope rows)) = some declaredLayout :=
  kernel_rfl%

-- The rows that the layout has for `bool`.
kernel_refl puts_bool : declaredLayout.put .bool equals some ⟨1, kernel_rfl%⟩
kernel_refl takes_bool : declaredLayout.take .bool equals some ⟨4, kernel_rfl%⟩

/-- The declared layout has the laws in the model that does not flip: every value of `bool`
is writable. -/
noncomputable def declaredLaws : declaredLayout.Lawful (model false) where
  Wire := List Bool
  empty := []
  append := fun first second => first ++ second
  append_assoc := List.append_assoc
  empty_append := List.nil_append
  append_empty := List.append_nil
  encode := encode false
  Writable := fun type _ => type = .bool
  ofWriter := fun writer => writer
  toReader := fun content => content
  start_empty := rfl
  put_appends := by
    intro type put row value writable writer
    subst writable
    have same : put = ⟨1, kernel_rfl%⟩ := Option.some.inj (row.symm.trans puts_bool)
    subst same
    cases value <;> rfl
  close_read := fun _ => rfl
  take_reads := by
    intro type take populated row value writable rest
    subst writable
    have same : take = ⟨4, kernel_rfl%⟩ := Option.some.inj (row.symm.trans takes_bool)
    subst same
    cases value <;> rfl
  exhausted_empty := rfl

kernel_refl result_projects : (projectProtocols result.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def derived : Projected rows typed.functions result.headers :=
  okValue (projectProtocols result.protocols) result_projects

/-- The constructed entry: the newest protocol of the result. -/
noncomputable def constructedEntry : Var result.headers
    ((serializeRule (functions := typed.functions) declaredLayout).entryHeader declaration.roles
      header) :=
  ⟨0, kernel_rfl%⟩

kernel_refl prover_named :
  (derived.callees.find constructedEntry declaration.roles.prover).isSome equals true
kernel_refl verifier_named :
  (derived.callees.find constructedEntry declaration.roles.verifier).isSome equals true

/-- The constructed prover and verifier. -/
noncomputable def derivedProver : Var derived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) declaredLayout).entryHeader
        declaration.roles header)) :=
  Option.get _ prover_named

noncomputable def derivedVerifier : Var derived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) declaredLayout).entryHeader
        declaration.roles header)) :=
  Option.get _ verifier_named

/-- The pipeline of the declaration has the result. -/
theorem constructs : construct typed declaration = .ok result := okValue_eq _ construct_accepts

/-- `construct_complete` at the package and the declaration: what is left. -/
theorem complete_from_declaration :
    CompleteFrom typed declaration result
      (construct_roles_differ typed declaration result constructs) declaredLayout entry derived
      derivedProver derivedVerifier :=
  complete_from typed declaration result constructs declaredSuite rfl
    (fun flip => FunctionsReturn.suite
      (fun {header} callee inputs => by
        obtain ⟨index, valid⟩ := callee
        match index, valid with
        | 0, valid => cases Option.some.inj valid; exact ThreadTogether.returns_done kernel_rfl%
        | 1, valid => cases Option.some.inj valid; exact ThreadTogether.returns_done kernel_rfl%
        | index + 2, valid => cases valid)
      declaredSuite)
    declaredLayout names_layout entry kernel_rfl% derived (okValue_eq _ result_projects)
    constructedEntry rfl derivedProver derivedVerifier (Option.some_get prover_named).symm
    (Option.some_get verifier_named).symm

/-- The constructed prover, in the model that has the laws. -/
noncomputable def proves :=
  ((derived.programs.table (model false) (typed.program.functionTable (model false))
        result.identities).get derivedProver []
      (inputsWithoutProof (model false) (proof := declaredLayout.proof) (rest := header.inputs)
        (construct_roles_differ typed declaration result constructs)
        (proverShare (model false) declaration.roles .nil))).bind fun outputs =>
    .done (provedOutputs (model false) declaration.roles.prover outputs)

/-- The constructed verifier, in the model that has the laws, on a proof. -/
noncomputable def verifies (proof : List Bool) :=
  (derived.programs.table (model false) (typed.program.functionTable (model false))
      result.identities).get derivedVerifier []
    (proofInputs (model false) declaration.roles.verifier (proof := declaredLayout.proof)
      (rest := header.inputs) proof (verifierShare (model false) declaration.roles .nil))

/-- `construct_complete` at the package, its declaration and the model in which the
declared layout has the laws, with every premise discharged: the result of the pipeline,
the suite and the layout that the declaration names, the position of the entry, the
projection and the two role programs by the kernel; the suite, which returns; the laws of
the layout; the inputs, which agree on the statement; the messages of the interactive
prover, which are writable; and completeness of the interactive entry. The scheme of the
constructed prover and verifier is complete, with the verifier's result `true` accepted. -/
theorem declared_complete : DerivedComplete proves verifies (acceptedDerived false) :=
  complete_from_declaration (model false) declaredLaws .nil (inputs_agree false).copiesEqual
    writable (acceptedOwn false) (complete false)

-- The two programs as the kernel evaluates them.
kernel_refl prover_proves :
  (returned proves).map (fun result => (result.1 : List Bool)) equals some [true]

kernel_refl verifier_accepts :
  (returned (verifies [true])).map (verifierResult false) equals some true

/-! #### The serialize step of the declaration alone

The package read as a construction whose Fiat–Shamir step is authored: the serialize step
of the declaration on its protocols. -/

kernel_refl serialize_accepts :
  (serializeProtocols declaration Identities.written typed.program.protocols).isOk equals true

/-- The result of the serialize step of the declaration. -/
noncomputable def authored : Stepped typed.typeTable rows typed.functions :=
  okValue (serializeProtocols declaration Identities.written typed.program.protocols)
    serialize_accepts

kernel_refl authored_projects : (projectProtocols authored.protocols).isOk equals true

/-- The role programs of the result. -/
noncomputable def authoredDerived : Projected rows typed.functions authored.headers :=
  okValue (projectProtocols authored.protocols) authored_projects

/-- The serialized entry: the newest protocol of the result. -/
noncomputable def authoredEntry : Var authored.headers
    ((serializeRule (functions := typed.functions) declaredLayout).entryHeader declaration.roles
      header) :=
  ⟨0, kernel_rfl%⟩

kernel_refl authored_prover_named :
  (authoredDerived.callees.find authoredEntry declaration.roles.prover).isSome equals true
kernel_refl authored_verifier_named :
  (authoredDerived.callees.find authoredEntry declaration.roles.verifier).isSome equals true

/-- The derived prover and verifier. -/
noncomputable def authoredProver : Var authoredDerived.headers
    (roleHeader declaration.roles.prover
      ((serializeRule (functions := typed.functions) declaredLayout).entryHeader
        declaration.roles header)) :=
  Option.get _ authored_prover_named

noncomputable def authoredVerifier : Var authoredDerived.headers
    (roleHeader declaration.roles.verifier
      ((serializeRule (functions := typed.functions) declaredLayout).entryHeader
        declaration.roles header)) :=
  Option.get _ authored_verifier_named

/-- The derived prover, in the model that has the laws. -/
noncomputable def authoredProves :=
  ((authoredDerived.programs.table (model false) (typed.program.functionTable (model false))
        authored.identities).get authoredProver []
      (inputsWithoutProof (model false) (proof := declaredLayout.proof) (rest := header.inputs)
        roles_differ (proverShare (model false) declaration.roles .nil))).bind fun outputs =>
    .done (provedOutputs (model false) declaration.roles.prover outputs)

/-- The derived verifier, in the model that has the laws, on a proof. -/
noncomputable def authoredVerifies (proof : List Bool) :=
  (authoredDerived.programs.table (model false) (typed.program.functionTable (model false))
      authored.identities).get authoredVerifier []
    (proofInputs (model false) declaration.roles.verifier (proof := declaredLayout.proof)
      (rest := header.inputs) proof (verifierShare (model false) declaration.roles .nil))

/-- `serializeProtocols_complete` at the package, its declaration and the model in which
the declared layout has the laws, with every premise discharged: no suite and no condition
on the inputs. -/
theorem authored_complete :
    DerivedComplete authoredProves authoredVerifies (acceptedDerived false) := by
  obtain ⟨found, isNewest, derives⟩ := serializeProtocols_complete (model := model false)
    declaration Identities.written typed.program authored (okValue_eq _ serialize_accepts)
    declaredLayout names_layout entry rfl authoredDerived (okValue_eq _ authored_projects)
  have same : found = authoredEntry := Var.ext isNewest
  subst same
  exact derives authoredProver authoredVerifier (Option.some_get authored_prover_named).symm
    (Option.some_get authored_verifier_named).symm declaredLaws .nil writable (acceptedOwn false)
    (complete false)

end Declared

end Toy

end DerivedScheme

/-! ## Axioms -/

section Axioms

open Zkc.Core

-- The condition on the inputs (`Zkc.Core.ThreadTogetherFiatShamir`).
#print axioms StatementAgrees.copiesEqual
#print axioms EntryCouples.of_stronger
#print axioms fiatShamirEntry_couples_of_copies
#print axioms fiatShamir_entry_together_of_copies
#print axioms fiatShamir_together

-- `Zkc.Core.DerivedScheme`
#print axioms outputsWithoutProof_inputsWithoutProof
#print axioms consKept_unkeep_absent
#print axioms inputsWithoutProof_outputsWithoutProof
#print axioms unkeep_consKept_value
#print axioms ownValues_proof
#print axioms ownValues_withoutProof
#print axioms ReturnsAlone.map
#print axioms threadHandler_resends
#print axioms Deriver.run_quiet
#print axioms fiatShamirMeaning_resends
#print axioms fiatShamir_sends
#print axioms fiatShamir_serialize_replays
#print axioms SerializedReplaysOn.derivedComplete
#print axioms serialize_complete
#print axioms fiatShamir_serialize_complete
#print axioms serializeProtocols_steps
#print axioms serializeProtocols_complete
#print axioms construct_roles_differ
#print axioms construct_complete

-- The condition on the sends of a process under a handler (`Zkc.Core.SerializeReplay`).
#print axioms EverySend.of_quiet
#print axioms EverySend.after_quiet
#print axioms passEffect_sends
#print axioms EverySend.interpretWith

-- The checks of this file.
#print axioms DerivedScheme.verifier_outputs_read_back
#print axioms DerivedScheme.own_proof_dropped
#print axioms DerivedScheme.Copies.two_copies_equal
#print axioms DerivedScheme.Copies.third_copy_disagrees
#print axioms DerivedScheme.Copies.different_copies_unequal
#print axioms DerivedScheme.passing_resends
#print axioms DerivedScheme.leaking_not_resends
#print axioms DerivedScheme.passed_sends_nothing
#print axioms DerivedScheme.leaked_sends
#print axioms DerivedScheme.Carried.carries_bool
#print axioms DerivedScheme.Carried.bare_not_carries
#print axioms DerivedScheme.Carried.exchanging_carried
#print axioms DerivedScheme.Carried.exchanging_not_carried
#print axioms DerivedScheme.Carried.bare_refused
#print axioms DerivedScheme.Sends.interactive_sends
#print axioms DerivedScheme.Sends.derived_sends
#print axioms DerivedScheme.Sends.derived_shape
#print axioms DerivedScheme.complete_from
#print axioms DerivedScheme.Collecting.complete
#print axioms DerivedScheme.Sumcheck.complete
#print axioms DerivedScheme.Schnorr.complete
#print axioms DerivedScheme.Toy.complete
#print axioms DerivedScheme.Toy.serialized_complete
#print axioms DerivedScheme.Toy.flipped_not_complete
#print axioms DerivedScheme.Toy.suite_returns
#print axioms DerivedScheme.Toy.inputs_agree
#print axioms DerivedScheme.Toy.constructed_complete
#print axioms DerivedScheme.Toy.Declared.names_layout
#print axioms DerivedScheme.Toy.Declared.complete_from_declaration
#print axioms DerivedScheme.Toy.Declared.declared_complete
#print axioms DerivedScheme.Toy.Declared.authored_complete

end Axioms
