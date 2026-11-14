import Zkc.Tests.Core.Threading

/-! The whole-program theorem of a threading step, applied to `schnorr` with a suite of
functions.

`fixtures/construction/schnorr-source.json` is the package that the frontend printed for
`schnorr` with a suite written in the source: one protocol, in which the prover samples a
nonce, sends a commitment, receives a challenge that the verifier draws, and sends a
response; and six functions, which the declaration names as the start, the absorptions and
the derivation of the suite. Unlike the packages of `Tests/Core/Threading.lean` and
`Tests/Core/ThreadingSumcheck.lean`, the rule of this suite calls functions, the entry has
a statement that both roles absorb, and the rewritten operations are operations of the
entry itself.

What is checked, for an arbitrary model:

- the six functions perform no effect (`Functions.table_quiet`);
- `stepProtocols_entry` at each step and `stepProtocols_twice_entry` for the two together,
  with every hypothesis discharged from the package;
- the start of the entry returns for the prover alone and for the verifier alone, whatever
  the inputs: the start function of the suite is found and called on the statement;
- the marks of both steps: the two exchanges and the draw, and not the prover's sample.

What is not checked here: an applied protocol (the package has none), the hypotheses one
by one (`Tests/Core/ThreadingWitnesses.lean`), and a run of the programs
(`Tests/Core/ConstructSchnorrSource.lean` compares the results with the tool's). -/

set_option autoImplicit false

open Zkc.Source Zkc.Core
open Threading (okValue okValue_eq newest_entry fiatShamir_of_suite serializeProtocols_of_layout
  construct_of_fiatShamir marksAt interactions returns roles)

namespace ThreadingSchnorr

raw_package raw from file "fixtures/construction/schnorr-source.json"
raw_declaration declaration from file "fixtures/construction/schnorr-source.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

-- The entry is the protocol 0, the prover the role 0 and the verifier the role 1.
kernel_refl declared : (declaration.entry, declaration.prover, declaration.verifier) equals
  (0, 0, 1)

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

/-- The meanings of the functions of the package. -/
noncomputable abbrev functionTable (model : Model) : FunctionTable model typed.functions :=
  typed.program.functionTable model

-- The package has six functions.
kernel_refl functions_counted : typed.functions.length equals 6

/-- They perform no effect. -/
theorem quiet (model : Model) : QuietTable (functionTable model) :=
  Functions.table_quiet typed.program.functions

/-- The header of the entry `schnorr`, and the entry. -/
noncomputable abbrev schnorrHeader : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev schnorr : Var typed.protocols schnorrHeader := ⟨0, kernel_rfl%⟩

/-! ## The Fiat–Shamir step -/

kernel_refl suite_declared : declaration.suite.isSome equals true

/-- The suite of the declaration, over the functions of the package. -/
noncomputable def suite : Suite operations typed.functions :=
  Suite.ofRaw (tableScope operations) (tableScope typed.functions)
    (declaration.suite.get suite_declared)

/-- The Fiat–Shamir rule of the suite, with its threaded types, what it does and what its
entry does. -/
noncomputable abbrev suiteThreads : Threads := ⟨suite.state, suite.state⟩

noncomputable abbrev suiteRule : Rule suiteThreads operations typed.functions :=
  fiatShamirRule suite

noncomputable abbrev suiteMeaning (model : Model) : RuleMeaning model suiteThreads operations :=
  fiatShamirMeaning suite (functionTable model)

noncomputable abbrev suiteEntry (model : Model) : EntryMeaning model suiteThreads suiteRule :=
  fiatShamirEntry suite (functionTable model)

/-- The Fiat–Shamir step on the protocols of the package, with the declared entry. -/
noncomputable abbrev fiatShamirStep :
    Except StepRefusal (Stepped typed.typeTable operations typed.functions) :=
  stepProtocols suiteThreads suiteRule Identities.written 0 roles typed.program.protocols

kernel_refl third_role_free :
  thirdRoleRefusal typed.program.protocols
    (List.replicate (typed.protocols.length - 1 - declaration.entry) [] ++
      [[(⟨some declaration.prover, some declaration.verifier, declaration.online⟩ : Reach)]])
  equals none

/-- The step of the tool on the package is this step. -/
theorem fiatShamir_is_step : fiatShamir typed declaration = fiatShamirStep :=
  fiatShamir_of_suite typed declaration (declaration.suite.get suite_declared) rfl third_role_free

kernel_refl fiatShamir_returns : fiatShamirStep.isOk equals true

noncomputable def once : Stepped typed.typeTable operations typed.functions :=
  okValue fiatShamirStep fiatShamir_returns

theorem fiatShamir_steps : fiatShamirStep = .ok once := okValue_eq _ _

kernel_refl once_newest : once.origins.head?.map (·.entry) equals some true

/-- The header of the entry after the Fiat–Shamir step, and its image. -/
noncomputable abbrev onceHeader : ProtocolHeader := suiteRule.entryHeader roles schnorrHeader

noncomputable abbrev onceEntry : Var once.headers onceHeader := ⟨0, kernel_rfl%⟩

/-- The marks of the Fiat–Shamir step, at a site relative to the entry. -/
noncomputable abbrev fiatShamirMarks : Site → Option (Mark operations) :=
  stepMarks suiteThreads suiteRule Identities.written 0 roles typed.program.protocols

/-- `stepProtocols_entry` at the package and the Fiat–Shamir rule. -/
theorem fiatShamir_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) (suiteRule.entryPorts roles schnorrHeader).inputs) :
    (once.protocols.table model (functionTable model) once.identities).get onceEntry path side
        arguments =
      ((suiteEntry model).start side roles schnorrHeader arguments).bind fun state =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get
              schnorr path side
              ((suiteEntry model).arguments side roles schnorrHeader arguments)).interpretWith
            (threadHandler (suiteMeaning model) (marksBelow path fiatShamirMarks)
              (side roles.prover) (side roles.verifier)) state).bind fun result =>
          (suiteEntry model).finish side roles schnorrHeader result := by
  obtain ⟨origin, earlier, newest, isEntry⟩ := newest_entry once_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_entry (quiet model)
    (fiatShamirRule_sound suite (functionTable model))
    (fiatShamirEntry_sound suite (functionTable model)) Identities.written 0 roles
    typed.program.protocols once fiatShamir_steps schnorr rfl origin earlier newest isEntry
  have same : image = onceEntry := Var.ext first
  subst same
  exact threads path side one arguments

/-- The start of the entry returns, for the prover alone and for the verifier alone,
whatever the inputs: each role calls the start function of the suite on its copies of the
statement. -/
theorem fiatShamir_start_returns_prover (model : Model)
    (arguments : Values (SideValue model (single 0)) schnorrHeader.inputs) :
    returns ((suiteEntry model).start (single 0) roles schnorrHeader arguments) = true :=
  kernel_rfl%

theorem fiatShamir_start_returns_verifier (model : Model)
    (arguments : Values (SideValue model (single 1)) schnorrHeader.inputs) :
    returns ((suiteEntry model).start (single 1) roles schnorrHeader arguments) = true :=
  kernel_rfl%

-- The prover sends at the sites 1 and 3 and the verifier draws for the prover at the
-- site 2; the site 0 is the prover's sample, which is not an interaction.
kernel_refl written_interactions : raw.protocols.map (fun protocol => interactions protocol.body)
  equals [[("exchange", [0, 1], 1), ("draw", [1, 0], 2), ("exchange", [0, 1], 3)]]

-- The marks of the step: the two exchanges and the draw, and not the sample.
kernel_refl fiatShamir_marks :
  marksAt fiatShamirMarks [⟨[], 0, 0⟩, ⟨[], 0, 1⟩, ⟨[], 0, 2⟩, ⟨[], 0, 3⟩, ⟨[], 0, 4⟩] equals
    [none, some (.exchange 0 0 1 false 1), some (.draw true 0 0 1 false 2 0),
      some (.exchange 0 0 1 false 3), none]

/-! ## The serialize step on the result -/

kernel_refl layout_declared :
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome equals true

/-- The layout of the declaration, over the rows of the package. -/
noncomputable def layout : Layout operations :=
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).get layout_declared

/-- The serialize rule of the layout, with its threaded types, what it does and what its
entry does. -/
noncomputable abbrev layoutThreads : Threads := ⟨layout.writer, layout.reader⟩

noncomputable abbrev layoutRule : Rule layoutThreads operations typed.functions :=
  serializeRule layout

noncomputable abbrev layoutMeaning (model : Model) : RuleMeaning model layoutThreads operations :=
  serializeMeaning layout

noncomputable abbrev layoutEntry (model : Model) : EntryMeaning model layoutThreads layoutRule :=
  serializeEntry layout

/-- The serialize step on the result of the Fiat–Shamir step, with the newest protocol as
the entry. -/
noncomputable abbrev serializeStep :
    Except StepRefusal (Stepped typed.typeTable operations typed.functions) :=
  stepProtocols layoutThreads layoutRule once.identities (once.headers.length - 1) roles
    once.protocols

/-- The construction of the tool on the package is this step. -/
theorem construct_is_step : construct typed declaration = serializeStep :=
  (construct_of_fiatShamir typed declaration once
    (fiatShamir_is_step.trans fiatShamir_steps)).trans
    (serializeProtocols_of_layout declaration once.identities once.protocols layout
      (Option.some_get _).symm)

kernel_refl serialize_returns : serializeStep.isOk equals true

noncomputable def twice : Stepped typed.typeTable operations typed.functions :=
  okValue serializeStep serialize_returns

theorem serialize_steps : serializeStep = .ok twice := okValue_eq _ _

kernel_refl twice_newest : twice.origins.head?.map (·.entry) equals some true

/-- The header of the entry after both steps, and its image. -/
noncomputable abbrev twiceHeader : ProtocolHeader := layoutRule.entryHeader roles onceHeader

noncomputable abbrev twiceEntry : Var twice.headers twiceHeader := ⟨0, kernel_rfl%⟩

/-- The marks of the serialize step, at a site relative to the entry. -/
noncomputable abbrev serializeMarks : Site → Option (Mark operations) :=
  stepMarks layoutThreads layoutRule once.identities (once.headers.length - 1) roles once.protocols

/-- `stepProtocols_entry` at the result of the Fiat–Shamir step and the serialize rule. -/
theorem serialize_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) (layoutRule.entryPorts roles onceHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry path side
        arguments =
      ((layoutEntry model).start side roles onceHeader arguments).bind fun state =>
        (((once.protocols.table model (functionTable model) once.identities).get onceEntry path
              side ((layoutEntry model).arguments side roles onceHeader arguments)).interpretWith
            (threadHandler (layoutMeaning model) (marksBelow path serializeMarks)
              (side roles.prover) (side roles.verifier)) state).bind fun result =>
          (layoutEntry model).finish side roles onceHeader result := by
  obtain ⟨origin, earlier, newest, isEntry⟩ := newest_entry twice_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_entry (quiet model)
    (serializeRule_sound layout (functionTable model))
    (serializeEntry_sound layout (functionTable model)) once.identities
    (once.headers.length - 1) roles once.protocols twice serialize_steps onceEntry
    (Nat.sub_self _).symm origin earlier newest isEntry
  have same : image = twiceEntry := Var.ext first
  subst same
  exact threads path side one arguments

-- The marks of the serialize step: the two exchanges; the draw is derived after the first
-- step and is not marked.
kernel_refl serialize_marks :
  marksAt serializeMarks [⟨[], 0, 0⟩, ⟨[], 0, 1⟩, ⟨[], 0, 2⟩, ⟨[], 0, 3⟩] equals
    [none, some (.exchange 0 0 1 false 1), none, some (.exchange 0 0 1 false 3)]

/-- `stepProtocols_twice_entry` at the package. -/
theorem fiatShamir_then_serialize_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) (layoutRule.entryPorts roles onceHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry path side
        arguments =
      (composedStart (suiteEntry model) (layoutEntry model) side roles schnorrHeader
          arguments).bind fun states =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get
              schnorr path side
              (composedArguments (suiteEntry model) (layoutEntry model) side roles schnorrHeader
                arguments)).interpretWith
            (PIR.composeHandlers
              (threadHandler (suiteMeaning model) (marksBelow path fiatShamirMarks)
                (side roles.prover) (side roles.verifier))
              (threadHandler (layoutMeaning model) (marksBelow path serializeMarks)
                (side roles.prover) (side roles.verifier))) states).bind fun result =>
          composedFinish (suiteEntry model) (layoutEntry model) side roles schnorrHeader
            result := by
  obtain ⟨firstOrigin, firstEarlier, firstNewest, firstEntry⟩ := newest_entry once_newest
  obtain ⟨secondOrigin, secondEarlier, secondNewest, secondEntry⟩ := newest_entry twice_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_twice_entry (quiet model)
    (fiatShamirRule_sound suite (functionTable model))
    (fiatShamirEntry_sound suite (functionTable model))
    (serializeRule_sound layout (functionTable model))
    (serializeEntry_sound layout (functionTable model)) Identities.written 0 roles
    typed.program.protocols once fiatShamir_steps twice serialize_steps schnorr rfl ((Stepped.rewroteEntry_of_newest firstNewest).trans firstEntry)
    ((Stepped.rewroteEntry_of_newest secondNewest).trans secondEntry)
  have same : image = twiceEntry := Var.ext first
  subst same
  exact threads path side one arguments

#print axioms quiet
#print axioms fiatShamir_is_step
#print axioms construct_is_step
#print axioms fiatShamir_entry
#print axioms fiatShamir_start_returns_prover
#print axioms serialize_entry
#print axioms fiatShamir_then_serialize_entry

end ThreadingSchnorr
