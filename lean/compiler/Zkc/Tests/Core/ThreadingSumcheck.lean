import Zkc.Tests.Core.Threading

/-! The whole-program theorem of a threading step, applied to `sumcheck`.

`fixtures/construction/sumcheck.json` is the package that the frontend printed for
`sumcheck`: three functions, the protocol `round`, in which the prover sends two sums and
the verifier draws a challenge for the prover, and the entry `sumcheck`, which applies
`round` in a loop. Unlike the package of `Tests/Core/Threading.lean` it has functions, and
its applied protocol still has exchanges after the Fiat–Shamir step, so both steps make an
image of it that threads.

What is checked, for an arbitrary model:

- the functions of the package perform no effect (`Functions.table_quiet` at a table of
  three functions);
- `stepProtocols_entry` at each step and `stepProtocols_twice_entry` for the two together,
  with every hypothesis discharged from the package;
- `rewriteProtocols_threads` at each step: the image of `round` after the Fiat–Shamir step
  is `round` interpreted by every handler that follows its marks, and the image of that
  image after the serialize step is it interpreted by every handler that follows its marks;
- the marks of both steps below the site of the application, as the kernel evaluates them.

What is not checked here: the statements for the prover alone and for the verifier alone
with the entry's start and finish written out, the hypotheses one by one
(`Tests/Core/ThreadingWitnesses.lean`), and a run of the programs
(`Tests/Core/ConstructSumcheck.lean`). -/

set_option autoImplicit false

open Zkc.Source Zkc.Core
open Threading (okValue okValue_eq newest_entry fiatShamir_of_suite serializeProtocols_of_layout
  construct_of_fiatShamir marksAt interactions roles)

namespace ThreadingSumcheck

raw_package raw from file "fixtures/construction/sumcheck.json"
raw_declaration declaration from file "fixtures/construction/sumcheck.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

-- The entry is the protocol 1, the prover the role 0 and the verifier the role 1.
kernel_refl declared : (declaration.entry, declaration.prover, declaration.verifier) equals
  (1, 0, 1)

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

/-! ## The functions -/

/-- The meanings of the functions of the package. -/
noncomputable abbrev functionTable (model : Model) : FunctionTable model typed.functions :=
  typed.program.functionTable model

-- The package has three functions.
kernel_refl functions_counted : typed.functions.length equals 3

/-- They perform no effect. -/
theorem quiet (model : Model) : QuietTable (functionTable model) :=
  Functions.table_quiet typed.program.functions

/-- The newest of them, `final_check`. -/
noncomputable abbrev finalCheck : Var typed.functions (typed.functions.headD default) :=
  ⟨0, kernel_rfl%⟩

/-- So `final_check` returns or stops, on every argument. -/
theorem finalCheck_quiet (model : Model)
    (arguments : Values model.Value (typed.functions.headD default).inputs) :
    ((functionTable model).get finalCheck arguments).Quiet :=
  quiet model finalCheck arguments

/-! ## The Fiat–Shamir step -/

kernel_refl suite_declared : declaration.suite.isSome equals true

/-- The suite of the declaration, over the rows of the package. -/
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
  stepProtocols suiteThreads suiteRule Identities.written 1 roles typed.program.protocols

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

/-- The header of the entry `sumcheck`, the newest protocol, and the entry. -/
noncomputable abbrev sumcheckHeader : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev sumcheck : Var typed.protocols sumcheckHeader := ⟨0, kernel_rfl%⟩

/-- The header of the entry after the Fiat–Shamir step, and its image. -/
noncomputable abbrev onceHeader : ProtocolHeader := suiteRule.entryHeader roles sumcheckHeader

noncomputable abbrev onceEntry : Var once.headers onceHeader := ⟨0, kernel_rfl%⟩

/-- The marks of the Fiat–Shamir step, at a site relative to the entry. -/
noncomputable abbrev fiatShamirMarks : Site → Option (Mark operations) :=
  stepMarks suiteThreads suiteRule Identities.written 1 roles typed.program.protocols

/-- `stepProtocols_entry` at the package and the Fiat–Shamir rule. -/
theorem fiatShamir_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) (suiteRule.entryPorts roles sumcheckHeader).inputs) :
    (once.protocols.table model (functionTable model) once.identities).get onceEntry path side
        arguments =
      ((suiteEntry model).start side roles sumcheckHeader arguments).bind fun state =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get
              sumcheck path side
              ((suiteEntry model).arguments side roles sumcheckHeader arguments)).interpretWith
            (threadHandler (suiteMeaning model) (marksBelow path fiatShamirMarks)
              (side roles.prover) (side roles.verifier)) state).bind fun result =>
          (suiteEntry model).finish side roles sumcheckHeader result := by
  obtain ⟨origin, earlier, newest, isEntry⟩ := newest_entry once_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_entry (quiet model)
    (fiatShamirRule_sound suite (functionTable model))
    (fiatShamirEntry_sound suite (functionTable model)) Identities.written 1 roles
    typed.program.protocols once fiatShamir_steps sumcheck rfl origin earlier newest isEntry
  have same : image = onceEntry := Var.ext first
  subst same
  exact threads path side one arguments

/-! ## The applied protocol under the Fiat–Shamir step -/

/-- The header of the applied protocol `round`, and the protocol. -/
noncomputable abbrev roundHeader : ProtocolHeader := typed.protocols.tail.headD default

noncomputable abbrev round : Var typed.protocols roundHeader := ⟨1, kernel_rfl%⟩

/-- The images that the Fiat–Shamir step makes of the protocols. -/
noncomputable abbrev fiatShamirImages :
    Except StepRefusal
      (Rewritten suiteThreads typed.typeTable operations typed.functions typed.protocols) :=
  rewriteProtocols suiteThreads suiteRule Identities.written typed.program.protocols
    (entryDemands typed.protocols.length 1 roles)

kernel_refl fiatShamir_images : fiatShamirImages.isOk equals true

noncomputable def onceImages :
    Rewritten suiteThreads typed.typeTable operations typed.functions typed.protocols :=
  okValue fiatShamirImages fiatShamir_images

theorem fiatShamir_rewrites : fiatShamirImages = .ok onceImages := okValue_eq _ _

/-- The result of the step is these images. -/
theorem once_images :
    once = ⟨onceImages.new, onceImages.protocols, onceImages.origins, onceImages.counted⟩ := by
  obtain ⟨rewritten, rewrites, same⟩ := stepProtocols_rewritten Identities.written 1 roles
    typed.program.protocols once fiatShamir_steps
  have unique : rewritten = onceImages := Except.ok.inj (rewrites.symm.trans fiatShamir_rewrites)
  subst unique
  exact same

-- `round` has an image that threads for the two roles.
kernel_refl round_threaded : (onceImages.table.find round (some roles)).isSome equals true

/-- The image of `round` that threads. -/
noncomputable def onceRound :
    Var onceImages.new (Threads.header suiteThreads (some roles) roundHeader) :=
  (onceImages.table.find round (some roles)).get round_threaded

/-- `rewriteProtocols_threads` at the package and the Fiat–Shamir rule: the image of `round`
is `round` interpreted by every handler that follows its marks, for every side with exactly
one transcript role. -/
theorem fiatShamir_round_threads (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (handler : ThreadHandler model suiteThreads (side roles.prover) (side roles.verifier))
    (follows : Follows (suiteMeaning model) (side roles.prover) (side roles.verifier) handler path
      (onceImages.marks.get round roles))
    (state : ThreadState model suiteThreads (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) roundHeader.inputs) :
    (onceImages.protocols.table model (functionTable model)
          (originIdentities onceImages.origins)).get onceRound path side
        (.cons state.1 (.cons state.2 arguments)) =
      (((typed.program.protocols.table model (functionTable model) Identities.written).get
            round path side arguments).interpretWith handler state).bind fun result =>
        .done (threadedValues result) := by
  have callees := rewriteProtocols_threads (quiet model)
    (fiatShamirRule_sound suite (functionTable model)) Identities.written typed.program.protocols
    _ onceImages fiatShamir_rewrites
  exact callees.threaded round roles onceRound (Option.some_get _).symm path side
    (side roles.prover) (side roles.verifier) rfl rfl handler
    (by rw [stepFits_get]; exact ⟨one, follows⟩) state.1 state.2 arguments

-- `round`, the protocol with the identity 0: the prover sends at the sites 0 and 1 and the
-- verifier draws for the prover at the site 2. `sumcheck`, with the identity 1, applies
-- `round` at the site 0.
kernel_refl written_interactions : raw.protocols.map (fun protocol => interactions protocol.body)
  equals [[("exchange", [0, 1], 0), ("exchange", [0, 1], 1), ("draw", [1, 0], 2)],
    [("apply", [0], 0)]]

-- The marks of the step: the three operations of `round` below the site of the
-- application, and no site of the entry itself.
kernel_refl fiatShamir_marks :
  marksAt fiatShamirMarks [⟨[0], 0, 0⟩, ⟨[0], 0, 1⟩, ⟨[0], 0, 2⟩, ⟨[0], 0, 3⟩, ⟨[], 1, 0⟩] equals
    [some (.exchange 0 0 1 false 0), some (.exchange 0 0 1 false 1),
      some (.draw true 0 0 1 false 2 0), none, none]

-- The marks of `round` for the two roles are the same, at its own sites.
kernel_refl round_marks :
  marksAt (onceImages.marks.get round roles) [⟨[], 0, 0⟩, ⟨[], 0, 1⟩, ⟨[], 0, 2⟩, ⟨[], 0, 3⟩]
    equals
    [some (.exchange 0 0 1 false 0), some (.exchange 0 0 1 false 1),
      some (.draw true 0 0 1 false 2 0), none]

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

/-- `stepProtocols_twice_entry` at the package. -/
theorem fiatShamir_then_serialize_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) (layoutRule.entryPorts roles onceHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry path side
        arguments =
      (composedStart (suiteEntry model) (layoutEntry model) side roles sumcheckHeader
          arguments).bind fun states =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get
              sumcheck path side
              (composedArguments (suiteEntry model) (layoutEntry model) side roles sumcheckHeader
                arguments)).interpretWith
            (PIR.composeHandlers
              (threadHandler (suiteMeaning model) (marksBelow path fiatShamirMarks)
                (side roles.prover) (side roles.verifier))
              (threadHandler (layoutMeaning model) (marksBelow path serializeMarks)
                (side roles.prover) (side roles.verifier))) states).bind fun result =>
          composedFinish (suiteEntry model) (layoutEntry model) side roles sumcheckHeader
            result := by
  obtain ⟨firstOrigin, firstEarlier, firstNewest, firstEntry⟩ := newest_entry once_newest
  obtain ⟨secondOrigin, secondEarlier, secondNewest, secondEntry⟩ := newest_entry twice_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_twice_entry (quiet model)
    (fiatShamirRule_sound suite (functionTable model))
    (fiatShamirEntry_sound suite (functionTable model))
    (serializeRule_sound layout (functionTable model))
    (serializeEntry_sound layout (functionTable model)) Identities.written 1 roles
    typed.program.protocols once fiatShamir_steps twice serialize_steps sumcheck rfl ((Stepped.rewroteEntry_of_newest firstNewest).trans firstEntry)
    ((Stepped.rewroteEntry_of_newest secondNewest).trans secondEntry)
  have same : image = twiceEntry := Var.ext first
  subst same
  exact threads path side one arguments

/-! ## The applied protocol under the serialize step -/

/-- The header of the image of `round` after the Fiat–Shamir step, and the image among the
protocols of the first result. -/
noncomputable abbrev onceRoundHeader : ProtocolHeader :=
  Threads.header suiteThreads (some roles) roundHeader

noncomputable abbrev onceCallee : Var once.headers onceRoundHeader := ⟨1, kernel_rfl%⟩

/-- The images that the serialize step makes of the protocols of the first result. -/
noncomputable abbrev serializeImages :
    Except StepRefusal
      (Rewritten layoutThreads typed.typeTable operations typed.functions once.headers) :=
  rewriteProtocols layoutThreads layoutRule once.identities once.protocols
    (entryDemands once.headers.length (once.headers.length - 1) roles)

kernel_refl serialize_images : serializeImages.isOk equals true

noncomputable def twiceImages :
    Rewritten layoutThreads typed.typeTable operations typed.functions once.headers :=
  okValue serializeImages serialize_images

theorem serialize_rewrites : serializeImages = .ok twiceImages := okValue_eq _ _

-- The image of `round` keeps its two exchanges: the serialize step makes an image of it
-- that threads, and no copy.
kernel_refl callee_threaded : (twiceImages.table.find onceCallee (some roles)).isSome equals true
kernel_refl callee_not_copied : (twiceImages.table.find onceCallee none).isSome equals false

/-- The image, after the serialize step, of the image of `round`. -/
noncomputable def twiceCallee :
    Var twiceImages.new (Threads.header layoutThreads (some roles) onceRoundHeader) :=
  (twiceImages.table.find onceCallee (some roles)).get callee_threaded

/-- `rewriteProtocols_threads` at the result of the Fiat–Shamir step and the serialize
rule: the image of the image of `round` is that image interpreted by every handler that
follows its marks, for every side with exactly one transcript role. -/
theorem serialize_round_threads (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (handler : ThreadHandler model layoutThreads (side roles.prover) (side roles.verifier))
    (follows : Follows (layoutMeaning model) (side roles.prover) (side roles.verifier) handler path
      (twiceImages.marks.get onceCallee roles))
    (state : ThreadState model layoutThreads (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) onceRoundHeader.inputs) :
    (twiceImages.protocols.table model (functionTable model)
          (originIdentities twiceImages.origins)).get twiceCallee path side
        (.cons state.1 (.cons state.2 arguments)) =
      (((once.protocols.table model (functionTable model) once.identities).get onceCallee path
            side arguments).interpretWith handler state).bind fun result =>
        .done (threadedValues result) := by
  have callees := rewriteProtocols_threads (quiet model)
    (serializeRule_sound layout (functionTable model)) once.identities once.protocols _
    twiceImages serialize_rewrites
  exact callees.threaded onceCallee roles twiceCallee (Option.some_get _).symm path side
    (side roles.prover) (side roles.verifier) rfl rfl handler
    (by rw [stepFits_get]; exact ⟨one, follows⟩) state.1 state.2 arguments

-- The marks of the serialize step: the two exchanges of the image of `round` below the
-- site of the application; the draw is derived after the first step and is not marked.
kernel_refl serialize_marks :
  marksAt serializeMarks [⟨[0], 0, 0⟩, ⟨[0], 0, 1⟩, ⟨[0], 0, 2⟩, ⟨[], 1, 0⟩] equals
    [some (.exchange 0 0 1 false 0), some (.exchange 0 0 1 false 1), none, none]

#print axioms finalCheck_quiet
#print axioms fiatShamir_is_step
#print axioms construct_is_step
#print axioms fiatShamir_entry
#print axioms fiatShamir_round_threads
#print axioms serialize_entry
#print axioms serialize_round_threads
#print axioms fiatShamir_then_serialize_entry

end ThreadingSumcheck
