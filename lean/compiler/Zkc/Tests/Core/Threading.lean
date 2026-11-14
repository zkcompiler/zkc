import Zkc.Tests.Core.Declare
import Zkc.Tests.Core.Reflexivity
import Zkc.Core.ThreadCompose
import Zkc.Core.ThreadEntryRules
import Zkc.Core.ThreadRules
import Zkc.Core.ThreadFiatShamir
import Zkc.Core.ThreadProgram
import Zkc.Core.ProjectMeaning

/-! The whole-program theorem of a threading step, applied to a program.

`fixtures/construction/collecting.json` has the protocol `rounds` of a prover and a
verifier: a loop in which the prover sends twice and the verifier draws a coin for the
prover, and a loop that applies the protocol `challenge`, in which the verifier draws a
coin for the prover. The declaration names `rounds` as the entry, the role 0 as the prover
and the role 1 as the verifier, a catalogue suite and a layout.

What is checked, for an arbitrary model:

- The Fiat–Shamir step of the tool on the package is `stepProtocols` with the rule of the
  declared suite, and it returns (`fiatShamir_is_step`, `fiatShamir_steps`); the
  construction of the tool is then `stepProtocols` with the rule of the declared layout on
  the first result, and it returns (`construct_is_step`, `serialize_steps`).
- `stepProtocols_entry` at each step (`fiatShamir_entry`, `serialize_entry`): the newest
  protocol of the result is the entry interpreted by the handler of the step's marks,
  between the start and the finish of the rule's entry, for every side with exactly one
  transcript role. Every hypothesis is discharged from the package: the equation of the
  step, the position of the entry and the origin of the newest image by the kernel, the
  functions without an effect by `Functions.table_quiet`, the rules and their entries by
  their soundness theorems. Each is also stated for the prover alone and for the verifier
  alone, with the memberships and the entry's start and finish written out, and the start
  of the Fiat–Shamir entry returns for each of them, whatever the inputs.
- `rewriteProtocols_threads`, through `stepProtocols_rewritten`, at the Fiat–Shamir step
  (`fiatShamir_challenge_threads`): the image of `challenge` that threads is `challenge`
  interpreted by every handler that follows its marks. The handler of those marks is one
  (`fiatShamir_challenge_handler`), and so is, below the site of the application, the
  handler that interprets the entry (`fiatShamir_challenge_under_entry_handler`).
- At the serialize step the image of `challenge` has no exchange left, so the step copies
  it: `rewriteProtocols_plain` gives that the copy has its meaning
  (`serialize_callee_copied`), and `rewriteProtocols_threads` applies
  (`serialize_callees`).
- `stepProtocols_twice_entry` for the two steps together
  (`fiatShamir_then_serialize_entry`).
- The marks of both steps, as the kernel evaluates them: an exchange from the prover to the
  verifier and a draw between the two are marked at their sites, the draw of `challenge`
  below the site of its application, and no other site.

What is not checked here: a protocol with an image that threads under the serialize step
and a package with functions (`Tests/Core/ThreadingSumcheck.lean` has both), a suite
whose rule calls functions (`Tests/Core/ThreadingSchnorr.lean`), and a run of the handlers
(`Tests/Core/ConstructCollecting.lean` runs the three programs with the executor). The
witnesses and the failing examples of the hypotheses are in
`Tests/Core/ThreadingWitnesses.lean`. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Threading

/-! ## What the checks use -/

/-- The value of a result that the kernel evaluates to one. -/
def okValue {ε α : Type} (result : Except ε α) (isOk : result.isOk = true) : α :=
  match result, isOk with
  | .ok value, _ => value

theorem okValue_eq {ε α : Type} (result : Except ε α) (isOk : result.isOk = true) :
    result = .ok (okValue result isOk) := by
  match result, isOk with
  | .ok value, _ => rfl

/-- The Fiat–Shamir step of the tool is the stepping transformer with the rule of the
declared suite, when no third role excludes the step. -/
theorem fiatShamir_of_suite (typed : Typed) (declaration : Raw.Declaration) (declared : Raw.Suite)
    (hasSuite : declaration.suite = some declared)
    (free : thirdRoleRefusal typed.program.protocols
      (List.replicate (typed.protocols.length - 1 - declaration.entry) [] ++
        [[(⟨some declaration.prover, some declaration.verifier, declaration.online⟩ : Reach)]]) =
      none) :
    fiatShamir typed declaration =
      stepProtocols
        ⟨(Suite.ofRaw (tableScope (typed.table.map (·.signature))) (tableScope typed.functions)
            declared).state,
          (Suite.ofRaw (tableScope (typed.table.map (·.signature))) (tableScope typed.functions)
            declared).state⟩
        (fiatShamirRule (Suite.ofRaw (tableScope (typed.table.map (·.signature)))
          (tableScope typed.functions) declared))
        Identities.written declaration.entry ⟨declaration.prover, declaration.verifier⟩
        typed.program.protocols := by
  unfold fiatShamir
  rw [hasSuite]
  simp only [free]

/-- The serialize step of the tool is the stepping transformer with the rule of the
declared layout, on the newest protocol. -/
theorem serializeProtocols_of_layout {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (declaration : Raw.Declaration) (identities : Identities)
    (program : Protocols typeTable operations functions protocols) (layout : Layout operations)
    (hasLayout : declaration.layout.bind (Layout.ofRaw (tableScope operations)) = some layout) :
    serializeProtocols declaration identities program =
      stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities
        (protocols.length - 1) ⟨declaration.prover, declaration.verifier⟩ program := by
  unfold serializeProtocols
  rw [hasLayout]

/-- The construction of the tool is its serialize step on the result of its Fiat–Shamir
step. -/
theorem construct_of_fiatShamir (typed : Typed) (declaration : Raw.Declaration)
    (once : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (steps : fiatShamir typed declaration = .ok once) :
    construct typed declaration =
      serializeProtocols declaration once.identities once.protocols := by
  unfold construct
  rw [steps]

/-- The newest protocol of a step's result whose newest origin is an entry. -/
theorem newest_entry {origins : List Origin}
    (isEntry : origins.head?.map (·.entry) = some true) :
    ∃ origin earlier, origins = origin :: earlier ∧ origin.entry = true := by
  cases origins with
  | nil => cases isEntry
  | cons origin earlier => exact ⟨origin, earlier, rfl, Option.some.inj isEntry⟩

/-- Whether a process returns at once. -/
def returns {model : Model} {α : Type} : PIR.Process (Effects model) α → Bool
  | .done _ => true
  | _ => false

/-- A mark as data: for an exchange the identity of the definition, the prover, the
verifier, whether the definition has several images, and the site; for a draw also whether
the verifier owns it and the number of its law. -/
inductive MarkData where
  | exchange (definition prover verifier : Nat) (specialized : Bool) (site : Nat)
  | draw (byVerifier : Bool) (definition prover verifier : Nat) (specialized : Bool)
      (site law : Nat)
  deriving Repr, DecidableEq

def markData {operations : List OperationSignature} : Mark operations → MarkData
  | .exchange place site =>
      .exchange place.definition place.roles.prover place.roles.verifier place.specialized site
  | .draw byVerifier place site law =>
      .draw byVerifier place.definition place.roles.prover place.roles.verifier place.specialized
        site law.index

mutual
  /-- The exchanges, draws and applications of a raw region, nested regions included, each
  with its site: an exchange with its sender and receiver, a draw with its owner and
  receivers, an application with its callee. -/
  def interactions : Raw.ProtocolRegion → List (String × List Nat × Nat)
    | .ret _ => []
    | .stop _ => []
    | .step (.exchange sender receiver site _) next =>
        ("exchange", [sender, receiver], site) :: interactions next
    | .step (.draw owner receivers site _ _) next =>
        ("draw", owner :: receivers, site) :: interactions next
    | .step (.apply callee _ site _) next => ("apply", [callee], site) :: interactions next
    | .step (.repeat _ _ _ _ _ body) next => interactions body ++ interactions next
    | .step (.choose _ _ _ _ _ arms) next => armInteractions arms ++ interactions next
    | .step _ next => interactions next
    | .block _ body next => interactions body ++ interactions next

  def armInteractions : Raw.ProtocolArms → List (String × List Nat × Nat)
    | .none => []
    | .arm region rest => interactions region ++ armInteractions rest
end

/-- The marks at several sites, as data. -/
abbrev marksAt {operations : List OperationSignature} (marks : Site → Option (Mark operations))
    (sites : List Site) : List (Option MarkData) :=
  sites.map fun site => (marks site).map markData

/-! ## The package -/

raw_package raw from file "fixtures/construction/collecting.json"
raw_declaration declaration from file "fixtures/construction/collecting.declaration.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

-- The entry is the protocol 1, the prover the role 0 and the verifier the role 1.
kernel_refl declared : (declaration.entry, declaration.prover, declaration.verifier) equals
  (1, 0, 1)

/-- The two transcript roles of the declaration. -/
abbrev roles : TranscriptRoles := ⟨0, 1⟩

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

/-- The meanings of the functions of the package. -/
noncomputable abbrev functionTable (model : Model) : FunctionTable model typed.functions :=
  typed.program.functionTable model

/-- The functions of the package perform no effect. The package has no function:
`Tests/Core/ThreadingSumcheck.lean` has the statement for a package with functions. -/
theorem quiet (model : Model) : QuietTable (functionTable model) :=
  Functions.table_quiet typed.program.functions

/-- The header of the entry `rounds`, the newest protocol, and the entry. -/
noncomputable abbrev roundsHeader : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev rounds : Var typed.protocols roundsHeader := ⟨0, kernel_rfl%⟩

/-- The header of the applied protocol `challenge`, and the protocol. -/
noncomputable abbrev challengeHeader : ProtocolHeader := typed.protocols.tail.headD default

noncomputable abbrev challenge : Var typed.protocols challengeHeader := ⟨1, kernel_rfl%⟩

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
  stepProtocols suiteThreads suiteRule Identities.written 1 roles
    typed.program.protocols

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

-- The result has two protocols: the image of the entry, the newest, and before it an image
-- of `challenge` that is not an entry.
kernel_refl once_origins : once.origins.map (fun origin => (origin.definition, origin.entry))
  equals [(1, true), (0, false)]

kernel_refl once_newest : once.origins.head?.map (·.entry) equals some true

/-- The header of the entry after the Fiat–Shamir step. -/
noncomputable abbrev onceHeader : ProtocolHeader :=
  (suiteRule.entryPorts roles roundsHeader).header roundsHeader

/-- The image of the entry: the newest protocol of the result. -/
noncomputable abbrev onceEntry : Var once.headers onceHeader := ⟨0, kernel_rfl%⟩

/-- The marks of the Fiat–Shamir step, at a site relative to the entry. -/
noncomputable abbrev fiatShamirMarks : Site → Option (Mark operations) :=
  stepMarks suiteThreads suiteRule Identities.written 1 roles
    typed.program.protocols

/-- `stepProtocols_entry` at the package and the Fiat–Shamir rule. -/
theorem fiatShamir_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side)
      (suiteRule.entryPorts roles roundsHeader).inputs) :
    (once.protocols.table model (functionTable model) once.identities).get onceEntry path side
        arguments =
      ((suiteEntry model).start side roles roundsHeader arguments).bind
        fun state =>
          (((typed.program.protocols.table model (functionTable model) Identities.written).get
                rounds path side
                ((suiteEntry model).arguments side roles roundsHeader
                  arguments)).interpretWith
              (threadHandler (suiteMeaning model)
                (marksBelow path fiatShamirMarks)
                (side roles.prover) (side roles.verifier)) state).bind fun result =>
            (suiteEntry model).finish side roles roundsHeader result := by
  obtain ⟨origin, earlier, newest, isEntry⟩ := newest_entry once_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_entry (quiet model)
    (fiatShamirRule_sound suite (functionTable model))
    (fiatShamirEntry_sound suite (functionTable model)) Identities.written 1 roles
    typed.program.protocols once fiatShamir_steps rounds rfl origin earlier newest isEntry
  have same : image = onceEntry := Var.ext first
  subst same
  exact threads path side one arguments

/-! ## The applied protocol under the Fiat–Shamir step -/

/-- The images that the Fiat–Shamir step makes of the protocols, with the table from the
protocols to their images and the marks. -/
noncomputable abbrev fiatShamirImages :
    Except StepRefusal
      (Rewritten suiteThreads typed.typeTable operations typed.functions
        typed.protocols) :=
  rewriteProtocols suiteThreads suiteRule Identities.written
    typed.program.protocols (entryDemands typed.protocols.length 1 roles)

kernel_refl fiatShamir_images : fiatShamirImages.isOk equals true

noncomputable def onceImages :
    Rewritten suiteThreads typed.typeTable operations typed.functions
      typed.protocols :=
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

-- `challenge` has an image that threads for the two roles, and no copy.
kernel_refl challenge_threaded : (onceImages.table.find challenge (some roles)).isSome equals true
kernel_refl challenge_not_copied : (onceImages.table.find challenge none).isSome equals false

/-- The image of `challenge` that threads. -/
noncomputable def onceChallenge :
    Var onceImages.new
      (Threads.header suiteThreads (some roles) challengeHeader) :=
  (onceImages.table.find challenge (some roles)).get challenge_threaded

-- It is the protocol before the entry's image.
kernel_refl onceChallenge_position : (onceChallenge.index, onceImages.new.length) equals (1, 2)

/-- `rewriteProtocols_threads` at the package and the Fiat–Shamir rule: the image of
`challenge` is `challenge` interpreted by every handler that follows its marks, for every
side with exactly one transcript role. -/
theorem fiatShamir_challenge_threads (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (handler : ThreadHandler model suiteThreads (side roles.prover)
      (side roles.verifier))
    (follows : Follows (suiteMeaning model) (side roles.prover)
      (side roles.verifier) handler path (onceImages.marks.get challenge roles))
    (state : ThreadState model suiteThreads (side roles.prover)
      (side roles.verifier))
    (arguments : Values (SideValue model side) challengeHeader.inputs) :
    (onceImages.protocols.table model (functionTable model)
          (originIdentities onceImages.origins)).get onceChallenge path side
        (.cons state.1 (.cons state.2 arguments)) =
      (((typed.program.protocols.table model (functionTable model) Identities.written).get
            challenge path side arguments).interpretWith handler state).bind fun result =>
        .done (threadedValues result) := by
  have callees := rewriteProtocols_threads (quiet model)
    (fiatShamirRule_sound suite (functionTable model)) Identities.written typed.program.protocols
    _ onceImages fiatShamir_rewrites
  exact callees.threaded challenge roles onceChallenge (Option.some_get _).symm path side
    (side roles.prover) (side roles.verifier) rfl rfl handler
    (by rw [stepFits_get]; exact ⟨one, follows⟩) state.1 state.2 arguments

/-- The same for the handler of the marks of `challenge`: a handler that follows them
exists. -/
theorem fiatShamir_challenge_handler (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (state : ThreadState model suiteThreads (side roles.prover)
      (side roles.verifier))
    (arguments : Values (SideValue model side) challengeHeader.inputs) :
    (onceImages.protocols.table model (functionTable model)
          (originIdentities onceImages.origins)).get onceChallenge path side
        (.cons state.1 (.cons state.2 arguments)) =
      (((typed.program.protocols.table model (functionTable model) Identities.written).get
            challenge path side arguments).interpretWith
          (threadHandler (suiteMeaning model)
            (marksBelow path (onceImages.marks.get challenge roles)) (side roles.prover)
            (side roles.verifier)) state).bind fun result =>
        .done (threadedValues result) :=
  fiatShamir_challenge_threads model path side one _
    (threadHandler_follows _ _ _ _ path) state arguments

/-! ## The marks of the Fiat–Shamir step -/

-- `challenge`, the protocol with the identity 0: the verifier draws a coin for the prover
-- at the site 0. `rounds`, with the identity 1: inside the first loop the prover sends at
-- the sites 0 and 2 and the verifier draws for the prover at the site 1; inside the second
-- loop `challenge` is applied at the site 3.
kernel_refl written_interactions : raw.protocols.map (fun protocol => interactions protocol.body)
  equals [[("draw", [1, 0], 0)],
    [("exchange", [0, 1], 0), ("draw", [1, 0], 1), ("exchange", [0, 1], 2), ("apply", [0], 3)]]

-- The two exchanges of `rounds` are marked at their sites, and the draw at its site, as a
-- draw that the verifier owns, with the law 0.
kernel_refl fiatShamir_marks_own :
  marksAt fiatShamirMarks [⟨[], 1, 0⟩, ⟨[], 1, 1⟩, ⟨[], 1, 2⟩] equals
    [some (.exchange 1 0 1 false 0), some (.draw true 1 0 1 false 1 0),
      some (.exchange 1 0 1 false 2)]

-- The draw of `challenge` is marked below the site of the application, with the identity
-- and the roles of `challenge`.
kernel_refl fiatShamir_marks_below :
  marksAt fiatShamirMarks [⟨[3], 0, 0⟩] equals [some (.draw true 0 0 1 false 0 0)]

-- No other site is marked: the site of the application itself, a site that no operation
-- has, another site below the application, a site below a site that applies nothing, and
-- a site two applications down.
kernel_refl fiatShamir_marks_none :
  marksAt fiatShamirMarks [⟨[], 1, 3⟩, ⟨[], 1, 4⟩, ⟨[3], 0, 1⟩, ⟨[0], 0, 0⟩, ⟨[3, 3], 0, 0⟩]
    equals [none, none, none, none, none]

-- The marks of `challenge` for the two roles are the marks of the entry below the site of
-- the application.
kernel_refl challenge_marks :
  marksAt (onceImages.marks.get challenge roles) [⟨[], 0, 0⟩, ⟨[], 0, 1⟩, ⟨[0], 0, 0⟩] equals
    [some (.draw true 0 0 1 false 0 0), none, none]

/-- At every site below the site of the application, not only at those above: the marks
of the entry are the marks of `challenge`. -/
theorem marks_below_application (rest : List Nat) (definition number : Nat) :
    fiatShamirMarks ⟨3 :: rest, definition, number⟩ =
      onceImages.marks.get challenge roles ⟨rest, definition, number⟩ :=
  match rest, number with
  | [], 0 => kernel_rfl%
  | [], _ + 1 => kernel_rfl%
  | _ :: _, _ => kernel_rfl%

/-- So the handler of the entry's marks follows the marks of `challenge` below the site of
the application. -/
theorem entry_handler_follows_challenge (model : Model) (prover verifier : Bool)
    (path : List Nat) :
    Follows (suiteMeaning model) prover verifier
      (threadHandler (suiteMeaning model) (marksBelow path fiatShamirMarks) prover verifier)
      (path ++ [3]) (onceImages.marks.get challenge roles) :=
  (threadHandler_follows _ _ _ _ path).below 3 _ marks_below_application

/-- The image of `challenge`, reached under the site of the application, is `challenge`
interpreted by the handler that interprets the entry. -/
theorem fiatShamir_challenge_under_entry_handler (model : Model) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (state : ThreadState model suiteThreads (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) challengeHeader.inputs) :
    (onceImages.protocols.table model (functionTable model)
          (originIdentities onceImages.origins)).get onceChallenge [3] side
        (.cons state.1 (.cons state.2 arguments)) =
      (((typed.program.protocols.table model (functionTable model) Identities.written).get
            challenge [3] side arguments).interpretWith
          (threadHandler (suiteMeaning model) (marksBelow [] fiatShamirMarks) (side roles.prover)
            (side roles.verifier)) state).bind fun result =>
        .done (threadedValues result) :=
  fiatShamir_challenge_threads model [3] side one _
    (entry_handler_follows_challenge model _ _ []) state arguments

-- A mark is read by the path and the site number alone: the marks do not compare the
-- identity of the definition, which the path determines for the effects of a program.
kernel_refl marks_ignore_identity :
  marksAt fiatShamirMarks [⟨[], 7, 0⟩, ⟨[3], 7, 0⟩] equals
    [some (.exchange 1 0 1 false 0), some (.draw true 0 0 1 false 0 0)]

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
  stepProtocols layoutThreads layoutRule once.identities
    (once.headers.length - 1) roles once.protocols

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

/-- The header of the entry after both steps. -/
noncomputable abbrev twiceHeader : ProtocolHeader :=
  (layoutRule.entryPorts roles onceHeader).header
    onceHeader

/-- The image of the entry after both steps: the newest protocol of the second result. -/
noncomputable abbrev twiceEntry : Var twice.headers twiceHeader := ⟨0, kernel_rfl%⟩

/-- The marks of the serialize step, at a site relative to the entry. -/
noncomputable abbrev serializeMarks : Site → Option (Mark operations) :=
  stepMarks layoutThreads layoutRule once.identities (once.headers.length - 1) roles once.protocols

/-- `stepProtocols_entry` at the result of the Fiat–Shamir step and the serialize rule. -/
theorem serialize_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side)
      (layoutRule.entryPorts roles onceHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry path side
        arguments =
      ((layoutEntry model).start side roles onceHeader arguments).bind fun state =>
        (((once.protocols.table model (functionTable model) once.identities).get onceEntry path
              side ((layoutEntry model).arguments side roles onceHeader arguments)).interpretWith
            (threadHandler (layoutMeaning model)
              (marksBelow path serializeMarks)
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

-- The image of `rounds` keeps its identity and its two exchanges at their sites: they are
-- marked. The draws are derived after the first step, and nothing else is marked: not the
-- site of the draw, and no site below the application.
kernel_refl serialize_marks :
  marksAt serializeMarks [⟨[], 1, 0⟩, ⟨[], 1, 1⟩, ⟨[], 1, 2⟩, ⟨[], 1, 3⟩, ⟨[3], 0, 0⟩] equals
    [some (.exchange 1 0 1 false 0), none, some (.exchange 1 0 1 false 2), none, none]

/-! ## The applied protocol under the serialize step -/

/-- The image of `challenge` in the result of the Fiat–Shamir step. -/
noncomputable abbrev onceCallee :
    Var once.headers (Threads.header suiteThreads (some roles) challengeHeader) :=
  ⟨1, kernel_rfl%⟩

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

-- The image of `challenge` has no exchange after the first step: the serialize step copies
-- it and makes no image of it that threads.
kernel_refl callee_copied : (twiceImages.table.find onceCallee none).isSome equals true
kernel_refl callee_not_threaded :
  (twiceImages.table.find onceCallee (some roles)).isSome equals false

/-- The copy of the image of `challenge`. -/
noncomputable def twiceCallee :
    Var twiceImages.new (Threads.header suiteThreads (some roles) challengeHeader) :=
  (twiceImages.table.find onceCallee none).get callee_copied

/-- `rewriteProtocols_plain` at the result of the Fiat–Shamir step and the serialize rule:
the copy of the image of `challenge` has its meaning. -/
theorem serialize_callee_copied (model : Model) :
    (twiceImages.protocols.table model (functionTable model)
        (originIdentities twiceImages.origins)).get twiceCallee =
      (once.protocols.table model (functionTable model) once.identities).get onceCallee :=
  rewriteProtocols_plain (rule := layoutRule) once.identities once.protocols _ twiceImages
    serialize_rewrites onceCallee twiceCallee (Option.some_get _).symm

/-- `rewriteProtocols_threads` at the same: the statement about every callee, of which the
part about copies gives the same equation. No protocol of this program has an image that
threads under the serialize step, so the other part says nothing here; the package of
`sumcheck` has one. -/
theorem serialize_callees (model : Model) :
    CalleesThread twiceImages.table
      (once.protocols.table model (functionTable model) once.identities)
      (twiceImages.protocols.table model (functionTable model)
        (originIdentities twiceImages.origins))
      (stepFits (layoutMeaning model) twiceImages.marks) :=
  rewriteProtocols_threads (quiet model) (serializeRule_sound layout (functionTable model))
    once.identities once.protocols _ twiceImages serialize_rewrites

/-! ## The two steps together -/

/-- `stepProtocols_twice_entry` at the package: the newest protocol after both steps is the
entry interpreted by the handler of the Fiat–Shamir step and then the handler of the
serialize step, between the starts and the finishes of the two entries. -/
theorem fiatShamir_then_serialize_entry (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) (layoutRule.entryPorts roles onceHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry path side
        arguments =
      (composedStart (suiteEntry model) (layoutEntry model) side roles roundsHeader
          arguments).bind fun states =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get
              rounds path side
              (composedArguments (suiteEntry model) (layoutEntry model) side roles roundsHeader
                arguments)).interpretWith
            (PIR.composeHandlers
              (threadHandler (suiteMeaning model) (marksBelow path fiatShamirMarks)
                (side roles.prover) (side roles.verifier))
              (threadHandler (layoutMeaning model) (marksBelow path serializeMarks)
                (side roles.prover) (side roles.verifier))) states).bind fun result =>
          composedFinish (suiteEntry model) (layoutEntry model) side roles roundsHeader result := by
  obtain ⟨firstOrigin, firstEarlier, firstNewest, firstEntry⟩ := newest_entry once_newest
  obtain ⟨secondOrigin, secondEarlier, secondNewest, secondEntry⟩ := newest_entry twice_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_twice_entry (quiet model)
    (fiatShamirRule_sound suite (functionTable model))
    (fiatShamirEntry_sound suite (functionTable model))
    (serializeRule_sound layout (functionTable model))
    (serializeEntry_sound layout (functionTable model)) Identities.written 1 roles
    typed.program.protocols once fiatShamir_steps twice serialize_steps rounds rfl ((Stepped.rewroteEntry_of_newest firstNewest).trans firstEntry)
    ((Stepped.rewroteEntry_of_newest secondNewest).trans secondEntry)
  have same : image = twiceEntry := Var.ext first
  subst same
  exact threads path side one arguments

/-! ## The side of the prover alone and the side of the verifier alone -/

/-- The side of the prover holds exactly one transcript role, and so does the side of the
verifier. -/
theorem prover_alone : OneTranscriptRole (single 0 roles.prover) (single 0 roles.verifier) :=
  .inl ⟨rfl, rfl⟩

theorem verifier_alone : OneTranscriptRole (single 1 roles.prover) (single 1 roles.verifier) :=
  .inr ⟨rfl, rfl⟩

/-- The image of the entry after the Fiat–Shamir step, for the prover alone: the prover's
start, then the entry interpreted by the handler of the marks, which carries the prover's
state and nothing for the verifier; the two final states are dropped. -/
theorem fiatShamir_entry_prover (model : Model)
    (arguments : Values (SideValue model (single 0)) roundsHeader.inputs) :
    (once.protocols.table model (functionTable model) once.identities).get onceEntry []
        (single 0) arguments =
      ((suiteEntry model).start (single 0) roles roundsHeader arguments).bind fun state =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get
              rounds [] (single 0) arguments).interpretWith
            (threadHandler (suiteMeaning model) fiatShamirMarks true false) state).bind
          fun result => .done result.1 :=
  fiatShamir_entry model [] (single 0) prover_alone arguments

/-- The same for the verifier alone. -/
theorem fiatShamir_entry_verifier (model : Model)
    (arguments : Values (SideValue model (single 1)) roundsHeader.inputs) :
    (once.protocols.table model (functionTable model) once.identities).get onceEntry []
        (single 1) arguments =
      ((suiteEntry model).start (single 1) roles roundsHeader arguments).bind fun state =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get
              rounds [] (single 1) arguments).interpretWith
            (threadHandler (suiteMeaning model) fiatShamirMarks false true) state).bind
          fun result => .done result.1 :=
  fiatShamir_entry model [] (single 1) verifier_alone arguments

/-- The start of the entry returns, for the prover alone and for the verifier alone, whatever
the inputs: the suite has a start and a row for every part of the statement, so the image
of the entry is not a process that stops before the entry runs. -/
theorem fiatShamir_start_returns_prover (model : Model)
    (arguments : Values (SideValue model (single 0)) roundsHeader.inputs) :
    returns ((suiteEntry model).start (single 0) roles roundsHeader arguments) = true :=
  kernel_rfl%

theorem fiatShamir_start_returns_verifier (model : Model)
    (arguments : Values (SideValue model (single 1)) roundsHeader.inputs) :
    returns ((suiteEntry model).start (single 1) roles roundsHeader arguments) = true :=
  kernel_rfl%

/-- The image of the entry after the serialize step, for the prover alone: the prover opens
a writer; the image of the first step runs under the handler of the marks on the inputs
after the proof; the prover closes the writer into the proof, the first output. -/
theorem serialize_entry_prover (model : Model)
    (arguments : Values (SideValue model (single 0))
      (layoutRule.entryPorts roles onceHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry []
        (single 0) arguments =
      (layout.opening true false (arguments.get .here)).bind fun state =>
        (((once.protocols.table model (functionTable model) once.identities).get onceEntry []
              (single 0) arguments.tail).interpretWith
            (threadHandler (layoutMeaning model) serializeMarks true false) state).bind
          fun result =>
            (layout.closing true false result.2).bind fun proof => .done (.cons proof result.1) :=
  serialize_entry model [] (single 0) prover_alone arguments

/-- The same for the verifier alone: the verifier opens a reader on the proof, the first
input, and after the body guards that the reader is exhausted. -/
theorem serialize_entry_verifier (model : Model)
    (arguments : Values (SideValue model (single 1))
      (layoutRule.entryPorts roles onceHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry []
        (single 1) arguments =
      (layout.opening false true (arguments.get .here)).bind fun state =>
        (((once.protocols.table model (functionTable model) once.identities).get onceEntry []
              (single 1) arguments.tail).interpretWith
            (threadHandler (layoutMeaning model) serializeMarks false true) state).bind
          fun result =>
            (layout.closing false true result.2).bind fun proof => .done (.cons proof result.1) :=
  serialize_entry model [] (single 1) verifier_alone arguments

#print axioms fiatShamir_is_step
#print axioms construct_is_step
#print axioms fiatShamir_entry
#print axioms fiatShamir_challenge_threads
#print axioms fiatShamir_challenge_handler
#print axioms fiatShamir_challenge_under_entry_handler
#print axioms serialize_entry
#print axioms serialize_callee_copied
#print axioms serialize_callees
#print axioms fiatShamir_then_serialize_entry
#print axioms fiatShamir_start_returns_prover
#print axioms fiatShamir_entry_prover
#print axioms fiatShamir_entry_verifier
#print axioms serialize_entry_prover
#print axioms serialize_entry_verifier

end Threading
