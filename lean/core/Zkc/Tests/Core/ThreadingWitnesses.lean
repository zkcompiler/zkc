import Zkc.Tests.Core.Threading

/-! Witnesses and failing examples of what the theorems of a threading step assume.

Every hypothesis of the whole-program theorem and of the statements it is built from holds
of something and fails of something, at the package of `Tests/Core/Threading.lean` unless
said otherwise.

- `OneTranscriptRole`: holds of the side of the prover and of the side of the verifier
  (`Threading.prover_alone`, `Threading.verifier_alone`); fails of the side of both and of
  the side of no role.
- `Follows`: the handler of the marks follows them (`marks_handler_follows`); the handler
  that performs every effect as it is does not follow the marks of the Fiat–Shamir step,
  because it does not absorb the first message of `rounds` (`passing_not_follows`, in a
  model in which absorbing changes the state).
- `PassesBelow`, `TablePasses`: the handler that performs every effect passes below every
  path, a handler that counts does not; the protocols of the package are passed
  (`Protocols.table_passes`), a table whose protocol performs an effect outside its path is
  not.
- `Fits`: `region_fits` gives it for the body of `rounds`, the handler of its marks and a
  side with one transcript role (`rounds_fits`). For the side of both transcript roles no
  handler fits the body (`rounds_never_fits_both`): the first exchange performs no effect
  there, and the rule changes the two states. For the side of no role no handler fits it
  either (`rounds_never_fits_nobody`), for another reason: what fits the image of an
  applied protocol (`stepFits`) asks for exactly one transcript role. So the theorems say
  nothing of a role that is neither the prover nor the verifier.
- `RuleSound`, `EntrySound`: the two rules and their entries are sound; the Fiat–Shamir rule
  is not sound for a meaning that leaves the states as they are, and its entry does not run
  as a meaning whose start stops.
- `QuietTable`: fails of a table whose function performs an effect. The package has no
  function; `Tests/Core/ThreadingSumcheck.lean` has the statement for a package with
  functions.
- Pairwise different sites: the sites of `rounds` are `[3, 2, 1, 0]`; a region with one
  site twice fails.
- `CalleesThread`, `PlainCallees`, `stepFits`: they hold of the images of the package by
  the theorems; no handler of the side of both roles fits the image of `challenge`; the
  statement about the callees fails when every handler is said to fit, and the statement
  about the copies fails of a table in which every protocol stops.
- An entry that the Fiat–Shamir step copies: `stepProtocols_plain_entry` and
  `stepProtocols_plain_then_entry` at a package whose entry exchanges nothing.

Not here: `Rule.External` (`Tests/Core/StepRefusals.lean`). The failing examples of
`Follows`, of `Fits` for the side of both roles and of `RuleSound` are for one model: in the
one-point model a state has one value and nothing can change it. The others are for every
model. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core
open Threading

namespace ThreadingWitnesses

/-! ## Sides -/

/-- The side of both transcript roles, and the side of no role. -/
abbrev both : Side := fun role => Nat.beq role 0 || Nat.beq role 1

abbrev nobody : Side := fun _ => false

/-- Exactly one transcript role: the side of both does not hold exactly one, and neither
does the side of no role. -/
theorem both_not_one : ¬ OneTranscriptRole (both roles.prover) (both roles.verifier) := by
  rintro (⟨_, isVerifier⟩ | ⟨isProver, _⟩)
  · exact Bool.noConfusion isVerifier
  · exact Bool.noConfusion isProver

theorem nobody_not_one : ¬ OneTranscriptRole (nobody roles.prover) (nobody roles.verifier) := by
  rintro (⟨isProver, _⟩ | ⟨_, isVerifier⟩)
  · exact Bool.noConfusion isProver
  · exact Bool.noConfusion isVerifier

/-! ## A model in which absorbing changes the state -/

/-- A model whose nominal carriers are the natural numbers: a literal is 0, and every pure
row returns 1 in every nominal carrier. A state that starts at 0 is 1 after any row. -/
def markingModel : Model where
  Carrier _ := Nat
  pure row populated _ := Ty.inhabitants (fun _ => (1 : Nat)) row.outputs populated
  restricted _ _ := none
  «opaque» _ _ := .error .abort
  literal _ _ := 0

/-- The handler that performs every effect as it is. -/
def passing (model : Model) (S : Type) :
    PIR.StatefulInterpretation (Effects model) (Effects model) S :=
  fun effect state => passEffect effect state

/-- What a process that sends once and then returns, returns. -/
def afterSend {model : Model} {α : Type} : PIR.Process (Effects model) α → Option α
  | .call (.send ..) next =>
      match next PUnit.unit with
      | .done value => some value
      | _ => none
  | _ => none

/-- What a process that returns at once, returns. -/
def returned {model : Model} {α : Type} : PIR.Process (Effects model) α → Option α
  | .done value => some value
  | _ => none

/-! ## `Follows` -/

/-- The prover's state 0 and nothing for the verifier. -/
def proverStart : ThreadState markingModel suiteThreads true false := ((0 : Nat), PUnit.unit)

/-- The prover's first message of `rounds`: a `send` of a value of the field at the site 0
of the definition with the identity 1. -/
def firstSend : Effect markingModel.Value := .send ⟨[], 1, 0⟩ (.nominal 0) (5 : Nat)

/-- At the first message the handler of the marks absorbs the value: the prover's state is
1 after it. -/
theorem marked_send_absorbs :
    afterSend (threadHandler (suiteMeaning markingModel) fiatShamirMarks true false firstSend
        proverStart) =
      some (PUnit.unit, ((1 : Nat), PUnit.unit)) :=
  kernel_rfl%

/-- The handler that performs every effect as it is does not follow the marks of the
Fiat–Shamir step on `rounds`: at the first message it leaves the prover's state as it is. -/
theorem passing_not_follows :
    ¬ Follows (suiteMeaning markingModel) true false (passing markingModel _) []
      fiatShamirMarks := by
  intro follows
  have acts := congrArg afterSend (follows firstSend [] rfl proverStart)
  have same : some (PUnit.unit, proverStart) = some (PUnit.unit, ((1 : Nat), PUnit.unit)) :=
    acts.trans marked_send_absorbs
  have changed : (0 : Nat) = 1 := congrArg (fun result => result.2.1) (Option.some.inj same)
  exact absurd changed (by decide)

/-- The handler of the marks follows them, below any path. -/
theorem marks_handler_follows (model : Model) (prover verifier : Bool) (path : List Nat) :
    Follows (suiteMeaning model) prover verifier
      (threadHandler (suiteMeaning model) (marksBelow path fiatShamirMarks) prover verifier) path
      fiatShamirMarks :=
  threadHandler_follows _ _ _ _ path

/-! ## `PassesBelow` and `TablePasses` -/

/-- The handler that performs every effect as it is performs every effect below a path as
it is. -/
theorem passing_passes (model : Model) (S : Type) (path : List Nat) :
    PassesBelow (passing model S) path :=
  fun _ _ _ _ => rfl

/-- The handler that performs every effect and counts the effects it handled. -/
def counting (model : Model) : PIR.StatefulInterpretation (Effects model) (Effects model) Nat :=
  fun effect count => .call effect fun reply => .done (reply, count + 1)

/-- It does not perform the effects below a path as they are: it changes its state. -/
theorem counting_not_passes (model : Model) (path : List Nat) :
    ¬ PassesBelow (counting model) path := by
  intro passes
  have acts := congrArg afterSend
    (passes (.send ⟨path, 0, 0⟩ .bool false) [] (List.append_nil path).symm 0)
  have changed : (1 : Nat) = 0 := congrArg (fun result => result.2) (Option.some.inj acts)
  exact absurd changed (by decide)

/-- Every protocol of the package is passed by a handler that performs the effects below
its path as they are. -/
theorem package_passes (model : Model) :
    TablePasses (typed.program.protocols.table model (functionTable model) Identities.written) :=
  Protocols.table_passes (quiet model) Identities.written typed.program.protocols

/-- So the handler that performs every effect as it is passes `rounds`. -/
theorem passing_passes_rounds (model : Model) (S : Type) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) roundsHeader.inputs) :
    PIR.Passes (passing model S)
      ((typed.program.protocols.table model (functionTable model) Identities.written).get rounds
        path side arguments) :=
  package_passes model (passing model S) rounds path side arguments (passing_passes model S path)

/-- A protocol of one role without inputs and outputs. -/
abbrev idleHeader : ProtocolHeader := ⟨1, [], [], .none, false⟩

/-- A table whose protocol receives at a site with an empty path, whatever the path under
which it is reached. No program has this meaning: the effects of a protocol are below its
path. -/
def strayTable (model : Model) : ProtocolTable model [idleHeader] :=
  .cons (fun _ _ _ => .call (.receive ⟨[], 0, 0⟩ .bool) fun _ => .done .nil) .nil

/-- A handler that stops at an effect with an empty path and performs every other effect
as it is. -/
def belowOnly (model : Model) : PIR.StatefulInterpretation (Effects model) (Effects model) Unit :=
  fun effect state =>
    match effect.site.path with
    | [] => .halt .refused
    | _ :: _ => passEffect effect state

/-- Whether a process stops at once. -/
def stops {model : Model} {α : Type} : PIR.Process (Effects model) α → Bool
  | .halt _ => true
  | _ => false

/-- The table is not passed: the handler performs the effects below the path `[7]` as they
are and stops the protocol reached under that path. -/
theorem stray_not_passes (model : Model) : ¬ TablePasses (strayTable model) := by
  intro passes
  have below : PassesBelow (belowOnly model) [7] := by
    intro effect rest under state
    show (match effect.site.path with
      | [] => PIR.Process.halt .refused
      | _ :: _ => passEffect effect state) = passEffect effect state
    rw [under]
    rfl
  have passed := passes (belowOnly model) (Var.here : Var [idleHeader] idleHeader) [7] nobody .nil
    below ()
  exact Bool.noConfusion (congrArg stops passed : true = false)

/-! ## `Fits` -/

/-- The definition of the newest protocol. -/
def newestDefinition {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {header : ProtocolHeader} {earlier : List ProtocolHeader} :
    Protocols typeTable operations functions (header :: earlier) →
      ProtocolDefinition operations functions earlier header
  | .snoc _ definition _ => definition

/-- It is well formed. -/
theorem newestDefinition_wellFormed {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {header : ProtocolHeader} {earlier : List ProtocolHeader} :
    ∀ protocols : Protocols typeTable operations functions (header :: earlier),
      (newestDefinition protocols).violation typeTable = none
  | .snoc _ _ wellFormed => wellFormed

/-- The protocols of the package, as the entry after `challenge`. -/
noncomputable abbrev written :
    Protocols typed.typeTable operations typed.functions [roundsHeader, challengeHeader] :=
  typed.program.protocols

/-- The definition of `rounds` and the protocols before it. -/
noncomputable abbrev roundsDefinition :
    ProtocolDefinition operations typed.functions [challengeHeader] roundsHeader :=
  newestDefinition written

noncomputable abbrev beforeRounds :
    Protocols typed.typeTable operations typed.functions [challengeHeader] :=
  written.earlier

-- The sites of `rounds`, the latest first, are pairwise different.
kernel_refl rounds_sites : regionSites roundsDefinition.body equals [3, 2, 1, 0]

theorem rounds_sites_differ : (regionSites roundsDefinition.body).Nodup :=
  ProtocolDefinition.regionSites_nodup (newestDefinition_wellFormed written)

-- How the Fiat–Shamir step reaches `challenge` from the entry: applied with the prover
-- and the verifier as its roles 0 and 1.
kernel_refl challenge_demands :
  propagate [.entry roles] (applications roundsDefinition.body []) [] equals
    [[.applied (some 0) (some 1)]]

/-- The images that the Fiat–Shamir step makes of the protocols before `rounds`. -/
noncomputable abbrev earlierImages :
    Except StepRefusal
      (Rewritten suiteThreads typed.typeTable operations typed.functions [challengeHeader]) :=
  rewriteProtocols suiteThreads suiteRule Identities.written beforeRounds
    [[.applied (some 0) (some 1)]]

kernel_refl earlier_images : earlierImages.isOk equals true

noncomputable def prior :
    Rewritten suiteThreads typed.typeTable operations typed.functions [challengeHeader] :=
  okValue earlierImages earlier_images

/-- Where the operations of `rounds` stand for the step. -/
abbrev roundsPlace : Place := ⟨1, roles, false⟩

/-- The marks of the body of `rounds`, over the images of `challenge`. -/
noncomputable abbrev roundsMarks : Site → Option (Mark operations) :=
  regionMarks prior.table.threads prior.marks roundsPlace roundsDefinition.body

-- They are the marks of the step.
kernel_refl rounds_marks :
  marksAt roundsMarks [⟨[], 1, 0⟩, ⟨[], 1, 1⟩, ⟨[], 1, 2⟩, ⟨[], 1, 3⟩, ⟨[3], 0, 0⟩] equals
    marksAt fiatShamirMarks [⟨[], 1, 0⟩, ⟨[], 1, 1⟩, ⟨[], 1, 2⟩, ⟨[], 1, 3⟩, ⟨[3], 0, 0⟩]

/-- `region_fits` at the body of `rounds`: for a side with exactly one transcript role, the
handler of the marks fits the body. -/
theorem rounds_fits (model : Model) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier)) (path : List Nat) :
    Fits suiteThreads suiteRule (suiteMeaning model) (functionTable model)
      (beforeRounds.table model (functionTable model) Identities.written) prior.table
      (stepFits (suiteMeaning model) prior.marks) roundsPlace side (ownSites 1 path)
      (threadHandler (suiteMeaning model) (marksBelow path roundsMarks) (side roles.prover)
        (side roles.verifier))
      roundsDefinition.body :=
  region_fits suiteRule (suiteMeaning model) (quiet model)
    (Protocols.table_passes (quiet model) Identities.written beforeRounds) prior.table prior.marks
    roundsPlace side one 1 path _ roundsDefinition.body rounds_sites_differ
    (threadHandler_follows _ _ _ _ path)

/-- At the side of the prover. -/
theorem rounds_fits_prover (model : Model) :
    Fits suiteThreads suiteRule (suiteMeaning model) (functionTable model)
      (beforeRounds.table model (functionTable model) Identities.written) prior.table
      (stepFits (suiteMeaning model) prior.marks) roundsPlace (single 0) (ownSites 1 [])
      (threadHandler (suiteMeaning model) roundsMarks true false) roundsDefinition.body :=
  rounds_fits model (single 0) prover_alone []

/-- The states 0 of both roles. -/
def bothStart :
    ThreadState markingModel suiteThreads (both roles.prover) (both roles.verifier) :=
  ((0 : Nat), (0 : Nat))

/-- The state with which a process that returns at once, returns. -/
def returnedState {model : Model} {α S : Type} : PIR.Process (Effects model) (α × S) → Option S
  | .done result => some result.2
  | _ => none

/-- No handler fits the body of `rounds` for the side of both transcript roles. The first
exchange of the loop is between two roles of the side: its process performs no effect, so
a handler leaves the state as it is; the rule absorbs the message into both states, and in
this model the states change. The theorems are therefore stated for sides with exactly one
transcript role. -/
theorem rounds_never_fits_both
    (handler : ThreadHandler markingModel suiteThreads (both roles.prover) (both roles.verifier)) :
    ¬ Fits suiteThreads suiteRule (suiteMeaning markingModel) (functionTable markingModel)
      (beforeRounds.table markingModel (functionTable markingModel) Identities.written)
      prior.table (stepFits (suiteMeaning markingModel) prior.marks) roundsPlace both
      (ownSites 1 []) handler roundsDefinition.body := by
  intro fits
  -- The step threads the region of the first loop, so the handler fits the region; its
  -- second operation is the exchange.
  have inLoop := fits.1 kernel_rfl%
  have atExchange := inLoop.1.1 rfl rfl
  have acts := congrArg returnedState (atExchange (.cons (5 : Nat) .nil) bothStart)
  have same : some bothStart = some (((1 : Nat), (1 : Nat)) :
      ThreadState markingModel suiteThreads (both roles.prover) (both roles.verifier)) :=
    acts
  have changed : (0 : Nat) = 1 := congrArg (fun state => state.1) (Option.some.inj same)
  exact absurd changed (by decide)

/-- No handler fits the body of `rounds` for the side of no role either, in any model. The
second loop applies `challenge`, whose image threads, and what fits that image
(`stepFits`) asks for a side with exactly one transcript role. The whole-program theorem
therefore says nothing of a role that is neither the prover nor the verifier. -/
theorem rounds_never_fits_nobody (model : Model)
    (handler : ThreadHandler model suiteThreads (nobody roles.prover) (nobody roles.verifier)) :
    ¬ Fits suiteThreads suiteRule (suiteMeaning model) (functionTable model)
      (beforeRounds.table model (functionTable model) Identities.written) prior.table
      (stepFits (suiteMeaning model) prior.marks) roundsPlace nobody (ownSites 1 []) handler
      roundsDefinition.body := by
  intro fits
  -- The step threads the region of the second loop; its operation is the application.
  have inLoop := fits.2.2.1 kernel_rfl%
  have fit := inLoop.1.1 _
    (Option.some_get (kernel_rfl% : (_ : Option _).isSome = true)).symm
  exact nobody_not_one fit.1

/-! ## `RuleSound` -/

/-- The two rules are sound for what they do, over the functions of the package. -/
theorem suite_rule_sound (model : Model) :
    RuleSound suiteRule (suiteMeaning model) (functionTable model) :=
  fiatShamirRule_sound suite (functionTable model)

theorem layout_rule_sound (model : Model) :
    RuleSound layoutRule (layoutMeaning model) (functionTable model) :=
  serializeRule_sound layout (functionTable model)

/-- A meaning that does nothing at an exchange: the message is exchanged and the two states
stay as they are. -/
def idleMeaning (model : Model) : RuleMeaning model suiteThreads operations where
  exchange := fun prover verifier _ _ effects type value state =>
    (exchangeStep model effects type prover verifier value).bind fun received =>
      .done (received, state)
  draw := fun _ _ _ _ _ _ _ _ _ => .halt .refused

/-- A context of a message of the field held by the prover and the two states. -/
noncomputable abbrev exchangeContext : List Located :=
  [suiteThreads.second roles, suiteThreads.first roles, ⟨.nominal 0, roles.prover⟩]

/-- What the Fiat–Shamir rule emits at the first exchange of `rounds`. -/
noncomputable abbrev emittedExchange :
    Except StepRefusal
      (Emitted (ProtocolDialect operations typed.functions [] true) exchangeContext
        [⟨.nominal 0, roles.verifier⟩, suiteThreads.first roles, suiteThreads.second roles]) :=
  suiteRule.exchange roundsPlace 0 (.nominal 0) (.there (.there .here)) (.there .here) .here

kernel_refl exchange_emitted : emittedExchange.isOk equals true

/-- For the side of the prover: the message 5 and the prover's state 0. -/
noncomputable def exchangeEnvironment :
    Environment (SideValue markingModel (single 0)) exchangeContext :=
  Environment.push (ty := suiteThreads.second roles)
    (Environment.push (ty := suiteThreads.first roles)
      (Environment.push (ty := (⟨.nominal 0, roles.prover⟩ : Located))
        (Environment.empty (Value := SideValue markingModel (single 0))) (5 : Nat))
      (0 : Nat))
    PUnit.unit

/-- The Fiat–Shamir rule is not sound for the meaning that does nothing: what it emits at
the exchange leaves the prover's state at 1, and the meaning says 0. -/
theorem idleMeaning_not_sound :
    ¬ RuleSound suiteRule (idleMeaning markingModel) (functionTable markingModel) := by
  intro sound
  obtain ⟨later, runs, reads⟩ := sound.exchange (protocols := []) (deployed := true) .nil
    (ownSites 1 []) (single 0) roundsPlace 0 (.nominal 0) (.there (.there .here)) (.there .here)
    .here (okValue emittedExchange exchange_emitted) (okValue_eq _ _) exchangeEnvironment
  -- Whatever follows the emitted operations: here, a return of the prover's new state.
  have ran := congrArg afterSend
    (runs
      (.ret (.cons ((okValue emittedExchange exchange_emitted).values.get (.there .here)) .nil)))
  have emitted : afterSend
      ((okValue emittedExchange exchange_emitted).wrap
          (.ret (.cons ((okValue emittedExchange exchange_emitted).values.get (.there .here))
            .nil))
        |>.denote (labelledMeaning markingModel (ownSites 1 []) (functionTable markingModel) .nil
          (single 0)) exchangeEnvironment) =
      some (.cons (1 : Nat) .nil) :=
    kernel_rfl%
  have read := (reads (PUnit.unit, ((0 : Nat), PUnit.unit))).2.1
  have same := Option.some.inj (emitted.symm.trans ran)
  have changed : (1 : Nat) = 0 := (congrArg (fun values => values.get .here) same).trans read
  exact absurd changed (by decide)

/-! ## `EntrySound` -/

/-- The entries of the two rules are sound for what they do. -/
theorem suite_entry_sound (model : Model) :
    EntrySound suiteRule (suiteEntry model) (functionTable model) :=
  fiatShamirEntry_sound suite (functionTable model)

theorem layout_entry_sound (model : Model) :
    EntrySound layoutRule (layoutEntry model) (functionTable model) :=
  serializeEntry_sound layout (functionTable model)

/-- What the entry of the Fiat–Shamir rule does, with a start that stops instead. -/
noncomputable def stoppingEntry (model : Model) : EntryMeaning model suiteThreads suiteRule :=
  { suiteEntry model with start := fun _ _ _ _ => .halt .refused }

/-- A protocol of two roles without inputs and outputs. -/
abbrev pairHeader : ProtocolHeader := ⟨2, [], [], .none, false⟩

/-- A threaded body that returns the two states it is given. -/
noncomputable def returningBody {Δ : List Located} (_ : Renaming (bindAll [] pairHeader.inputs) Δ)
    (first : Var Δ (suiteThreads.first roles)) (second : Var Δ (suiteThreads.second roles)) :
    Except StepRefusal
      (Region (ProtocolDialect operations typed.functions [] true) Δ
        (suiteThreads.states roles ++ pairHeader.outputs)) :=
  .ok (.ret (.cons first (.cons second .nil)))

/-- The region that the rule makes of it. -/
noncomputable abbrev enteredBody :
    Except StepRefusal
      (Region (ProtocolDialect operations typed.functions [] true)
        (bindAll [] (suiteRule.entryPorts roles pairHeader).inputs)
        (suiteRule.entryPorts roles pairHeader).outputs) :=
  suiteRule.entry roundsPlace pairHeader returningBody

kernel_refl body_entered : enteredBody.isOk equals true

/-- For the side of the prover the region returns: its start does not stop. -/
theorem entered_returns (model : Model) :
    stops ((okValue enteredBody body_entered).denote
      (labelledMeaning model (ownSites 1 []) (functionTable model) .nil (single 0))
      (Environment.ofValues .nil)) = false :=
  kernel_rfl%

/-- The entry of the Fiat–Shamir rule does not run as that meaning says: `EntrySound` is a
condition on the start. -/
theorem stoppingEntry_not_sound (model : Model) :
    ¬ EntrySound suiteRule (stoppingEntry model) (functionTable model) := by
  intro sound
  have runs := sound.runs (protocols := []) (deployed := true) .nil (ownSites 1 []) (single 0)
    roundsPlace pairHeader returningBody (okValue enteredBody body_entered) (okValue_eq _ _)
    (fun _ state => .done (.cons state.1 (.cons state.2 .nil)))
    (fun _ _ _ threaded made _ _ _ => by cases made; rfl) .nil
  have stopped : stops ((okValue enteredBody body_entered).denote
      (labelledMeaning model (ownSites 1 []) (functionTable model) .nil (single 0))
      (Environment.ofValues .nil)) = true :=
    congrArg stops runs
  exact Bool.noConfusion ((entered_returns model).symm.trans stopped)

/-! ## `QuietTable` -/

/-- A function without inputs and outputs. -/
abbrev idleFunction : FunctionHeader := ⟨[], [], false⟩

/-- A table whose function performs an effect. No function of a program has this meaning. -/
def loudTable (model : Model) : FunctionTable model [idleFunction] :=
  .cons (fun _ => .call (.receive ⟨[], 0, 0⟩ .bool) fun _ => .done .nil) .nil

theorem loudTable_not_quiet (model : Model) : ¬ QuietTable (loudTable model) :=
  fun quiet => quiet (Var.here : Var [idleFunction] idleFunction) .nil

/-! ## Sites that are pairwise different -/

/-- A region of two exchanges at one site. No well-formed definition has it. -/
def repeatedSite :
    Region (ProtocolDialect ([] : List OperationSignature) ([] : List FunctionHeader) [] true)
      [⟨.bool, 0⟩] [] :=
  .letOp (.exchange 0 1 4 .bool) (.cons .here .nil) .nil <|
    .letOp (.exchange 0 1 4 .bool) (.cons (.there .here) .nil) .nil <| .ret .nil

theorem repeatedSite_sites : regionSites repeatedSite = [4, 4] := rfl

theorem repeatedSite_not_nodup : ¬ (regionSites repeatedSite).Nodup := by
  rw [repeatedSite_sites]
  decide

/-! ## `CalleesThread`, `PlainCallees` and what fits a callee -/

/-- The images of the protocols of the package thread under the Fiat–Shamir step, for
handlers that follow the marks of their definitions (`stepFits`). -/
theorem fiatShamir_callees (model : Model) :
    CalleesThread onceImages.table
      (typed.program.protocols.table model (functionTable model) Identities.written)
      (onceImages.protocols.table model (functionTable model)
        (originIdentities onceImages.origins))
      (stepFits (suiteMeaning model) onceImages.marks) :=
  rewriteProtocols_threads (quiet model) (suite_rule_sound model) Identities.written
    typed.program.protocols _ onceImages fiatShamir_rewrites

/-- The copies that the serialize step makes have the meanings of their definitions. The
Fiat–Shamir step makes no copy of a protocol of this package; the serialize step copies
the image of `challenge` (`Threading.callee_copied`). -/
theorem serialize_copies (model : Model) :
    PlainCallees twiceImages.table
      (once.protocols.table model (functionTable model) once.identities)
      (twiceImages.protocols.table model (functionTable model)
        (originIdentities twiceImages.origins)) :=
  rewriteProtocols_plain (rule := layoutRule) once.identities once.protocols _ twiceImages
    serialize_rewrites

/-- A table in which every protocol stops. -/
def stoppingTable (model : Model) :
    (protocols : List ProtocolHeader) → ProtocolTable model protocols
  | [] => .nil
  | _ :: rest => .cons (fun _ _ _ => .halt .refused) (stoppingTable model rest)

/-- For the prover the image of `challenge` after the Fiat–Shamir step returns at once. -/
theorem callee_returns (model : Model) :
    returns ((once.protocols.table model (functionTable model) once.identities).get onceCallee []
      (single 0) (.cons (model.literal 1 []) (.cons PUnit.unit .nil))) = true :=
  kernel_rfl%

/-- The stopping protocol at the position of its copy does not. -/
theorem stopping_copy_stops (model : Model) :
    returns ((stoppingTable model twiceImages.new).get twiceCallee [] (single 0)
      (.cons (model.literal 1 []) (.cons PUnit.unit .nil))) = false :=
  kernel_rfl%

/-- The copies do not have the meanings of their definitions in a table in which every
protocol stops: the statement about copies is a condition on the table of the result. -/
theorem stopping_not_copies (model : Model) :
    ¬ PlainCallees twiceImages.table
      (once.protocols.table model (functionTable model) once.identities)
      (stoppingTable model twiceImages.new) := by
  intro copies
  have same := copies onceCallee twiceCallee (Option.some_get _).symm
  have applied := congrArg
    (fun meaning : (Threads.header suiteThreads (some roles) challengeHeader).Meaning model =>
      returns (meaning [] (single 0) (.cons (model.literal 1 []) (.cons PUnit.unit .nil))))
    same
  exact Bool.noConfusion
    (((stopping_copy_stops model).symm.trans applied).trans (callee_returns model))

/-- What fits the image of `challenge`: the handler of its marks, for the side of the
prover. -/
theorem challenge_fit (model : Model) (path : List Nat) :
    (stepFits (suiteMeaning model) onceImages.marks).get challenge roles path (single 0) true
      false rfl rfl
      (threadHandler (suiteMeaning model) (marksBelow path (onceImages.marks.get challenge roles))
        true false) := by
  rw [stepFits_get]
  exact ⟨prover_alone, threadHandler_follows _ _ _ _ path⟩

/-- No handler of the side of both transcript roles fits it. -/
theorem challenge_never_fit_both (model : Model) (path : List Nat)
    (handler : ThreadHandler model suiteThreads true true) :
    ¬ (stepFits (suiteMeaning model) onceImages.marks).get challenge roles path both true true
      rfl rfl handler := by
  rw [stepFits_get]
  exact fun fit => both_not_one fit.1

/-- A predicate that every handler satisfies, for every protocol of the package. -/
def everyHandlerFits (model : Model) : Values (CalleeFit model suiteThreads) typed.protocols :=
  .cons (fun _ _ _ _ _ _ _ _ => True) (.cons (fun _ _ _ _ _ _ _ _ => True) .nil)

/-- For the prover the image of `challenge` returns at once: the prover derives its coin. -/
theorem challenge_image_returns (model : Model) :
    returns ((onceImages.protocols.table model (functionTable model)
        (originIdentities onceImages.origins)).get onceChallenge [] (single 0)
      (.cons (model.literal 1 []) (.cons PUnit.unit .nil))) = true :=
  kernel_rfl%

/-- `challenge` under the handler that performs every effect as it is does not: the prover
receives the coin. -/
theorem challenge_passed_receives (model : Model) :
    returns ((((typed.program.protocols.table model (functionTable model)
          Identities.written).get challenge [] (single 0) .nil).interpretWith
        (passing model (ThreadState model suiteThreads true false))
        (model.literal 1 [], PUnit.unit)).bind fun result =>
      .done (Values.cons (Value := SideValue model (single 0)) (ty := suiteThreads.first roles)
        result.2.1
        (Values.cons (Value := SideValue model (single 0)) (ty := suiteThreads.second roles)
          result.2.2 result.1))) = false :=
  kernel_rfl%

/-- The statement about the callees fails when every handler fits: the image of `challenge`
is not `challenge` under the handler that performs every effect as it is. What fits a
callee is a condition. -/
theorem callees_not_thread_every_handler (model : Model) :
    ¬ CalleesThread onceImages.table
      (typed.program.protocols.table model (functionTable model) Identities.written)
      (onceImages.protocols.table model (functionTable model)
        (originIdentities onceImages.origins))
      (everyHandlerFits model) := by
  intro callees
  have threads := callees.threaded challenge roles onceChallenge (Option.some_get _).symm []
    (single 0) true false rfl rfl (passing model _) trivial (model.literal 1 []) PUnit.unit .nil
  have same := congrArg returns threads
  exact Bool.noConfusion
    (((challenge_image_returns model).symm.trans same).trans (challenge_passed_receives model))

/-! ## An entry that the Fiat–Shamir step copies -/

namespace Idle

/-- The tables of the package with one protocol of two roles in which the verifier makes a
literal and nothing is exchanged or drawn. -/
noncomputable abbrev raw : Raw.Package :=
  { Threading.raw with
    protocols := [⟨false, 2, [], [], [], .step (.at 1 (.literal (.bool true))) (.ret [])⟩]
    names := none }

/-- The declaration with that protocol as the entry. -/
noncomputable abbrev declaration : Raw.Declaration :=
  { Threading.declaration with entry := 0 }

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

noncomputable def suite : Suite operations typed.functions :=
  Suite.ofRaw (tableScope operations) (tableScope typed.functions)
    (declaration.suite.get suite_declared)

noncomputable abbrev suiteThreads : Threads := ⟨suite.state, suite.state⟩

noncomputable abbrev suiteRule : Rule suiteThreads operations typed.functions :=
  fiatShamirRule suite

kernel_refl layout_declared :
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome equals true

noncomputable def layout : Layout operations :=
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).get layout_declared

noncomputable abbrev layoutThreads : Threads := ⟨layout.writer, layout.reader⟩

noncomputable abbrev layoutRule : Rule layoutThreads operations typed.functions :=
  serializeRule layout

noncomputable abbrev functionTable (model : Model) : FunctionTable model typed.functions :=
  typed.program.functionTable model

/-- The header of the entry, and the entry. -/
noncomputable abbrev entryHeader : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev entry : Var typed.protocols entryHeader := ⟨0, kernel_rfl%⟩

/-- The Fiat–Shamir step. -/
noncomputable abbrev fiatShamirStep :
    Except StepRefusal (Stepped typed.typeTable operations typed.functions) :=
  stepProtocols suiteThreads suiteRule Identities.written 0 roles typed.program.protocols

kernel_refl fiatShamir_returns : fiatShamirStep.isOk equals true

noncomputable def once : Stepped typed.typeTable operations typed.functions :=
  okValue fiatShamirStep fiatShamir_returns

-- The entry has no operation that the step rewrites: the newest protocol of the result is
-- a copy.
kernel_refl once_copied : once.origins.head?.map (·.entry) equals some false

/-- The newest protocol of a step's result whose newest origin is a copy. -/
theorem newest_copy {origins : List Origin}
    (isCopy : origins.head?.map (·.entry) = some false) :
    ∃ origin earlier, origins = origin :: earlier ∧ origin.entry = false := by
  cases origins with
  | nil => cases isCopy
  | cons origin earlier => exact ⟨origin, earlier, rfl, Option.some.inj isCopy⟩

/-- The copy of the entry. -/
noncomputable abbrev onceEntry : Var once.headers entryHeader := ⟨0, kernel_rfl%⟩

/-- `stepProtocols_plain_entry` at this package and the Fiat–Shamir rule: the copy has the
meaning of the entry. -/
theorem fiatShamir_copies_entry (model : Model) :
    (once.protocols.table model (functionTable model) once.identities).get onceEntry =
      (typed.program.protocols.table model (functionTable model) Identities.written).get entry := by
  obtain ⟨origin, earlier, newest, isCopy⟩ := newest_copy once_copied
  obtain ⟨image, first, same⟩ := stepProtocols_plain_entry (model := model)
    (functionTable := functionTable model) (rule := suiteRule) Identities.written 0 roles
    typed.program.protocols once (okValue_eq _ _) entry rfl origin earlier newest isCopy
  have isNewest : image = onceEntry := Var.ext first
  subst isNewest
  exact same

/-- The serialize step on the result. It rewrites an entry without an exchange too: the
proof is a port of the entry. -/
noncomputable abbrev serializeStep :
    Except StepRefusal (Stepped typed.typeTable operations typed.functions) :=
  stepProtocols layoutThreads layoutRule once.identities (once.headers.length - 1) roles
    once.protocols

kernel_refl serialize_returns : serializeStep.isOk equals true

noncomputable def twice : Stepped typed.typeTable operations typed.functions :=
  okValue serializeStep serialize_returns

kernel_refl twice_newest : twice.origins.head?.map (·.entry) equals some true

noncomputable abbrev twiceEntry :
    Var twice.headers (layoutRule.entryHeader roles entryHeader) :=
  ⟨0, kernel_rfl%⟩

/-- `stepProtocols_plain_then_entry` at this package: after both steps the newest protocol
is the entry interpreted by the handler of the serialize step, between the start and the
finish of the serialize rule's entry. -/
theorem copied_then_serialized (model : Model) (path : List Nat) (side : Side)
    (one : OneTranscriptRole (side roles.prover) (side roles.verifier))
    (arguments : Values (SideValue model side) (layoutRule.entryPorts roles entryHeader).inputs) :
    (twice.protocols.table model (functionTable model) twice.identities).get twiceEntry path side
        arguments =
      ((serializeEntry (functions := typed.functions) layout).start side roles entryHeader
          arguments).bind fun state =>
        (((typed.program.protocols.table model (functionTable model) Identities.written).get entry
              path side
              ((serializeEntry (functions := typed.functions) layout).arguments side roles
                entryHeader arguments)).interpretWith
            (threadHandler (serializeMeaning layout)
              (marksBelow path
                (stepMarks layoutThreads layoutRule once.identities (once.headers.length - 1)
                  roles once.protocols))
              (side roles.prover) (side roles.verifier)) state).bind fun result =>
          (serializeEntry (functions := typed.functions) layout).finish side roles entryHeader
            result := by
  obtain ⟨firstOrigin, firstEarlier, firstNewest, isCopy⟩ := newest_copy once_copied
  obtain ⟨secondOrigin, secondEarlier, secondNewest, isEntry⟩ := newest_entry twice_newest
  obtain ⟨image, first, threads⟩ := stepProtocols_plain_then_entry
    (firstRule := suiteRule) (Functions.table_quiet typed.program.functions)
    (serializeRule_sound layout (functionTable model))
    (serializeEntry_sound layout (functionTable model)) Identities.written 0 roles
    typed.program.protocols once (okValue_eq _ _) twice (okValue_eq _ _) entry rfl ((Stepped.rewroteEntry_of_newest firstNewest).trans isCopy)
    ((Stepped.rewroteEntry_of_newest secondNewest).trans isEntry)
  have isNewest : image = twiceEntry := Var.ext first
  subst isNewest
  exact threads path side one arguments

end Idle

#print axioms both_not_one
#print axioms nobody_not_one
#print axioms passing_not_follows
#print axioms counting_not_passes
#print axioms passing_passes_rounds
#print axioms stray_not_passes
#print axioms rounds_fits
#print axioms rounds_never_fits_both
#print axioms rounds_never_fits_nobody
#print axioms idleMeaning_not_sound
#print axioms stoppingEntry_not_sound
#print axioms loudTable_not_quiet
#print axioms repeatedSite_not_nodup
#print axioms stopping_not_copies
#print axioms challenge_fit
#print axioms challenge_never_fit_both
#print axioms callees_not_thread_every_handler
#print axioms Idle.fiatShamir_copies_entry
#print axioms Idle.copied_then_serialized

end ThreadingWitnesses
