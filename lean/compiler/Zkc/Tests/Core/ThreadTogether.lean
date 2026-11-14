import Zkc.Tests.Core.Samplers
import Zkc.Tests.Core.ThreadingSumcheck
import Zkc.Tests.Core.ThreadingSchnorr
import Zkc.Tests.Core.ThreadingWitnesses
import Zkc.Core.ThreadTogetherFiatShamir

/-! The Fiat–Shamir image of an entry for a side that holds both transcript roles: the
theorem at three packages, and a witness and a failing example of what it is stated with.

- **Every run.** `EveryRun` holds of the honest package of `Tests/Core/Samplers.lean` with
  the verifier's `true` as the condition and fails with `false`; it fails of the package
  whose verifier stops and of a process that sends. `groupedComplete_iff_everyRun` is used
  in both directions at the honest package. A sampler with another coin at one site and
  count answers that request with the coin and every other request as before.
- **Refinement.** A process refines itself; a process that stops refines nothing that
  returns.
- **`Suite.Returns`.** It holds of the catalogue suites of `collecting` and `sumcheck`, by
  `Suite.ofRaw_catalogue_returns`, and of the source suite of `schnorr-source`, because each
  of the six functions of the package returns on every input in every model (the kernel
  evaluates each to a returned value). It fails of a suite whose absorbing function stops.
- **`RuleCouples`.** It holds of the Fiat–Shamir rule of `collecting`. It fails of a meaning
  whose two roles derive different coins at the draw that the rule rewrites.
- **`EntryCouples`.** It holds of the Fiat–Shamir entry of `collecting`. It fails of an entry
  whose start stops and of an entry whose finish stops.
- **`StatementAgrees`.** It holds of two equal copies and fails of two different ones, at a
  header of one agreed input; and it holds at the entry of `collecting` of inputs in which
  the prover and the verifier hold the same challenge and the same count.
- **The theorem.** `fiatShamir_entry_together` at the Fiat–Shamir step of `collecting`,
  `sumcheck` and `schnorr-source`, with every premise but the condition on the inputs
  discharged from the package: the equation of the step, the position of the entry and the
  origin of the newest image by the kernel, `Suite.Returns` as above. At `collecting` it is
  also stated at the side of both roles on inputs that agree, and as completeness for every
  sampler (`fiatShamir_complete`). `fiatShamir_entry_copied_together` at a package whose
  entry the step copies. The image of the applied protocol `challenge` of `collecting`
  refines it (`rewriteProtocols_refines`).
- **Every premise at once.** A package over the tables of `collecting` whose entry returns
  on every run in every model: `Program.fiatShamir_together` and `fiatShamir_complete` with
  every premise discharged. The kernel evaluates the entry to one draw and the image to a
  returned value, the one the theorem gives.

What is not checked here: a run of the image by the executor
(`Tests/Core/ConstructCollecting.lean` runs the programs), and the serialize step. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ThreadTogether

/-- The side of both transcript roles. -/
abbrev both : Side := ThreadingWitnesses.both

/-- The relation of two transcript states of a model: they are equal. -/
abbrev equalStates (model : Model) (state : Ty) :
    model.Value state → model.Value state → Prop :=
  fun atProver atVerifier => atProver = atVerifier

/-- A process that returns at once returns a value. -/
theorem returns_done {model : Model} {α : Type} {process : PIR.Process (Effects model) α}
    (returns : Threading.returns process = true) : ∃ value, process = .done value := by
  cases process with
  | done value => exact ⟨value, rfl⟩
  | halt reason => cases returns
  | call effect next => cases returns

/-! ## Every run -/

/-- Every run of the honest package returns, the verifier `true`. -/
theorem honest_every_run (model : Model) :
    EveryRun (Samplers.returned model true)
      (Samplers.grouped model Samplers.honest Samplers.honestEntry) :=
  (Samplers.honest_complete model).everyRun

/-- From every run back to every sampler. -/
theorem honest_complete_again (model : Model) :
    GroupedComplete (Samplers.grouped model Samplers.honest Samplers.honestEntry)
      (Samplers.returned model true) :=
  (honest_every_run model).groupedComplete

/-- Not every run of the honest package returns the verifier's `false`: the condition is a
condition on what a run returns. -/
theorem honest_not_every_run_false (model : Model) :
    ¬ EveryRun (Samplers.returned model false)
      (Samplers.grouped model Samplers.honest Samplers.honestEntry) :=
  fun every => Samplers.honest_not_complete_false model every.groupedComplete

/-- No run of the package whose verifier stops returns. -/
theorem rejecting_not_every_run (model : Model) :
    ¬ EveryRun (fun _ => True)
      (Samplers.grouped model Samplers.rejecting Samplers.rejectingEntry) := by
  rw [Samplers.rejecting_stops]
  exact id

/-- A process that has returned `true` returns `true` on every run. -/
theorem returned_every_run (model : Model) :
    EveryRun (· = true) (.done true : PIR.Process (Effects model) Bool) := rfl

/-- A process that sends does not return on every run: a grouped process has nobody to send
to. -/
theorem sending_not_every_run (model : Model) :
    ¬ EveryRun (fun _ => True)
      (.call (.send ⟨[], 0, 0⟩ .bool true) fun _ => .done true :
        PIR.Process (Effects model) Bool) :=
  id

/-- A sampler with the coin `true` at one site and count answers that request with it, and
the request before it as the sampler did. -/
theorem withCoin_answers (model : Model) (site : Site) (law : SamplingRow)
    (coin : model.Value law.output) :
    ((Samplers.sampler model).withCoin site 3 law.output coin).answer site 3 law = coin ∧
      ((Samplers.sampler model).withCoin site 3 law.output coin).answer site 2 law =
        (Samplers.sampler model).answer site 2 law :=
  ⟨Sampler.withCoin_answer _ site 3 law coin,
    Sampler.withCoin_elsewhere _ site 3 law.output coin (fun same => by cases same.2) _ _⟩

/-! ## Refinement -/

/-- A process refines itself. -/
theorem honest_refines_itself (model : Model) :
    Refines (fun value image => image = value)
      (Samplers.grouped model Samplers.honest Samplers.honestEntry)
      (Samplers.grouped model Samplers.honest Samplers.honestEntry) :=
  Refines.same _

/-- A process that stops does not refine one that returns, whatever the relation. -/
theorem stopped_not_refines (model : Model) :
    ¬ Refines (fun _ _ => True) (.done () : PIR.Process (Effects model) Unit)
      (.halt .reject : PIR.Process (Effects model) Unit) :=
  fun refines => refines (fun _ => True) trivial

/-! ## `Suite.Returns` -/

/-- Whether a declared suite is a catalogue suite. -/
def isCatalogue : Raw.Suite → Bool
  | .catalogue .. => true
  | .source .. => false

/-- The suite of a catalogue declaration returns, over every table of functions. -/
theorem catalogue_returns {operations : List OperationSignature} {functions : List FunctionHeader}
    (rows : Scope operations) (callees : Scope functions) (declared : Raw.Suite)
    (catalogue : isCatalogue declared = true) {model : Model}
    (functionTable : FunctionTable model functions) :
    (Suite.ofRaw rows callees declared).Returns functionTable := by
  cases declared with
  | catalogue state label start absorbing deriving_ identity =>
      exact Suite.ofRaw_catalogue_returns rows callees state label start absorbing deriving_
        identity functionTable
  | source state start absorbing deriving_ sites => cases catalogue

kernel_refl collecting_catalogue :
  isCatalogue (Threading.declaration.suite.get Threading.suite_declared) equals true

kernel_refl sumcheck_catalogue :
  isCatalogue (ThreadingSumcheck.declaration.suite.get ThreadingSumcheck.suite_declared) equals true

kernel_refl schnorr_source :
  isCatalogue (ThreadingSchnorr.declaration.suite.get ThreadingSchnorr.suite_declared) equals false

/-- The suite of `collecting` returns. -/
theorem collecting_returns (model : Model) :
    Threading.suite.Returns (Threading.functionTable model) :=
  catalogue_returns _ _ _ collecting_catalogue _

/-- The suite of `sumcheck` returns, whatever the two functions of the package do: no entry
of the suite is a function. -/
theorem sumcheck_returns (model : Model) :
    ThreadingSumcheck.suite.Returns (ThreadingSumcheck.functionTable model) :=
  catalogue_returns _ _ _ sumcheck_catalogue _

/-- Each of the six functions of `schnorr-source` returns on every input, in every model:
their rows are pure. -/
theorem schnorr_functions_return (model : Model) :
    FunctionsReturn (ThreadingSchnorr.functionTable model) := by
  intro header callee inputs
  obtain ⟨index, valid⟩ := callee
  match index, valid with
  | 0, valid => cases Option.some.inj valid; exact returns_done kernel_rfl%
  | 1, valid => cases Option.some.inj valid; exact returns_done kernel_rfl%
  | 2, valid => cases Option.some.inj valid; exact returns_done kernel_rfl%
  | 3, valid => cases Option.some.inj valid; exact returns_done kernel_rfl%
  | 4, valid => cases Option.some.inj valid; exact returns_done kernel_rfl%
  | 5, valid => cases Option.some.inj valid; exact returns_done kernel_rfl%
  | index + 6, valid => cases valid

/-- The source suite of `schnorr-source` returns. -/
theorem schnorr_returns (model : Model) :
    ThreadingSchnorr.suite.Returns (ThreadingSchnorr.functionTable model) :=
  FunctionsReturn.suite (schnorr_functions_return model) _

/-- A function of a state and a value. -/
abbrev absorbHeader : FunctionHeader := ⟨[.bool, .bool], [.bool], false⟩

/-- A table whose one function stops. -/
def stoppingFunctions (model : Model) : FunctionTable model [absorbHeader] :=
  .cons (fun _ => .halt .abort) .nil

/-- A suite whose state is `bool` and whose absorber of a `bool` is that function. -/
def stoppingSuite : Suite [] [absorbHeader] where
  state := .bool
  start := fun _ => none
  absorb := fun _ type =>
    match type with
    | .bool => some (.handler ⟨0, rfl⟩)
    | _ => none
  derive := fun _ _ _ => none

/-- What the prover does to absorb `false` into the state `false` stops. -/
theorem stoppingSuite_stops (model : Model) :
    Threading.returns
      ((Absorber.handler (operations := []) (state := .bool) (type := .bool)
        (⟨0, rfl⟩ : Var [absorbHeader] absorbHeader)).run (stoppingFunctions model) true false
        false) = false :=
  rfl

/-- The suite does not return over that table: `Suite.Returns` is a condition on the
functions of a source suite. -/
theorem stoppingSuite_not_returns (model : Model) :
    ¬ stoppingSuite.Returns (stoppingFunctions model) := by
  intro returns
  obtain ⟨next, absorbs⟩ :=
    returns.absorbs (.statement 0) .bool (.handler ⟨0, rfl⟩) rfl false false
  have ran := congrArg Threading.returns absorbs
  exact Bool.noConfusion ((stoppingSuite_stops model).symm.trans ran)

/-- Not every function of that table returns. -/
theorem stoppingFunctions_not_return (model : Model) :
    ¬ FunctionsReturn (stoppingFunctions model) :=
  fun returns => stoppingSuite_not_returns model (FunctionsReturn.suite returns stoppingSuite)

/-! ## `RuleCouples` -/

/-- The Fiat–Shamir rule of `collecting` keeps equal states equal. -/
theorem collecting_rule_couples (model : Model) :
    RuleCouples Threading.suiteRule (Threading.suiteMeaning model)
      (equalStates model Threading.suite.state) :=
  fiatShamirRule_couples Threading.suite (Threading.functionTable model) (collecting_returns model)

/-- The two states of the rule of `collecting`, for a draw. -/
noncomputable abbrev drawContext : List Located :=
  [Threading.suiteThreads.second Threading.roles, Threading.suiteThreads.first Threading.roles]

/-- The law of the field, the row 0 of the package. -/
noncomputable abbrev fieldLaw : Var Threading.operations ⟨[], [.nominal 0], .sampling⟩ :=
  ⟨0, kernel_rfl%⟩

/-- What the Fiat–Shamir rule emits at the draw of `rounds`. -/
noncomputable abbrev emittedDraw :
    Except StepRefusal
      (Emitted (ProtocolDialect Threading.operations Threading.typed.functions [] true)
        drawContext
        [⟨.nominal 0, Threading.roles.prover⟩, ⟨.nominal 0, Threading.roles.verifier⟩,
          Threading.suiteThreads.first Threading.roles,
          Threading.suiteThreads.second Threading.roles]) :=
  Threading.suiteRule.draw ThreadingWitnesses.roundsPlace 1 fieldLaw (.there .here) .here

kernel_refl draw_emitted : emittedDraw.isOk equals true

/-- A meaning whose two roles derive different coins at a draw of a nominal type: the
prover 0 and the verifier 1, in the model whose nominal carriers are the natural numbers. -/
def skewedMeaning :
    RuleMeaning ThreadingWitnesses.markingModel Threading.suiteThreads Threading.operations where
  exchange := fun _ _ _ _ _ _ _ _ => .halt .refused
  draw := fun prover verifier _ _ _ _ output _ state =>
    match output with
    | .nominal _ => .done ((Held.of prover (0 : Nat), Held.of verifier (1 : Nat)), state)
    | _ => .halt .refused

/-- The rule obligation fails of that meaning: from equal states the two roles hold
different coins. -/
theorem skewedMeaning_not_couples :
    ¬ RuleCouples Threading.suiteRule skewedMeaning
      (equalStates ThreadingWitnesses.markingModel Threading.suite.state) := by
  intro couples
  obtain ⟨coin, nextProver, nextVerifier, acts, _⟩ :=
    couples.draw (protocols := []) (deployed := true) ThreadingWitnesses.roundsPlace 1 fieldLaw
      (.there .here) .here (Threading.okValue emittedDraw draw_emitted)
      (Threading.okValue_eq _ _) ⟨[], 1, 1⟩ (0 : Nat) (0 : Nat) rfl
  have same := PIR.Process.done.inj acts
  have first : (0 : Nat) = coin := congrArg (fun result => result.1.1) same
  have second : (1 : Nat) = coin := congrArg (fun result => result.1.2) same
  exact absurd (first.trans second.symm) (by decide)

/-! ## `StatementAgrees` -/

/-- A protocol of two roles with one agreed input, a `bool` that each role holds. -/
abbrev agreedHeader : ProtocolHeader :=
  ⟨2, [⟨.bool, 0⟩, ⟨.bool, 1⟩], [],
    ⟨[⟨.bool, ⟨0, .here⟩, [⟨1, .there .here⟩]⟩], []⟩, false⟩

/-- The two copies, as the side of both roles holds them. -/
abbrev copies (model : Model) (atProver atVerifier : Bool) :
    Values (SideValue model both) agreedHeader.inputs :=
  .cons (ty := (⟨.bool, 0⟩ : Located)) atProver (.cons (ty := (⟨.bool, 1⟩ : Located)) atVerifier .nil)

-- The statement of the header is its one agreement.
kernel_refl agreed_statement :
  statementOf Threading.roles agreedHeader equals
    [⟨.bool, ⟨0, .here⟩, [⟨1, .there .here⟩]⟩]

/-- An agreement of two copies holds when the side holds both and they are equal. -/
theorem two_copies_hold (model : Model) (side : Side) {ports : List Located} (type : Ty)
    (first second : Copy ports type) (values : Values (SideValue model side) ports)
    (equal : ∀ (firstInside : side first.holder = true) (secondInside : side second.holder = true),
      Held.value (side first.holder) firstInside (values.get first.port) =
        Held.value (side second.holder) secondInside (values.get second.port)) :
    (⟨type, first, [second]⟩ : Agreement ports).Holds model side values := by
  intro one oneMember other otherMember oneInside otherInside
  simp only [Agreement.copies, List.mem_cons, List.not_mem_nil, or_false] at oneMember otherMember
  rcases oneMember with oneIs | oneIs <;> rcases otherMember with otherIs | otherIs
  all_goals
    have oneSame := oneIs.symm
    have otherSame := otherIs.symm
    subst oneSame
    subst otherSame
  · rfl
  · exact equal oneInside otherInside
  · exact (equal otherInside oneInside).symm
  · rfl

/-- Two equal copies agree. -/
theorem equal_copies_agree (model : Model) (copy : Bool) :
    StatementAgrees model both Threading.roles agreedHeader (copies model copy copy) := by
  intro agreement member
  rw [agreed_statement] at member
  cases List.mem_singleton.mp member
  exact two_copies_hold model both .bool _ _ _ fun _ _ => rfl

/-- Two different copies do not: the condition is a condition on the inputs. -/
theorem different_copies_disagree (model : Model) :
    ¬ StatementAgrees model both Threading.roles agreedHeader (copies model true false) := by
  intro agrees
  have holds := agrees ⟨.bool, ⟨0, .here⟩, [⟨1, .there .here⟩]⟩
    (by rw [agreed_statement]; exact List.mem_singleton.mpr rfl)
  have equal : true = false :=
    holds ⟨0, .here⟩ List.mem_cons_self ⟨1, .there .here⟩
      (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl
  exact Bool.noConfusion equal

-- The statement of `rounds`: the challenge and the count, each held by both roles.
kernel_refl collecting_statement :
  statementOf Threading.roles Threading.roundsHeader equals
    [⟨.nominal 0, ⟨0, ⟨0, kernel_rfl%⟩⟩, [⟨1, ⟨1, kernel_rfl%⟩⟩]⟩,
      ⟨.nat, ⟨0, ⟨2, kernel_rfl%⟩⟩, [⟨1, ⟨3, kernel_rfl%⟩⟩]⟩]

/-- Inputs of `rounds` in which the prover and the verifier hold one challenge and one
count. -/
abbrev honestInputs (model : Model) (challenge : model.Value (.nominal 0)) (count : Nat) :
    Values (SideValue model both) Threading.roundsHeader.inputs :=
  .cons (ty := (⟨.nominal 0, 0⟩ : Located)) challenge
    (.cons (ty := (⟨.nominal 0, 1⟩ : Located)) challenge
      (.cons (ty := (⟨.nat, 0⟩ : Located)) count
        (.cons (ty := (⟨.nat, 1⟩ : Located)) count .nil)))

/-- They agree on the statement. -/
theorem honest_inputs_agree (model : Model) (challenge : model.Value (.nominal 0)) (count : Nat) :
    StatementAgrees model both Threading.roles Threading.roundsHeader
      (honestInputs model challenge count) := by
  intro agreement member
  rw [collecting_statement] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact two_copies_hold model both _ _ _ _ fun _ _ => rfl
  · cases List.mem_singleton.mp member
    exact two_copies_hold model both _ _ _ _ fun _ _ => rfl

/-! ## `EntryCouples` -/

/-- The entry of the Fiat–Shamir rule of `collecting` starts the two states equal. -/
theorem collecting_entry_couples (model : Model) :
    EntryCouples Threading.suiteRule (Threading.suiteEntry model) (Threading.functionTable model)
      (equalStates model Threading.suite.state)
      (fun side roles header arguments => StatementAgrees model side roles header arguments) :=
  fiatShamirEntry_couples Threading.suite (Threading.functionTable model)
    (collecting_returns model)

/-- A header without inputs has no statement, so every input agrees on it. -/
theorem pair_agrees (model : Model) (side : Side) :
    StatementAgrees model side Threading.roles ThreadingWitnesses.pairHeader .nil :=
  fun _ member => nomatch member

/-- The obligation fails of an entry whose start stops: for the side of both roles, the
region that the rule made of a body returns, and the meaning says that the start does not. -/
theorem stoppingEntry_not_couples (model : Model) :
    ¬ EntryCouples Threading.suiteRule (ThreadingWitnesses.stoppingEntry model)
      (Threading.functionTable model) (equalStates model Threading.suite.state)
      (fun side roles header arguments => StatementAgrees model side roles header arguments) := by
  intro couples
  obtain ⟨Δ, rename, first, second, threaded, env, _, _, starts, _⟩ :=
    couples.runs (protocols := []) (deployed := true) .nil (ownSites 1 []) both
      ThreadingWitnesses.roundsPlace ThreadingWitnesses.pairHeader ThreadingWitnesses.returningBody
      (Threading.okValue ThreadingWitnesses.enteredBody ThreadingWitnesses.body_entered)
      (Threading.okValue_eq _ _) rfl rfl .nil (pair_agrees model both)
  cases starts

/-- What the entry of the Fiat–Shamir rule does, with a finish that stops instead. -/
noncomputable def stoppingFinish (model : Model) :
    EntryMeaning model Threading.suiteThreads Threading.suiteRule :=
  { Threading.suiteEntry model with finish := fun _ _ _ _ => .halt .refused }

/-- The obligation fails of an entry whose finish stops, in the model whose states are
natural numbers. -/
theorem stoppingFinish_not_couples :
    ¬ EntryCouples Threading.suiteRule (stoppingFinish ThreadingWitnesses.markingModel)
      (Threading.functionTable ThreadingWitnesses.markingModel)
      (equalStates ThreadingWitnesses.markingModel Threading.suite.state)
      (fun side roles header arguments =>
        StatementAgrees ThreadingWitnesses.markingModel side roles header arguments) := by
  intro couples
  obtain ⟨result, finishes⟩ :=
    couples.finishes both Threading.roles ThreadingWitnesses.pairHeader rfl rfl .nil
      ((0 : Nat), (0 : Nat)) rfl
  cases finishes

/-! ## The theorem at `collecting` -/

/-- `fiatShamir_entry_together` at `collecting`: for a side that holds the prover and the
verifier and inputs that agree on the statement, whenever every run of `rounds` returns
outputs of which a condition holds, every run of its Fiat–Shamir image returns such
outputs. -/
theorem collecting_together (model : Model) (path : List Nat) (side : Side)
    (isProver : side Threading.roles.prover = true)
    (isVerifier : side Threading.roles.verifier = true)
    (arguments : Values (SideValue model side) Threading.roundsHeader.inputs)
    (agrees : StatementAgrees model side Threading.roles Threading.roundsHeader arguments)
    (holds : Values (SideValue model side) Threading.roundsHeader.outputs → Prop) :
    EveryRun holds
        ((Threading.typed.program.protocols.table model (Threading.functionTable model)
          Identities.written).get Threading.rounds path side arguments) →
      EveryRun holds
        ((Threading.once.protocols.table model (Threading.functionTable model)
          Threading.once.identities).get Threading.onceEntry path side arguments) := by
  obtain ⟨origin, earlier, newest, isEntry⟩ := Threading.newest_entry Threading.once_newest
  obtain ⟨image, first, together⟩ := fiatShamir_entry_together Threading.suite
    (collecting_returns model) Identities.written 1 Threading.roles
    Threading.typed.program.protocols Threading.once Threading.fiatShamir_steps Threading.rounds
    rfl ((Stepped.rewroteEntry_of_newest newest).trans isEntry)
  have same : image = Threading.onceEntry := Var.ext first
  subst same
  exact together path side isProver isVerifier arguments agrees holds

/-- At the side of both roles and inputs with one challenge and one count. -/
theorem collecting_honest_together (model : Model) (challenge : model.Value (.nominal 0))
    (count : Nat) (holds : Values (SideValue model both) Threading.roundsHeader.outputs → Prop) :
    EveryRun holds
        ((Threading.typed.program.protocols.table model (Threading.functionTable model)
          Identities.written).get Threading.rounds [] both
          (honestInputs model challenge count)) →
      EveryRun holds
        ((Threading.once.protocols.table model (Threading.functionTable model)
          Threading.once.identities).get Threading.onceEntry [] both
          (honestInputs model challenge count)) :=
  -- Applied with every argument written: the elaborator would otherwise evaluate the image
  -- at this side to look for further arguments of the conclusion.
  @collecting_together model [] both rfl rfl (honestInputs model challenge count)
    (honest_inputs_agree model challenge count) holds

/-- `fiatShamir_complete` at `collecting`: if `rounds` is complete for every sampler on those
inputs, so is its Fiat–Shamir image, with the same accepted outputs. -/
theorem collecting_complete (model : Model) (challenge : model.Value (.nominal 0)) (count : Nat)
    (accepted : Values (SideValue model both) Threading.roundsHeader.outputs → Prop) :
    GroupedComplete
        ((Threading.typed.program.protocols.table model (Threading.functionTable model)
          Identities.written).get Threading.rounds [] both
          (honestInputs model challenge count)) accepted →
      GroupedComplete
        ((Threading.once.protocols.table model (Threading.functionTable model)
          Threading.once.identities).get Threading.onceEntry [] both
          (honestInputs model challenge count)) accepted := by
  obtain ⟨image, first, complete⟩ := fiatShamir_complete Threading.suite
    (collecting_returns model) Identities.written 1 Threading.roles
    Threading.typed.program.protocols Threading.once Threading.fiatShamir_steps Threading.rounds
    rfl
  have same : image = Threading.onceEntry := Var.ext first
  subst same
  exact complete [] both rfl rfl (honestInputs model challenge count)
    (honest_inputs_agree model challenge count) accepted

/-- `rewriteProtocols_refines` at the Fiat–Shamir step of `collecting`: the image of the
applied protocol `challenge` refines it from equal states, for a side that holds both of its
transcript roles, and returns its outputs after equal states. -/
theorem collecting_challenge_refines (model : Model) (path : List Nat) (side : Side)
    (isProver : side Threading.roles.prover = true)
    (isVerifier : side Threading.roles.verifier = true)
    (state : ThreadState model Threading.suiteThreads (side Threading.roles.prover)
      (side Threading.roles.verifier))
    (arguments : Values (SideValue model side) Threading.challengeHeader.inputs)
    (equal : CoupledState (equalStates model Threading.suite.state) isProver isVerifier state) :
    Refines
      (CoupledImage (equalStates model Threading.suite.state) isProver isVerifier
        (threadedValues (roles := Threading.roles)))
      ((Threading.typed.program.protocols.table model (Threading.functionTable model)
        Identities.written).get Threading.challenge path side arguments)
      ((Threading.onceImages.protocols.table model (Threading.functionTable model)
        (originIdentities Threading.onceImages.origins)).get Threading.onceChallenge path side
        (.cons state.1 (.cons state.2 arguments))) :=
  (rewriteProtocols_refines (fiatShamirRule_sound Threading.suite (Threading.functionTable model))
    (collecting_rule_couples model) Identities.written Threading.typed.program.protocols _
    Threading.onceImages Threading.fiatShamir_rewrites).threaded Threading.challenge
    Threading.roles Threading.onceChallenge (Option.some_get _).symm path side isProver isVerifier
    state arguments equal

/-! ## The theorem at `sumcheck` -/

/-- `fiatShamir_entry_together` at `sumcheck`. -/
theorem sumcheck_together (model : Model) (path : List Nat) (side : Side)
    (isProver : side Threading.roles.prover = true)
    (isVerifier : side Threading.roles.verifier = true)
    (arguments : Values (SideValue model side) ThreadingSumcheck.sumcheckHeader.inputs)
    (agrees : StatementAgrees model side Threading.roles ThreadingSumcheck.sumcheckHeader
      arguments)
    (holds : Values (SideValue model side) ThreadingSumcheck.sumcheckHeader.outputs → Prop) :
    EveryRun holds
        ((ThreadingSumcheck.typed.program.protocols.table model
          (ThreadingSumcheck.functionTable model) Identities.written).get
          ThreadingSumcheck.sumcheck path side arguments) →
      EveryRun holds
        ((ThreadingSumcheck.once.protocols.table model (ThreadingSumcheck.functionTable model)
          ThreadingSumcheck.once.identities).get ThreadingSumcheck.onceEntry path side
          arguments) := by
  obtain ⟨origin, earlier, newest, isEntry⟩ :=
    Threading.newest_entry ThreadingSumcheck.once_newest
  obtain ⟨image, first, together⟩ := fiatShamir_entry_together ThreadingSumcheck.suite
    (sumcheck_returns model) Identities.written 1 Threading.roles
    ThreadingSumcheck.typed.program.protocols ThreadingSumcheck.once
    ThreadingSumcheck.fiatShamir_steps ThreadingSumcheck.sumcheck rfl
    ((Stepped.rewroteEntry_of_newest newest).trans isEntry)
  have same : image = ThreadingSumcheck.onceEntry := Var.ext first
  subst same
  exact together path side isProver isVerifier arguments agrees holds

/-! ## The theorem at `schnorr-source` -/

/-- `fiatShamir_entry_together` at `schnorr-source`, whose suite calls functions of the
package: `Suite.Returns` is discharged, because every function returns. -/
theorem schnorr_together (model : Model) (path : List Nat) (side : Side)
    (isProver : side Threading.roles.prover = true)
    (isVerifier : side Threading.roles.verifier = true)
    (arguments : Values (SideValue model side) ThreadingSchnorr.schnorrHeader.inputs)
    (agrees : StatementAgrees model side Threading.roles ThreadingSchnorr.schnorrHeader arguments)
    (holds : Values (SideValue model side) ThreadingSchnorr.schnorrHeader.outputs → Prop) :
    EveryRun holds
        ((ThreadingSchnorr.typed.program.protocols.table model
          (ThreadingSchnorr.functionTable model) Identities.written).get ThreadingSchnorr.schnorr
          path side arguments) →
      EveryRun holds
        ((ThreadingSchnorr.once.protocols.table model (ThreadingSchnorr.functionTable model)
          ThreadingSchnorr.once.identities).get ThreadingSchnorr.onceEntry path side
          arguments) := by
  obtain ⟨origin, earlier, newest, isEntry⟩ :=
    Threading.newest_entry ThreadingSchnorr.once_newest
  obtain ⟨image, first, together⟩ := fiatShamir_entry_together ThreadingSchnorr.suite
    (schnorr_returns model) Identities.written 0 Threading.roles
    ThreadingSchnorr.typed.program.protocols ThreadingSchnorr.once
    ThreadingSchnorr.fiatShamir_steps ThreadingSchnorr.schnorr rfl
    ((Stepped.rewroteEntry_of_newest newest).trans isEntry)
  have same : image = ThreadingSchnorr.onceEntry := Var.ext first
  subst same
  exact together path side isProver isVerifier arguments agrees holds

/-! ## An entry that the step copies -/

/-- `fiatShamir_entry_copied_together` at the package whose entry exchanges nothing: every
run of the copy returns what every run of the entry returns, for every side. -/
theorem copied_together (model : Model) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) ThreadingWitnesses.Idle.entryHeader.inputs)
    (holds : Values (SideValue model side) ThreadingWitnesses.Idle.entryHeader.outputs → Prop) :
    EveryRun holds
        ((ThreadingWitnesses.Idle.typed.program.protocols.table model
          (ThreadingWitnesses.Idle.functionTable model) Identities.written).get
          ThreadingWitnesses.Idle.entry path side arguments) →
      EveryRun holds
        ((ThreadingWitnesses.Idle.once.protocols.table model
          (ThreadingWitnesses.Idle.functionTable model)
          ThreadingWitnesses.Idle.once.identities).get ThreadingWitnesses.Idle.onceEntry path side
          arguments) := by
  obtain ⟨origin, earlier, newest, isCopy⟩ :=
    ThreadingWitnesses.Idle.newest_copy ThreadingWitnesses.Idle.once_copied
  obtain ⟨image, first, together⟩ := fiatShamir_entry_copied_together (model := model)
    (functionTable := ThreadingWitnesses.Idle.functionTable model) ThreadingWitnesses.Idle.suite
    Identities.written 0 Threading.roles ThreadingWitnesses.Idle.typed.program.protocols
    ThreadingWitnesses.Idle.once (Threading.okValue_eq _ _) ThreadingWitnesses.Idle.entry rfl
    ((Stepped.rewroteEntry_of_newest newest).trans isCopy)
  have same : image = ThreadingWitnesses.Idle.onceEntry := Var.ext first
  subst same
  exact together path side arguments holds

/-! ## A package whose entry returns on every run, in every model

Every premise of the theorem holds of it, so its conclusion is not vacuous: the prover makes
the number 5 and sends it, the verifier draws a coin of the field for the prover, and the
verifier returns the number. The entry performs one draw; its Fiat–Shamir image performs no
effect. -/

namespace Returning

/-- The tables of `collecting` with that one protocol. -/
noncomputable abbrev raw : Raw.Package :=
  { Threading.raw with
    protocols := [⟨false, 2, [], [⟨.nat, 1⟩], [],
      .step (.at 0 (.literal (.nat 5))) <|
      .step (.exchange 0 1 0 0) <|
      .step (.draw 1 [0] 1 0 []) <|
      .ret [1]⟩]
    names := none }

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

/-- The suite of the declaration of `collecting`, over this package. -/
noncomputable def suite : Suite operations typed.functions :=
  Suite.ofRaw (tableScope operations) (tableScope typed.functions)
    (Threading.declaration.suite.get Threading.suite_declared)

/-- It returns: it is a catalogue suite. -/
theorem suite_returns (model : Model) : suite.Returns (typed.program.functionTable model) :=
  catalogue_returns _ _ _ collecting_catalogue _

/-- The header of the entry, and the entry. -/
noncomputable abbrev entryHeader : ProtocolHeader := typed.protocols.headD default

noncomputable abbrev entry : Var typed.protocols entryHeader := ⟨0, kernel_rfl%⟩

/-- The Fiat–Shamir step. -/
noncomputable abbrev fiatShamirStep :
    Except StepRefusal (Stepped typed.typeTable operations typed.functions) :=
  stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) Identities.written 0
    Threading.roles typed.program.protocols

kernel_refl fiatShamir_returns : fiatShamirStep.isOk equals true

noncomputable def once : Stepped typed.typeTable operations typed.functions :=
  Threading.okValue fiatShamirStep fiatShamir_returns

-- The step rewrote the entry.
kernel_refl once_rewritten : once.origins.head?.map (·.entry) equals some true

/-- The image of the entry. -/
noncomputable abbrev onceEntry : Var once.headers entryHeader := ⟨0, kernel_rfl%⟩

-- The entry has no input, so its statement is empty.
kernel_refl no_statement : statementOf Threading.roles entryHeader equals []

/-- The inputs agree on the statement. -/
theorem inputs_agree (model : Model) :
    StatementAgrees model both Threading.roles entryHeader .nil := by
  intro agreement member
  rw [no_statement] at member
  cases member

/-- The grouped meaning of the entry, with the meanings of the program's own functions. -/
noncomputable abbrev interactive (model : Model) :
    PIR.Process (Effects model) (Values (SideValue model both) entryHeader.outputs) :=
  (typed.program.protocolTable model Identities.written).get entry [] both .nil

/-- The grouped meaning of its Fiat–Shamir image. -/
noncomputable abbrev derived (model : Model) :
    PIR.Process (Effects model) (Values (SideValue model both) entryHeader.outputs) :=
  (once.protocols.table model (typed.program.functionTable model) once.identities).get onceEntry
    [] both .nil

/-- The verifier returns the number 5. -/
abbrev returnsFive (model : Model) : Values (SideValue model both) entryHeader.outputs → Prop :=
  fun outputs => Held.value (X := Nat) (both 1) rfl (outputs.get .here) = 5

/-- The entry is one draw of the law of the field, after which the verifier returns 5. -/
theorem interactive_draws (model : Model) :
    interactive model =
      .call (.draw ⟨[], 0, 1⟩ ⟨0, [], .nominal 0, rfl⟩ .nil) fun _ =>
        .done (.cons (ty := (⟨.nat, 1⟩ : Located)) (5 : Nat) .nil) :=
  kernel_rfl%

/-- Every run of the entry returns, the verifier 5: whatever the coin. -/
theorem interactive_every_run (model : Model) :
    EveryRun (returnsFive model) (interactive model) := by
  rw [interactive_draws]
  exact fun _ => rfl

/-- `Program.fiatShamir_together` at the package, with every premise discharged: every run
of the image returns, the verifier 5. -/
theorem derived_every_run (model : Model) : EveryRun (returnsFive model) (derived model) := by
  obtain ⟨image, first, together⟩ := Program.fiatShamir_together suite typed.program
    (suite_returns model) Identities.written 0 Threading.roles once (Threading.okValue_eq _ _)
    entry rfl
  have same : image = onceEntry := Var.ext first
  subst same
  exact together [] both rfl rfl .nil (inputs_agree model) (returnsFive model)
    (interactive_every_run model)

/-- The image as the kernel evaluates it: it performs no effect and returns 5, as the
theorem says. -/
theorem derived_returns (model : Model) :
    derived model = .done (.cons (ty := (⟨.nat, 1⟩ : Located)) (5 : Nat) .nil) :=
  kernel_rfl%

/-- `fiatShamir_complete` at the package: the entry is complete for every sampler, and so is
its image. -/
theorem derived_complete (model : Model) : GroupedComplete (derived model) (returnsFive model) := by
  obtain ⟨image, first, complete⟩ := fiatShamir_complete suite (suite_returns model)
    Identities.written 0 Threading.roles typed.program.protocols once (Threading.okValue_eq _ _)
    entry rfl
  have same : image = onceEntry := Var.ext first
  subst same
  exact complete [] both rfl rfl .nil (inputs_agree model) (returnsFive model)
    (interactive_every_run model).groupedComplete

end Returning

/-! ## Axioms -/

-- Every run and every sampler.
#print axioms Sampler.withCoin_answer
#print axioms Sampler.withCoin_elsewhere
#print axioms Asked.le_next
#print axioms Asked.next_self
#print axioms ReturnsAlone.of_later_coins
#print axioms ReturnsAlone.withoutCoin
#print axioms everyRun_of_returnsAlone
#print axioms returnsAlone_of_everyRun
#print axioms GroupedComplete.everyRun
#print axioms EveryRun.groupedComplete
#print axioms groupedComplete_iff_everyRun

-- Refinement and the laws of `repeat` and `choose`.
#print axioms Refines.done
#print axioms Refines.halt
#print axioms Refines.mono
#print axioms Refines.bind
#print axioms Refines.same
#print axioms Refines.bind_same
#print axioms Refines.of_eq
#print axioms Refines.andThen
#print axioms Refines.draw
#print axioms Refines.step
#print axioms CoupledState.of_eq
#print axioms CoupledState.along
#print axioms CoupledState.back
#print axioms RuleCouples.exchange_at
#print axioms RuleCouples.draw_at
#print axioms agreed_related
#print axioms repeatIterations_refines
#print axioms repeatProcess_refines
#print axioms repeat_refines
#print axioms selectArm_refines
#print axioms alternativeProcess_refines
#print axioms chosenRegion_refines
#print axioms choose_refines
#print axioms CalleesRefine.weaken

-- A region.
#print axioms same_step
#print axioms ret_refines
#print axioms stop_refines
#print axioms bind_refines
#print axioms at_refines
#print axioms sample_refines
#print axioms exchange_refines
#print axioms draw_refines
#print axioms repeat_region_refines
#print axioms choose_region_refines
#print axioms apply_operation_refines
#print axioms apply_refines
#print axioms threadRegion_refines
#print axioms threadRegions_refines

-- A program.
#print axioms definition_refines
#print axioms rewriteProtocols_refines
#print axioms rewriteProtocols_entry_together
#print axioms stepProtocols_entry_together

-- The Fiat–Shamir rule.
#print axioms Emitted.Gives.wrap_done
#print axioms Absorber.row_returns
#print axioms Deriver.row_returns
#print axioms Suite.Rows.returns
#print axioms appliedRow_some
#print axioms Suite.ofRaw_catalogue_rows
#print axioms Suite.ofRaw_catalogue_returns
#print axioms FunctionsReturn.suite
#print axioms Absorber.run_member
#print axioms fiatShamirRule_couples
#print axioms Agreement.copyOf_some
#print axioms Agreement.Holds.copies
#print axioms StatementAgrees.copies
#print axioms statementValues_together
#print axioms Suite.statementRun_together
#print axioms separatorStart_member
#print axioms holdValues_get_here
#print axioms Suite.startRun_together
#print axioms fiatShamirEntry_couples
#print axioms fiatShamir_entry_together
#print axioms fiatShamir_entry_copied_together
#print axioms fiatShamir_together
#print axioms fiatShamir_complete
#print axioms Program.fiatShamir_together

-- The checks of this file.
#print axioms honest_every_run
#print axioms honest_complete_again
#print axioms honest_not_every_run_false
#print axioms rejecting_not_every_run
#print axioms sending_not_every_run
#print axioms withCoin_answers
#print axioms stopped_not_refines
#print axioms collecting_returns
#print axioms sumcheck_returns
#print axioms schnorr_functions_return
#print axioms schnorr_returns
#print axioms stoppingSuite_not_returns
#print axioms stoppingFunctions_not_return
#print axioms collecting_rule_couples
#print axioms skewedMeaning_not_couples
#print axioms equal_copies_agree
#print axioms different_copies_disagree
#print axioms honest_inputs_agree
#print axioms collecting_entry_couples
#print axioms stoppingEntry_not_couples
#print axioms stoppingFinish_not_couples
#print axioms collecting_together
#print axioms collecting_honest_together
#print axioms collecting_complete
#print axioms collecting_challenge_refines
#print axioms sumcheck_together
#print axioms schnorr_together
#print axioms copied_together
#print axioms Returning.interactive_every_run
#print axioms Returning.derived_every_run
#print axioms Returning.derived_returns
#print axioms Returning.derived_complete

end ThreadTogether
