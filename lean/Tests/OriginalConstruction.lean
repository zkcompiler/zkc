import Zkc.Construction.OriginalCorrespondence
import Zkc.Construction.AuthoredPairProducer
import Zkc.Source.KernelRfl
import Mathlib.Data.ZMod.Basic

/-! An admitted original and actual artifact, with separate producer and
validator certificates. All message values and all handler responses remain
symbolic. This fixture is deliberately small; it is not a Sumcheck theorem. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.OriginalConstruction
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Original

private def source : Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "Root"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"Root", .protocol, .publicDef, [.boolean], [.boolean],
    some ⟨["P", "V"], [["P"]], [["V"]]⟩, [], none,
    .block [.instruction (.exchange "P" "V") [0] [.boolean] [] "m",
      .instruction (.guard "V") [0] [] [] "g"] (.ret [0])⟩]
  contracts := [⟨"Root", []⟩]
  catalogue := ⟨[], [], []⟩

private def body : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "m") .nil .nil <|
  .letOp (.exchange .boolean 0 1 "m") (.cons .here .nil) .nil <|
  .letOp (.mark "g") .nil .nil <|
  .letOp (.guard 1 "g") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

private def definition : CheckedProtocol :=
  ⟨⟨"Root", ["P", "V"], [.boolean], [.boolean], [[0]], [[1]]⟩,
    body.erase, body, body.elaborate_erase⟩

private def payload : UnitPayload where
  definitions := []
  protocols := [definition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := by rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

private def program : Program := ⟨source, payload⟩
example : check source = .ok program := by rfl

private def model : DomainModel := ringModel (ZMod 5) (ZMod 5)
private def context : Context := ⟨"Root", ["P", "V"], 0, 1, 0, "random.F/0", none, "suite", []⟩
private def message : Template := ⟨"Root", [], ["message", "Root", "m", "m", "P", "V"]⟩
private def routing (mode : Domain.Mode) : Routing :=
  ⟨source, context, mode, 0, [message], [], [], []⟩

private abbrev OriginalResult := Values (Component model.Value) [.boolean] × State model.toCarriers
private def initial : State model.toCarriers := {}
private def observed : State model.toCarriers :=
  ⟨[], [.message (context.message "m" 0 1) (.boolean true)]⟩

private def originalProducer (value : Bool) :=
  Original.participant model program (routing .producer) 0 (.cons (some value) .nil) initial
private def originalValidator :=
  Original.participant model program (routing .validator) 1 (.cons none .nil) initial

private def producerNormal (value : Bool) : PIR.Process (Domain.effects model.toCarriers) OriginalResult :=
  .call (.send "m" "m" "V" (.boolean value)) fun _ =>
  .call (.observe (.message (context.message "m" 0 1) (.boolean value))) fun _ =>
    .done (.cons none .nil, ⟨[], [.message (context.message "m" 0 1) (.boolean value)]⟩)
private def validatorNormal : PIR.Process (Domain.effects model.toCarriers) OriginalResult :=
  .call (.receive .boolean "m" "m" "P") fun value =>
  .call (.observe (.message (context.message "m" 0 1) (.boolean value))) fun _ =>
    if value then .done (.cons (some value) .nil,
      ⟨[], [.message (context.message "m" 0 1) (.boolean value)]⟩)
    else .halt .reject

private theorem producer_original (value : Bool) : originalProducer value = producerNormal value := by kernel_rfl
private theorem validator_original : originalValidator = validatorNormal := by
  change PIR.Process.call (I := Domain.effects model.toCarriers) (.receive .boolean "m" "m" "P") _ = _
  congr 1
  funext value
  change PIR.Process.call (I := Domain.effects model.toCarriers) (.observe (.message (context.message "m" 0 1) (.boolean value))) _ = _
  congr 1
  funext reply
  cases value <;> kernel_rfl

private def policy : Policy := ⟨"Root", "P", "V", 0, "suite", [], [], [], "fixture", "fixture"⟩
private def producer : Participant where
  source := "fixture"
  candidate := "fixture"
  policy := policy
  symbol := "producer"
  inputs := [.data .boolean, .transcript "suite"]
  outputs := [.transcript "suite"]
  instructions := [⟨.send "m" "m" "V", [0], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "suite" message, [1, 0, 2], [.transcript "suite"], []⟩]
  returned := [3]
private def validator : Participant where
  source := "fixture"
  candidate := "fixture"
  policy := policy
  symbol := "validator"
  inputs := [.transcript "suite"]
  outputs := [.data .boolean, .transcript "suite"]
  instructions := [⟨.receive "m" "m" "P" .boolean, [], [.data .boolean], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "suite" message, [0, 1, 2], [.transcript "suite"], []⟩,
    ⟨.guard "g", [1], [], []⟩]
  returned := [1, 3]

private def producerInputs (value : Bool) : Domain.Environment model.toCarriers :=
  [.data (.boolean value), .transcript "suite" []]
private def validatorInputs : Domain.Environment model.toCarriers := [.transcript "suite" []]

-- The exact source optional return is absent at the producer and present at
-- the validator. The complete artifact output also retains its transcript.
private def producerReturns (original : OriginalResult) (actual : Domain.Result model.toCarriers) : Prop :=
  ValuesHolds actual.values [.absent] original.1 ∧
  actual.values = [.transcript "suite" original.2.history] ∧ original.2.frames = []
private def validatorReturns (original : OriginalResult) (actual : Domain.Result model.toCarriers) : Prop :=
  ValuesHolds actual.values [.data 0] original.1 ∧
  ValuesHolds actual.environment [.data 1] original.1 ∧
  actual.values[0]? = actual.environment[1]? ∧
  actual.values[1]? = some (.transcript "suite" original.2.history) ∧
  actual.values.length = 2 ∧
  original.2.frames = []

-- Every checkpoint retains the source input/transcript prefix. Individual
-- live output locations are checked in validatorReturns, including the full ABI.
private def producerLive (value : Bool) (_ : PIR.Process (Domain.effects model.toCarriers) OriginalResult)
    (frame : Domain.Environment model.toCarriers) : Prop :=
  producerInputs value <+: frame
private def validatorLive (_ : PIR.Process (Domain.effects model.toCarriers) OriginalResult)
    (frame : Domain.Environment model.toCarriers) : Prop := validatorInputs <+: frame

private def producerFinal (value : Bool) : Domain.Environment model.toCarriers :=
  producerInputs value ++ [.indices [],
    .transcript "suite" [.message (context.message "m" 0 1) (.boolean value)]]
private def producerTarget (value : Bool) : PIR.Process (Domain.effects model.toCarriers) (Domain.Result model.toCarriers) :=
  .call (.checkpoint (producerInputs value)) fun _ =>
  .call (.checkpoint (producerInputs value)) fun _ =>
  .call (.send "m" "m" "V" (.boolean value)) fun _ =>
  .call (.checkpoint (producerInputs value)) fun _ =>
  .call (.checkpoint (producerInputs value)) fun _ =>
  .call (.checkpoint (producerInputs value ++ [.indices []])) fun _ =>
  .call (.checkpoint (producerInputs value ++ [.indices []])) fun _ =>
  .call (.observe (.message (context.message "m" 0 1) (.boolean value))) fun _ =>
  .call (.checkpoint (producerFinal value)) fun _ =>
    .done ⟨[.transcript "suite" [.message (context.message "m" 0 1) (.boolean value)]], producerFinal value⟩

private theorem producer_target (value : Bool) :
    Domain.participant model program context producer (producerInputs value) = producerTarget value := by
  kernel_rfl

/-- Separate producer correspondence for every original input Boolean. -/
private def producer_certificate (value : Bool) :
    Simulation producerReturns (producerLive value) (originalProducer value)
      (Domain.participant model program context producer (producerInputs value)) := by
  rw [producer_original, producer_target]
  unfold producerNormal producerTarget
  apply Simulation.checkpoint _ (by simp [producerLive])
  apply Simulation.checkpoint _ (by simp [producerLive])
  apply Simulation.call
  intro sent
  apply Simulation.checkpoint _ (by simp [producerLive])
  apply Simulation.checkpoint _ (by simp [producerLive])
  apply Simulation.checkpoint _ (by simp [producerLive, List.prefix_append])
  apply Simulation.checkpoint _ (by simp [producerLive, List.prefix_append])
  apply Simulation.call
  intro observed
  apply Simulation.checkpoint _ (by simp [producerLive, producerFinal, List.prefix_append])
  apply Simulation.done
  exact ⟨⟨rfl, trivial⟩, rfl, rfl⟩

private def validatorFrame (value : Bool) : Domain.Environment model.toCarriers :=
  validatorInputs ++ [.data (.boolean value), .indices [],
    .transcript "suite" [.message (context.message "m" 0 1) (.boolean value)]]
private def validatorTarget : PIR.Process (Domain.effects model.toCarriers) (Domain.Result model.toCarriers) :=
  .call (.checkpoint validatorInputs) fun _ =>
  .call (.checkpoint validatorInputs) fun _ =>
  .call (.receive .boolean "m" "m" "P") fun value =>
  .call (.checkpoint (validatorInputs ++ [.data (.boolean value)])) fun _ =>
  .call (.checkpoint (validatorInputs ++ [.data (.boolean value)])) fun _ =>
  .call (.checkpoint (validatorInputs ++ [.data (.boolean value), .indices []])) fun _ =>
  .call (.checkpoint (validatorInputs ++ [.data (.boolean value), .indices []])) fun _ =>
  .call (.observe (.message (context.message "m" 0 1) (.boolean value))) fun _ =>
  .call (.checkpoint (validatorFrame value)) fun _ =>
  .call (.checkpoint (validatorFrame value)) fun _ =>
    if value then
      .call (.checkpoint (validatorFrame value)) fun _ =>
        .done ⟨[.data (.boolean value),
          .transcript "suite" [.message (context.message "m" 0 1) (.boolean value)]], validatorFrame value⟩
    else .halt .reject

private theorem validator_target :
    Domain.participant model program context validator validatorInputs = validatorTarget := by
  change PIR.Process.call (I := Domain.effects model.toCarriers) (.checkpoint validatorInputs) _ = _
  congr 1
  funext first
  change PIR.Process.call (I := Domain.effects model.toCarriers) (.checkpoint validatorInputs) _ = _
  congr 1
  funext second
  change PIR.Process.call (I := Domain.effects model.toCarriers) (.receive .boolean "m" "m" "P") _ = _
  congr 1
  funext value
  cases value <;> kernel_rfl

/-- Separate validator correspondence for all typed replies, including reject. -/
private def validator_certificate :
    Simulation validatorReturns validatorLive originalValidator
      (Domain.participant model program context validator validatorInputs) := by
  rw [validator_original, validator_target]
  unfold validatorNormal validatorTarget
  apply Simulation.checkpoint _ (by simp [validatorLive])
  apply Simulation.checkpoint _ (by simp [validatorLive])
  apply Simulation.call
  intro value
  apply Simulation.checkpoint _ (by simp [validatorLive, List.prefix_append])
  apply Simulation.checkpoint _ (by simp [validatorLive, List.prefix_append])
  apply Simulation.checkpoint _ (by simp [validatorLive, List.prefix_append])
  apply Simulation.checkpoint _ (by simp [validatorLive, List.prefix_append])
  apply Simulation.call
  intro observed
  apply Simulation.checkpoint _ (by simp [validatorLive, validatorFrame, List.prefix_append])
  apply Simulation.checkpoint _ (by simp [validatorLive, validatorFrame, List.prefix_append])
  cases value with
  | false => exact .halt .reject
  | true =>
      apply Simulation.checkpoint _ (by simp [validatorLive, validatorFrame, List.prefix_append])
      apply Simulation.done
      exact ⟨⟨⟨true, rfl, rfl⟩, trivial⟩, ⟨⟨true, rfl, rfl⟩, trivial⟩, rfl, rfl, rfl, rfl⟩

-- This is full runtime transport, for every lawful monad, shared keyed oracle,
-- local-service interpreter, proof and oracle initial state. It is not a finite
-- execution test or an acceptance-only theorem.
theorem pair_correspondence {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (value : Bool) (oracle : Domain.Oracle m model.toCarriers S) (state : S)
    (services : Domain.LocalServices m model.toCarriers S) :
    Domain.executePair model program context producer validator (producerInputs value) validatorInputs
      oracle state services =
      (do
        let original ← Domain.run .producer oracle (producer_certificate value).paired
          ⟨producerInputs value, [], state⟩ services
        let produced := mapExecution Prod.snd original
        match produced.outcome with
        | .stopped _ => pure ⟨produced, none⟩
        | .returned _ =>
            let original ← Domain.run .validator oracle validator_certificate.paired
              ⟨validatorInputs, produced.state.proof, produced.state.oracle⟩ services
            pure ⟨produced, some (mapExecution Prod.snd original)⟩) :=
  Original.executePair_eq (model := model) (program := program) (routing := routing .producer)
    (producer := producer) (validator := validator)
    (producerInputs := producerInputs value) (validatorInputs := validatorInputs)
    (producer_certificate value) validator_certificate oracle state services

-- Structural producer admission alone permits an extra calculated false guard.
-- The semantic certificate must reject that actual altered artifact.
private def rejectingProducer : Participant :=
  { producer with instructions := producer.instructions ++
      [⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
       ⟨.guard "added-guard", [4], [], []⟩] }
example : AuthoredPair.checkProducer program context rejectingProducer = .ok () := by kernel_rfl

private def noOracle : Domain.Oracle Id model.toCarriers Unit :=
  fun _ _ state => (.stopped .refused, state)

private theorem rejecting_outcome :
    (Domain.run .producer noOracle
      (((Domain.participant model program context rejectingProducer (producerInputs true)).bind
        (fun _ => .done ())).interpret forgetCheckpoints)
      ⟨producerInputs true, [], ()⟩).outcome = .stopped .reject := by kernel_rfl
private theorem original_outcome :
    (Domain.run .producer noOracle
      (((originalProducer true).bind (fun _ => .done ())).interpret forgetCheckpoints)
      ⟨producerInputs true, [], ()⟩).outcome = .returned () := by kernel_rfl

/-- This is impossibility of correspondence for the actual admitted altered
artifact, not just a comparison of final Boolean values or artifact syntax. -/
theorem rejecting_producer_impossible : IsEmpty (Simulation producerReturns (producerLive true) (originalProducer true)
    (Domain.participant model program context rejectingProducer (producerInputs true))) := by
  constructor
  intro certificate
  have outcome := congrArg (fun process =>
    (Domain.run .producer noOracle process ⟨producerInputs true, [], ()⟩).outcome) certificate.shape
  have contradiction := rejecting_outcome.symm.trans outcome |>.trans original_outcome
  cases contradiction

-- The semantic certificate refuses an extra rejecting guard after success.
example (value : OriginalResult) :
    IsEmpty (Simulation producerReturns (producerLive true)
      (.done value) (.halt .reject)) := Simulation.done_not_halt _ _

#print axioms Tests.OriginalConstruction.pair_correspondence
#print axioms Tests.OriginalConstruction.rejecting_producer_impossible
#print axioms Zkc.Construction.Original.Simulation.runM
#print axioms Zkc.Construction.Original.executePair_eq

end Tests.OriginalConstruction
