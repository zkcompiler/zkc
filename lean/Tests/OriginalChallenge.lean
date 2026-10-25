import Zkc.Construction.OriginalCorrespondence
import Zkc.Source.KernelRfl
import Mathlib.Data.ZMod.Basic

/-! A complete original draw/delivery example. The producer's original receive
is constructed from that original public draw, rather than a proof read or an
unrelated query. Both roles connect to the actual nominal artifact for every
reply and every lawful monadic oracle, including failed calls and post-state. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
namespace Tests.OriginalChallenge
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Construction.Original

private def snapshot : Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "Root"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"Root", .protocol, .publicDef, [.service "random.bls12-381.fr/0"], [.field "bls12-381.fr"],
    some ⟨["P", "V"], [["V"]], [["P", "V"]]⟩, [], some (.protocol ⟨"Root", []⟩),
    .block [.instruction (.draw "V" "bls12-381.fr") [0] [.field "bls12-381.fr"] [] "q",
      .instruction (.exchange "V" "P") [0] [.field "bls12-381.fr"] [] "d"] (.ret [0])⟩]
  contracts := [⟨"Root", []⟩]
  catalogue := admittedCatalogue

private def body : Region protocolDialect [.service "random.bls12-381.fr/0"] [.field "bls12-381.fr"] :=
  .letOp (.mark "q") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "q") (.cons .here .nil) .nil <|
  .letOp (.mark "d") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "d") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)
private def definition : CheckedProtocol :=
  ⟨⟨"Root", ["P", "V"], [.service "random.bls12-381.fr/0"], [.field "bls12-381.fr"], [[1]], [[0, 1]]⟩,
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
private def program : Program := ⟨snapshot, payload⟩
example : check snapshot = .ok program := by rfl

private def model : DomainModel := ringModel (ZMod 5) (ZMod 5)
private def context : Context :=
  ⟨"Root", ["P", "V"], 0, 1, 0, "random.bls12-381.fr/0", some (.draw "bls12-381.fr"), "suite", [("q", "d")]⟩
private def draw : Template := ⟨"Root", [], ["query", "Root", "q", "input_0", "random.bls12-381.fr/0", "draw", "V"]⟩
private def delivery : Template := ⟨"Root", [], ["message", "Root", "d", "d", "V", "P"]⟩
private def queryOrigin := context.query "q" (.draw "bls12-381.fr")
private def deliveryOrigin := context.message "d" 1 0
private def routing (mode : Domain.Mode) : Routing :=
  ⟨snapshot, context, mode, 73, [delivery], [draw], [⟨draw, delivery⟩], []⟩

-- A runtime handle is associated with the source capability by the ABI. It
-- need not equal the source root port position (0 in this fixture).
example : (routing .validator).draw [] "q" "bls12-381.fr" 73 = some queryOrigin := by decide +kernel
example : (routing .validator).draw [] "q" "bls12-381.fr" 0 = none := by decide +kernel
example : (routing .producer).delivery [] "d" "bls12-381.fr" 1 = some (queryOrigin, deliveryOrigin) := by
  decide +kernel
example : (routing .producer).delivery [⟨"unrelated", 0⟩] "d" "bls12-381.fr" 1 = none := by decide +kernel
example : (routing .producer).delivery [] "d" "other-field" 1 = none := by decide +kernel

private abbrev OriginalResult := Values (Component model.Value) [.field "bls12-381.fr"] × State model.toCarriers
private def initial : State model.toCarriers := {}
private def inputs : Domain.Environment model.toCarriers := [.transcript "suite" []]
private def originalInputs (mode : Domain.Mode) : Values (Component model.Value) [.service "random.bls12-381.fr/0"] :=
  .cons (match mode with | .producer => none | .validator => some 73) .nil
private def original (mode : Domain.Mode) :=
  Original.participant model program (routing mode)
    (match mode with | .producer => 0 | .validator => 1) (originalInputs mode) initial
private def normal : PIR.Process (Domain.effects model.toCarriers) OriginalResult :=
  .call (.query [] queryOrigin) fun value =>
  .call (.observe (.message deliveryOrigin (.field "bls12-381.fr" value))) fun _ =>
    .done (.cons (some value) .nil,
      ⟨[], [.challenge queryOrigin, .message deliveryOrigin (.field "bls12-381.fr" value)]⟩)
private theorem original_normal (mode : Domain.Mode) : original mode = normal := by
  cases mode <;> kernel_rfl

private def policy : Policy :=
  ⟨"Root", "P", "V", 0, "suite", [], [], [("q", "d")], "fixture", "fixture"⟩
private def artifact : Participant where
  source := "fixture"
  candidate := "fixture"
  policy := policy
  symbol := "participant"
  inputs := [.transcript "suite"]
  outputs := [.data (.field "bls12-381.fr"), .transcript "suite"]
  instructions := [⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "suite" "bls12-381.fr" draw, [0, 1], [.data (.field "bls12-381.fr"), .transcript "suite"], []⟩,
    ⟨.observe "suite" delivery, [3, 2, 1], [.transcript "suite"], []⟩]
  returned := [2, 4]

private def queried (value : ZMod 5) : Domain.Environment model.toCarriers :=
  inputs ++ [.indices [], .data (.field "bls12-381.fr" value), .transcript "suite" [.challenge queryOrigin]]
private def final (value : ZMod 5) : Domain.Environment model.toCarriers :=
  queried value ++ [.transcript "suite" [.challenge queryOrigin, .message deliveryOrigin (.field "bls12-381.fr" value)]]
private def target : PIR.Process (Domain.effects model.toCarriers) (Domain.Result model.toCarriers) :=
  .call (.checkpoint inputs) fun _ =>
  .call (.checkpoint inputs) fun _ =>
  .call (.checkpoint (inputs ++ [.indices []])) fun _ =>
  .call (.checkpoint (inputs ++ [.indices []])) fun _ =>
  .call (.query [] queryOrigin) fun value =>
  .call (.checkpoint (queried value)) fun _ =>
  .call (.checkpoint (queried value)) fun _ =>
  .call (.observe (.message deliveryOrigin (.field "bls12-381.fr" value))) fun _ =>
  .call (.checkpoint (final value)) fun _ =>
    .done ⟨[.data (.field "bls12-381.fr" value),
      .transcript "suite" [.challenge queryOrigin, .message deliveryOrigin (.field "bls12-381.fr" value)]], final value⟩
private theorem artifact_target :
    Domain.participant model program context artifact inputs = target := by kernel_rfl

private def returns (original : OriginalResult) (actual : Domain.Result model.toCarriers) : Prop :=
  ValuesHolds actual.values [.data 0] original.1 ∧
  ValuesHolds actual.environment [.data 2] original.1 ∧
  actual.values[1]? = some (.transcript "suite" original.2.history) ∧
  actual.values.length = 2 ∧ original.2.frames = []
private def live (_ : PIR.Process (Domain.effects model.toCarriers) OriginalResult)
    (frame : Domain.Environment model.toCarriers) : Prop := inputs <+: frame

private def certificate (mode : Domain.Mode) :
    Simulation returns live (original mode) (Domain.participant model program context artifact inputs) := by
  rw [original_normal, artifact_target]
  unfold normal target
  apply Simulation.checkpoint _ (by simp [live])
  apply Simulation.checkpoint _ (by simp [live])
  apply Simulation.checkpoint _ (by simp [live, List.prefix_append])
  apply Simulation.checkpoint _ (by simp [live, List.prefix_append])
  apply Simulation.call
  intro value
  apply Simulation.checkpoint _ (by simp [live, queried, List.prefix_append])
  apply Simulation.checkpoint _ (by simp [live, queried, List.prefix_append])
  apply Simulation.call
  intro observed
  apply Simulation.checkpoint _ (by simp [live, final, queried, List.prefix_append])
  apply Simulation.done
  exact ⟨⟨⟨value, rfl, rfl⟩, trivial⟩, ⟨⟨value, rfl, rfl⟩, trivial⟩, rfl, rfl, rfl⟩

/-- The complete paired experiment retains query failures, proof, all nominal
observations, private-service interpreter and oracle post-state. -/
theorem pair_correspondence {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m model.toCarriers S) (state : S)
    (services : Domain.LocalServices m model.toCarriers S) :
    Domain.executePair model program context artifact artifact inputs inputs oracle state services =
      (do
        let original ← Domain.run .producer oracle (certificate .producer).paired ⟨inputs, [], state⟩ services
        let produced := mapExecution Prod.snd original
        match produced.outcome with
        | .stopped _ => pure ⟨produced, none⟩
        | .returned _ =>
            let original ← Domain.run .validator oracle (certificate .validator).paired
              ⟨inputs, produced.state.proof, produced.state.oracle⟩ services
            pure ⟨produced, some (mapExecution Prod.snd original)⟩) :=
  Original.executePair_eq (model := model) (program := program) (routing := routing .producer)
    (producer := artifact) (validator := artifact) (producerInputs := inputs) (validatorInputs := inputs)
    (certificate .producer) (certificate .validator) oracle state services

#print axioms Tests.OriginalChallenge.pair_correspondence
#print axioms Tests.OriginalChallenge.certificate
end Tests.OriginalChallenge
