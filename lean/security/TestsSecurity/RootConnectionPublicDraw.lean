module

public import TestsSecurity.RootConnectionFixture
public import ZkcSecurity.Claims.Methods.RootConnectionClaims

@[expose] public section

/-! A small admitted public-draw source and its finite certified artifact.
This fixture exercises a genuine history-indexed query and a non-Boolean
residual for every nominal model and every oracle reply. Source admission and
finite connection are proved separately; native/export admission, coverage and
cryptographic security are outside this fixture's receipts.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
namespace TestsSecurity.RootConnectionPublicDraw
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionInputs ConnectionRoot ZkcSecurity.FiatShamir
attribute [local implicit_reducible] CheckedProtocol.signature

def field : Ty := .field "bls12-381.fr"
def service : Ty := .service "random.bls12-381.fr/0"
def body : Region protocolDialect [service] [.boolean, field] :=
  .letOp (.mark "challenge") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "challenge") (.cons .here .nil) .nil <|
  .letOp (.mark "delivery") .nil .nil <|
  .letOp (.exchange field 1 0 "delivery") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant true) rfl) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def definition : CheckedProtocol :=
  ⟨⟨"PublicDraw", ["P", "V"], [service], [.boolean, field], [[1]], [[1], [0, 1]]⟩,
    body.erase, body, body.elaborate_erase⟩
def function : Function :=
  ⟨"PublicDraw", .protocol, .publicDef, [service], [.boolean, field],
    some ⟨["P", "V"], [["V"]], [["V"], ["P", "V"]]⟩,
    [], some (.protocol ⟨"PublicDraw", []⟩), .block [
      .instruction (.draw "V" "bls12-381.fr") [0] [field] [] "challenge",
      .instruction (.exchange "V" "P") [0] [field] [] "delivery",
      .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0, 1])⟩
def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "PublicDraw"
  domains := []
  relations := []
  bindings := []
  definitions := [.function function]
  contracts := [⟨"PublicDraw", []⟩]
  catalogue := blsRows
def payload : UnitPayload where
  definitions := []
  protocols := [definition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := by kernel_rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel
def program : Program := ⟨snapshot, payload⟩
theorem admitted : check snapshot = .ok program := by kernel_rfl

def context : Context := .fiatShamir "PublicDraw" ["P", "V"] 0 1 0
  "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) "suite" [("challenge", "delivery")]
def draw : Template := ⟨"PublicDraw", [],
  ["query", "PublicDraw", "challenge", "input_0", "random.bls12-381.fr/0", "draw", "V"]⟩
def delivery : Template := ⟨"PublicDraw", [], ["message", "PublicDraw", "delivery", "delivery", "V", "P"]⟩
def routing : Original.Routing :=
  ⟨snapshot, context, .validator, 73, [delivery], [draw], [⟨draw, delivery⟩], []⟩
def artifact : Participant where
  source := snapshot.source
  candidate := "certified-public-draw-fixture"
  symbol := "validator"
  policy := ⟨"PublicDraw", "P", "V", 0, "", [], [], [], "suite", "fixture"⟩
  inputs := [.transcript "suite"]
  outputs := [.data .boolean, .data field, .transcript "suite"]
  instructions := [
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "suite" "bls12-381.fr" draw, [0, 1], [.data field, .transcript "suite"], []⟩,
    ⟨.observe "suite" delivery, [3, 2, 1], [.transcript "suite"], []⟩,
    ⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩]
  returned := [5, 2, 4]
def pattern : InputPattern definition.inputs := .cons (.capability "random.bls12-381.fr/0" 73) .nil
def inputLayout : InputLayout definition.signature context 1 artifact.inputs where
  locations := [.capability 73]
  pattern := pattern
  shape := by derive_connection_inputs
  sorted := rfl
  visible := rfl
  layout := [.history "suite"]
  cells := by derive_connection_inputs
  length := rfl
  history := rfl
def outputLayout : ConnectionInstallation.ReturnLayout definition.signature context 1 artifact :=
  (ConnectionInstallation.ReturnLayout.build definition.signature context 1 artifact).toOption.get (by decide +kernel)
def target : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.challenge context "suite" "bls12-381.fr" draw 0 1
    [.data field, .transcript "suite"]) <|
  Domain.View.sequence (Domain.View.observe context "suite" delivery 3 2 1 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant true) [] [.data .boolean]) Domain.View.empty
def root : RootCertificate program routing 1 artifact where
  snapshot := rfl
  roleValid := by decide
  distinct := RosterDistinct.root _ _
  inputs := inputLayout
  output := outputLayout
  target := target
  correspondence := fun _ => Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty [.indices])
    (Domain.Correspondence.sequence
      (Domain.Correspondence.challenge "suite" "bls12-381.fr" draw 0 1 [.data field, .transcript "suite"])
      (Domain.Correspondence.sequence
        (Domain.Correspondence.observe "suite" delivery 3 2 1 [.transcript "suite"])
        (Domain.Correspondence.sequence
          (Domain.Correspondence.calculation (.booleanConstant true) [] [.data .boolean]) Domain.Correspondence.empty)))
  alignment := {
    self := rfl
    historyProfile := rfl
    form := (normalize {} definition.body 1 2 pattern).toOption.getD (.halt .refused)
    normalized := rfl
    alignment := by derive_connection_alignment }

def installed (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  RootConnection.publicBridge root _ rfl rfl model physical

/-- The producer's folded endpoint reads the delivered challenge through the
same public query. This remains distinct from running a producer handler. -/
def producerRouting : Original.Routing := { routing with mode := .producer }
def producerArtifact : Participant := { artifact with
  symbol := "producer"
  outputs := [.data field, .transcript "suite"]
  returned := [2, 4] }
def producerPattern : InputPattern definition.inputs := .cons .absent .nil
def producerInputLayout : InputLayout definition.signature context 0 producerArtifact.inputs where
  locations := [.absent]
  pattern := producerPattern
  shape := by derive_connection_inputs
  sorted := rfl
  visible := rfl
  layout := [.history "suite"]
  cells := by derive_connection_inputs
  length := rfl
  history := rfl
def producerOutputLayout : ConnectionInstallation.ReturnLayout definition.signature context 0 producerArtifact :=
  (ConnectionInstallation.ReturnLayout.build definition.signature context 0 producerArtifact).toOption.get
    (by decide +kernel)
def producerRoot : RootCertificate program producerRouting 0 producerArtifact where
  snapshot := rfl
  roleValid := by decide
  distinct := RosterDistinct.root _ _
  inputs := producerInputLayout
  output := producerOutputLayout
  target := target
  correspondence := root.correspondence
  alignment := {
    self := rfl
    historyProfile := rfl
    form := (normalize {} definition.body 0 2 producerPattern).toOption.getD (.halt .refused)
    normalized := rfl
    alignment := by derive_connection_alignment }
def producerInstalled (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  RootConnection.publicBridge producerRoot _ rfl rfl model physical

/-- The actual query is keyed by the exact ABI history. Its arbitrary reply
is returned as a residual and observed at the subsequent delivery occurrence. -/
theorem readback (model : DomainModel) (history : Domain.History model.toCarriers)
    (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    (fun result => (Zkc.Transcript.mapOutcome (fun target => target.values) result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution oracle
        (Domain.participant model program context artifact [.transcript "suite" history]) suffix =
      let challenge := context.query "challenge" (.draw "bls12-381.fr")
      let answer := oracle history (.challenge challenge)
      (.returned [.data (.boolean true), .data (.field "bls12-381.fr" answer),
        .transcript "suite" ((history ++ [.challenge challenge]) ++
          [.message (context.message "delivery" 1 0) (.field "bls12-381.fr" answer)])], suffix) := by
  kernel_rfl

theorem selected_acceptance (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      m (Domain.Raw event)) (proof : Domain.Proof model.toCarriers) :
    (fun result => (Zkc.Transcript.mapOutcome
      (fun target => Domain.acceptanceAt 0 target.values) result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution oracle
        (Domain.participant model program context artifact physical) proof =
    (fun result => (Zkc.Transcript.mapOutcome (fun source => source.1.get .here) result.1,
      result.2)) <$>
      Zkc.Transcript.transform NominalDomain.interface oracle
        (RootConnection.publicPresentation root model physical) (root.inputs.initial physical).history proof :=
  RootConnection.publicReadAcceptance root _ rfl rfl .here rfl model physical oracle proof

#print axioms admitted
#print axioms root
#print axioms installed
#print axioms producerRoot
#print axioms producerInstalled
#print axioms readback
#print axioms selected_acceptance
#print axioms RootConnection.claimsInstallation
#print axioms RootConnection.publicBridge_inputFrame

end TestsSecurity.RootConnectionPublicDraw
