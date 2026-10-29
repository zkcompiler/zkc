import ZkcTools.ConstructionBindings.Alignment

/-! Finite actual-source controls. Both forms are computed by the existing
normalizer. Their connection derivations contain only the generic proposer.
The tests quantify arbitrary nominal models and source/reply values. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionCertificate
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

private def field : Ty := .field "bls12-381.fr"
private def inputs : List Ty := [field, field]
private def outputs : List Ty := [.boolean, field]

def arithmeticBody : Region protocolDialect inputs outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldSubtract "bls12-381.fr") rfl) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant true) rfl) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def arithmeticPattern : InputPattern inputs := .cons .present (.cons .present .nil)
def arithmeticForm : Form [] [] arithmeticPattern.scope outputs :=
  (normalize {} arithmeticBody 0 2 arithmeticPattern).toOption.getD (.halt .refused)

example : normalize {} arithmeticBody 0 2 arithmeticPattern = .ok arithmeticForm := rfl

def arithmeticLayout : Layout arithmeticPattern.scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here)))]

def arithmeticView (swapped : Bool := false) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.fieldSubtract "bls12-381.fr")
    (if swapped then [1, 0] else [0, 1]) [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant true) [] [.data .boolean])
    Domain.View.empty

private def emptySnapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "arithmetic"
  domains := []
  relations := []
  bindings := []
  definitions := []
  contracts := []
  catalogue := blsCatalogue

def arithmeticFunction : Function :=
  ⟨"arithmetic", .protocol, .publicDef, inputs, outputs,
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["P", "V"], ["P", "V"]]⟩,
    [], some (.protocol ⟨"arithmetic", []⟩),
    .block [.instruction (.fieldSubtract "bls12-381.fr") [0, 1] [field] [] "",
      .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0, 1])⟩
def arithmeticSnapshot : Snapshot := { emptySnapshot with
  definitions := [.function arithmeticFunction], contracts := [⟨"arithmetic", []⟩] }
def arithmeticChecked : CheckedProtocol :=
  ⟨⟨"arithmetic", ["P", "V"], inputs, outputs, [[0, 1], [0, 1]], [[0, 1], [0, 1]]⟩,
    arithmeticBody.erase, arithmeticBody, arithmeticBody.elaborate_erase⟩
example : checkProtocol arithmeticSnapshot [] [] arithmeticFunction = .ok arithmeticChecked := rfl
example : (check arithmeticSnapshot).isOk = true := by kernel_rfl

def arithmeticRouting : Original.Routing :=
  ⟨arithmeticSnapshot, .plain "arithmetic" ["P", "V"] 0 1, .producer, 0, [], [], [], []⟩

def arithmeticCertificate : Derivation arithmeticRouting {} [] [] outputs 0 (List.replicate outputs.length [0, 1]) [.data 3, .data 2] none [] arithmeticLayout arithmeticForm (arithmeticView false) := by
  derive_connection_alignment

/-- A receive, a nominal calculation, a guard and a send, on arbitrary inputs
and replies. The final tuple retains the non-Boolean residual. -/
def messageBody : Region protocolDialect inputs outputs :=
  .letOp (.mark "incoming") .nil .nil <|
  .letOp (.exchange field 0 1 "incoming") (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldSubtract "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "bls12-381.fr" 0) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "check") .nil .nil <|
  .letOp (.guard 1 "check") (.cons .here .nil) .nil <|
  .letOp (.mark "outgoing") .nil .nil <|
  .letOp (.exchange field 1 0 "outgoing") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant true) rfl) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def messagePattern : InputPattern inputs := .cons .present (.cons .absent .nil)
def messageForm : Form [] [] messagePattern.scope outputs :=
  (normalize {} messageBody 1 2 messagePattern).toOption.getD (.halt .refused)

example : normalize {} messageBody 1 2 messagePattern = .ok messageForm := rfl

def messageLayout : Layout messagePattern.scope := [.data (.present (.var .here))]

def messageFunction : Function :=
  ⟨"message", .protocol, .publicDef, inputs, outputs,
    some ⟨["P", "V"], [["V"], ["P"]], [["P", "V"], ["P", "V"]]⟩,
    [], some (.protocol ⟨"message", []⟩),
      .block [
        .instruction (.exchange "P" "V") [1] [field] [] "incoming",
        .instruction (.fieldSubtract "bls12-381.fr") [1, 0] [field] [] "",
        .instruction (.fieldConstant "bls12-381.fr" "0") [] [field] [] "",
        .instruction (.fieldEqual "bls12-381.fr") [1, 0] [.boolean] [] "",
        .instruction (.guard "V") [0] [] [] "check",
        .instruction (.exchange "V" "P") [2] [field] [] "outgoing",
        .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0, 1])⟩

def messageSnapshot : Snapshot := { emptySnapshot with
  entry := "message", definitions := [.function messageFunction], contracts := [⟨"message", []⟩] }
def messageChecked : CheckedProtocol :=
  ⟨⟨"message", ["P", "V"], inputs, outputs, [[1], [0]], [[0, 1], [0, 1]]⟩,
    messageBody.erase, messageBody, messageBody.elaborate_erase⟩
example : checkProtocol messageSnapshot [] [] messageFunction = .ok messageChecked := rfl
example : (check messageSnapshot).isOk = true := by kernel_rfl

def messageRouting : Original.Routing :=
  ⟨messageSnapshot, .plain "message" ["P", "V"] 0 1, .validator, 0,
    [⟨"message", [], ["message", "message", "incoming", "incoming", "P", "V"]⟩,
      ⟨"message", [], ["message", "message", "outgoing", "outgoing", "V", "P"]⟩], [], [], []⟩

def messageView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.receive "incoming" "incoming" "P" field [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.fieldSubtract "bls12-381.fr") [0, 1] [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.fieldConstant "bls12-381.fr" 0) [] [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.fieldEqual "bls12-381.fr") [2, 3] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.guard 4 []) <|
  Domain.View.sequence (Domain.View.send "outgoing" "outgoing" "P" 2 []) <|
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant true) [] [.data .boolean])
    Domain.View.empty

def messageCertificate : Derivation messageRouting {} [] [] outputs 1 (List.replicate outputs.length [0, 1]) [.data 5, .data 2] none [] messageLayout messageForm messageView := by
  derive_connection_alignment

example : arithmeticCertificate.size = 3 := rfl
example : messageCertificate.size = 8 := rfl

def arithmeticAccepted : Certificate arithmeticRouting {} [] 0 2 arithmeticChecked arithmeticPattern [.data 3, .data 2] none [] arithmeticLayout (arithmeticView false) := by
  derive_connection_alignment

def messageAccepted : Certificate messageRouting {} [] 1 2 messageChecked messagePattern [.data 5, .data 2] none [] messageLayout messageView := by
  derive_connection_alignment

-- The sole public soundness boundary starts at the actual checked source body,
-- with its actual input tuple, arbitrary models, replies and initial history.
example (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (state : Original.State model.toCarriers) (stack : state.frames = [])
    (binders : Binders model arithmeticPattern.scope) (abi : Original.InputABI)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations (arithmeticPattern.environment model binders))
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history arithmeticLayout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns arithmeticRouting 0 arithmeticChecked.outputScopes [.data 3, .data 2] none state.frames captured)
      (Original.InputLive abi (arithmeticPattern.environment model binders) captured)
      (Original.fold arithmeticRouting (arithmeticBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions tables 0 protocols {} Occurrence.iterations)
        (arithmeticPattern.environment model binders).get) state) (arithmeticView false model environment) :=
  arithmeticAccepted.simulation (RosterDistinct.root _ _) model tables (fun entry => entry.elim0) protocols state
    binders stack abi captured sorts bound inputRead environment related retained

example (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (state : Original.State model.toCarriers) (stack : state.frames = [])
    (binders : Binders model messagePattern.scope) (abi : Original.InputABI)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations (messagePattern.environment model binders))
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history messageLayout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns messageRouting 1 messageChecked.outputScopes [.data 5, .data 2] none state.frames captured)
      (Original.InputLive abi (messagePattern.environment model binders) captured)
      (Original.fold messageRouting (messageBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions tables 1 protocols {} Occurrence.iterations)
        (messagePattern.environment model binders).get) state) (messageView model environment) :=
  messageAccepted.simulation (RosterDistinct.root _ _) model tables (fun entry => entry.elim0) protocols state
    binders stack abi captured sorts bound inputRead environment related retained

-- A producer of alignment data cannot change the independently fixed output
-- row, even while preserving the acceptance result.
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] outputs 0 (List.replicate outputs.length [0, 1]) [.data 3, .data 2] none [] arithmeticLayout arithmeticForm (arithmeticView true) := by
  derive_connection_alignment

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] outputs 0 (List.replicate outputs.length [0, 1]) [.data 3, .data 0] none [] arithmeticLayout arithmeticForm (arithmeticView false) := by
  derive_connection_alignment

def changedResidualView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.fieldAdd "bls12-381.fr") [0, 1] [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant true) [] [.data .boolean])
    Domain.View.empty

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] outputs 0 (List.replicate outputs.length [0, 1]) [.data 3, .data 2] none [] arithmeticLayout arithmeticForm changedResidualView := by
  derive_connection_alignment

def extraFalseView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.fieldSubtract "bls12-381.fr") [0, 1] [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant true) [] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant false) [] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.guard 4 []) Domain.View.empty

/-- error: alignment-guard-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] outputs 0 (List.replicate outputs.length [0, 1]) [.data 3, .data 2] none [] arithmeticLayout arithmeticForm extraFalseView := by
  derive_connection_alignment

/-- error: alignment-route-request-history-coordinate-or-operand-mismatch -/
#guard_msgs (substring := true) in
example : Derivation { messageRouting with messages := [] } {} [] [] outputs 1 (List.replicate outputs.length [0, 1]) [.data 5, .data 2] none [] messageLayout messageForm messageView := by
  derive_connection_alignment

/-- error: alignment-route-request-history-coordinate-or-operand-mismatch -/
#guard_msgs (substring := true) in
example : Derivation { messageRouting with messages := messageRouting.messages ++ messageRouting.messages } {} [] [] outputs 1 (List.replicate outputs.length [0, 1]) [.data 5, .data 2] none [] messageLayout messageForm messageView := by
  derive_connection_alignment

/-- error: alignment-route-request-history-coordinate-or-operand-mismatch -/
#guard_msgs (substring := true) in
example : Derivation { messageRouting with messages := [⟨"other", [],
    ["message", "message", "incoming", "incoming", "P", "V"]⟩] } {} [] [] outputs 1 (List.replicate outputs.length [0, 1]) [.data 5, .data 2] none [] messageLayout messageForm messageView := by
  derive_connection_alignment

-- A transcript designation can never discharge a nominal data operand.
-- Public-history actions themselves remain outside this plain fragment.
/-- error: alignment-operand-not-data -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] outputs 0 (List.replicate outputs.length [0, 1]) [.data 3, .data 2] none [] [.history "stale", .data (.present (.var (.there .here)))] arithmeticForm (arithmeticView false) := by
  derive_connection_alignment

def literalBody : Region protocolDialect [] [.boolean] :=
  .letOp (.calculate (.booleanConstant true) rfl) .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.calculate .booleanAnd rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def literalForm : Form [] [] [] [.boolean] :=
  (normalize {} literalBody 0 2 .nil).toOption.getD (.halt .refused)
def literalView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant true) [] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant false) [] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.calculation model .booleanAnd [0, 1] [.data .boolean]) Domain.View.empty

example : normalize {} literalBody 0 2 .nil = .ok literalForm := rfl
example : Derivation arithmeticRouting {} [] [] [.boolean] 0 [[0, 1]] [.data 2] none [] [] literalForm literalView := by
  derive_connection_alignment

def falseGuardBody : Region protocolDialect [] [] :=
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.guard 0 "reject") (.cons .here .nil) .nil <| .ret .nil
def falseGuardForm : Form [] [] [] [] :=
  (normalize {} falseGuardBody 0 2 .nil).toOption.getD (.halt .refused)
def falseGuardView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.calculation model (.booleanConstant false) [] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.guard 0 []) Domain.View.empty

example : normalize {} falseGuardBody 0 2 .nil = .ok falseGuardForm := rfl
example : Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] [] falseGuardForm falseGuardView := by
  derive_connection_alignment

def booleanGuardForm : Form [] [] [.value .boolean] [.boolean] :=
  .guard .boolean (.var .here) (.bool true) (.done (.cons (.present (.var .here)) .nil))
example : Derivation arithmeticRouting {} [] [] [.boolean] 0 [[0, 1]] [.data 0] none [] [.data (.present (.var .here))] booleanGuardForm (fun _ => Domain.View.sequence (Domain.View.guard 0 []) Domain.View.empty) := by
  derive_connection_alignment

-- A true guard removed by normalization is still a real target checkpoint.
example : Derivation arithmeticRouting {} [] [] [.boolean] 0 [[0, 1]] [.data 0] none [] ([.data (.present (.bool true))] : Layout []) (.done (.cons (.present (.bool true)) .nil)) (fun _ => Domain.View.sequence (Domain.View.guard 0 []) Domain.View.empty) := by
  derive_connection_alignment

example (reason : PIR.Stop) : Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] ([] : Layout []) (.halt reason) (fun _ _ => .halt reason) := by
  derive_connection_alignment

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] ([] : Layout []) (.halt .refused) (fun _ _ => .halt .reject) := by
  derive_connection_alignment

private def unknownHelper : Helper := ⟨"unknown", .math, [], []⟩
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] ([] : Layout []) (.strict unknownHelper .nil (.done .nil)) (fun _ => Domain.View.empty) := by
  derive_connection_alignment

/-- error: alignment-compute-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] ([] : Layout [.value (.vector "bls12-381.fr"), .value .index]) (.compute (.boundedAt "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.done .nil)) (fun _ => Domain.View.empty) := by
  derive_connection_alignment

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] ([] : Layout [.value (.service "random.bls12-381.fr/0")]) (.query "query" "bls12-381.fr" (.cons (.var .here) .nil) (.done .nil)) (fun _ => Domain.View.empty) := by
  derive_connection_alignment

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] ([] : Layout [.component .boolean]) (.split (.input .here) (.halt .incomplete) (.done .nil)) (fun _ => Domain.View.empty) := by
  derive_connection_alignment

/-- error: alignment-loop-view-mismatch -/
#guard_msgs (substring := true) in
example (spec : RepeatSpec)
    (callback : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
    (state : Values (Comp [] []) spec.state) (captures : Values (Comp [] []) spec.captures) :
    Derivation arithmeticRouting {} [] [] [] 0 [] [] none [] ([] : Layout []) (.repeat spec "loop" callback (.present (.index 2)) state captures (.done .nil)) (fun _ => Domain.View.empty) := by
  derive_connection_alignment

private def callee : CalleeKey := ⟨⟨"callee", ["P", "V"], [], [], [], []⟩, 0, .nil, []⟩
/-- error: alignment-unsupported-callee -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [callee] [] 0 [] [] none [] ([] : Layout []) (.apply ⟨0, by decide⟩ callee.signature [0, 1] "call" .nil (.done .nil)) (fun _ => Domain.View.empty) := by
  derive_connection_alignment

/-- error: alignment-reference-out-of-range -/
#guard_msgs (substring := true) in
example : Derivation arithmeticRouting {} [] [] outputs 0 (List.replicate outputs.length [0, 1]) [.data 3, .data 2] none [] arithmeticLayout arithmeticForm (fun model => Domain.View.sequence
      (Domain.View.calculation model (.fieldSubtract "bls12-381.fr") [0, 17] [.data field]) Domain.View.empty) := by
  derive_connection_alignment

end Tests.ConnectionCertificate
