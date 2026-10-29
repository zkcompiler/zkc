import Tests.ConnectionPartialCertificate

/-! Retained nominal Math bodies with exact captured dependency prefixes.
Admission, table identity and outcome controls are separate: a mathematical
bound declaration is never supplied as a successful-invocation hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.ConnectionHelperCertificate
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

def field : Ty := .field "bls12-381.fr"
def scalarInputs : List Ty := [field, field]
def scalarLeafBody (changed : Bool) : Region dialect scalarInputs [field] :=
  if changed then
    .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
  else
    .letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
def scalarLeaf (changed : Bool) : CheckedDefinition :=
  ⟨"difference", .math, scalarInputs, [field], (scalarLeafBody changed).erase,
    scalarLeafBody changed, (scalarLeafBody changed).elaborate_erase⟩
def scalarPairBody : Region dialect scalarInputs [field, field] :=
  .letOp (.invoke (scalarLeaf false).helper) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def scalarPair : CheckedDefinition :=
  ⟨"differenceAndInput", .math, scalarInputs, [field, field], scalarPairBody.erase,
    scalarPairBody, scalarPairBody.elaborate_erase⟩
def scalarDefinitions (changed : Bool) : List CheckedDefinition := [scalarLeaf changed, scalarPair]
def scalarBody : Region protocolDialect scalarInputs [field, field] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke scalarPair.helper) rfl) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def scalarSource : CheckedProtocol :=
  ⟨⟨"main", ["P"], scalarInputs, [field, field], [[0], [0]], [[0], [0]]⟩,
    scalarBody.erase, scalarBody, scalarBody.elaborate_erase⟩
def scalarFunction : Function :=
  ⟨"main", .protocol, .publicDef, scalarInputs, [field, field],
    some ⟨["P"], [["P"], ["P"]], [["P"], ["P"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [.instruction (.call "differenceAndInput") [0, 1] [field, field] [] ""] (.ret [0, 1])⟩
def scalarSnapshot (changed : Bool) : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [
    .function ⟨"difference", .math, .privateDef, scalarInputs, [field], none, [], none,
      .block [.instruction (if changed then .fieldAdd "bls12-381.fr" else .fieldSubtract "bls12-381.fr")
        [0, 1] [field] [] ""] (.ret [0])⟩,
    .function ⟨"differenceAndInput", .math, .privateDef, scalarInputs, [field, field], none, [], none,
      .block [.instruction (.call "difference") [0, 1] [field] [] ""] (.ret [0, 1])⟩,
    .function scalarFunction]
  contracts := [⟨"main", []⟩]
  catalogue := blsCatalogue
def scalarUnit (changed : Bool) : UnitPayload where
  definitions := scalarDefinitions changed
  protocols := [scalarSource]
  entryIndex := ⟨0, by decide⟩
  linked := by cases changed <;> decide +kernel
  protocolsLinked := by cases changed <;> decide +kernel
  available := by
    apply checkUnitAvailability_ok_of_isOk
    cases changed <;> kernel_rfl
  realizationClosed := by cases changed <;> decide +kernel
  mapClosed := by cases changed <;> decide +kernel
def scalarProgram (changed : Bool) : Program := ⟨scalarSnapshot changed, scalarUnit changed⟩
example (changed : Bool) : check (scalarSnapshot changed) = .ok (scalarProgram changed) := by
  cases changed <;> kernel_rfl
def scalarRouting : Original.Routing :=
  ⟨scalarSnapshot false, .plain "main" ["P"] 0 1, .producer, 0, [], [], [], []⟩
def scalarPattern : InputPattern scalarInputs := .cons .present (.cons .present .nil)
def scalarLayout : Layout scalarPattern.scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here)))]
def scalarView (changed : Bool) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.helper model (scalarProgram changed) "differenceAndInput"
    [0, 1] [.data field, .data field]) Domain.View.empty
def scalarAccepted : Certificate scalarRouting [] {} (scalarDefinitions false) 0 1 scalarSource scalarPattern
    [.data 2, .data 3] scalarLayout (scalarView false) := by derive_connection_alignment
example : scalarAccepted.alignment.size = 2 := rfl

-- A bounded helper is admitted with a bound declaration, but its actual body
-- still refuses OOB invocations. Its enclosing mathematical function captures
-- exactly the prefix containing the leaf. The admitted entry here is empty;
-- the extra typed caller below tests arbitrary invocation, including OOB.
def readInputs : List Ty := [.vector "bls12-381.fr", .index]
def readLeafBody : Region dialect readInputs [field] :=
  .letOp (.boundedAt "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
def readLeaf : CheckedDefinition :=
  ⟨"read", .math, readInputs, [field], readLeafBody.erase, readLeafBody, readLeafBody.elaborate_erase⟩
def readPairBody : Region dialect readInputs [field, .index] :=
  .letOp (.invoke readLeaf.helper) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here (.cons (.there (.there .here)) .nil))
def readPair : CheckedDefinition :=
  ⟨"readAndIndex", .math, readInputs, [field, .index], readPairBody.erase,
    readPairBody, readPairBody.elaborate_erase⟩
def readDefinitions : List CheckedDefinition := [readLeaf, readPair]
def emptyBody : Region protocolDialect [] [] := .ret .nil
def emptySource : CheckedProtocol :=
  ⟨⟨"main", ["P"], [], [], [], []⟩, emptyBody.erase, emptyBody, emptyBody.elaborate_erase⟩
def readSnapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [
    .function ⟨"read", .math, .privateDef, readInputs, [field], none, [⟨1, 0, 0⟩], none,
      .block [.instruction (.boundedAt "bls12-381.fr") [0, 1] [field] [] ""] (.ret [0])⟩,
    .function ⟨"readAndIndex", .math, .privateDef, readInputs, [field, .index], none, [⟨1, 0, 0⟩], none,
      .block [.instruction (.call "read") [0, 1] [field] [] ""] (.ret [0, 2])⟩,
    .function ⟨"main", .protocol, .publicDef, [], [], some ⟨["P"], [], []⟩,
      [], some (.protocol ⟨"main", []⟩), .block [] (.ret [])⟩]
  contracts := [⟨"main", []⟩]
  catalogue := blsCatalogue
def readUnit : UnitPayload where
  definitions := readDefinitions
  protocols := [emptySource]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := by
    apply checkUnitAvailability_ok_of_isOk
    kernel_rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel
def readProgram : Program := ⟨readSnapshot, readUnit⟩
example : check readSnapshot = .ok readProgram := by kernel_rfl

def readBody : Region protocolDialect readInputs [field, .index] :=
  .letOp (.calculate (.invoke readPair.helper) rfl) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def readSource : CheckedProtocol :=
  ⟨⟨"readCaller", ["P"], readInputs, [field, .index], [[0], [0]], [[0], [0]]⟩,
    readBody.erase, readBody, readBody.elaborate_erase⟩
def readPattern : InputPattern readInputs := .cons .optional (.cons .optional .nil)
def readLayout : Layout readPattern.scope := [.data (.input .here), .data (.input (.there .here))]
def readView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.helper model readProgram "readAndIndex" [0, 1] [.data field, .data .index])
    Domain.View.empty
def readAccepted : Certificate scalarRouting [] {} readDefinitions 0 1 readSource readPattern
    [.data 2, .data 3] readLayout readView := by derive_connection_alignment
example : readAccepted.alignment.size = 2 := rfl

def repeatedBody : Region protocolDialect readInputs [field, .boolean, .boolean] :=
  .letOp (.calculate (.invoke readPair.helper) rfl) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.calculate .indexEqual rfl)
    (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.calculate .indexEqual rfl)
    (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)))
def repeatedSource : CheckedProtocol :=
  ⟨⟨"repeatedRead", ["P"], readInputs, [field, .boolean, .boolean], [[0], [0]], [[0], [0], [0]]⟩,
    repeatedBody.erase, repeatedBody, repeatedBody.elaborate_erase⟩
def repeatedView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.helper model readProgram "readAndIndex" [0, 1] [.data field, .data .index]) <|
  Domain.View.sequence (Domain.View.calculation model .indexEqual [3, 1] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.calculation model .indexEqual [3, 1] [.data .boolean]) Domain.View.empty
def repeatedAccepted : Certificate scalarRouting [] {} readDefinitions 0 1 repeatedSource readPattern
    [.data 2, .data 4, .data 5] readLayout repeatedView := by derive_connection_alignment
example : repeatedAccepted.alignment.size = 6 := rfl

-- There is one public accepted-data boundary, including its structural table
-- binding. No mathematical reference, totality or helper outcome is supplied.
example (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model readDefinitions tables)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (state : Original.State model.toCarriers) (stack : state.frames = [])
    (binders : Binders model readPattern.scope) (abi : Original.InputABI)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations (readPattern.environment model binders))
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history readLayout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns [.data 2, .data 3] state captured)
      (Original.InputLive abi (readPattern.environment model binders) captured)
      (Original.fold scalarRouting (readBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions tables 0 protocols {} Occurrence.iterations)
        (readPattern.environment model binders).get) state) (readView model environment) :=
  readAccepted.simulation rfl (RosterDistinct.root _ _) model tables bindings protocols state stack
    binders abi captured sorts bound inputRead environment related retained

def readTables (model : DomainModel) : Tables model (Occurrence.signature model.toCarriers) :=
  readDefinitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩
example (model : DomainModel) : ConnectionHelpers.TablesMatch model readDefinitions (readTables model) := fun _ => rfl

-- Exact actual helper invocations, including their captured dependent helper.
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    invoke (Domain.helperTable model readProgram) readPair.helper (.cons [value] (.cons 0 .nil)) =
      .done (.cons value (.cons 0 .nil)) := by kernel_rfl
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    Domain.View.helper model readProgram "readAndIndex" [0, 1] [.data field, .data .index]
      [.data (.vector "bls12-381.fr" [value]), .data (.index 0)] =
      .done [.data (.vector "bls12-381.fr" [value]), .data (.index 0),
        .data (.field "bls12-381.fr" value), .data (.index 0)] := by kernel_rfl
example (model : DomainModel) (value : model.Field "other") :
    Domain.View.helper model readProgram "readAndIndex" [0, 1] [.data field, .data .index]
      [.data (.vector "other" [value]), .data (.index 0)] = .halt .refused := by kernel_rfl
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    invoke (Domain.helperTable model readProgram) readPair.helper (.cons [value] (.cons 1 .nil)) =
      .halt .refused := by kernel_rfl
example (model : DomainModel) :
    invoke (Domain.helperTable model readProgram) readPair.helper (.cons [] (.cons 0 .nil)) =
      .halt .refused := by kernel_rfl
example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    readView model [.data (.vector "bls12-381.fr" [value]), .data (.index 1)] =
      .call (.checkpoint [.data (.vector "bls12-381.fr" [value]), .data (.index 1)])
        (fun _ => .halt .refused) := by kernel_rfl

-- On absent input the mathematical component body propagates absence and
-- still returns the independent index. A physical helper call cannot encode
-- that tuple, so the certificate must refuse this optional invocation.
example (model : DomainModel) (index : Nat) :
    readBody.denote (participantMeaningWithOn model (.silent _) Occurrence.actions (readTables model)
      0 [] {} Occurrence.iterations) (Values.cons none (.cons (some index) .nil)).get =
      .done (.cons none (.cons (some index) .nil)) := by kernel_rfl

/-- error: alignment-helper-declaration-mismatch -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} (scalarDefinitions false) 0 1 scalarSource scalarPattern
    [.data 2, .data 3] scalarLayout (scalarView true) := by derive_connection_alignment

/-- error: alignment-helper-key-mismatch -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} (scalarDefinitions false) 0 1 readSource readPattern
    [.data 2, .data 3] readLayout (scalarView false) := by derive_connection_alignment

/-- error: alignment-helper-operand-readback-mismatch-or-optional -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} readDefinitions 0 1 readSource readPattern
    [.data 2, .data 3] [.unused, .unused] readView := by derive_connection_alignment

/-- error: alignment-helper-operand-readback-mismatch-or-optional -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} readDefinitions 0 1 readSource
    (.cons .absent (.cons .present .nil)) [.data 2, .data 3]
    [.unused, .data (.present (.var .here))] readView := by derive_connection_alignment

/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} readDefinitions 0 1 readSource readPattern
    [.data 2, .data 2] readLayout readView := by derive_connection_alignment

/-- error: alignment-helper-static-mismatch -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} readDefinitions 0 1 readSource readPattern
    [.data 2, .data 3] readLayout
    (fun model => Domain.View.sequence (Domain.View.helper model readProgram "read" [0, 1]
      [.data field, .data .index]) Domain.View.empty) := by derive_connection_alignment

-- Keeping the name while changing the complete output signature is refused.
def changedKey : Helper := { readPair.helper with outputs := [field, field] }
def changedKeyBody : Region protocolDialect readInputs [field, field] :=
  .letOp (.calculate (.invoke changedKey) rfl) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def changedKeySource : CheckedProtocol :=
  ⟨⟨"changedKey", ["P"], readInputs, [field, field], [[0], [0]], [[0], [0]]⟩,
    changedKeyBody.erase, changedKeyBody, changedKeyBody.elaborate_erase⟩
/-- error: alignment-helper-key-mismatch -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} readDefinitions 0 1 changedKeySource readPattern
    [.data 2, .data 3] readLayout
    (fun model => Domain.View.sequence (Domain.View.helper model readProgram "readAndIndex" [0, 1]
      [.data field, .data field]) Domain.View.empty) := by derive_connection_alignment

/-- error: alignment-helper-static-mismatch -/
#guard_msgs (substring := true) in
example : Certificate scalarRouting [] {} readDefinitions 0 1 readSource readPattern
    [.data 2, .data 3] readLayout
    (fun model => Domain.View.sequence (Domain.View.helper model readProgram "readAndIndex" [0, 1]
      [.data field, .data field]) Domain.View.empty) := by derive_connection_alignment

end Tests.ConnectionHelperCertificate
