module

public import Zkc.Source.Structured.OracleInvariant
public import Zkc.Source.Structured.CommonCoordinateCheck

@[expose] public section

/-! Checked-root ingress. A root store is constructed from the selected source's actual
input bindings. The environment supplies row counts and ordinary input components; it
cannot supply virtual tables, bodies, a replacement Oracle table, or an arbitrary store.
Receiver/provider consistency with holder data is an explicit environment obligation,
separate from this logical source execution and from a public transcript claim. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

structure OracleSubject (snapshot : Snapshot) where
  imported : Imported snapshot
  unit : CheckedOracleUnit
  selected : imported.program.payload.oracleUnit = some unit
  coordinates : CommonCoordinate.UnitCertificate snapshot
    imported.program.payload.protocols imported.program.payload.protocols

theorem OracleSubject.source {snapshot : Snapshot} (subject : OracleSubject snapshot) :
    subject.unit.snapshot = snapshot := subject.imported.oracleSource subject.selected

def Imported.oracleSubject {snapshot : Snapshot} (imported : Imported snapshot) :
    Except String (OracleSubject snapshot) :=
  match selected : imported.program.payload.oracleUnit with
  | none => .error "oracle-runtime-not-selected"
  | some unit => do
    let coordinates ← CommonCoordinate.certify snapshot imported.program.payload.protocols
    return ⟨imported, unit, selected, coordinates⟩

structure OracleRootBinding where
  kind : OracleKind
  holder : Nat
  receivers : List Nat
  bounds : List (String × Nat)
  dataPort : Nat
  handlePort : Nat
  location : OracleLocation

namespace OracleIngress

/-- Track only literal entry ports through the actual lowered spine. An internal pair
from components/application results is handled by the runtime, not installed as an input.
Every root logical leaf must have exactly one actual source binding. -/
def bindings : RawRegion Ty ProtocolOp → List (Option Nat) →
    Except String (List OracleRootBinding)
  | .ret _, _ => .ok []
  | .stop _, _ => .error "oracle-root-stop"
  | .bind .., _ => .error "oracle-root-binding-region"
  | .letOp op operands results _ next, origins => do
    let remaining ← bindings next (List.replicate results.length none ++ origins)
    match op with
    | .oracle (.input sort holder receivers bounds) location =>
      let [data, handle] := operands.map (fun index => origins[index]?.getD none)
        | throw "oracle-root-binding-arity"
      match data, handle with
      | none, none => return remaining
      | some dataPort, some handlePort =>
        let .singleton kind := sort | throw "oracle-root-sequence-ingress"
        return ⟨kind, holder, receivers, bounds, dataPort, handlePort, location⟩ :: remaining
      | _, _ => throw "oracle-root-pair-provenance"
    | _ => return remaining

def sourceBindings (entry : CheckedProtocol) : Except String (List OracleRootBinding) := do
  let bindings ← bindings entry.raw ((List.range entry.inputs.length).map some)
  let handles := entry.inputs.zipIdx.filterMap fun (type, index) =>
    if type.isOracleFamily then some index else none
  if (bindings.map (·.handlePort)).eraseDups.length != bindings.length then
    throw "oracle-root-duplicate-binding"
  if (bindings.map (·.dataPort)).eraseDups.length != bindings.length then
    throw "oracle-root-pair-provenance"
  if !handles.all (fun port => bindings.any (·.handlePort == port)) ||
      !bindings.all (fun binding => handles.contains binding.handlePort) then
    throw "oracle-root-missing-binding"
  return bindings

def replace {V : Ty → Type} {types : List Ty} {type : Ty} :
    Values V types → Var types type → V type → Values V types
  | .cons _ rest, .here, value => .cons value rest
  | .cons head rest, .there position, value => .cons head (replace rest position value)

structure Installed (model : DomainModel) (unit : CheckedOracleUnit) (types : List Ty) (participant : Nat) where
  inputs : Values (Component (ProtocolValue model.toCarriers)) types
  entries : OracleEntries model unit.snapshot unit.domains unit.math
  reachable : OracleStore.Reachable participant entries

/-- An actual binding installs only an immutable base table at its fixed input anchor.
The holder data and receiver anchor are checked before the source's oracle_input executes.
Input anchors differ from source construction anchors even at the same source location. -/
def install (model : DomainModel) (unit : CheckedOracleUnit) {types : List Ty}
    (root self : Nat) (bindings : List OracleRootBinding) (rows : List Nat)
    (current : Installed model unit types self) : Except String (Installed model unit types self) := do
  match bindings, rows with
  | [], [] => return current
  | binding :: remaining, count :: counts =>
    let some dataPort := Var.decode types binding.kind.data binding.dataPort
      | throw "oracle-root-data-type"
    let some handlePort := Var.decode types (.oracle binding.kind) binding.handlePort
      | throw "oracle-root-handle-type"
    if !OracleStore.validRows binding.kind count ||
        !OracleStore.validBounds binding.kind binding.bounds count then throw "oracle-root-shape"
    let anchor : OracleAnchor := ⟨⟨root, []⟩, .input binding.handlePort⟩
    let contents ← if self == binding.holder then do
      let some data := (current.inputs.get dataPort).bind ProtocolValue.toConcrete
        | throw "oracle-root-holder-data"
      let data := oracleDataRows model.toCarriers binding.kind data
      if data.length != count then throw "oracle-root-shape"
      pure (some data)
      else pure none
    if binding.receivers.contains self then
      if (current.inputs.get handlePort).bind ProtocolValue.toConcrete != some anchor then
        throw "oracle-root-anchor"
    if OracleStore.visible self binding.holder binding.receivers then
      let table : OracleStoredTable model unit.snapshot unit.domains unit.math binding.kind.answer :=
        ⟨anchor, count, binding.holder, binding.receivers, .base contents⟩
      if fresh : OracleStore.hasAnchor current.entries anchor = false then
        let entries := ⟨binding.kind.answer, table⟩ :: current.entries
        let inputs := if self == binding.holder then
          replace current.inputs dataPort (some (.deferred (OracleStore.view table)))
          else current.inputs
        let updated : Installed model unit types self :=
          ⟨inputs, entries, .inserted table current.reachable fresh trivial⟩
        install model unit root self remaining counts updated
      else throw "oracle-root-duplicate-anchor"
    else install model unit root self remaining counts current
  | _, _ => throw "oracle-root-shape-count"

end OracleIngress

structure OracleStart {snapshot : Snapshot} (subject : OracleSubject snapshot)
    (model : DomainModel) (participant : Nat) (S : Type) where
  bindings : List OracleRootBinding
  sourceBindings : OracleIngress.sourceBindings subject.imported.program.payload.entry = .ok bindings
  rows : List Nat
  ordinaryInputs : Values (Component model.Value) subject.imported.program.payload.entry.inputs
  installed : OracleIngress.Installed model subject.unit subject.imported.program.payload.entry.inputs participant
  constructed : OracleIngress.install model subject.unit
    (subject.unit.snapshot.definitions.findIdx (·.name == subject.unit.snapshot.entry)) participant bindings rows
    ⟨ProtocolValue.embedComponents ordinaryInputs, [], .empty⟩ = .ok installed
  provider : S

/-- Proof-carrying checked ingress is produced by the computational checker, not authored
as structural glue by a protocol author. Root sequence ingress has no installed contract. -/
def OracleSubject.start {snapshot : Snapshot} (subject : OracleSubject snapshot)
    (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) subject.imported.program.payload.entry.inputs)
    (rows : List Nat) {S : Type} (provider : S) :
    Except String (OracleStart subject model self S) := do
  if self ≥ subject.imported.program.payload.entry.roles.length then throw "oracle-root-role"
  match sourceBindings : OracleIngress.sourceBindings subject.imported.program.payload.entry with
  | .error code => throw code
  | .ok bindings =>
    let root := subject.unit.snapshot.definitions.findIdx (·.name == subject.unit.snapshot.entry)
    match constructed : OracleIngress.install model subject.unit root self bindings rows
      ⟨ProtocolValue.embedComponents inputs, [], .empty⟩ with
    | .error code => throw code
    | .ok installed => return ⟨bindings, sourceBindings, rows, inputs, installed, constructed, provider⟩

def OracleStart.state {snapshot : Snapshot} {subject : OracleSubject snapshot}
    {model : DomainModel} {self : Nat} {S : Type} (start : OracleStart subject model self S) :
    OracleProtocol.State model subject.unit.snapshot subject.unit.domains subject.unit.math S :=
  let root := subject.unit.snapshot.definitions.findIdx (·.name == subject.unit.snapshot.entry)
  ⟨⟨self, start.installed.entries, start.provider, 0⟩,
    {invocation := ⟨root, []⟩, definition := root}, []⟩

def OracleStart.run {snapshot : Snapshot} {subject : OracleSubject snapshot}
    {model : DomainModel} {self : Nat} {S E : Type} (start : OracleStart subject model self S)
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :=
  (subject.imported.program.oracleParticipant model self start.installed.inputs).run
    (OracleProtocol.handler model subject.unit.oracles ordinary base) start.state

theorem OracleStart.run_reachable {snapshot : Snapshot} {subject : OracleSubject snapshot}
    {model : DomainModel} {self : Nat} {S E : Type} (start : OracleStart subject model self S)
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :
    OracleProtocol.Reachable (start.run ordinary base).state :=
  OracleProtocol.run_reachable subject.unit.oracles ordinary base _ start.state start.installed.reachable

end Zkc.Source.Structured
