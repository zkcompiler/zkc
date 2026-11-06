module

public import Zkc.Source.Structured.OracleStore

@[expose] public section

/-! Local interpretation of typed logical requests. This handler does not authenticate receiver
answers or choose a realization. Public source-unit admission remains a separate consumer. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

namespace OracleExecution
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

def refusal {A : Type} (state : OracleRuntimeState model snapshot domains math S) (location : OracleLocation) (code : String) :
    PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E) A :=
  ⟨.stopped .refused, state, [.refusal location code]⟩

def returned {A : Type} (state : OracleRuntimeState model snapshot domains math S) (value : A) :
    PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E) A := ⟨.returned value, state, []⟩

def deferredView {carriers : Carriers} {type : Ty} (sort : OracleLogicalSort)
    (value : ProtocolValue carriers type) : Option (OracleDataView sort) :=
  match value with
  | @ProtocolValue.deferred _ actual view =>
      if equal : actual = sort then some (equal ▸ view) else none
  | _ => none

def singletonView (state : OracleRuntimeState model snapshot domains math S) (kind : OracleKind) (holder : Nat) (receivers : List Nat)
    (bounds : List (String × Nat)) (anchor : OracleAnchor) :
    Option (OracleDataView (.singleton kind)) := do
  let table ← OracleStore.find state.entries kind.answer anchor
  if table.holder != holder || !OracleStore.sameMembers table.receivers receivers ||
      !OracleStore.visible state.self holder receivers ||
      !OracleStore.validRows kind table.rows || !OracleStore.validBounds kind bounds table.rows then
    none
  else some (OracleStore.view table)

def sequenceReferences (state : OracleRuntimeState model snapshot domains math S) (kind : OracleKind) (holder : Nat)
    (receivers : List Nat) (bounds : List (String × Nat)) : List OracleAnchor →
      Option (List (OracleReference kind))
  | [] => some []
  | anchor :: rest => do
      let view ← singletonView state kind holder receivers bounds anchor
      let rest ← sequenceReferences state kind holder receivers bounds rest
      some (view.references :: rest)

def pairedView (state : OracleRuntimeState model snapshot domains math S) (sort : OracleLogicalSort) (holder : Nat)
    (receivers : List Nat) (bounds : List (String × Nat)) :
    model.Value sort.type → Option (OracleDataView sort) :=
  match sort with
  | .singleton kind => singletonView state kind holder receivers bounds
  | .sequence kind maximum => fun anchors ↦ do
      if anchors.length > maximum || maximum ≥ indexLimit then none else
        let references ← sequenceReferences state kind holder receivers bounds anchors
        some ⟨holder, receivers, references⟩

def kindBounds (kind : OracleKind) : List (String × Nat) :=
  match kind.rows with | some _ => [] | none => [("rows", indexLimit - 1)]

def sortBounds : OracleLogicalSort → List (String × Nat)
  | .singleton kind | .sequence kind _ => kindBounds kind

/-- Sequence manipulation checks handle metadata without querying or forcing data. -/
def visibleReference (state : OracleRuntimeState model snapshot domains math S)
    (kind : OracleKind) (anchor : OracleAnchor) : Bool :=
  match OracleStore.find state.entries kind.answer anchor with
  | none => false
  | some table => OracleStore.validRows kind table.rows &&
      OracleStore.visible state.self table.holder table.receivers

def capturesPresent {carriers : Carriers} : {types : List Ty} →
    Values (Component (ProtocolValue carriers)) types → Option (Values carriers.Value types)
  | _, .nil => some .nil
  | _, .cons value values => do
      let value ← value
      let concrete ← value.toConcrete
      let values ← capturesPresent values
      some (.cons concrete values)

def missingArgument {carriers : Carriers} : {types : List Ty} →
    Values (Component (ProtocolValue carriers)) types → Bool
  | _, .nil => false
  | _, .cons value rest => value.isNone || missingArgument rest

def capturedSourcesValidOn (self : Nat) (entries : OracleEntries model snapshot domains math)
    (holder : Nat) (receivers : List Nat) : {types : List Ty} →
    Values model.Value types → Bool
  | [], .nil => true
  | .oracle kind :: _, .cons anchor rest =>
      (singletonView (⟨self, entries, (), 0⟩ : OracleRuntimeState model snapshot domains math Unit)
        kind holder receivers (kindBounds kind) anchor).isSome &&
        capturedSourcesValidOn self entries holder receivers rest
  | _ :: _, .cons _ rest => capturedSourcesValidOn self entries holder receivers rest

def capturedSourcesValid (state : OracleRuntimeState model snapshot domains math S)
    (holder : Nat) (receivers : List Nat) {types : List Ty}
    (captures : Values model.Value types) : Bool :=
  capturedSourcesValidOn state.self state.entries holder receivers captures

def declaredRows (signature : OracleSignature) (captures : Values model.Value signature.inputs.dropLast) :
    Option Nat :=
  match signature.kind.rows with
  | some fixed => some fixed
  | none => do
      let [("rows", input)] := signature.shapeArguments | none
      let position ← Var.decode signature.inputs.dropLast .index input
      some (captures.get position)

/-- Interpret the twelve descriptors, retaining unused-result checks. Ordinary actions and
services are independent arms of the existing dependent effect sum. -/
def operation (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (location : OracleLocation) (self : Nat) (resolveRole : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E)
      (Values (Component (ProtocolValue model.toCarriers)) op.results) :=
  let fail := fun {A : Type} code ↦ (refusal state location code : PIR.Execution _ _ A)
  let pureResult := fun {A : Type} (value : A) ↦ (returned state value : PIR.Execution _ _ A)
  let skip := fun types ↦ pureResult (Values.absent (ProtocolValue model.toCarriers) types)
  if self != state.self then fail "oracle-request-role"
  else match op with
  | .query kind (some owner) =>
    let .cons handle (.cons position .nil) := arguments
    if resolveRole owner != state.self then skip [kind.answer]
    else match handle.bind ProtocolValue.toConcrete, position.bind ProtocolValue.toConcrete with
    | some anchor, some position =>
      let result := OracleStore.read model base
        ⟨kind, anchor, position, location, []⟩ state
      let outcome := match result.outcome with
        | .stopped reason => .stopped reason
        | .returned value => .returned (.cons (some (ProtocolValue.ofConcrete _ value)) .nil)
      ⟨outcome, result.state, result.events⟩
    | _, _ => ⟨.stopped .incomplete, state, []⟩
  | .query _ none => fail "oracle-inherited-owner-outside-body"
  | .send (.table row fixed) holder receivers bounds =>
    let .cons data (.cons dimension .nil) := arguments
    let holder := resolveRole holder
    let receivers := receivers.map resolveRole
    if !OracleStore.visible state.self holder receivers then skip [.oracle (.table row fixed)]
    else match dimension.bind ProtocolValue.toConcrete with
    | none => ⟨.stopped .incomplete, state, []⟩
    | some rows =>
      let kind := OracleKind.table row fixed
      if !OracleStore.validRows kind rows || !OracleStore.validBounds kind bounds rows then
        fail "oracle-send-shape"
      else
        let contents := if state.self == holder then
          data.bind ProtocolValue.toConcrete |>.map (oracleDataRows model.toCarriers kind)
          else some []
        match contents with
        | none => if data.isNone then ⟨.stopped .incomplete, state, []⟩
          else fail "oracle-send-concrete-demand"
        | some contents =>
          if state.self == holder && contents.length != rows then fail "oracle-send-shape"
          else
            let anchor := location.anchor
            let table : OracleStoredTable model snapshot domains math row :=
              ⟨anchor, rows, holder, receivers,
                .base (if state.self == holder then some contents else none)⟩
            match OracleStore.insert state.entries table with
            | none => fail "oracle-duplicate-construction"
            | some entries =>
              ⟨.returned (.cons (some (ProtocolValue.ofConcrete (.oracle kind) anchor)) .nil),
                {state with entries := entries},
                receivers.map (fun receiver ↦ .delivery location holder receiver anchor)⟩
  | .contents kind holder =>
    let .cons handle .nil := arguments
    if resolveRole holder != state.self then skip [kind.data]
    else match handle.bind ProtocolValue.toConcrete with
    | none => ⟨.stopped .incomplete, state, []⟩
    | some anchor =>
      match OracleStore.find state.entries kind.answer anchor with
      | none => fail "oracle-contents-anchor"
      | some table =>
        if table.holder != state.self || !OracleStore.validRows kind table.rows then
          fail "oracle-contents-holder"
        else pureResult (.cons (some (ProtocolValue.deferred (OracleStore.view table))) .nil)
  | .shape kind dimension =>
    let .cons handle .nil := arguments
    match handle.bind ProtocolValue.toConcrete with
    | none => pureResult (.cons none .nil)
    | some anchor =>
      match OracleStore.find state.entries kind.answer anchor with
      | none => fail "oracle-shape-anchor"
      | some table =>
        if dimension != "rows" || !OracleStore.validRows kind table.rows ||
            !OracleStore.visible state.self table.holder table.receivers then
          fail "oracle-shape-dimension"
        else pureResult (.cons (some (ProtocolValue.ofConcrete .index table.rows)) .nil)
  | .forgetShape (.table sourceRow sourceRows) (.table targetRow targetRows) =>
    let .cons handle .nil := arguments
    if sourceRow != targetRow || sourceRows.isNone || targetRows.isSome then
      fail "oracle-shape-refinement"
    else match handle.bind ProtocolValue.toConcrete with
    | none => pureResult (.cons none .nil)
    | some anchor =>
      match OracleStore.find state.entries sourceRow anchor with
      | none => fail "oracle-shape-anchor"
      | some table =>
        if !OracleStore.validRows (.table sourceRow sourceRows) table.rows ||
            !OracleStore.visible state.self table.holder table.receivers then
          fail "oracle-shape-refinement"
        else pureResult (.cons (some (ProtocolValue.ofConcrete (.oracle (.table targetRow targetRows))
          anchor)) .nil)
  | .sequenceEmpty kind maximum roles =>
    if !(roles.map resolveRole).contains state.self then skip [.oracleSequence kind maximum]
    else if maximum ≥ indexLimit then fail "oracle-sequence-capacity"
    else pureResult (.cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) [])) .nil)
  | .sequenceAppend kind maximum roles =>
    let .cons handles (.cons handle .nil) := arguments
    if !(roles.map resolveRole).contains state.self then skip [.oracleSequence kind maximum]
    else match handles.bind ProtocolValue.toConcrete, handle.bind ProtocolValue.toConcrete with
    | some anchors, some anchor =>
      if anchors.length ≥ maximum || maximum ≥ indexLimit then fail "oracle-sequence-capacity"
      else if !anchors.all (visibleReference state kind) || !visibleReference state kind anchor then
        fail "oracle-sequence-anchor"
      else pureResult (.cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum)
        (anchors ++ [anchor]))) .nil)
    | _, _ => ⟨.stopped .incomplete, state, []⟩
  | .sequenceAt kind maximum roles =>
    let .cons handles (.cons position .nil) := arguments
    if !(roles.map resolveRole).contains state.self then skip [.oracle kind]
    else match handles.bind ProtocolValue.toConcrete, position.bind ProtocolValue.toConcrete with
    | some anchors, some index =>
      if anchors.length > maximum || maximum ≥ indexLimit || index ≥ indexLimit then
        fail "oracle-sequence-capacity"
      else if !anchors.all (visibleReference state kind) then fail "oracle-sequence-anchor"
      else match anchors[index]? with
      | none => fail "oracle-sequence-index"
      | some anchor => pureResult (.cons (some (ProtocolValue.ofConcrete (.oracle kind) anchor)) .nil)
    | _, _ => ⟨.stopped .incomplete, state, []⟩
  | .sequenceLength _kind maximum =>
    let .cons handles .nil := arguments
    match handles.bind ProtocolValue.toConcrete with
    | none => pureResult (.cons none .nil)
    | some anchors =>
      if anchors.length > maximum || maximum ≥ indexLimit then fail "oracle-sequence-capacity"
      else pureResult (.cons (some (ProtocolValue.ofConcrete .index anchors.length)) .nil)
  | .components sort holder receivers =>
    let .cons handles .nil := arguments
    let holder := resolveRole holder
    let receivers := receivers.map resolveRole
    if !OracleStore.visible state.self holder receivers then skip [sort.dataType, sort.type]
    else match handles.bind ProtocolValue.toConcrete with
    | none => ⟨.stopped .incomplete, state, []⟩
    | some anchors =>
      match pairedView state sort holder receivers (sortBounds sort) anchors with
      | none => fail "oracle-components-pair"
      | some view => pureResult (.cons
          (if state.self == holder then some (ProtocolValue.deferred view) else none)
          (.cons (if receivers.contains state.self then
            some (ProtocolValue.ofConcrete sort.type anchors) else none) .nil))
  | .input sort holder receivers bounds =>
    let .cons data (.cons handles .nil) := arguments
    let holder := resolveRole holder
    let receivers := receivers.map resolveRole
    if !OracleStore.visible state.self holder receivers then skip [sort.type]
    else
      let holderView := data.bind (deferredView sort)
      let anchors := if state.self == holder then holderView.map (fun view ↦ view.anchors _)
        else handles.bind ProtocolValue.toConcrete
      match anchors with
      | none => if data.isSome then fail "oracle-input-root-pair-unavailable"
          else ⟨.stopped .incomplete, state, []⟩
      | some anchors =>
        match pairedView state sort holder receivers bounds anchors with
        | none => fail "oracle-input-pair"
        | some view =>
          if state.self == holder && !(holderView.any (OracleStore.samePair view)) then
            fail "oracle-input-pair"
          else pureResult (.cons (some (ProtocolValue.ofConcrete sort.type (view.anchors _))) .nil)
  | .virtual signature holder receivers =>
    let args := arguments
    let holder := resolveRole holder
    let receivers := receivers.map resolveRole
    if !OracleStore.visible state.self holder receivers then skip [.oracle signature.kind]
    else match oracles.find? (fun checked ↦ checked.declaration.signature == signature) with
    | none => fail "oracle-virtual-declaration"
    | some checked =>
      if same : checked.declaration.signature = signature then
        match capturesPresent args with
        | none => if missingArgument args then ⟨.stopped .incomplete, state, []⟩
          else fail "oracle-virtual-capture-concrete-demand"
        | some captures =>
          match declaredRows signature captures with
          | none => fail "oracle-virtual-shape"
          | some rows =>
            if !OracleStore.validRows signature.kind rows ||
                !OracleStore.validBounds signature.kind signature.shapeBounds rows ||
                !capturedSourcesValid state holder receivers captures then
              fail "oracle-virtual-captures"
            else
              let captures := (congrArg (fun signature ↦ signature.inputs.dropLast) same).symm ▸ captures
              let table : OracleStoredTable model snapshot domains math signature.kind.answer :=
                ⟨location.anchor, rows, holder, receivers,
                  .virtual checked (congrArg (fun signature ↦ signature.kind.answer) same) captures⟩
              match OracleStore.insert state.entries table with
              | none => fail "oracle-duplicate-construction"
              | some entries =>
                ⟨.returned (.cons (some (ProtocolValue.ofConcrete (.oracle signature.kind)
                  location.anchor)) .nil), {state with entries := entries}, []⟩
      else fail "oracle-virtual-declaration"


def handler (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :
    PIR.Handler (oracleInterface model.toCarriers)
      (OracleRuntimeState model snapshot domains math S) (OracleEvent E) :=
  fun request state ↦ operation model oracles base request.location request.self request.roles
    request.operation request.arguments state

end OracleExecution
end Zkc.Source.Structured
