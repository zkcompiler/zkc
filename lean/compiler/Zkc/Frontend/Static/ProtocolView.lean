module

public import Zkc.Frontend.Static.Basic

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Static
open Syntax

/-- Required by a closed generated record. A protocol body enters the store after its
role placement and Core checks. The same body determines the nominal type at every use. -/
def checkedViewProtocol (inst : InstanceId) (place : Span) : CompileM Typing.ProtocolCode := do
  let known := (← getResults).body? inst
  if known.isNone || (known matches some .inProgress) then
    liftM ((← read).protocolBody inst place)
  let results ← getResults
  match results.body? inst with
  | some (.protocol code) =>
    if let some why := code.waiting then throw (.waiting why)
    return code
  | some (.waiting why) => throw (.waiting why)
  | some (.exhausted e) => throw (.exhausted e)
  | some .failed => throw .abandoned
  | _ => throw (.defect "view requested of a body that is not a checked protocol")
def drawType (law : Typed.RowRef) : CompileM ClosedType := do
  let ("law.uniform", #[.type t]) := (law.name, law.statics)
    | throw (.waiting "field type of an unrecognized sampling law")
  return t

def mayHaveField (view : ProtocolView) (role : Option Nat) : EventAudience → Bool
  | .transfer to owner => match view with
    | .run => true
    | .received _ => role.any to.contains
    | .coins _ => owner.isSome && owner == role
    | .inputs _ => false
  | .privateCoins owners => (view matches .coins _) && owners.all (fun rs => role.any rs.contains)
  | .unresolved => true

/-- Classify an event for the requested view before asking for its shape. A local
choice, loop or private sample imposes no field on an uninvolved role. -/
def eventFields (view : ProtocolView) (role : Option Nat) (sources : Array SourceEvent)
    (events : Array Typed.CheckedEvent) : CompileM (Array Typed.ViewField) := do
  let mut fields := #[]
  for occurrence in events do
    let .event _ id event _ nested _ := occurrence | do
      if let .untypedLoop span := occurrence then
        if let some site := sources.find? (fun s => span.startByte <= s.span.startByte &&
            s.span.startByte < span.stopByte && mayHaveField view role s.audience) then
          throw (.waiting s!"generated {view.member} field {site.name.getD "(unnamed)"} at {site.span.render}: empty loop")
      continue
    let some source := sources[id]? | throw (.defect "missing source event of a view")
    let name := source.name.getD s!"site{id}"
    let pending (shape : String) := Interrupt.waiting s!"generated {view.member} field {name} at {source.span.render}: {shape}"
    let audience : EventAudience := match event with
      | .send _ _ _ to => .transfer to none
      | .draw _ _ owner to => .transfer to (some owner)
      | .sample _ _ owner | .attempt _ owner => .privateCoins (some (.single owner))
      | .apply .. => .unresolved
    unless mayHaveField view role audience do continue
    if let .apply _ _ _ _ participants _ := event then
      unless role.all participants.contains do continue
    if nested then throw (pending "choice or loop")
    let type ← match event with
      | .send _ value .. => pure value.type
      | .draw _ law .. | .sample _ law .. => drawType law
      | .attempt .. => throw (pending "coins of an attempt")
      | .apply .. => throw (pending "protocol application")
    fields := fields.push ⟨.event id, name, type⟩
  return fields

def deriveViewFields (inst : InstanceId) (view : ProtocolView) (place : Span) :
    CompileM (Array Typed.ViewField) := do
  let state ← get
  let some key := state.results.key? inst | throw .abandoned
  let some decl := state.modules.lowered? key.declaration | throw .abandoned
  let .protocol head .. := decl.content | throw (.defect "expected a protocol head")
  let role := match view with
    | .run => none
    | .inputs r | .received r | .coins r => some r
  let role ← role.mapM fun r => do
    let some id := head.roster.idxOf? r | refuse "SX9" place s!"unknown role `{r}` in a generated view"
    pure id
  if let (.inputs _, some owner) := (view, role) then
    let some (.protocol ports _) := state.results.content? inst | throw (.waiting "the closed protocol signature")
    unless ports.size == head.ports.size do throw (.defect "port arity changed during typing")
    let mut fields := #[]
    for ((written, (name, type)), i) in (head.ports.zip ports).zipIdx do
      if written.holders.contains owner && !written.specification && written.readers.isNone then
        let some type := type | throw (.waiting s!"the closed type of port `{name}`")
        fields := fields.push ⟨.port i, name, type⟩
    return fields
  discard <| checkedViewProtocol inst place
  let some checked := (← getResults).checked? inst | throw (.defect "missing checked protocol")
  let fields ← eventFields view role head.events checked.events
  let mut names : Std.HashSet String := {}
  for f in fields do
    if names.contains f.name then refuse "SX9" place s!"ambiguous generated view selector `{f.name}`"
    names := names.insert f.name
  return fields

/-- Intern the nominal record with the same query dependency on a first use or a cache hit. -/
def protocolViewRecord (inst : InstanceId) (view : ProtocolView) (place : Span) :
    CompileM InstanceId := do
  let some protocol := (← getResults).key? inst | throw .abandoned
  let key := {protocol with view := some view}
  let requester ← currentRequest?
  if let some record := (← getResults).instance? key then
    if let some from_ := requester then modifyResults (·.addRequest from_ ⟨.signature, record⟩)
    return record
  let fields ← deriveViewFields inst view place
  let frame := { subject := Message.ofText view.member, span := place : ChainFrame }
  modifyGetResults fun results =>
    let (table, record, _) := results.signatures.intern key frame requester
    let table := table.setState record (.done (.viewRecord fields))
    let results := {results with signatures := table}
    let recordRef := ⟨.signature, record⟩
    let dependency := match view with | .inputs _ => QueryKind.signature | _ => .body
    let results := results.addRequest recordRef ⟨dependency, inst⟩
    (record, requester.elim results fun from_ => results.addRequest from_ recordRef)

/-- Look up the ordered source schema of the actual nominal record chosen by ordinary typing. -/
def nominalViewFields (record : InstanceId) : CompileM (Array Typed.ViewField) := do
  let some (.viewRecord fields) := (← getResults).signature? record
    | throw (.defect "expected a checked nominal protocol view")
  return fields

def protocolViewFields (inst : InstanceId) (view : ProtocolView) (place : Span) :
    CompileM (Array Typed.ViewField) := do
  nominalViewFields (← protocolViewRecord inst view place)

/-- A fork asks whether at least `limit` choices exist. Positive powers saturate as soon
as their partial product reaches the limit; 0^0 still denotes the empty sequence. -/
def cappedPower (base exponent limit : Nat) : Nat := Id.run do
  if exponent == 0 then return min 1 limit
  if base ≤ 1 then return min base limit
  let mut result := min 1 limit
  let mut factor := min base limit
  let mut remaining := exponent
  while remaining > 0 && result < limit do
    if factor == limit then return limit
    if remaining % 2 == 1 then result := min limit (result * factor)
    remaining := remaining / 2
    factor := min limit (factor * factor)
  return result

/-- The capacity of a draw truncated to the requested multiplicity. Only the separately
materialized run tree needs its exact leaf count and normal static-evaluation budget. -/
partial def viewLawCapacity (type : ClosedType) (limit : Nat) : CompileM Nat := do
  if limit == 0 then return 0
  match type with
  | .bool => return min limit 2
  | .index n => return min limit n
  | .nominal row #[] =>
    if let some entry := (← getVocabulary).type? row then
      if let some (_, n) := entry.naturalMembers.find? (·.1 == "Order") then return min limit n
  | .nonzero base => return (← viewLawCapacity base (limit + 1)) - 1
  | .seq _ (some 0) => return 1
  | .seq elem (some size) => return cappedPower (← viewLawCapacity elem limit) size limit
  | .tuple parts _ =>
    let mut product := 1
    for part in parts do
      product := min limit (product * (← viewLawCapacity part limit))
      if product == 0 then return 0
    return product
  | _ => pure ()
  throw (.waiting "the cardinality of a draw in a generated run tree")

end Zkc.Frontend.Static
