module

public import Zkc.Source.Structured.OracleBody
public import Zkc.Source.Structured.OracleEffects

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

@[expose] public section

/-! Immutable role-local logical tables and retained-body expansion. A receiver's base answers
come from the supplied provider, never another participant's private data. Provider states and
events survive every stop through `Execution.follow` and `Process.run`. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def OracleKind.rows : OracleKind → Option Nat
  | .table _ rows => rows

def oracleDataRows (carriers : Carriers) : (kind : OracleKind) →
    carriers.Value kind.data → List (carriers.Value kind.answer)
  | .table (.polynomial _) _, values => values
  | .table (.field _) _, values => values
  | .table (.group _) _, values => values
  | .table .index _, values => values
  | .table .boolean _, values => values
  | .table (.vector _) _, values => values
  | .table (.groups _) _, values => values
  | .table .indices _, values => values
  | .table (.service _) _, values => values
  | .table (.oracle _) _, values => values
  | .table (.oracleSequence ..) _, values => values
  | .table (.sequence _) _, values => values
  | .table (.product ..) _, values => values
  | .table (.resourceUnit _) _, values => values

def oracleRowsData (carriers : Carriers) : (kind : OracleKind) →
    List (carriers.Value kind.answer) → carriers.Value kind.data
  | .table (.polynomial _) _, values => values
  | .table (.field _) _, values => values
  | .table (.group _) _, values => values
  | .table .index _, values => values
  | .table .boolean _, values => values
  | .table (.vector _) _, values => values
  | .table (.groups _) _, values => values
  | .table .indices _, values => values
  | .table (.service _) _, values => values
  | .table (.oracle _) _, values => values
  | .table (.oracleSequence ..) _, values => values
  | .table (.sequence _) _, values => values
  | .table (.product ..) _, values => values
  | .table (.resourceUnit _) _, values => values

theorem oracleRowsData_dataRows (carriers : Carriers) (kind : OracleKind)
    (value : carriers.Value kind.data) :
    oracleRowsData carriers kind (oracleDataRows carriers kind value) = value := by
  cases kind with | table row rows => cases row <;> rfl

inductive OraclePayload (model : DomainModel) (snapshot : Snapshot)
    (domains : List DomainSpec) (math : OracleMathEnvironment) : Ty → Type where
  | base {row : Ty} (data : Option (List (model.Value row))) :
      OraclePayload model snapshot domains math row
  | virtual {row : Ty} (checked : CheckedOracle snapshot domains math)
      (answerType : checked.declaration.kind.answer = row)
      (captures : Values model.Value checked.declaration.inputs.dropLast) :
      OraclePayload model snapshot domains math row

structure OracleStoredTable (model : DomainModel) (snapshot : Snapshot)
    (domains : List DomainSpec) (math : OracleMathEnvironment) (row : Ty) where
  anchor : OracleAnchor
  rows : Nat
  holder : Nat
  receivers : List Nat
  payload : OraclePayload model snapshot domains math row

abbrev OracleEntries (model : DomainModel) (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) :=
  List ((row : Ty) × OracleStoredTable model snapshot domains math row)

/-- This audit is internal logical execution evidence, not a public/adversarial observation
contract. The caller chooses the public projection separately. -/
inductive OracleEvent (E : Type) where
  | query (request : OracleRead)
  | delivery (location : OracleLocation) (holder receiver : Nat) (anchor : OracleAnchor)
  | refusal (location : OracleLocation) (code : String)
  | provider (event : E)

structure OracleRuntimeState (model : DomainModel) (snapshot : Snapshot)
    (domains : List DomainSpec) (math : OracleMathEnvironment) (S : Type) where
  self : Nat
  entries : OracleEntries model snapshot domains math := []
  provider : S
  queries : Nat := 0

namespace OracleStore
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

def find (entries : OracleEntries model snapshot domains math) (row : Ty)
    (anchor : OracleAnchor) : Option (OracleStoredTable model snapshot domains math row) :=
  match entries with
  | [] => none
  | ⟨storedRow, table⟩ :: rest =>
    if equal : storedRow = row then
      if table.anchor = anchor then some (equal ▸ table) else find rest row anchor
    else find rest row anchor

def visible (self holder : Nat) (receivers : List Nat) : Bool :=
  self == holder || receivers.contains self

def validRows (kind : OracleKind) (rows : Nat) : Bool :=
  rows < indexLimit && match kind.rows with
    | none => true
    | some fixed => rows == fixed

def validBounds (kind : OracleKind) (bounds : List (String × Nat)) (rows : Nat) : Bool :=
  match kind.rows, bounds with
  | none, [("rows", maximum)] => maximum < indexLimit && rows ≤ maximum
  | some _, [] => true
  | _, _ => false

def hasAnchor (entries : OracleEntries model snapshot domains math) (anchor : OracleAnchor) : Bool :=
  entries.any (fun entry ↦ entry.2.anchor == anchor)

/-- Freshness is structural, not payload equality. Existing entries are immutable. -/
def insert (entries : OracleEntries model snapshot domains math) {row : Ty}
    (table : OracleStoredTable model snapshot domains math row) :
    Option (OracleEntries model snapshot domains math) :=
  if hasAnchor entries table.anchor then none else some (⟨row, table⟩ :: entries)

theorem insert_duplicate (entries : OracleEntries model snapshot domains math) {row : Ty}
    (table : OracleStoredTable model snapshot domains math row)
    (duplicate : hasAnchor entries table.anchor = true) : insert entries table = none := by
  simp [insert, duplicate]

/-- The immutable prefix at construction supplies the decreasing recursion. No execution
fuel, synthetic exhaustion, or eager footprint expansion is used. Child failures retain
the complete provider state and already reached events. -/
def answer (model : DomainModel)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (self : Nat) :
    OracleEntries model snapshot domains math → (request : OracleRead) →
      (S × Nat) → PIR.Execution (S × Nat) (OracleEvent E) (model.Value request.kind.answer)
  | [], request, state =>
      ⟨.stopped .refused, (state.1, state.2 + 1), [.query request]⟩
  | ⟨row, table⟩ :: older, request, state =>
    if equal : row = request.kind.answer then
      if table.anchor = request.anchor then
        let state := (state.1, state.2 + 1)
        if !visible self table.holder table.receivers ||
            !validRows request.kind table.rows || request.position ≥ table.rows then
          ⟨.stopped .refused, state, [.query request]⟩
        else match table.payload with
        | .base _ =>
          let result := base request state.1
          ⟨result.outcome, (result.state, state.2),
            .query request :: result.events.map OracleEvent.provider⟩
        | .virtual checked answerType captures =>
          -- Header admission below fixes this exact append equation.
          if inputShape : checked.declaration.inputs =
              checked.declaration.inputs.dropLast ++ [.index] then
            let args : Values model.Value checked.declaration.inputs :=
              inputShape.symm ▸ captures.append (.cons request.position .nil)
            let result := (checked.denote model args.present).run
              (fun (child : OracleRead) current ↦
                let expanded := request.expand child
                answer model base self older expanded current) state
            let outcome := match result.outcome with
              | .stopped reason => .stopped reason
              | .returned values => match values.get .here with
                | none => .stopped .incomplete
                | some value => .returned (equal ▸ answerType ▸ value)
            ⟨outcome, result.state, .query request :: result.events⟩
          else ⟨.stopped .refused, state, [.query request]⟩
      else answer model base self older request state
    else answer model base self older request state

def read (model : DomainModel)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (request : OracleRead)
    (state : OracleRuntimeState model snapshot domains math S) :
    PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E)
      (model.Value request.kind.answer) :=
  let result := answer model base state.self state.entries request (state.provider, state.queries)
  ⟨result.outcome, {state with provider := result.state.1, queries := result.state.2}, result.events⟩

def reference {kind : OracleKind} (table : OracleStoredTable model snapshot domains math kind.answer) :
    OracleReference kind :=
  ⟨table.anchor, by cases kind; exact .cons table.rows .nil⟩

def view {kind : OracleKind} (table : OracleStoredTable model snapshot domains math kind.answer) :
    OracleDataView (.singleton kind) :=
  ⟨table.holder, table.receivers, reference table⟩

def referenceRows {kind : OracleKind} (reference : OracleReference kind) : Nat :=
  by cases kind; exact reference.shape.get .here

def sameMembers (left right : List Nat) : Bool :=
  left.all right.contains && right.all left.contains

def sameReference {kind : OracleKind} (left right : OracleReference kind) : Bool :=
  left.anchor == right.anchor && referenceRows left == referenceRows right

def sameReferenceList {kind : OracleKind} :
    List (OracleReference kind) → List (OracleReference kind) → Bool
  | [], [] => true
  | left :: rest, right :: tail => sameReference left right && sameReferenceList rest tail
  | _, _ => false

def samePair {sort : OracleLogicalSort} (left right : OracleDataView sort) : Bool :=
  left.holder == right.holder && sameMembers left.receivers right.receivers &&
    match sort, left, right with
    | .singleton _, left, right => sameReference left.references right.references
    | .sequence _ _, left, right => sameReferenceList left.references right.references

def baseData (state : OracleRuntimeState model snapshot domains math S)
    (kind : OracleKind) (holder : Nat) (receivers : List Nat) (ref : OracleReference kind) :
    Except String (model.Value kind.data) := do
  let some table := find state.entries kind.answer ref.anchor | throw "oracle-data-anchor"
  if table.holder != holder || holder != state.self || !sameMembers table.receivers receivers ||
      table.rows != referenceRows ref || !validRows kind table.rows then
    throw "oracle-data-pair"
  match table.payload with
  | .base (some rows) =>
    if rows.length != table.rows then throw "oracle-data-shape"
    else return oracleRowsData model.toCarriers kind rows
  | .base none => throw "oracle-data-unavailable"
  | .virtual .. => throw "oracle-virtual-concrete-demand"

/-- Demand is allowed only for stored base data at its holder. In particular shape reads and
forwarding do not enter this function. Virtual demand has an explicit located refusal. -/
def demandBase (request : OracleDataDemand)
    (location : OracleLocation) (state : OracleRuntimeState model snapshot domains math S) :
    PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E)
      (model.Value request.sort.dataType) :=
  let failure := fun {A : Type} code ↦
    (⟨.stopped .refused, state, [.refusal location code]⟩ : PIR.Execution _ _ A)
  if request.requester != state.self || request.view.holder != state.self then
    failure "oracle-data-holder"
  else match request.sort, request.view with
  | .singleton kind, supplied =>
    match baseData state kind supplied.holder supplied.receivers supplied.references with
    | .ok data => ⟨.returned data, state, []⟩
    | .error code => failure code
  | .sequence kind maximum, supplied =>
    if supplied.references.length > maximum || maximum ≥ indexLimit then
      failure "oracle-data-capacity"
    else match supplied.references.mapM (baseData state kind supplied.holder supplied.receivers) with
    | .ok data => ⟨.returned data, state, []⟩
    | .error code => failure code

end OracleStore
end Zkc.Source.Structured

-- Realize shared equations here so every client imports the same stored proof.
-- Independent lazy generation can attach different private helpers to one public name.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getUnfoldEqnFor? ``Zkc.Source.Structured.OracleStore.answer
