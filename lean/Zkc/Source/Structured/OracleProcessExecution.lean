module

public import Zkc.Source.Structured.OracleProcessStore

@[expose] public section

/-! Query expansion and handler-independent reuse of all remaining Oracle descriptors. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

/-- Only role-owned query descriptors can reach the base provider. -/
def externalQuery : OracleOp → Bool
  | .query _ (some _) => true
  | _ => false

/-- A computational default used exclusively behind the proved independence boundary. -/
def refusingBase : PIR.Handler (oracleReadInterface model.toCarriers) S E :=
  fun _ state ↦ ⟨.stopped .refused, state, []⟩

/-- Every non-query branch is definitionally independent of an arbitrary base handler. -/
theorem operation_independent (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (left right : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S)
    (effectFree : externalQuery op = false) :
    OracleExecution.operation model oracles left location self roles op arguments state =
      OracleExecution.operation model oracles right location self roles op arguments state := by
  cases op <;> try rfl
  case query kind owner =>
    cases owner with
    | none => rfl
    | some owner => cases effectFree
  case send kind holder receivers bounds =>
    cases kind
    rfl
  case forgetShape source target =>
    cases source
    cases target
    rfl

/-- The sole effectful Oracle descriptor, with its typed operands exposed. -/
def query (model : DomainModel) (location : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (kind : OracleKind) (owner : Nat)
    (handle : Component (ProtocolValue model.toCarriers) (.oracle kind))
    (position : Component (ProtocolValue model.toCarriers) kind.query)
    (state : OracleRuntimeState model snapshot domains math S) :
    PIR.Process (Interface model S E)
      (PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E)
        (Values (Component (ProtocolValue model.toCarriers)) [kind.answer])) :=
  if self != state.self then .done (OracleExecution.refusal state location "oracle-request-role")
  else if roles owner != state.self then
    .done (OracleExecution.returned state (Values.absent _ [kind.answer]))
  else match handle.bind ProtocolValue.toConcrete, position.bind ProtocolValue.toConcrete with
  | some anchor, some position =>
    mapResult (fun result ↦
      let outcome := match result.outcome with
        | .stopped reason => .stopped reason
        | .returned value => .returned (.cons (some (ProtocolValue.ofConcrete _ value)) .nil)
      ⟨outcome, result.state, result.events⟩)
      (read model ⟨kind, anchor, position, location, []⟩ state)
  | _, _ => .done ⟨.stopped .incomplete, state, []⟩

/-- Expand the query arm; every other descriptor uses its unchanged, independent meaning. -/
def operation (model : DomainModel) (oracles : List (CheckedOracle snapshot domains math))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    PIR.Process (Interface model S E)
      (PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E)
        (Values (Component (ProtocolValue model.toCarriers)) op.results)) :=
  match op with
  | .query kind (some owner) =>
    query model location self roles kind owner (arguments.get .here)
      (arguments.get (.there .here)) state
  | op =>
    .done (OracleExecution.operation model oracles refusingBase
      location self roles op arguments state)

theorem query_presentation (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (kind : OracleKind) (owner : Nat)
    (handle : Component (ProtocolValue model.toCarriers) (.oracle kind))
    (position : Component (ProtocolValue model.toCarriers) kind.query)
    (state : OracleRuntimeState model snapshot domains math S) :
    operation (E := E) model oracles location self roles (.query kind (some owner))
      (.cons handle (.cons position .nil)) state =
        query model location self roles kind owner handle position state := rfl

/-- An equation for the existing query branch, with explicit typed operands. -/
theorem query_meaning (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (kind : OracleKind) (owner : Nat)
    (handle : Component (ProtocolValue model.toCarriers) (.oracle kind))
    (position : Component (ProtocolValue model.toCarriers) kind.query)
    (state : OracleRuntimeState model snapshot domains math S) :
    OracleExecution.operation model oracles base location self roles (.query kind (some owner))
      (.cons handle (.cons position .nil)) state =
    if self != state.self then OracleExecution.refusal state location "oracle-request-role"
    else if roles owner != state.self then
      OracleExecution.returned state (Values.absent _ [kind.answer])
    else match handle.bind ProtocolValue.toConcrete, position.bind ProtocolValue.toConcrete with
    | some anchor, some position =>
      let result := OracleStore.read model base ⟨kind, anchor, position, location, []⟩ state
      ⟨(match result.outcome with
        | .stopped reason => .stopped reason
        | .returned value => .returned (.cons (some (ProtocolValue.ofConcrete _ value)) .nil)),
        result.state, result.events⟩
    | _, _ => ⟨.stopped .incomplete, state, []⟩ := by
  rfl

set_option smartUnfolding false in
theorem operation_represents (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    Represents (handler (externalHandler ordinary base))
      (operation model oracles location self roles op arguments state)
      (OracleExecution.operation model oracles base location self roles op arguments state) := by
  cases op <;> try rfl
  case query kind owner =>
    cases owner with
    | none => rfl
    | some owner =>
      cases arguments
      rename_i handle rest
      cases rest
      rename_i position rest
      cases rest
      rw [query_meaning, query_presentation]
      unfold query
      split
      · rfl
      · split
        · rfl
        · split
          · exact represents_map _ _ _ _ (read_represents model ordinary base _ state)
          · rfl

end Zkc.Source.Structured.OracleProcess
