module

public import Zkc.Source.Structured.OracleProcessTotal

@[expose] public section

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
namespace Tests.OracleProcessData

abbrev model : DomainModel := ringModel Int Int
abbrev kind : OracleKind := .table .index (some 2)

def predicate : Function :=
  ⟨"admissible", .math, .privateDef, [.indices], [.boolean], none, [], none,
    .block [.instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0])⟩

/-- Both child queries use the original capture and index; the first result is unused. -/
def declaration : OracleDeclaration :=
  ⟨"Repeated", [.oracle kind, .index], kind, "admissible_rows", [], [],
    .block [
      .instruction (.oracle (.query none kind)) [0, 1] [.index] [] "first",
      .instruction (.oracle (.query none kind)) [1, 2] [.index] [] "second"] (.ret [0])⟩

def snapshot : Snapshot :=
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000", "main", [],
    [⟨"admissible_rows", .privateDef, "zkc.language.formula/0", "rows", "0",
      [.indices], [.boolean], ["oracle-admissibility"], some "admissible", []⟩], [],
    [.function predicate, .oracle declaration], [], blsRows, {}⟩

def predicateRaw : RawRegion Ty Op :=
  .letOp (.booleanConstant true) [] [.boolean] .nil (.ret [0])

def predicateChecked : CheckedDefinition :=
  ⟨"admissible", .math, [.indices], [.boolean], predicateRaw,
    .letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil)), rfl⟩

def math : OracleMathEnvironment where
  definitions := [predicateChecked]
  linked := by simp [DeclarationsLinked, CheckedDefinition.helpers, predicateChecked,
    predicateRaw, RawRegion.operations, RawRegions.operations, Op.helpers]
  pureBodies := by
    intro definition member
    have same : definition = predicateChecked := by simpa using member
    subst definition
    exact ⟨rfl, rfl⟩

theorem associated : math.Associated snapshot [] := by
  constructor
  · intro definition member
    have same : definition = predicateChecked := by simpa [math] using member
    subst definition
    exact ⟨predicate, by simp [snapshot], rfl, rfl, rfl⟩
  · intro function member _
    have same : function = predicate := by simpa [snapshot] using member
    subst function
    exact ⟨predicateChecked, by simp [math], rfl⟩

/-- The fixture is produced by the actual checked Oracle admission function. -/
def checked : CheckedOracle snapshot [] math :=
  (checkOracle snapshot [] math associated 1).toOption.get (by decide +kernel)

def location (index : Nat) : OracleLocation :=
  ⟨⟨3, [.application 5 [7, 1, 0], .iteration 5 [7, 1, 2] 4]⟩, 1, [7, 1, index]⟩

def anchor (index : Nat) : OracleAnchor := (location index).anchor

def baseTable : OracleStoredTable model snapshot [] math .index :=
  ⟨anchor 0, 2, 0, [1], .base (some [10, 20])⟩

def virtualTable (index captured : Nat) : OracleStoredTable model snapshot [] math .index :=
  ⟨anchor index, 2, 0, [1], .virtual checked rfl (.cons (anchor captured) .nil)⟩

deriving instance DecidableEq, Repr for OracleRead
deriving instance DecidableEq for OracleEvent
deriving instance DecidableEq for OracleProtocol.Event

inductive ProviderEvent where
  | ordinary (site : String)
  | base (request : OracleRead) (hit : Bool)
  deriving DecidableEq, Repr

structure Provider where
  cache : List (OracleAnchor × Nat) := []
  calls : Nat := 0
  hits : Nat := 0
  ordinaryCalls : Nat := 0
  order : List Bool := []
  deriving DecidableEq, Repr

def baseOutcome (failure : Option (Nat × PIR.Stop)) (request : OracleRead) (next : Provider) :
    (kind : OracleKind) → PIR.Outcome (model.Value kind.answer)
  | .table .index _ => match failure with
    | some (call, reason) => if call == next.calls then .stopped reason
      else .returned (10 + request.position)
    | none => .returned (10 + request.position)
  | _ => .stopped .refused

def base (failure : Option (Nat × PIR.Stop) := none) :
    PIR.Handler (oracleReadInterface model.toCarriers) Provider ProviderEvent :=
  fun request state ↦
    let key := (request.anchor, request.position)
    let hit := state.cache.contains key
    let next : Provider := {state with
      cache := if hit then state.cache else state.cache ++ [key]
      calls := state.calls + 1
      hits := state.hits + if hit then 1 else 0
      order := state.order ++ [false]}
    ⟨baseOutcome failure request next request.kind, next, [.base request hit]⟩

def ordinary (failure : Bool := false) :
    PIR.Handler (participantInterfaceOn model.toCarriers) Provider ProviderEvent :=
  fun action state ↦
    let next := {state with
      ordinaryCalls := state.ordinaryCalls + 1, order := state.order ++ [true]}
    match action with
    | .query site (.sampleIndex _) _ =>
      ⟨if failure then .stopped .reject else .returned state.calls, next, [.ordinary site]⟩
    | _ => ⟨.stopped .refused, next, []⟩

def runtime : OracleRuntimeState model snapshot [] math Provider :=
  ⟨0, [⟨.index, virtualTable 2 1⟩, ⟨.index, virtualTable 1 0⟩, ⟨.index, baseTable⟩], {}, 0⟩

def state : OracleProtocol.State model snapshot [] math Provider :=
  ⟨runtime, {invocation := (location 9).invocation, definition := 1, row := (location 9).row}, []⟩

def request (owner : Nat := 0) : OracleRequest model.toCarriers :=
  ⟨.query kind (some owner), location 9, 0, id,
    .cons (some (ProtocolValue.ofConcrete (.oracle kind) (anchor 2)))
      (.cons (some (ProtocolValue.ofConcrete .index 0)) .nil)⟩

def ordinaryRequest : (participantInterfaceOn model.toCarriers).Op :=
  .query "ordinary" (.sampleIndex "finite-control") (.cons 0 (.cons 2 .nil))

/-- Mixed ordinary and base effects, repeated queries and a real source halt. -/
def process (stopAfter : Bool := false) : PIR.Process (OracleProtocol.Interface model) Nat :=
  .call (.ordinary ordinaryRequest) fun _ ↦
    .call (.oracle (request 0)) fun _ ↦
      .call (.ordinary ordinaryRequest) fun _ ↦
        .call (.oracle (request 0)) fun _ ↦
          if stopAfter then .halt .reject else .done 17

/-- An ordinary sampled reply selects the actual source Oracle position before expansion. -/
def adaptiveProcess : PIR.Process (OracleProtocol.Interface model) (Option Nat) :=
  .call (.ordinary ordinaryRequest) fun position ↦
    let sampled : OracleRequest model.toCarriers :=
      ⟨.query kind (some 0), location 9, 0, id,
        .cons (some (ProtocolValue.ofConcrete (.oracle kind) (anchor 2)))
          (.cons (some (ProtocolValue.ofConcrete .index position)) .nil)⟩
    .call (.oracle sampled) fun values ↦
      .done ((values.get .here).bind ProtocolValue.toConcrete)

def ordinaryChoice (choice : Nat) :
    PIR.Handler (participantInterfaceOn model.toCarriers) Provider ProviderEvent :=
  fun action state ↦
    match action with
    | .query site (.sampleIndex _) _ =>
      ⟨.returned choice, {state with
        ordinaryCalls := state.ordinaryCalls + 1
        order := state.order ++ [true]}, [.ordinary site]⟩
    | action => ordinary false action state

end Tests.OracleProcessData
