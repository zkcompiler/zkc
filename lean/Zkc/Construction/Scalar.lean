module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Construction.FiatShamir
public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.Structured.Participant

@[expose] public section

/-! The scalar byte ABI and primitive operation adapter.

This leaf owns the scalar/vector representation used by executable codecs and
native frames. It delegates arithmetic to the authoritative structured domain
evaluator. It contains no interpreter of constructed instructions. Aggregate
eligibility and nominal data interpretation remain owned by Domain.
-/
set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source
open Zkc.Source.Common.Native (ScalarValue)
variable {F G : Type}

/-- Runtime values of exported programs: scalar data, indices, vectors,
transcript histories and occurrence coordinates. -/
inductive Value (F G : Type) where
  | data (payload : Payload F G)
  | index (value : Nat)
  | vector (domain : String) (values : List F)
  | transcript (history : History F G)
  | indices (coordinates : List Nat)
  /-- Outside the selected construction value profile; decoding always refuses. -/
  | unsupported

deriving instance DecidableEq for Value

/-- Types whose values this construction profile carries. Aggregate transcript
encoding requires its own construction rule; admitting a source type is not one. -/
def dataType : Structured.Ty → Bool
  | .boolean | .index | .field _ | .group _ | .vector _ => true
  | _ => false

namespace Value

/-- A structured value as an exported value. Services are never carried. -/
def encode : (ty : Structured.Ty) → Structured.assignment F G ty → Value F G
  | .boolean, value => .data (.boolean value)
  | .field domain, value => .data (.field domain value)
  | .group domain, value => .data (.group domain value)
  | .index, value => .index value
  | .vector domain, values => .vector domain values
  | .service _, handle => .index handle
  | .indices, _ | .groups _, _ | .oracle _, _ | .oracleSequence .., _
  | .sequence _, _ | .product .., _ => .unsupported

/-- Read an exported value at a structured type; services never decode. -/
def decode : (ty : Structured.Ty) → Value F G → Option (Structured.assignment F G ty)
  | .boolean, .data (.boolean value) => some value
  | .field domain, .data (.field other value) => if domain = other then some value else none
  | .group domain, .data (.group other value) => if domain = other then some value else none
  | .index, .index value => some value
  | .vector domain, .vector other values => if domain = other then some values else none
  | _, _ => none

theorem decode_encode {ty : Structured.Ty} (data : dataType ty = true)
    (value : Structured.assignment F G ty) : decode ty (encode ty value) = some value := by
  cases ty <;> simp_all [encode, decode, dataType]

end Value

/-- Decode ordered values at declared types. -/
def decodeValues : (tys : List Structured.Ty) → List (Value F G) →
    Option (Values (Structured.assignment F G) tys)
  | [], [] => some .nil
  | ty :: tys, value :: values => do
      let head ← Value.decode ty value
      let tail ← decodeValues tys values
      pure (.cons head tail)
  | _, _ => none

def encodeValues : {tys : List Structured.Ty} → Values (Structured.assignment F G) tys →
    List (Value F G)
  | [], .nil => []
  | ty :: _, .cons value rest => Value.encode ty value :: encodeValues rest

/-- A finished outcome as a process. -/
def ofOutcome {I : PIR.Signature} {A : Type} : PIR.Outcome A → PIR.Process I A
  | .returned value => .done value
  | .stopped reason => .halt reason

/-- The outcome of a process that cannot call. -/
def closedOutcome {A : Type} : PIR.Process Structured.closedInterface A → PIR.Outcome A
  | .done value => .returned value
  | .halt reason => .stopped reason
  | .call operation _ => (show Empty from operation).elim

namespace Calculation
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The selected calculation is an adapter to the authoritative nominal
operation evaluator at the uniform model. It has no separate arithmetic cases. -/
def evaluate (calculation : Calculation)
    (arguments : Values (Structured.assignment F G) calculation.op.arguments) :
    PIR.Outcome (Values (Structured.assignment F G) calculation.op.results) :=
  closedOutcome (Structured.Evaluation.operationOn (Structured.ringModel F G)
    Structured.SiteObservations.closed [] calculation.op arguments
    (by cases calculation <;> exact .nil))

/-- Operational equations for retained executable clients, proved by the
shared evaluator rather than a separate calculation interpreter. -/
theorem evaluate_indexEqual (a b : Nat) :
    (Calculation.indexEqual).evaluate (F := F) (G := G) (.cons a (.cons b .nil)) =
      .returned (.cons (decide (a = b)) .nil) := rfl

theorem evaluate_fieldEqual (domain : String) (a b : F) :
    (Calculation.fieldEqual domain).evaluate (G := G) (.cons a (.cons b .nil)) =
      .returned (.cons (decide (a = b)) .nil) := rfl

theorem evaluate_fieldConstant (domain : String) (value : Nat) :
    (Calculation.fieldConstant domain value).evaluate (F := F) (G := G) .nil =
      .returned (.cons (value : F) .nil) := rfl

theorem evaluate_boundedAt (domain : String) (values : List F) (index : Nat) :
    (Calculation.boundedAt domain).evaluate (G := G) (.cons values (.cons index .nil)) =
      match values[index]? with
      | some value => .returned (.cons value .nil)
      | none => .stopped .refused := by
  simp only [evaluate, Calculation.op, Structured.Evaluation.operationOn_boundedAt]
  cases values[index]? <;> rfl

/-- The structured evaluator agrees with the carrier meaning, under every
effect interface, site observation and helper table. -/
theorem operation_eq {I : PIR.Signature} (observations : Structured.SiteObservations I)
    (table : Structured.Evaluation.Meanings F G I) (calculation : Calculation)
    (arguments : Values (Structured.assignment F G) calculation.op.arguments)
    (bodies : Values (RegionFunction (Structured.assignment F G) I) calculation.op.regions) :
    Structured.Evaluation.operation observations table calculation.op arguments bodies =
      ofOutcome (calculation.evaluate arguments) := by
  cases calculation <;> cases bodies
  case boundedAt domain =>
    rcases arguments with _ | ⟨container, _ | ⟨index, _ | _⟩⟩
    simp only [Calculation.op, Structured.Evaluation.operation_boundedAt,
      evaluate, Structured.Evaluation.operationOn_boundedAt]
    cases container[index]? <;> rfl
  all_goals
    rcases arguments with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
    rfl

end Calculation

/-- Invoke a checked helper by name in a closed helper table. The arguments are
decoded at the found helper's input types and its results encoded. -/
def callHelper (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
    (name : String) (arguments : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  match table.find? (fun entry => entry.helper.name == name) with
  | none => .stopped .refused
  | some entry =>
      match decodeValues entry.helper.inputs arguments with
      | none => .stopped .refused
      | some values =>
          match closedOutcome (entry.invoke values) with
          | .returned results => .returned (encodeValues results)
          | .stopped reason => .stopped reason

/-- A calculation on exported values. -/
def calculate [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (calculation : Calculation) (arguments : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  match decodeValues calculation.op.arguments arguments with
  | none => .stopped .refused
  | some values =>
      match calculation.evaluate values with
      | .returned results => .returned (encodeValues results)
      | .stopped reason => .stopped reason

def dataAt (env : List (Value F G)) (index : Nat) : Option (Payload F G) :=
  match env[index]? with
  | some (.data payload) => some payload
  | _ => none

def transcriptAt (env : List (Value F G)) (index : Nat) : Option (History F G) :=
  match env[index]? with
  | some (.transcript history) => some history
  | _ => none

def indicesAt (env : List (Value F G)) (index : Nat) : List Nat :=
  match env[index]? with
  | some (.indices coordinates) => coordinates
  | _ => []

def indexAt (env : List (Value F G)) (index : Nat) : Option Nat :=
  match env[index]? with
  | some (.index value) => some value
  | _ => none

/-- Read references from an environment. -/
def read (env : List (Value F G)) (references : List Nat) : Option (List (Value F G)) :=
  references.mapM (env[·]?)



/-- A scalar structured type as a common transcript type. -/
def scalarType : Structured.Ty → Option Zkc.Source.Common.Native.Ty
  | .boolean => some .boolean
  | .field domain => some (.field domain)
  | .group domain => some (.group domain)
  | _ => none

/-- Send a payload to `receiver` at `site`. -/
def sendPayload {A : Type} (site : String) (receiver : Nat) (payload : Payload F G)
    (next : PIR.Process (Actions F G) A) : PIR.Process (Actions F G) A :=
  match payload with
  | .boolean value => .call (.send (ty := .boolean) site receiver value) fun _ => next
  | .field domain value => .call (.send (ty := .field domain) site receiver value) fun _ => next
  | .group domain value => .call (.send (ty := .group domain) site receiver value) fun _ => next

/-- Returned references, read from the final environment. -/
def finish (returned : List Nat) (env : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  match read env returned with
  | some values => .returned values
  | none => .stopped .refused

end Zkc.Construction

run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.decodeValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.scalarType
  discard <| Lean.Meta.getUnfoldEqnFor? ``Zkc.Construction.encodeValues
