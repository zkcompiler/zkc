module

public import Zkc.Source.Structured.Import
public import Zkc.Source.Finite
public import Mathlib.Algebra.Ring.Defs

@[expose] public section

/-! Owned logical meanings. The nominal BLS scalar domain is explicitly assigned
to `F`; arithmetic theorems may choose any commutative ring. The CLI chooses
`ZMod scalarModulus`. No native frames or resource counters are modeled here. -/

namespace Zkc.Source.Structured

def closedInterface : PIR.Signature := ⟨Empty, fun value => nomatch value⟩
abbrev Closed (A : Type) := PIR.Proc closedInterface A

/-- Explicit interpretation of the admitted nominal domain in a chosen ring.
Indices are naturals with the unsigned invariant below, not wrapping integers. -/
abbrev scalarAssignment (F : Type) : Ty → Type
  | .boolean => Bool
  | .index => Nat
  | .field _ => F
  | .vector _ => List F

def ValueValid {F : Type} : (type : Ty) → scalarAssignment F type → Prop
  | .boolean, _ | .field _, _ => True
  | .index, value => value < indexLimit
  | .vector _, values => values.length < indexLimit

def InputsValid {F : Type} {types : List Ty} (values : Values (scalarAssignment F) types) : Prop :=
  ∀ {type} (position : Var types type), ValueValid type (values.get position)

abbrev FunctionMeaning (F : Type) (helper : Helper) :=
  Values (scalarAssignment F) helper.inputs → Closed (Values (scalarAssignment F) helper.outputs)

structure DenotedDefinition (F : Type) where
  helper : Helper
  invoke : FunctionMeaning F helper

abbrev Meanings (F : Type) := List (DenotedDefinition F)

/-- Named invocation checks the complete signature; the checked table constructs
all implementations. A missing binding has an explicit defensive refusal.
Its unreachability for every admitted table is a separate, unproved obligation. -/
def invoke {F : Type} (table : Meanings F) (helper : Helper) : FunctionMeaning F helper :=
  match table.find? (fun entry => entry.helper.name == helper.name) with
  | none => fun _ => .halt .refused
  | some entry =>
    if h : entry.helper = helper then h ▸ entry.invoke
    else fun _ => .halt .refused

def DomainSpec.denote {F : Type} : (domain : DomainSpec) →
    Values (scalarAssignment F) domain.inputs → Finite.Domain (scalarAssignment F domain.item)
  | ⟨_, _, _, container, true⟩, arguments =>
      .check ((arguments.get container).length < indexLimit) .refused
        (.elements (List.range (arguments.get container).length))
  | ⟨_, _, _, container, false⟩, arguments =>
      .check ((arguments.get container).length < indexLimit) .refused
        (.elements (arguments.get container))


/-- Predicate is invoked before step, on I/A/C. False preserves the entire
current state. The step receives S/I/A/C, including zero-length S and C. -/
def foldTransition {F : Type} (table : Meanings F) (spec : FoldSpec)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (captures : Values (scalarAssignment F) spec.captures)
    (state : Values (scalarAssignment F) spec.state)
    (item : scalarAssignment F spec.domain.item) : Closed (Values (scalarAssignment F) spec.state) :=
  let callbackArguments := Values.cons item (arguments.append captures)
  let enabled : Closed (Values (scalarAssignment F) [.boolean]) :=
    if spec.predicate.isEmpty then .done (.cons true .nil)
    else invoke table spec.predicateHelper callbackArguments
  enabled.bind fun result =>
    if result.get .here then invoke table spec.stepHelper (state.append callbackArguments)
    else .done state

def denoteFold {F : Type} (table : Meanings F) (spec : FoldSpec)
    (values : Values (scalarAssignment F) spec.arguments) :
    Closed (Values (scalarAssignment F) spec.state) :=
  let (arguments, rest) := values.split spec.domain.inputs
  let (initial, captures) := rest.split spec.state
  Finite.execute (spec.domain.denote arguments) (foldTransition table spec arguments captures) initial

/-- Closed callback invocation adapter; the operation observes only returned
values and stopping, and never inspects callback process constructors. -/
def invokeCallback {F : Type} {inputs outputs : List Ty}
    (callback : RegionFunction (scalarAssignment F) closedInterface (inputs, outputs))
    (arguments : Values (scalarAssignment F) inputs) :
    Closed (Values (scalarAssignment F) outputs) := callback arguments

def denoteLoop {F : Type} (state captures : List Ty)
    (body : RegionFunction (scalarAssignment F) closedInterface
      (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (initial : Values (scalarAssignment F) state)
    (captured : Values (scalarAssignment F) captures) : Closed (Values (scalarAssignment F) state) :=
  Finite.execute (.elements (List.range' lower (upper - lower)))
    (fun current index =>
      (invokeCallback body (.cons index (current.append captured))).bind fun results =>
        .done (results.split state).1) initial

def denoteConditionalLoop {F : Type} (state captures : List Ty)
    (body : RegionFunction (scalarAssignment F) closedInterface
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (initial : Values (scalarAssignment F) state)
    (captured : Values (scalarAssignment F) captures) : Closed (Values (scalarAssignment F) state) :=
  (Finite.execute (.elements (List.range' lower (upper - lower)))
    (fun (current : Bool × Values (scalarAssignment F) state) index =>
      if current.1 then
        (invokeCallback body (.cons index (current.2.append captured))).bind fun results =>
          match results with
          | .cons continuing rest => .done (continuing, (rest.split state).1)
      else .done current) (true, initial)).bind fun result => .done result.2

def operation {F : Type} [CommRing F] [DecidableEq F] (table : Meanings F) :
    (op : Op) → Values (scalarAssignment F) op.arguments →
    Values (RegionFunction (scalarAssignment F) closedInterface) op.regions →
    Closed (Values (scalarAssignment F) op.results)
  | .fieldConstant _ value, .nil, .nil => .done (.cons (value : F) .nil)
  | .fieldAdd _, .cons a (.cons b .nil), .nil => .done (.cons (a + b) .nil)
  | .fieldSubtract _, .cons a (.cons b .nil), .nil => .done (.cons (a - b) .nil)
  | .fieldMultiply _, .cons a (.cons b .nil), .nil => .done (.cons (a * b) .nil)
  | .fieldEqual _, .cons a (.cons b .nil), .nil => .done (.cons (decide (a = b)) .nil)
  | .booleanConstant value, .nil, .nil => .done (.cons value .nil)
  | .booleanAnd, .cons a (.cons b .nil), .nil => .done (.cons (a && b) .nil)
  | .booleanOr, .cons a (.cons b .nil), .nil => .done (.cons (a || b) .nil)
  | .booleanXor, .cons a (.cons b .nil), .nil => .done (.cons (xor a b) .nil)
  | .booleanEqual, .cons a (.cons b .nil), .nil => .done (.cons (a == b) .nil)
  | .booleanNotEqual, .cons a (.cons b .nil), .nil => .done (.cons (a != b) .nil)
  | .select _, .cons condition (.cons yes (.cons no .nil)), .nil =>
      .done (.cons (if condition then yes else no) .nil)
  | .boundedAt _, .cons container (.cons index .nil), .nil =>
      match container[index]? with
      | some value => .done (.cons value .nil)
      | none => .halt .refused
  | .invoke helper, args, .nil => invoke table helper args
  | .fold spec, args, .nil => denoteFold table spec args
  | .branch _ _, .cons condition captures, .cons yes (.cons no .nil) =>
      invokeCallback (if condition then yes else no) captures
  | .loop state captures, .cons lower (.cons upper rest), .cons body .nil =>
      let (initial, captured) := rest.split state
      denoteLoop state captures body lower upper initial captured
  | .loopCondition state captures, .cons lower (.cons upper rest), .cons body .nil =>
      let (initial, captured) := rest.split state
      denoteConditionalLoop state captures body lower upper initial captured
  | .guard, .cons condition .nil, .nil => if condition then .done .nil else .halt .reject

def meaning (F : Type) [CommRing F] [DecidableEq F] (table : Meanings F) :
    RegionMeaning dialect closedInterface := ⟨scalarAssignment F, operation table⟩

def CheckedDefinition.helper (definition : CheckedDefinition) : Helper :=
  ⟨definition.name, definition.inputs, definition.outputs⟩

/-- Each body closes over the previously interpreted prefix, so recursion is
impossible and helper syntax is never inlined into callers. -/
def extendMeanings {F : Type} [CommRing F] [DecidableEq F]
    (table : Meanings F) (definition : CheckedDefinition) : Meanings F :=
  ⟨definition.helper, fun values => definition.body.denote (meaning F table) values.get⟩ :: table

def Payload.meanings (payload : Payload) (F : Type) [CommRing F] [DecidableEq F] : Meanings F :=
  payload.definitions.foldl extendMeanings []

def Payload.denote (payload : Payload) (F : Type) [CommRing F] [DecidableEq F]
    (inputs : Values (scalarAssignment F) payload.entry.inputs) :
    Closed (Values (scalarAssignment F) payload.entry.outputs) :=
  invoke (payload.meanings F) payload.entry.helper inputs

def Program.denote (program : Program) (F : Type) [CommRing F] [DecidableEq F]
    (inputs : Values (scalarAssignment F) program.payload.entry.inputs) :
    Closed (Values (scalarAssignment F) program.payload.entry.outputs) :=
  program.payload.denote F inputs

def closedOutcome {A : Type} : Closed A → PIR.Outcome A
  | .done value => .returned value
  | .halt reason => .stopped reason
  | .call impossible _ => nomatch impossible

end Zkc.Source.Structured
