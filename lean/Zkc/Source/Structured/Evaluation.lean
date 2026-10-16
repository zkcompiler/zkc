module

public import Zkc.Source.Structured.Algebra
public import Zkc.Source.Finite

@[expose] public section

/-! One arithmetic and control evaluator for explicit scalar/group values and
an arbitrary effect interface. Nested callbacks use the same closed-value meaning. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def DomainSpec.denote {F G : Type} : (domain : DomainSpec) →
    Values (assignment F G) domain.inputs → Finite.Domain (assignment F G domain.item)
  | ⟨_, _, _, container, true⟩, arguments =>
      .check ((arguments.get container).length < indexLimit) .refused
        (.elements (List.range (arguments.get container).length))
  | ⟨_, _, _, container, false⟩, arguments =>
      .check ((arguments.get container).length < indexLimit) .refused
        (.elements (arguments.get container))

namespace Evaluation

abbrev Meanings (F G : Type) (interface : PIR.Signature) :=
  HelperTable (assignment F G) interface

/-- Predicate is invoked before step, on I/A/C. False preserves the entire
current state. The step receives S/I/A/C, including zero-length S and C. -/
def foldTransition {F G : Type} {interface : PIR.Signature}
    (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (captures : Values (assignment F G) spec.captures)
    (state : Values (assignment F G) spec.state)
    (item : assignment F G spec.domain.item) : PIR.Proc interface (Values (assignment F G) spec.state) :=
  let callbackArguments := Values.cons item (arguments.append captures)
  let enabled : PIR.Proc interface (Values (assignment F G) [.boolean]) :=
    if spec.predicate.isEmpty then .done (.cons true .nil)
    else invoke table spec.predicateHelper callbackArguments
  enabled.bind fun result =>
    if result.get .here then invoke table spec.stepHelper (state.append callbackArguments)
    else .done state

def denoteFold {F G : Type} {interface : PIR.Signature}
    (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (values : Values (assignment F G) spec.arguments) :
    PIR.Proc interface (Values (assignment F G) spec.state) :=
  let (arguments, rest) := values.split spec.domain.inputs
  let (initial, captures) := rest.split spec.state
  Finite.execute (spec.domain.denote arguments) (foldTransition table spec arguments captures) initial

/-- Closed callback invocation adapter; the operation observes only returned
values and stopping, and never inspects callback process constructors. -/
def invokeCallback {F G : Type} {interface : PIR.Signature} {inputs outputs : List Ty}
    (callback : RegionFunction (assignment F G) interface (inputs, outputs))
    (arguments : Values (assignment F G) inputs) :
    PIR.Proc interface (Values (assignment F G) outputs) := callback arguments

def denoteLoop {F G : Type} {interface : PIR.Signature} (state captures : List Ty)
    (body : RegionFunction (assignment F G) interface
      (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) : PIR.Proc interface (Values (assignment F G) state) :=
  Finite.execute (.elements (List.range' lower (upper - lower)))
    (fun current index =>
      (invokeCallback body (.cons index (current.append captured))).bind fun results =>
        .done (results.split state).1) initial

def denoteConditionalLoop {F G : Type} {interface : PIR.Signature} (state captures : List Ty)
    (body : RegionFunction (assignment F G) interface
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) : PIR.Proc interface (Values (assignment F G) state) :=
  (Finite.execute (.elements (List.range' lower (upper - lower)))
    (fun (current : Bool × Values (assignment F G) state) index =>
      if current.1 then
        (invokeCallback body (.cons index (current.2.append captured))).bind fun results =>
          match results with
          | .cons continuing rest => .done (continuing, (rest.split state).1)
      else .done current) (true, initial)).bind fun result => .done result.2

def operation {F G : Type} {interface : PIR.Signature}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (observations : SiteObservations interface) (table : Meanings F G interface) :
    (op : Op) → Values (assignment F G) op.arguments →
    Values (RegionFunction (assignment F G) interface) op.regions →
    PIR.Proc interface (Values (assignment F G) op.results)
  | .fieldConstant _ value, .nil, .nil => .done (.cons (value : F) .nil)
  | .fieldAdd _, .cons a (.cons b .nil), .nil => .done (.cons (a + b) .nil)
  | .fieldSubtract _, .cons a (.cons b .nil), .nil => .done (.cons (a - b) .nil)
  | .fieldMultiply _, .cons a (.cons b .nil), .nil => .done (.cons (a * b) .nil)
  | .fieldEqual _, .cons a (.cons b .nil), .nil => .done (.cons (decide (a = b)) .nil)
  | .groupIdentity _, .nil, .nil =>
      .done (.cons 0 .nil)
  | .groupAdd _, .cons a (.cons b .nil), .nil => .done (.cons (a + b) .nil)
  | .groupScale _ _, .cons point (.cons scalar .nil), .nil =>
      .done (.cons (scalar • point) .nil)
  | .groupEqual _, .cons a (.cons b .nil), .nil => .done (.cons (decide (a = b)) .nil)
  | .mark site, .nil, .nil => observations.mark site |>.bind fun _ => .done .nil
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

-- Generate the dependent equation lemmas in their defining module. Otherwise
-- separate public clients can export competing lazily generated declarations.
attribute [local simp] operation

/-- Keep the value assignment visible to dependent clients; operation evaluation
remains a named definition with its own laws. -/
abbrev meaning {F G : Type} {interface : PIR.Signature}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (observations : SiteObservations interface) (table : Meanings F G interface) :
    RegionMeaning dialect interface := ⟨assignment F G, operation observations table⟩

end Evaluation

end Zkc.Source.Structured
