module

public import Zkc.Source.Structured.Meaning
public import Zkc.Source.Structured.DomainModels

@[expose] public section

/-! The structured evaluator over domain models.

These definitions are the uniform evaluator (`Primitive.evaluate`,
`Evaluation.operation`, map, fold and loop evaluation, helper tables) with the
one field type and one group type replaced by the carriers and structures of a
domain model: each field operation uses the ring of its own field identity,
each group operation the group of its own group identity, and scaling the
model's action of the named field on the named group. Definitions that only
name values take carriers; those that compute take a model.

The uniform evaluator is the instance at `ringModel F G`, by the equations at
the end of this module. It is kept as its own definition, so that existing
proofs, which unfold it case by case, are unchanged. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- Primitive evaluation over a field model. Only the ring structure and
decidable equality of each field identity are used. -/
def Primitive.evaluateOn (model : FieldModel) :
    (primitive : Primitive) → Values model.Value primitive.arguments →
      PIR.Outcome (Values model.Value primitive.results)
  | .indexConstant n, .nil =>
      if n < indexLimit then .returned (.cons n .nil) else .stopped .refused
  | .indexEqual, .cons a (.cons b .nil) =>
      checkedIndices a b (.returned (.cons (decide (a = b)) .nil))
  | .indexLess, .cons a (.cons b .nil) =>
      checkedIndices a b (.returned (.cons (decide (a < b)) .nil))
  | .indexAdd, .cons a (.cons b .nil) =>
      checkedIndices a b (if a + b < indexLimit then .returned (.cons (a + b) .nil)
        else .stopped .refused)
  | .indexMul, .cons a (.cons b .nil) =>
      checkedIndices a b (if a * b < indexLimit then .returned (.cons (a * b) .nil)
        else .stopped .refused)
  | .indexSub, .cons a (.cons b .nil) =>
      checkedIndices a b (if b ≤ a then .returned (.cons (a - b) .nil) else .stopped .refused)
  | .indexDiv, .cons a (.cons b .nil) =>
      checkedIndices a b (if b = 0 then .stopped .refused else .returned (.cons (a / b) .nil))
  | .indexMod, .cons a (.cons b .nil) =>
      checkedIndices a b (if b = 0 then .stopped .refused else .returned (.cons (a % b) .nil))
  | .vectorEmpty _, .nil => .returned (.cons [] .nil)
  | .vectorLength _, .cons xs .nil =>
      if xs.length < indexLimit then .returned (.cons xs.length .nil) else .stopped .exhausted
  | .vectorSum _, .cons xs .nil => .returned (.cons (xs.foldl (· + ·) 0) .nil)
  | .vectorSplit _, .cons xs .nil =>
      if xs.length > 0 ∧ xs.length % 2 = 0 then
        .returned (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
      else .stopped .refused
  | .vectorAppend _, .cons xs (.cons x .nil) => .returned (.cons (xs ++ [x]) .nil)
  | .vectorEqual _, .cons xs (.cons ys .nil) => .returned (.cons (decide (xs = ys)) .nil)
  | .fieldEqual _, .cons x (.cons y .nil) => .returned (.cons (decide (x = y)) .nil)

attribute [local simp] Primitive.evaluateOn

def DomainSpec.denoteOn {carriers : Carriers} : (domain : DomainSpec) →
    Values carriers.Value domain.inputs → Finite.Domain (carriers.Value domain.item)
  | ⟨_, _, _, container, true⟩, arguments =>
      .check ((arguments.get container).length < indexLimit) .exhausted
        (.elements (List.range (arguments.get container).length))
  | ⟨_, _, _, container, false⟩, arguments =>
      .check ((arguments.get container).length < indexLimit) .exhausted
        (.elements (arguments.get container))

namespace Evaluation

/-- Every row contributes a length, including unused helper operands. -/
def mapLengthsOn {carriers : Carriers} (field : String) : (mask : List Bool) →
    Values carriers.Value (mask.map (fun row => if row then .vector field else .field field)) →
      List Nat
  | [], .nil => []
  | true :: rest, .cons row args => row.length :: mapLengthsOn field rest args
  | false :: rest, .cons _ args => mapLengthsOn field rest args

/-- Construct the full scalar tuple in original argument order, retaining broadcasts. -/
def mapRowArgumentsOn {carriers : Carriers} (field : String) : (mask : List Bool) →
    Values carriers.Value (mask.map (fun row => if row then .vector field else .field field)) →
    Nat → Option (Values carriers.Value (mask.map (fun _ => .field field)))
  | [], .nil, _ => some .nil
  | true :: rest, .cons row args, index => do
      let value ← (show List (carriers.Field field) from row)[index]?
      let values ← mapRowArgumentsOn field rest args index
      pure (.cons value values)
  | false :: rest, .cons value args, index => do
      let values ← mapRowArgumentsOn field rest args index
      pure (.cons value values)

/-- One reached row calls the exact computed Math signature in the shared table. -/
def mapRowOn {carriers : Carriers} {I : PIR.Signature}
    (table : HelperTable carriers.Value I) (spec : MapSpec)
    (args : Values carriers.Value spec.arguments) (index : Nat) :
    PIR.Proc I (carriers.Field spec.field) :=
  match mapRowArgumentsOn spec.field spec.rowwise args index with
  | none => .halt .refused
  | some values => (invoke table spec.helper values).bind fun result => .done (result.get .here)

def denoteMapOn {carriers : Carriers} {I : PIR.Signature}
    (table : HelperTable carriers.Value I) (spec : MapSpec)
    (args : Values carriers.Value spec.arguments) :
    PIR.Proc I (Values carriers.Value [.vector spec.field]) :=
  Finite.admitThen (mapShape (mapLengthsOn spec.field spec.rowwise args)) fun length =>
    (mapRows (mapRowOn table spec args) (List.range length)).bind fun values =>
      .done (.cons values .nil)

attribute [local simp] mapLengthsOn mapRowArgumentsOn

/-- Helper tables over carriers. -/
abbrev MeaningsOn (carriers : Carriers) (interface : PIR.Signature) :=
  HelperTable carriers.Value interface

/-- The predicate runs before the step, on the item, domain arguments and
captures. False preserves the entire current state. -/
def foldTransitionOn {carriers : Carriers} {interface : PIR.Signature}
    (table : HelperTable carriers.Value interface) (spec : FoldSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (state : Values carriers.Value spec.state)
    (item : carriers.Value spec.domain.item) :
    PIR.Proc interface (Values carriers.Value spec.state) :=
  let callbackArguments := Values.cons item (arguments.append captures)
  let enabled : PIR.Proc interface (Values carriers.Value [.boolean]) :=
    if spec.predicate.isEmpty then .done (.cons true .nil)
    else invoke table spec.predicateHelper callbackArguments
  enabled.bind fun result =>
    if result.get .here then invoke table spec.stepHelper (state.append callbackArguments)
    else .done state

def denoteFoldOn {carriers : Carriers} {interface : PIR.Signature}
    (table : HelperTable carriers.Value interface) (spec : FoldSpec)
    (values : Values carriers.Value spec.arguments) :
    PIR.Proc interface (Values carriers.Value spec.state) :=
  let (arguments, rest) := values.split spec.domain.inputs
  let (initial, captures) := rest.split spec.state
  Finite.execute (spec.domain.denoteOn arguments) (foldTransitionOn table spec arguments captures)
    initial

/-- Closed callback invocation adapter; the operation observes only returned
values and stopping, and never inspects callback process constructors. -/
def invokeCallbackOn {carriers : Carriers} {interface : PIR.Signature} {inputs outputs : List Ty}
    (callback : RegionFunction carriers.Value interface (inputs, outputs))
    (arguments : Values carriers.Value inputs) :
    PIR.Proc interface (Values carriers.Value outputs) := callback arguments

def denoteLoopOn {carriers : Carriers} {interface : PIR.Signature} (state captures : List Ty)
    (body : RegionFunction carriers.Value interface
      (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (initial : Values carriers.Value state)
    (captured : Values carriers.Value captures) :
    PIR.Proc interface (Values carriers.Value state) :=
  Finite.execute (.elements (List.range' lower (upper - lower)))
    (fun current index =>
      (invokeCallbackOn body (.cons index (current.append captured))).bind fun results =>
        .done (results.split state).1) initial

def denoteConditionalLoopOn {carriers : Carriers} {interface : PIR.Signature}
    (state captures : List Ty)
    (body : RegionFunction carriers.Value interface
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (initial : Values carriers.Value state)
    (captured : Values carriers.Value captures) :
    PIR.Proc interface (Values carriers.Value state) :=
  (Finite.execute (.elements (List.range' lower (upper - lower)))
    (fun (current : Bool × Values carriers.Value state) index =>
      if current.1 then
        (invokeCallbackOn body (.cons index (current.2.append captured))).bind fun results =>
          match results with
          | .cons continuing rest => .done (continuing, (rest.split state).1)
      else .done current) (true, initial)).bind fun result => .done result.2

/-- Operation meanings over a domain model. Field operations use the ring of
the operation's field identity, group operations the group of its group
identity, and scaling the model's action of the named field on the named
group. -/
def operationOn (model : DomainModel) {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : MeaningsOn model.toCarriers interface) :
    (op : Op) → Values model.Value op.arguments →
    Values (RegionFunction model.Value interface) op.regions →
    PIR.Proc interface (Values model.Value op.results)
  | .exec primitive, args, .nil => primitiveOutcome (primitive.evaluateOn model.toFieldModel args)
  | .indexConstant value, .nil, .nil => .done (.cons value .nil)
  | .indexEqual, .cons a (.cons b .nil), .nil => .done (.cons (decide (a = b)) .nil)
  | .fieldConstant domain value, .nil, .nil => .done (.cons (value : model.Field domain) .nil)
  | .fieldAdd _, .cons a (.cons b .nil), .nil => .done (.cons (a + b) .nil)
  | .fieldSubtract _, .cons a (.cons b .nil), .nil => .done (.cons (a - b) .nil)
  | .fieldMultiply _, .cons a (.cons b .nil), .nil => .done (.cons (a * b) .nil)
  | .fieldEqual _, .cons a (.cons b .nil), .nil => .done (.cons (decide (a = b)) .nil)
  | .groupIdentity _, .nil, .nil => .done (.cons 0 .nil)
  | .groupAdd _, .cons a (.cons b .nil), .nil => .done (.cons (a + b) .nil)
  | .groupScale group field, .cons point (.cons scalar .nil), .nil =>
      .done (.cons (model.smul group field scalar point) .nil)
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
  | .fold spec, args, .nil => denoteFoldOn table spec args
  | .map spec, args, .nil => denoteMapOn table spec args
  | .branch _ _, .cons condition captures, .cons yes (.cons no .nil) =>
      invokeCallbackOn (if condition then yes else no) captures
  | .loop state captures, .cons lower (.cons upper rest), .cons body .nil =>
      let (initial, captured) := rest.split state
      denoteLoopOn state captures body lower upper initial captured
  | .loopCondition state captures, .cons lower (.cons upper rest), .cons body .nil =>
      let (initial, captured) := rest.split state
      denoteConditionalLoopOn state captures body lower upper initial captured
  | .guard, .cons condition .nil, .nil => if condition then .done .nil else .halt .reject

-- Generate the dependent equation lemmas in their defining module. Otherwise
-- separate public clients can export competing lazily generated declarations.
attribute [local simp] operationOn

/-- Keep the values visible to dependent clients; operation evaluation remains a
named definition with its own laws. -/
abbrev meaningOn (model : DomainModel) {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : MeaningsOn model.toCarriers interface) :
    RegionMeaning dialect interface := ⟨model.Value, operationOn model observations table⟩

section Model
variable (model : DomainModel) {interface : PIR.Signature}

/-- Each body closes over the previously interpreted prefix, so recursion is
impossible and helper syntax is never inlined into callers. -/
def extendMeaningsOn (observations : SiteObservations interface)
    (table : MeaningsOn model.toCarriers interface) (definition : CheckedDefinition) :
    MeaningsOn model.toCarriers interface :=
  ⟨definition.helper, fun values =>
    definition.body.denote (meaningOn model observations table) values.get⟩ :: table

def payloadMeaningsOn (observations : SiteObservations interface) (payload : Payload) :
    MeaningsOn model.toCarriers interface :=
  payload.definitions.foldl (extendMeaningsOn model observations) []

def payloadDenoteOn (observations : SiteObservations interface) (payload : Payload)
    (inputs : Values model.Value payload.entry.inputs) :
    PIR.Proc interface (Values model.Value payload.entry.outputs) :=
  payload.entry.body.denote
    (meaningOn model observations (payloadMeaningsOn model observations payload)) inputs.get

end Model

end Evaluation

/-- Closed helper tables over carriers. -/
abbrev MeaningsOn (carriers : Carriers) := Evaluation.MeaningsOn carriers closedInterface

/-- The closed meaning over a domain model. -/
abbrev meaningOn (model : DomainModel) := Evaluation.meaningOn model SiteObservations.closed

def Payload.meaningsOn (payload : Payload) (model : DomainModel) : MeaningsOn model.toCarriers :=
  Evaluation.payloadMeaningsOn model SiteObservations.closed payload

def Payload.denoteOn (payload : Payload) (model : DomainModel)
    (inputs : Values model.Value payload.entry.inputs) :
    Closed (Values model.Value payload.entry.outputs) :=
  Evaluation.payloadDenoteOn model SiteObservations.closed payload inputs

/-! The uniform evaluator is the instance at the uniform model. -/

section Uniform
variable {F G : Type}

theorem Primitive.evaluate_eq_evaluateOn [CommRing F] [DecidableEq F] :
    Primitive.evaluate (F := F) (G := G) = Primitive.evaluateOn (ringFieldModel F G) := by
  funext primitive args
  cases primitive <;> (iterate 3 (try (rcases args with _ | ⟨_, args⟩))) <;> rfl

theorem DomainSpec.denote_eq_denoteOn :
    DomainSpec.denote (F := F) (G := G) = DomainSpec.denoteOn (carriers := uniformCarriers F G) := by
  funext domain arguments
  rcases domain with ⟨_, _, _, _, _ | _⟩ <;> rfl

namespace Evaluation

theorem mapLengths_eq_mapLengthsOn (field : String) :
    ∀ (mask : List Bool) (args : Values (assignment F G)
      (mask.map (fun row => if row then .vector field else .field field))),
      mapLengths field mask args = mapLengthsOn (carriers := uniformCarriers F G) field mask args
  | [], .nil => rfl
  | true :: rest, .cons _ args => by
      simp only [mapLengths, mapLengthsOn, mapLengths_eq_mapLengthsOn field rest args]
  | false :: rest, .cons _ args => by
      simp only [mapLengths, mapLengthsOn, mapLengths_eq_mapLengthsOn field rest args]

theorem mapRowArguments_eq_mapRowArgumentsOn (field : String) :
    ∀ (mask : List Bool) (args : Values (assignment F G)
      (mask.map (fun row => if row then .vector field else .field field))) (index : Nat),
      mapRowArguments field mask args index =
        mapRowArgumentsOn (carriers := uniformCarriers F G) field mask args index
  | [], .nil, _ => rfl
  | true :: rest, .cons _ args, index => by
      simp only [mapRowArguments, mapRowArgumentsOn,
        mapRowArguments_eq_mapRowArgumentsOn field rest args index]
  | false :: rest, .cons _ args, index => by
      simp only [mapRowArguments, mapRowArgumentsOn,
        mapRowArguments_eq_mapRowArgumentsOn field rest args index]

theorem mapRow_eq_mapRowOn {I : PIR.Signature} (table : HelperTable (assignment F G) I)
    (spec : MapSpec) (args : Values (assignment F G) spec.arguments) (index : Nat) :
    mapRow table spec args index = mapRowOn (carriers := uniformCarriers F G) table spec args index := by
  have arguments := mapRowArguments_eq_mapRowArgumentsOn (F := F) (G := G) spec.field spec.rowwise args index
  simp only [mapRow, mapRowOn, arguments]
  cases mapRowArgumentsOn (carriers := uniformCarriers F G) spec.field spec.rowwise args index <;> rfl

theorem denoteMap_eq_denoteMapOn {I : PIR.Signature} (table : HelperTable (assignment F G) I)
    (spec : MapSpec) (args : Values (assignment F G) spec.arguments) :
    denoteMap table spec args = denoteMapOn (carriers := uniformCarriers F G) table spec args := by
  have rows : mapRow table spec args = mapRowOn (carriers := uniformCarriers F G) table spec args :=
    funext (mapRow_eq_mapRowOn table spec args)
  have lengths := mapLengths_eq_mapLengthsOn (F := F) (G := G) spec.field spec.rowwise args
  simp only [denoteMap, denoteMapOn, lengths, rows]

theorem foldTransition_eq_foldTransitionOn {interface : PIR.Signature}
    (table : HelperTable (assignment F G) interface) (spec : FoldSpec) :
    foldTransition table spec = foldTransitionOn (carriers := uniformCarriers F G) table spec := rfl

theorem denoteFold_eq_denoteFoldOn {interface : PIR.Signature}
    (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (values : Values (assignment F G) spec.arguments) :
    denoteFold table spec values = denoteFoldOn (carriers := uniformCarriers F G) table spec values := by
  simp only [denoteFold, denoteFoldOn, DomainSpec.denote_eq_denoteOn,
    foldTransition_eq_foldTransitionOn]

theorem denoteLoop_eq_denoteLoopOn {interface : PIR.Signature} (state captures : List Ty) :
    denoteLoop (F := F) (G := G) (interface := interface) state captures =
      denoteLoopOn (carriers := uniformCarriers F G) state captures := rfl

theorem denoteConditionalLoop_eq_denoteConditionalLoopOn {interface : PIR.Signature}
    (state captures : List Ty)
    (body : RegionFunction (assignment F G) interface
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) :
    denoteConditionalLoop state captures body lower upper initial captured =
      denoteConditionalLoopOn (carriers := uniformCarriers F G) state captures body lower upper
        initial captured := by
  unfold denoteConditionalLoop denoteConditionalLoopOn
  congr 2
  funext current index
  split
  · congr 1
    funext results
    rcases results with _ | ⟨continuing, rest⟩
    rfl
  · rfl

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem operationOn_boundedAt (model : DomainModel) {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : MeaningsOn model.toCarriers interface)
    (domain : String) (container : List (model.Field domain)) (index : Nat) :
    operationOn model observations table (.boundedAt domain) (.cons container (.cons index .nil)) .nil =
      match container[index]? with
      | some value => .done (.cons value .nil)
      | none => .halt .refused := rfl

theorem operation_boundedAt {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : Meanings F G interface)
    (domain : String) (container : List F) (index : Nat) :
    operation observations table (.boundedAt domain) (.cons container (.cons index .nil)) .nil =
      match container[index]? with
      | some value => .done (.cons value .nil)
      | none => .halt .refused := rfl

theorem operation_eq_operationOn {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : Meanings F G interface) :
    operation observations table = operationOn (ringModel F G) observations table := by
  funext op args bodies
  cases op with
  | exec primitive =>
    rcases bodies with _ | _
    exact congrArg primitiveOutcome
      (congrFun (congrFun (Primitive.evaluate_eq_evaluateOn (F := F) (G := G)) primitive) args)
  | fold spec =>
    rcases bodies with _ | _
    exact denoteFold_eq_denoteFoldOn table spec args
  | map spec =>
    rcases bodies with _ | _
    exact denoteMap_eq_denoteMapOn table spec args
  | loopCondition state captures =>
    rcases bodies with _ | ⟨body, _ | _⟩
    rcases args with _ | ⟨lower, _ | ⟨upper, rest⟩⟩
    exact denoteConditionalLoop_eq_denoteConditionalLoopOn state captures body lower upper _ _
  | boundedAt domain =>
    rcases bodies with _ | _
    rcases args with _ | ⟨container, _ | ⟨index, _ | _⟩⟩
    rw [operation_boundedAt, operationOn_boundedAt]
    cases (show List F from container)[index]? <;> rfl
  | invoke helper =>
    rcases bodies with _ | _
    rfl
  | branch captures outputs =>
    rcases bodies with _ | ⟨yes, _ | ⟨no, _ | _⟩⟩
    rcases args with _ | ⟨condition, captured⟩
    rfl
  | loop state captures =>
    rcases bodies with _ | ⟨body, _ | _⟩
    rcases args with _ | ⟨lower, _ | ⟨upper, rest⟩⟩
    rfl
  | _ =>
    (try rcases bodies with _ | _)
    (iterate 4 (try (rcases args with _ | ⟨_, args⟩)))
    rfl

/-- Denotations under the uniform evaluator are those under the uniform model. -/
theorem denote_meaning_eq_meaningOn {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : Meanings F G interface)
    {Γ out : List Ty} (region : Region dialect Γ out) (env : Environment (assignment F G) Γ) :
    region.denote (meaning observations table) env =
      region.denote (meaningOn (ringModel F G) observations table) env := by
  calc region.denote (meaning observations table) env
      = region.denote ⟨assignment F G, operation observations table⟩ env := rfl
    _ = region.denote ⟨assignment F G, operationOn (ringModel F G) observations table⟩ env := by
        rw [operation_eq_operationOn]
    _ = region.denote (meaningOn (ringModel F G) observations table) env := rfl

theorem meaning_eq_meaningOn {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : Meanings F G interface) :
    meaning observations table = meaningOn (ringModel F G) observations table := by
  simp only [meaning, meaningOn, operation_eq_operationOn]

theorem extendMeanings_eq_extendMeaningsOn {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : Meanings F G interface)
    (definition : CheckedDefinition) :
    extendMeanings observations table definition =
      extendMeaningsOn (ringModel F G) observations table definition := by
  unfold extendMeanings extendMeaningsOn
  congr 2
  funext values
  exact denote_meaning_eq_meaningOn observations table definition.body values.get

theorem payloadMeanings_eq_payloadMeaningsOn {interface : PIR.Signature}
    (observations : SiteObservations interface) (payload : Payload) :
    payloadMeanings (F := F) (G := G) observations payload =
      payloadMeaningsOn (ringModel F G) observations payload := by
  have extend : extendMeanings (F := F) (G := G) observations =
      extendMeaningsOn (ringModel F G) observations :=
    funext fun table => funext (extendMeanings_eq_extendMeaningsOn observations table)
  simp only [payloadMeanings, payloadMeaningsOn, extend]

theorem payloadDenote_eq_payloadDenoteOn {interface : PIR.Signature}
    (observations : SiteObservations interface) (payload : Payload)
    (inputs : Values (assignment F G) payload.entry.inputs) :
    payloadDenote observations payload inputs =
      payloadDenoteOn (ringModel F G) observations payload inputs := by
  unfold payloadDenote payloadDenoteOn
  rw [denote_meaning_eq_meaningOn, payloadMeanings_eq_payloadMeaningsOn]

end Evaluation

theorem Payload.denote_eq_denoteOn [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F]
    [DecidableEq G] (payload : Payload) (inputs : Values (assignment F G) payload.entry.inputs) :
    payload.denote F G inputs = payload.denoteOn (ringModel F G) inputs :=
  Evaluation.payloadDenote_eq_payloadDenoteOn SiteObservations.closed payload inputs

end Uniform

end Zkc.Source.Structured
