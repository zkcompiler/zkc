module

public import Zkc.Source.Structured.DomainComponent
public import Zkc.Source.Structured.Interpretation

@[expose] public section

/-! Effect interpretation for nominal structured values. Each field, group,
embedding and primitive retains its exact domain model. Translation commutes
with arbitrary callbacks and the actual captured helper-table prefixes,
including stopped executions and missing or mismatched helpers. -/
set_option autoImplicit false
namespace Zkc.Source.Structured
variable {I J : PIR.Signature}

namespace Evaluation

variable {model : DomainModel}

theorem foldTransitionOn_interpret (operations : PIR.OperationInterpretation I J)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right) (spec : FoldSpec)
    (arguments : Values model.Value spec.domain.inputs)
    (captures : Values model.Value spec.captures)
    (state : Values model.Value spec.state) (item : model.Value spec.domain.item) :
    (foldTransitionOn left spec arguments captures state item).interpret operations =
      foldTransitionOn right spec arguments captures state item := by
  unfold foldTransitionOn
  dsimp only [FoldSpec.predicateHelper, FoldSpec.stepHelper]
  rw [PIR.Process.interpret_bind]
  have enabled :
      ((if spec.predicate.isEmpty then PIR.Process.done (Values.cons true Values.nil)
        else invoke left spec.predicateHelper (.cons item (arguments.append captures))).interpret operations) =
      (if spec.predicate.isEmpty then PIR.Process.done (Values.cons true Values.nil)
        else invoke right spec.predicateHelper (.cons item (arguments.append captures))) := by
    dsimp only [FoldSpec.predicateHelper]
    by_cases present : spec.predicate.isEmpty = true
    · rw [ite_eq_left present, ite_eq_left present]; rfl
    · rw [ite_eq_right present, ite_eq_right present]; exact tables _ _
  dsimp only [FoldSpec.predicateHelper] at enabled
  rw [enabled]
  congr 1
  funext result
  by_cases enabled : result.get .here = true
  · rw [ite_eq_left enabled, ite_eq_left enabled]; exact tables _ _
  · rw [ite_eq_right enabled, ite_eq_right enabled]; rfl

theorem denoteFoldOn_interpret (operations : PIR.OperationInterpretation I J)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right) (spec : FoldSpec)
    (args : Values model.Value spec.arguments) :
    (denoteFoldOn left spec args).interpret operations = denoteFoldOn right spec args := by
  simp only [denoteFoldOn, Finite.interpret_execute, foldTransitionOn_interpret operations tables]

theorem mapRowOn_interpret (operations : PIR.OperationInterpretation I J)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right) (spec : MapSpec)
    (args : Values model.Value spec.arguments) (index : Nat) :
    (mapRowOn left spec args index).interpret operations = mapRowOn right spec args index := by
  unfold mapRowOn
  cases selected : mapRowArgumentsOn spec.field spec.rowwise args index with
  | none => rfl
  | some values =>
    simp only [PIR.Process.interpret_bind, tables spec.helper values, PIR.Process.interpret]

theorem denoteMapOn_interpret (operations : PIR.OperationInterpretation I J)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right) (spec : MapSpec)
    (args : Values model.Value spec.arguments) :
    (denoteMapOn left spec args).interpret operations = denoteMapOn right spec args := by
  simp only [denoteMapOn, Finite.interpret_admitThen, PIR.Process.interpret_bind,
    mapRows_interpret, mapRowOn_interpret operations tables, PIR.Process.interpret]

theorem denoteLoopOn_interpret (operations : PIR.OperationInterpretation I J)
    (state captures : List Ty)
    (body : RegionFunction model.Value I (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (initial : Values model.Value state)
    (captured : Values model.Value captures) :
    (denoteLoopOn state captures body lower upper initial captured).interpret operations =
      denoteLoopOn state captures (fun args => (body args).interpret operations) lower upper initial captured := by
  simp only [denoteLoopOn, Finite.interpret_execute, invokeCallbackOn, PIR.Process.interpret_bind,
    PIR.Process.interpret]

theorem denoteConditionalLoopOn_interpret (operations : PIR.OperationInterpretation I J)
    (state captures : List Ty)
    (body : RegionFunction model.Value I
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (initial : Values model.Value state)
    (captured : Values model.Value captures) :
    (denoteConditionalLoopOn state captures body lower upper initial captured).interpret operations =
      denoteConditionalLoopOn state captures (fun args => (body args).interpret operations)
        lower upper initial captured := by
  simp only [denoteConditionalLoopOn, PIR.Process.interpret_bind, Finite.interpret_execute,
    PIR.Process.interpret, invokeCallbackOn]
  congr 2
  funext current index
  split
  · rw [PIR.Process.interpret_bind]
    congr 1
    funext results
    cases results
    rfl
  · rfl



/-- Arbitrary effectful callbacks are translated pointwise, never inspected. -/
theorem operationOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right)
    (op : Op) (args : Values model.Value op.arguments)
    (bodies : Values (RegionFunction model.Value I) op.regions) :
    (operationOn model leftSites left op args bodies).interpret operations =
      operationOn model rightSites right op args (RegionFunctions.translate (dialect := dialect) operations bodies) := by
  cases op with
  | fieldEmbed | vectorLength =>
    cases args with
    | cons value rest => cases rest; cases bodies; rfl
  | indexConstant | fieldConstant | booleanConstant | groupIdentity => cases args; cases bodies; rfl
  | mark site =>
    cases args; cases bodies
    change ((leftSites.mark site).bind (fun _ => .done (Values.nil : Values model.Value []))).interpret operations =
      (rightSites.mark site).bind (fun _ => .done Values.nil)
    simp only [PIR.Process.interpret_bind, sites site, PIR.Process.interpret]
  | indexEqual | indexLess | indexPowerOfTwo | fieldAdd | fieldSubtract | fieldMultiply | fieldEqual | booleanAnd | booleanOr |
      booleanXor | booleanEqual | booleanNotEqual | groupAdd | groupScale | groupEqual =>
    cases args with
    | cons a rest => cases rest with
      | cons b rest => cases rest; cases bodies; rfl
  | boundedAt domain =>
    cases args with
    | cons container rest => cases rest with
      | cons index rest =>
        cases rest; cases bodies
        change (match container[index]? with
          | some value => (PIR.Process.done (.cons value .nil) : PIR.Process I (Values model.Value [.field domain]))
          | none => .halt .refused).interpret operations =
          (match container[index]? with
          | some value => .done (.cons value .nil)
          | none => .halt .refused)
        cases container[index]? <;> rfl
  | select =>
    cases args with
    | cons condition rest => cases rest with
      | cons yes rest => cases rest with
        | cons no rest => cases rest; cases bodies; rfl
  | exec primitive =>
    cases bodies
    change (primitiveOutcome (primitive.evaluateOn model.toFieldModel args)).interpret operations =
      primitiveOutcome (primitive.evaluateOn model.toFieldModel args)
    cases primitive.evaluateOn model.toFieldModel args <;> rfl
  | invoke helper => cases bodies; exact tables helper args
  | fold spec => cases bodies; exact denoteFoldOn_interpret operations tables spec args
  | map spec => cases bodies; exact denoteMapOn_interpret operations tables spec args
  | branch =>
    cases args with
    | cons condition captures => cases bodies with
      | cons yes rest => cases rest with
        | cons no rest => cases rest; cases condition <;> rfl
  | loop =>
    cases args with
    | cons lower rest => cases rest with
      | cons upper rest => cases bodies with
        | cons body tail => cases tail; exact denoteLoopOn_interpret operations _ _ body lower upper _ _
  | loopCondition =>
    cases args with
    | cons lower rest => cases rest with
      | cons upper rest => cases bodies with
        | cons body tail => cases tail; exact denoteConditionalLoopOn_interpret operations _ _ body lower upper _ _
  | guard =>
    cases args with
    | cons condition rest => cases rest; cases bodies; cases condition <;> rfl

def meaningTranslationOn (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right) :
    (meaningOn model leftSites left).Translation operations where
  operation := operationOn model rightSites right
  commutes op args bodies := (operationOn_interpret operations sites tables op args bodies).symm

theorem denoteOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right)
    {Γ out : List Ty} (region : Region dialect Γ out) (env : Environment model.Value Γ) :
    (region.denote (meaningOn model leftSites left) env).interpret operations =
      region.denote (meaningOn model rightSites right) env :=
  (region.denote_translate _ operations (meaningTranslationOn operations sites tables) env).symm

theorem extendMeaningsOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right) (definition : CheckedDefinition) :
    HelperTable.Interprets operations (extendMeaningsOn model leftSites left definition)
      (extendMeaningsOn model rightSites right definition) :=
  tables.cons definition.helper _ _ (fun args => denoteOn_interpret operations sites tables _ args.get)

/-- Each closure captures its own translated prefix. No final-table equation is assumed. -/
theorem foldMeaningsOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right) (definitions : List CheckedDefinition) :
    HelperTable.Interprets operations (definitions.foldl (extendMeaningsOn model leftSites) left)
      (definitions.foldl (extendMeaningsOn model rightSites) right) := by
  induction definitions generalizing left right with
  | nil => exact tables
  | cons definition rest ih => exact ih (extendMeaningsOn_interpret operations sites tables definition)

theorem payloadDenoteOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    (payload : Payload) (inputs : Values model.Value payload.entry.inputs) :
    (payloadDenoteOn model leftSites payload inputs).interpret operations = payloadDenoteOn model rightSites payload inputs :=
  denoteOn_interpret operations sites
    (foldMeaningsOn_interpret operations sites (.empty operations) payload.definitions) _ inputs.get

/-- Optional helper calls and nonoptional callbacks both retain correspondence. -/
structure ComponentTablesOn.Interprets (operations : PIR.OperationInterpretation I J)
    (left : ComponentTablesOn model.toCarriers I) (right : ComponentTablesOn model.toCarriers J) : Prop where
  closed : HelperTable.Interprets operations left.closed right.closed
  components : HelperTable.Interprets operations left.components right.components

theorem strictComponentOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : MeaningsOn model.toCarriers I} {right : MeaningsOn model.toCarriers J}
    (tables : HelperTable.Interprets operations left right)
    (op : Op) (args : Values (Component model.Value) op.arguments)
    (bodies : Values (RegionFunction model.Value I) op.regions) :
    (strictComponent (meaningOn model leftSites left) op args bodies).interpret operations =
      strictComponent (meaningOn model rightSites right) op args (RegionFunctions.translate operations bodies) := by
  unfold strictComponent
  cases sequenced : RoleFamily.sequence args with
  | none => rfl
  | some values =>
    simp only [meaningOn, PIR.Process.interpret_bind, operationOn_interpret operations sites tables,
      PIR.Process.interpret]

theorem componentOperationOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTablesOn model.toCarriers I} {right : ComponentTablesOn model.toCarriers J}
    (tables : ComponentTablesOn.Interprets operations left right)
    (op : Op) (args : Values (Component model.Value) op.arguments)
    (bodies : Values (RegionFunction model.Value I) op.regions) :
    (componentOperationOn model leftSites left op args bodies).interpret operations =
      componentOperationOn model rightSites right op args (RegionFunctions.translate operations bodies) := by
  cases op <;> try exact strictComponentOn_interpret operations sites tables.closed _ args bodies
  case exec primitive =>
    cases bodies
    dsimp only [componentOperationOn, RegionFunctions.translate]
    cases present : RoleFamily.sequence args with
    | none => rfl
    | some values =>
      simp only []
      rw [PIR.Process.interpret_bind]
      have lift : (primitiveOutcome (primitive.evaluateOn model.toFieldModel values)).interpret operations =
          primitiveOutcome (primitive.evaluateOn model.toFieldModel values) := by
        cases primitive.evaluateOn model.toFieldModel values <;> rfl
      rw [lift]
      rfl
  case map spec =>
    cases bodies
    dsimp only [Op.arguments] at args
    dsimp only [componentOperationOn, RegionFunctions.translate]
    cases present : RoleFamily.sequence args with
    | none => rfl
    | some values =>
      simp only [PIR.Process.interpret_bind, denoteMapOn_interpret operations tables.closed,
        PIR.Process.interpret]
  case invoke helper =>
    cases bodies
    by_cases math : helper.kind = .math
    · dsimp only [componentOperationOn, RegionFunctions.translate]
      simp only [math, ↓reduceIte]
      exact tables.components helper args
    · dsimp only [componentOperationOn, RegionFunctions.translate]
      simp only [math, ↓reduceIte]
      exact strictComponentOn_interpret operations sites tables.closed (.invoke helper) args .nil

theorem componentOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTablesOn model.toCarriers I} {right : ComponentTablesOn model.toCarriers J}
    (tables : ComponentTablesOn.Interprets operations left right)
    {Γ out : List Ty} (region : Region dialect Γ out)
    (env : Environment (Component model.Value) Γ) :
    (region.component (meaningOn model leftSites left.closed) (componentOperationOn model leftSites left) env).interpret operations =
      region.component (meaningOn model rightSites right.closed) (componentOperationOn model rightSites right) env :=
  region.component_translate (meaningOn model leftSites left.closed) operations
    (meaningTranslationOn operations sites tables.closed) _ _
    (componentOperationOn_interpret operations sites tables) env

theorem ComponentTablesOn.Interprets.empty (operations : PIR.OperationInterpretation I J) :
    ComponentTablesOn.Interprets (model := model) operations ⟨[], []⟩ ⟨[], []⟩ :=
  ⟨.empty operations, .empty operations⟩

theorem ComponentTablesOn.extend_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTablesOn model.toCarriers I} {right : ComponentTablesOn model.toCarriers J}
    (tables : ComponentTablesOn.Interprets operations left right) (definition : CheckedDefinition) :
    ComponentTablesOn.Interprets operations (left.extend model leftSites definition) (right.extend model rightSites definition) where
  closed := extendMeaningsOn_interpret operations sites tables.closed definition
  components := tables.components.cons definition.helper _ _
    (fun args => componentOn_interpret operations sites tables _ args.get)

theorem ComponentTablesOn.fold_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTablesOn model.toCarriers I} {right : ComponentTablesOn model.toCarriers J}
    (tables : ComponentTablesOn.Interprets operations left right) (definitions : List CheckedDefinition) :
    ComponentTablesOn.Interprets operations (definitions.foldl (ComponentTablesOn.extend model leftSites) left)
      (definitions.foldl (ComponentTablesOn.extend model rightSites) right) := by
  induction definitions generalizing left right with
  | nil => exact tables
  | cons definition rest ih => exact ih (ComponentTablesOn.extend_interpret operations sites tables definition)

theorem payloadComponentOn_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    (payload : Payload) (inputs : Values (Component model.Value) payload.entry.inputs) :
    (payloadComponentOn model leftSites payload inputs).interpret operations = payloadComponentOn model rightSites payload inputs :=
  componentOn_interpret operations sites
    (ComponentTablesOn.fold_interpret operations sites (.empty operations) payload.definitions) _ inputs.get

end Evaluation
end Zkc.Source.Structured
