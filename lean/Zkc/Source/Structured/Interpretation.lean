module

public import Zkc.Source.Structured.Component
public import Zkc.Source.RegionInterpretation

@[expose] public section

/-! Effect interpretation for the uniform structured evaluator. Values stay at
the same F/G assignment. Site and helper invocation laws lift through arbitrary
nonoptional callbacks, regions, and the actual prefix table construction.
These are process equations, not native projection or availability theorems. -/

set_option autoImplicit false
namespace Zkc.Source

/-- Component translation uses the original nonoptional translation for every
nested callback. Only the outer operands and returned values are optional. -/
theorem Region.component_translate {dialect : Dialect} {I J : PIR.Signature}
    (meaning : RegionMeaning dialect I) (operations : PIR.OperationInterpretation I J)
    (translation : meaning.Translation operations)
    (left : ComponentOperations meaning) (right : ComponentOperations translation.meaning)
    (commutes : ∀ op args bodies, (left op args bodies).interpret operations =
      right op args (RegionFunctions.translate operations bodies))
    {Γ out} (region : Region dialect Γ out) (env : Environment (Component meaning.Value) Γ) :
    (region.component meaning left env).interpret operations =
      region.component translation.meaning right env := by
  induction region using Region.rec (motive_2 := fun _ _ => True) with
  | ret => rfl
  | stop => rfl
  | letOp op args bodies next _ nextIH =>
    simp only [Region.component, PIR.Proc.interpret_bind,
      Regions.denote_translate meaning operations translation bodies, commutes, nextIH]
  | bind body next bodyIH nextIH =>
    simp only [Region.component, PIR.Proc.interpret_bind, bodyIH, nextIH]
  | nil => trivial
  | cons => trivial

end Zkc.Source

namespace Zkc.Source.Structured

variable {I J : PIR.Signature}

/-- Correspondence includes missing names and complete-signature mismatches. -/
def HelperTable.Interprets {Value : Ty → Type}
    (operations : PIR.OperationInterpretation I J)
    (left : HelperTable Value I) (right : HelperTable Value J) : Prop :=
  ∀ helper args, (invoke left helper args).interpret operations = invoke right helper args

theorem HelperTable.Interprets.empty {Value : Ty → Type}
    (operations : PIR.OperationInterpretation I J) :
    HelperTable.Interprets (Value := Value) operations [] [] := by
  intro helper args
  rfl

theorem HelperTable.Interprets.cons {Value : Ty → Type}
    {operations : PIR.OperationInterpretation I J}
    {left : HelperTable Value I} {right : HelperTable Value J}
    (tables : HelperTable.Interprets operations left right) (helper : Helper)
    (leftBody : HelperFunction Value I helper) (rightBody : HelperFunction Value J helper)
    (bodies : ∀ args, (leftBody args).interpret operations = rightBody args) :
    HelperTable.Interprets operations (⟨helper, leftBody⟩ :: left) (⟨helper, rightBody⟩ :: right) := by
  intro called args
  by_cases name : helper.name = called.name
  · by_cases signature : helper = called
    · subst called
      simpa only [invoke, List.find?_cons, beq_self_eq_true, ↓reduceIte, ↓reduceDIte] using bodies args
    · simp [invoke, name, signature, PIR.Proc.interpret]
  · rw [invoke_cons_other left ⟨helper, leftBody⟩ called name,
      invoke_cons_other right ⟨helper, rightBody⟩ called name]
    exact tables called args

def SiteObservations.Interprets (operations : PIR.OperationInterpretation I J)
    (left : SiteObservations I) (right : SiteObservations J) : Prop :=
  ∀ site, (left.mark site).interpret operations = right.mark site

theorem SiteObservations.silent_interpret (operations : PIR.OperationInterpretation I J) :
    SiteObservations.Interprets operations (.silent I) (.silent J) := by
  intro site
  rfl

/-- Closed processes have no operations to expand. Their values and stops remain. -/
def closedLift : PIR.OperationInterpretation closedInterface I := fun impossible => nomatch impossible

theorem SiteObservations.closed_interpret :
    SiteObservations.Interprets (closedLift (I := I)) .closed (.silent I) :=
  SiteObservations.silent_interpret closedLift

namespace Evaluation

variable {F G : Type}

theorem foldTransition_interpret (operations : PIR.OperationInterpretation I J)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right) (spec : FoldSpec)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (captures : Values (assignment F G) spec.captures)
    (state : Values (assignment F G) spec.state) (item : assignment F G spec.domain.item) :
    (foldTransition left spec arguments captures state item).interpret operations =
      foldTransition right spec arguments captures state item := by
  unfold foldTransition
  dsimp only [FoldSpec.predicateHelper, FoldSpec.stepHelper]
  rw [PIR.Proc.interpret_bind]
  have enabled :
      ((if spec.predicate.isEmpty then PIR.Proc.done (Values.cons true Values.nil)
        else invoke left spec.predicateHelper (.cons item (arguments.append captures))).interpret operations) =
      (if spec.predicate.isEmpty then PIR.Proc.done (Values.cons true Values.nil)
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

theorem denoteFold_interpret (operations : PIR.OperationInterpretation I J)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right) (spec : FoldSpec)
    (args : Values (assignment F G) spec.arguments) :
    (denoteFold left spec args).interpret operations = denoteFold right spec args := by
  simp only [denoteFold, Finite.interpret_execute, foldTransition_interpret operations tables]

theorem denoteLoop_interpret (operations : PIR.OperationInterpretation I J)
    (state captures : List Ty)
    (body : RegionFunction (assignment F G) I (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) :
    (denoteLoop state captures body lower upper initial captured).interpret operations =
      denoteLoop state captures (fun args => (body args).interpret operations) lower upper initial captured := by
  simp only [denoteLoop, Finite.interpret_execute, invokeCallback, PIR.Proc.interpret_bind,
    PIR.Proc.interpret]

theorem denoteConditionalLoop_interpret (operations : PIR.OperationInterpretation I J)
    (state captures : List Ty)
    (body : RegionFunction (assignment F G) I
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) :
    (denoteConditionalLoop state captures body lower upper initial captured).interpret operations =
      denoteConditionalLoop state captures (fun args => (body args).interpret operations)
        lower upper initial captured := by
  simp only [denoteConditionalLoop, PIR.Proc.interpret_bind, Finite.interpret_execute,
    PIR.Proc.interpret, invokeCallback]
  congr 2
  funext current index
  split
  · rw [PIR.Proc.interpret_bind]
    congr 1
    funext results
    cases results
    rfl
  · rfl

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Arbitrary effectful callbacks are translated pointwise, never inspected. -/
theorem operation_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right)
    (op : Op) (args : Values (assignment F G) op.arguments)
    (bodies : Values (RegionFunction (assignment F G) I) op.regions) :
    (operation leftSites left op args bodies).interpret operations =
      operation rightSites right op args (RegionFunctions.translate (dialect := dialect) operations bodies) := by
  cases op with
  | fieldConstant | booleanConstant | groupIdentity => cases args; cases bodies; rfl
  | mark site =>
    cases args; cases bodies
    change ((leftSites.mark site).bind (fun _ => .done (Values.nil : Values (assignment F G) []))).interpret operations =
      (rightSites.mark site).bind (fun _ => .done Values.nil)
    simp only [PIR.Proc.interpret_bind, sites site, PIR.Proc.interpret]
  | fieldAdd | fieldSubtract | fieldMultiply | fieldEqual | booleanAnd | booleanOr |
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
          | some value => (PIR.Proc.done (.cons value .nil) : PIR.Proc I (Values (assignment F G) [.field domain]))
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
  | invoke helper => cases bodies; exact tables helper args
  | fold spec => cases bodies; exact denoteFold_interpret operations tables spec args
  | branch =>
    cases args with
    | cons condition captures => cases bodies with
      | cons yes rest => cases rest with
        | cons no rest => cases rest; cases condition <;> rfl
  | loop =>
    cases args with
    | cons lower rest => cases rest with
      | cons upper rest => cases bodies with
        | cons body tail => cases tail; exact denoteLoop_interpret operations _ _ body lower upper _ _
  | loopCondition =>
    cases args with
    | cons lower rest => cases rest with
      | cons upper rest => cases bodies with
        | cons body tail => cases tail; exact denoteConditionalLoop_interpret operations _ _ body lower upper _ _
  | guard =>
    cases args with
    | cons condition rest => cases rest; cases bodies; cases condition <;> rfl

def meaningTranslation (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right) :
    (meaning leftSites left).Translation operations where
  operation := operation rightSites right
  commutes op args bodies := (operation_interpret operations sites tables op args bodies).symm

theorem denote_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right)
    {Γ out : List Ty} (region : Region dialect Γ out) (env : Environment (assignment F G) Γ) :
    (region.denote (meaning leftSites left) env).interpret operations =
      region.denote (meaning rightSites right) env :=
  (region.denote_translate _ operations (meaningTranslation operations sites tables) env).symm

theorem extendMeanings_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right) (definition : CheckedDefinition) :
    HelperTable.Interprets operations (extendMeanings leftSites left definition)
      (extendMeanings rightSites right definition) :=
  tables.cons definition.helper _ _ (fun args => denote_interpret operations sites tables _ args.get)

/-- Each closure captures its own translated prefix. No final-table equation is assumed. -/
theorem foldMeanings_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right) (definitions : List CheckedDefinition) :
    HelperTable.Interprets operations (definitions.foldl (extendMeanings leftSites) left)
      (definitions.foldl (extendMeanings rightSites) right) := by
  induction definitions generalizing left right with
  | nil => exact tables
  | cons definition rest ih => exact ih (extendMeanings_interpret operations sites tables definition)

theorem payloadDenote_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    (payload : Payload) (inputs : Values (assignment F G) payload.entry.inputs) :
    (payloadDenote leftSites payload inputs).interpret operations = payloadDenote rightSites payload inputs :=
  denote_interpret operations sites
    (foldMeanings_interpret operations sites (.empty operations) payload.definitions) _ inputs.get

/-- Optional helper calls and nonoptional callbacks both retain correspondence. -/
structure ComponentTables.Interprets (operations : PIR.OperationInterpretation I J)
    (left : ComponentTables F G I) (right : ComponentTables F G J) : Prop where
  closed : HelperTable.Interprets operations left.closed right.closed
  components : HelperTable.Interprets operations left.components right.components

theorem strictComponent_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : Meanings F G I} {right : Meanings F G J}
    (tables : HelperTable.Interprets operations left right)
    (op : Op) (args : Values (Component (assignment F G)) op.arguments)
    (bodies : Values (RegionFunction (assignment F G) I) op.regions) :
    (strictComponent (meaning leftSites left) op args bodies).interpret operations =
      strictComponent (meaning rightSites right) op args (RegionFunctions.translate operations bodies) := by
  unfold strictComponent
  cases sequenced : RoleFamily.sequence args with
  | none => rfl
  | some values =>
    simp only [meaning, PIR.Proc.interpret_bind, operation_interpret operations sites tables,
      PIR.Proc.interpret]

theorem componentOperation_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTables F G I} {right : ComponentTables F G J}
    (tables : ComponentTables.Interprets operations left right)
    (op : Op) (args : Values (Component (assignment F G)) op.arguments)
    (bodies : Values (RegionFunction (assignment F G) I) op.regions) :
    (componentOperation leftSites left op args bodies).interpret operations =
      componentOperation rightSites right op args (RegionFunctions.translate operations bodies) := by
  cases op <;> try exact strictComponent_interpret operations sites tables.closed _ args bodies
  case invoke helper =>
    cases bodies
    by_cases math : helper.kind = .math
    · simp only [componentOperation, math, ↓reduceIte, RegionFunctions.translate]
      exact tables.components helper args
    · simp only [componentOperation, math, ↓reduceIte, RegionFunctions.translate]
      exact strictComponent_interpret operations sites tables.closed (.invoke helper) args .nil

theorem component_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTables F G I} {right : ComponentTables F G J}
    (tables : ComponentTables.Interprets operations left right)
    {Γ out : List Ty} (region : Region dialect Γ out)
    (env : Environment (Component (assignment F G)) Γ) :
    (region.component (meaning leftSites left.closed) (componentOperation leftSites left) env).interpret operations =
      region.component (meaning rightSites right.closed) (componentOperation rightSites right) env :=
  region.component_translate (meaning leftSites left.closed) operations
    (meaningTranslation operations sites tables.closed) _ _
    (componentOperation_interpret operations sites tables) env

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem ComponentTables.Interprets.empty (operations : PIR.OperationInterpretation I J) :
    ComponentTables.Interprets (F := F) (G := G) operations ⟨[], []⟩ ⟨[], []⟩ :=
  ⟨.empty operations, .empty operations⟩

theorem ComponentTables.extend_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTables F G I} {right : ComponentTables F G J}
    (tables : ComponentTables.Interprets operations left right) (definition : CheckedDefinition) :
    ComponentTables.Interprets operations (left.extend leftSites definition) (right.extend rightSites definition) where
  closed := extendMeanings_interpret operations sites tables.closed definition
  components := tables.components.cons definition.helper _ _
    (fun args => component_interpret operations sites tables _ args.get)

theorem ComponentTables.fold_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {left : ComponentTables F G I} {right : ComponentTables F G J}
    (tables : ComponentTables.Interprets operations left right) (definitions : List CheckedDefinition) :
    ComponentTables.Interprets operations (definitions.foldl (ComponentTables.extend leftSites) left)
      (definitions.foldl (ComponentTables.extend rightSites) right) := by
  induction definitions generalizing left right with
  | nil => exact tables
  | cons definition rest ih => exact ih (ComponentTables.extend_interpret operations sites tables definition)

theorem payloadComponent_interpret (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    (payload : Payload) (inputs : Values (Component (assignment F G)) payload.entry.inputs) :
    (payloadComponent leftSites payload inputs).interpret operations = payloadComponent rightSites payload inputs :=
  component_interpret operations sites
    (ComponentTables.fold_interpret operations sites (.empty operations) payload.definitions) _ inputs.get

theorem foldMeanings_closedLift (definitions : List CheckedDefinition) :
    HelperTable.Interprets (closedLift (I := I))
      (definitions.foldl (extendMeanings (F := F) (G := G) SiteObservations.closed) [])
      (definitions.foldl (extendMeanings (.silent I)) []) :=
  foldMeanings_interpret closedLift SiteObservations.closed_interpret (.empty _) definitions

theorem ComponentTables.fold_closedLift (definitions : List CheckedDefinition) :
    ComponentTables.Interprets (closedLift (I := I))
      (definitions.foldl (ComponentTables.extend (F := F) (G := G) SiteObservations.closed) ⟨[], []⟩)
      (definitions.foldl (ComponentTables.extend (.silent I)) ⟨[], []⟩) :=
  ComponentTables.fold_interpret closedLift SiteObservations.closed_interpret (.empty _) definitions

end Evaluation
end Zkc.Source.Structured
