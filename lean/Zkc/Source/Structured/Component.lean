module

public import Zkc.Source.Structured.Meaning
public import Zkc.Source.Component

@[expose] public section

/-! Optional interpretation of shared named bodies, with the original closed
callbacks and strict non-call operations. This is a denotation, not availability
formation or participant dispatch: current Op.invoke still conflates Math and
Local calls. An owned Local boundary must invoke the closed table after requiring
all its inputs. No native profile or format is extended here.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured

abbrev ComponentMeanings (F : Type) :=
  HelperTable (Component (scalarAssignment F)) closedInterface

/-- Two instances of one generic table, built from the same stored bodies. -/
structure ComponentTables (F : Type) where
  closed : Meanings F
  components : ComponentMeanings F

variable {F : Type} [CommRing F] [DecidableEq F]

/-- Only named calls bypass operand sequencing. Every other operation delegates
to its existing implementation, so arithmetic, stops and callbacks are shared. -/
def componentOperation (tables : ComponentTables F) :
    ComponentOperations (meaning F tables.closed)
  | .invoke helper, args, .nil => invoke tables.components helper args
  | op, args, bodies => strictComponent (meaning F tables.closed) op args bodies

def ComponentTables.extend (tables : ComponentTables F) (definition : CheckedDefinition) :
    ComponentTables F where
  closed := extendMeanings tables.closed definition
  components := ⟨definition.helper, fun args =>
    definition.body.component (meaning F tables.closed) (componentOperation tables) args.get⟩ ::
      tables.components

def Payload.componentTables (payload : Payload) (F : Type) [CommRing F] [DecidableEq F] :
    ComponentTables F := payload.definitions.foldl ComponentTables.extend ⟨[], []⟩

def Payload.component (payload : Payload) (F : Type) [CommRing F] [DecidableEq F]
    (inputs : Values (Component (scalarAssignment F)) payload.entry.inputs) :
    Closed (Values (Component (scalarAssignment F)) payload.entry.outputs) :=
  invoke (payload.componentTables F).components payload.entry.helper inputs

def ComponentTables.Adequate (tables : ComponentTables F) : Prop :=
  ∀ helper args, invoke tables.components helper args.present =
    (invoke tables.closed helper args).bind fun results => .done results.present

theorem componentOperation_adequate (tables : ComponentTables F)
    (adequate : tables.Adequate) :
    ComponentOperations.Adequate (meaning F tables.closed) (componentOperation tables) := by
  intro op args bodies
  cases op <;> try exact strictComponent_adequate (meaning F tables.closed) _ args bodies
  case invoke helper =>
    cases bodies
    exact adequate helper args

omit [CommRing F] [DecidableEq F] in
theorem ComponentTables.adequate_empty : (⟨[], []⟩ : ComponentTables F).Adequate := by
  intro helper args
  rfl

theorem ComponentTables.adequate_extend (tables : ComponentTables F)
    (adequate : tables.Adequate) (definition : CheckedDefinition) :
    (tables.extend definition).Adequate := by
  intro helper args
  by_cases name : definition.helper.name = helper.name
  · by_cases signature : definition.helper = helper
    · subst helper
      simp only [extend, extendMeanings]
      simp [invoke]
      have presentEnv : @Eq (Environment (Component (scalarAssignment F)) definition.inputs)
          args.present.get (fun ref => some (args.get ref)) := by
        funext ty ref
        exact Values.get_present args ref
      rw [presentEnv]
      exact definition.body.component_present (meaning F tables.closed) (componentOperation tables)
        (componentOperation_adequate tables adequate) args.get
    · simp [extend, extendMeanings, invoke, name, signature, PIR.Proc.bind]
  · simp only [extend, extendMeanings]
    simp only [invoke, List.find?_cons, show (definition.helper.name == helper.name) = false from
      beq_eq_false_iff_ne.mpr name]
    exact adequate helper args

theorem ComponentTables.adequate_fold (tables : ComponentTables F)
    (adequate : tables.Adequate) (definitions : List CheckedDefinition) :
    (definitions.foldl ComponentTables.extend tables).Adequate := by
  induction definitions generalizing tables with
  | nil => exact adequate
  | cons definition rest ih => exact ih _ (tables.adequate_extend adequate definition)

theorem ComponentTables.closed_fold (tables : ComponentTables F)
    (definitions : List CheckedDefinition) :
    (definitions.foldl ComponentTables.extend tables).closed =
      definitions.foldl extendMeanings tables.closed := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih => exact ih (tables.extend definition)

theorem Payload.componentTables_closed (payload : Payload) :
    (payload.componentTables F).closed = payload.meanings F :=
  ComponentTables.closed_fold _ _

theorem Payload.componentTables_adequate (payload : Payload) :
    (payload.componentTables F).Adequate :=
  ComponentTables.adequate_fold _ ComponentTables.adequate_empty _

/-- All-present component execution equals closed execution with present results.
This preserves stops even for bodies outside the total mathematical fragment. -/
theorem Payload.component_present (payload : Payload)
    (inputs : Values (scalarAssignment F) payload.entry.inputs) :
    payload.component F inputs.present =
      (payload.denote F inputs).bind fun results => .done results.present := by
  have adequate := payload.componentTables_adequate (F := F) payload.entry.helper inputs
  simpa only [Payload.component, Payload.denote, payload.componentTables_closed,
    CheckedDefinition.helper] using adequate

end Zkc.Source.Structured
