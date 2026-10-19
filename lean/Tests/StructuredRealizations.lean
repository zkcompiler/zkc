module

public import Zkc.Source.Structured.RealizationTotality
public import ZkcExamples.Structured.RealizationValues

@[expose] public section

open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

namespace Tests.StructuredRealizations
abbrev ports : List Ty := [.vector scalarDomain, .index, .field scalarDomain]
abbrev results : List Ty := [.vector scalarDomain, .index, .field scalarDomain, .vector scalarDomain]

def math (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .math, .privateDef, inputs, outputs, none, [], none, body⟩
def zero : Definition := math "zero" ports [] (.block [] (.ret []))
def tuple : Definition := math "tuple" ports results (.block [] (.ret [0, 1, 2, 0]))
def root : Definition := math "root" ports results
  (.block [.instruction (.call "zero") [0, 1, 2] [] [] "",
    .instruction (.call "tuple") [0, 1, 2] results [] ""] (.ret [0, 1, 2, 3]))
def declaration : RealizationDeclaration := ⟨"realized", ports, results, "root"⟩
def emptyDeclaration : RealizationDeclaration := ⟨"empty", ports, [], "zero"⟩
def snapshot : Snapshot :=
  (let contractDefinitions : List Definition := [.function ⟨"main", .protocol, .publicDef, [], [], some ⟨["P"], [], []⟩,
      [], none, .block [] (.ret [])⟩, zero, tuple, root,
      .realization declaration, .realization emptyDeclaration]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows⟩)
def program : Program := (check snapshot).toOption.get (by decide +kernel)
def imported : Imported snapshot := ⟨program, rfl⟩
def summaries : IdentitySummaries := snapshot.identitySummaries.toOption.get (by decide +kernel)
def checked : CheckedDefinition :=
  (checkDefinition snapshot [] summaries (.realization declaration)).toOption.get (by decide +kernel)
def emptyChecked : CheckedDefinition :=
  (checkDefinition snapshot [] summaries (.realization emptyDeclaration)).toOption.get (by decide +kernel)

variable {F G : Type} {I : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
variable (observations : SiteObservations I)

-- Vector inputs, discarded zero-result call, then all four outputs preserved.
example (args : Values (assignment F G) ports) :
    Returns (checked.body.denote
      (Evaluation.meaning observations
        (program.payload.definitions.foldl (Evaluation.extendMeanings observations) [])) args.get) :=
  Evaluation.admitted_realization_returns observations program [] summaries declaration checked
    rfl (by decide +kernel) args

-- A zero-result root is an actual invocation, not a skipped proof obligation.
example (args : Values (assignment F G) ports) :
    Returns (emptyChecked.body.denote
      (Evaluation.meaning observations
        (program.payload.definitions.foldl (Evaluation.extendMeanings observations) [])) args.get) :=
  Evaluation.admitted_realization_returns observations program [] summaries emptyDeclaration emptyChecked
    rfl (by decide +kernel) args

-- Imported admission derives root selection; the actual retained body is invoked.
example (args : Values (assignment F G) ports) :
    Returns (invoke
      (program.payload.definitions.foldl (Evaluation.extendMeanings observations) [])
      checked.helper args) :=
  Evaluation.imported_realization_returns observations imported declaration
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))) checked
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))) rfl args

example (args : Values (assignment F G) ports) :
    Returns (invoke
      (program.payload.definitions.foldl (Evaluation.extendMeanings observations) [])
      emptyChecked.helper args) :=
  Evaluation.imported_realization_returns observations imported emptyDeclaration
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) emptyChecked
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))) rfl args

example : (Op.boundedAt scalarDomain).preparationAllowed .realization = false := rfl
example : (Op.exec (.indexConstant 0)).preparationAllowed .realization = false := rfl
example : (RawRegion.stop (Ty := Ty) (Op := Op) .reject).preparationAllowed .realization = false := rfl

open ZkcExamples.Structured
example (xs : List F) :
    invoke (RealizationValuesViews.program.payload.componentTables F G).components
      RealizationValuesViews.projectionHelper (.cons (some xs) (.cons none (.cons none .nil))) =
      .done (.cons (some xs) .nil) := RealizationValues.projection_optional (some xs) none none

example (xs : List F) :
    RealizationValuesViews.program.subject.participant F G 0
      (.cons (some xs) (.cons none (.cons none .nil))) = .halt .incomplete :=
  RealizationValues.participant_missing _ rfl

example : RealizationValuesViews.program.denote F G
    (PrimitiveLibrary.inputs ([] : List F) 0 0) = .halt .reject := by
  have rejected := RealizationValues.process_equation (G := G) ([] : List F) 0 0
    (by change 0 < indexLimit; decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa [PrimitiveLibrary.HasShape] using rejected

end Tests.StructuredRealizations
