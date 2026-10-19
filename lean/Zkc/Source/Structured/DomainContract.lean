module

public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.Structured.LogicalTranslation

@[expose] public section

/-! Relation and contract interpretations over domain models.

These are the relation environments, relation interpretations, interpreted
applications and contract interpretations of `ContractMeaning`, and the
relation meanings of `LogicalTranslation`, with the uniform values replaced by
a domain model's. Formula relations still mean the actual helper invocation,
now in the model's closed helper table.

A uniform environment or interpretation reads as one at `ringModel F G`
(`RelationEnvironment.toOn`, `RelationInterpretation.toOn`), with the same truth
of every application, by the equations at the end of this module. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The closed fold of a definition list over a model. -/
abbrev closedMeaningsOn (model : DomainModel) (definitions : List CheckedDefinition) :
    MeaningsOn model.toCarriers :=
  definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []

variable {snapshot : Snapshot} {imported : Imported snapshot}
variable {application : RelationApplication} {relation : RelationBinding snapshot application}

/-- One explicit interpretation environment per imported subject or experiment,
over carriers. -/
structure RelationEnvironmentOn {snapshot : Snapshot} (imported : Imported snapshot) (carriers : Carriers) where
  meanings : (index : Fin snapshot.relations.length) →
    Values carriers.Value (snapshot.relations.get index).inputs → Prop

/-- Invocation at the relation ABI uses the exact retained formula symbol and
the admitted helper table over the model. -/
def FormulaBinding.invokeRelationOn (model : DomainModel) (binding : FormulaBinding imported relation)
    (arguments : Values model.Value relation.declaration.inputs) :
    Closed (Values model.Value relation.declaration.outputs) :=
  invoke (closedMeaningsOn model imported.program.payload.definitions)
    ⟨binding.original.name, .math, relation.declaration.inputs, relation.declaration.outputs⟩ arguments

/-- Opaque meanings are explicit interpretation choices; formula meanings are
fixed by actual invocation over the model. -/
inductive RelationInterpretationOn (imported : Imported snapshot)
    {application : RelationApplication} (relation : RelationBinding snapshot application)
    (model : DomainModel) (environment : RelationEnvironmentOn imported model.toCarriers) where
  | formula (binding : FormulaBinding imported relation)
      (booleanOutput : relation.declaration.outputs = [.boolean])
      (domain predicate : Values model.Value relation.declaration.inputs → Prop)
      (decidablePredicate : DecidablePred predicate)
  | opaque (noFormula : relation.declaration.formula = none)
      (opaqueKind : relation.declaration.kind ≠ "zkc.language.formula/0")

namespace RelationInterpretationOn
variable {model : DomainModel} {environment : RelationEnvironmentOn imported model.toCarriers}

def Holds (interpretation : RelationInterpretationOn imported relation model environment)
    (arguments : Values model.Value relation.declaration.inputs) : Prop :=
  match interpretation with
  | .formula binding booleanOutput _ _ _ => binding.invokeRelationOn model arguments =
      .done (booleanOutput.symm ▸ (Values.cons true .nil))
  | .opaque _ _ => environment.meanings relation.index arguments

def FormulaLaw : RelationInterpretationOn imported relation model environment → Prop
  | .formula binding booleanOutput domain predicate decidablePredicate =>
    ∀ arguments, domain arguments → binding.invokeRelationOn model arguments =
      .done (booleanOutput.symm ▸ (Values.cons (@decide (predicate arguments)
        (decidablePredicate arguments)) .nil))
  | .opaque _ _ => True

def Domain (interpretation : RelationInterpretationOn imported relation model environment)
    (arguments : Values model.Value relation.declaration.inputs) : Prop :=
  match interpretation with
  | .formula _ _ domain _ _ => domain arguments
  | .opaque .. => True

def Predicate (interpretation : RelationInterpretationOn imported relation model environment)
    (arguments : Values model.Value relation.declaration.inputs) : Prop :=
  match interpretation with
  | .formula _ _ _ predicate _ => predicate arguments
  | .opaque _ _ => environment.meanings relation.index arguments

end RelationInterpretationOn

structure InterpretedApplicationOn (owner : ContractBinding imported) (application : RelationApplication)
    (model : DomainModel) (environment : RelationEnvironmentOn imported model.toCarriers) where
  binding : ApplicationBinding owner application
  interpretation : RelationInterpretationOn imported binding.relation model environment

def InterpretedApplicationOn.Holds {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {model : DomainModel} {environment : RelationEnvironmentOn imported model.toCarriers}
    (interpreted : InterpretedApplicationOn owner application model environment)
    (context : ProtocolContext)
    (boundary : BoundaryValuation model.Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments model.Value owner invocation) : Prop :=
  ∃ arguments, interpreted.binding.read context boundary assignments = some arguments ∧
    interpreted.interpretation.Holds arguments

/-- Every retained clause receives an interpretation over the model, including
every residual. -/
structure ContractInterpretationOn (owner : ContractBinding imported) (model : DomainModel)
    (environment : RelationEnvironmentOn imported model.toCarriers) where
  subjects : (index : Fin owner.contract.clauses.length) →
    InterpretedApplicationOn owner (owner.clause index).subject model environment
  residuals : (index : Fin owner.contract.clauses.length) →
    (residual : RelationApplication) → (owner.clause index).residual = some residual →
    InterpretedApplicationOn owner residual model environment
  decisions : (index : Fin owner.contract.clauses.length) →
    (selector : ContractSelector) → (owner.clause index).decision = some selector →
    { typed : BoundarySelector owner.protocol.signature .boolean // typed.erase = selector }

namespace ContractInterpretationOn
variable {owner : ContractBinding imported} {invocation : InvocationCoordinate} {model : DomainModel}
  {environment : RelationEnvironmentOn imported model.toCarriers}
  (interpretation : ContractInterpretationOn owner model environment) (context : ProtocolContext)

def Subject (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation model.Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments model.Value owner invocation) : Prop :=
  (interpretation.subjects index).Holds context boundary assignments

def Residual (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation model.Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments model.Value owner invocation) : Prop :=
  ∃ residual, ∃ selected : (owner.clause index).residual = some residual,
    (interpretation.residuals index residual selected).Holds context boundary assignments

def Accepts (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation model.Value owner.protocol.inputs owner.protocol.outputs) : Prop :=
  ∃ selector, ∃ selected : (owner.clause index).decision = some selector,
    (interpretation.decisions index selector selected).val.read context boundary = some true

end ContractInterpretationOn

/-- One meaning per retained relation over a model: a formula is its actual
helper invocation, otherwise the environment's opaque meaning. -/
def Logical.relationMeaningOn (model : DomainModel)
    (environment : RelationEnvironmentOn imported model.toCarriers)
    (index : Fin snapshot.relations.length)
    (arguments : Values model.Value (snapshot.relations.get index).inputs) : Prop :=
  match (snapshot.relations.get index).formula with
  | some name => ∃ boolean : (snapshot.relations.get index).outputs = [.boolean],
      invoke (closedMeaningsOn model imported.program.payload.definitions)
        ⟨name, .math, (snapshot.relations.get index).inputs, (snapshot.relations.get index).outputs⟩
        arguments = .done (boolean.symm ▸ Values.cons true .nil)
  | none => environment.meanings index arguments

/-! The uniform interpretations read at the uniform model. -/

section Uniform
variable {F G : Type}

/-- A uniform environment as one over the uniform carriers. -/
def RelationEnvironment.toOn (environment : RelationEnvironment imported F G) :
    RelationEnvironmentOn imported (uniformCarriers F G) :=
  ⟨environment.meanings⟩

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem closedMeanings_eq_closedMeaningsOn (definitions : List CheckedDefinition) :
    closedMeanings (F := F) (G := G) definitions = closedMeaningsOn (ringModel F G) definitions := by
  have extend : Evaluation.extendMeanings (F := F) (G := G) SiteObservations.closed =
      Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed :=
    funext fun table => funext
      (Evaluation.extendMeanings_eq_extendMeaningsOn SiteObservations.closed table)
  simp only [closedMeanings, closedMeaningsOn, extend]

theorem FormulaBinding.invokeRelation_eq_invokeRelationOn (binding : FormulaBinding imported relation)
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    binding.invokeRelation arguments = binding.invokeRelationOn (ringModel F G) arguments := by
  unfold FormulaBinding.invokeRelation FormulaBinding.invokeRelationOn
  rw [closedMeanings_eq_closedMeaningsOn]

/-- A uniform relation interpretation as one at the uniform model. -/
def RelationInterpretation.toOn {environment : RelationEnvironment imported F G} :
    RelationInterpretation imported relation F G environment →
      RelationInterpretationOn imported relation (ringModel F G) environment.toOn
  | .formula binding booleanOutput domain predicate decidablePredicate =>
      .formula binding booleanOutput domain predicate decidablePredicate
  | .opaque noFormula opaqueKind => .opaque noFormula opaqueKind

theorem RelationInterpretation.holds_toOn {environment : RelationEnvironment imported F G}
    (interpretation : RelationInterpretation imported relation F G environment)
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    interpretation.toOn.Holds arguments ↔ interpretation.Holds arguments := by
  cases interpretation with
  | formula binding booleanOutput domain predicate decidablePredicate =>
    show binding.invokeRelationOn (ringModel F G) arguments = _ ↔ binding.invokeRelation arguments = _
    rw [FormulaBinding.invokeRelation_eq_invokeRelationOn]
  | «opaque» => exact Iff.rfl

theorem RelationInterpretation.formulaLaw_toOn {environment : RelationEnvironment imported F G}
    (interpretation : RelationInterpretation imported relation F G environment) :
    interpretation.toOn.FormulaLaw ↔ interpretation.FormulaLaw := by
  cases interpretation with
  | formula binding booleanOutput domain predicate decidablePredicate =>
    show (∀ arguments, domain arguments → binding.invokeRelationOn (ringModel F G) arguments = _) ↔
      (∀ arguments, domain arguments → binding.invokeRelation arguments = _)
    simp only [FormulaBinding.invokeRelation_eq_invokeRelationOn]
  | «opaque» => exact Iff.rfl

theorem RelationInterpretation.domain_toOn {environment : RelationEnvironment imported F G}
    (interpretation : RelationInterpretation imported relation F G environment)
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    interpretation.toOn.Domain arguments ↔ interpretation.Domain arguments := by
  cases interpretation <;> exact Iff.rfl

theorem RelationInterpretation.predicate_toOn {environment : RelationEnvironment imported F G}
    (interpretation : RelationInterpretation imported relation F G environment)
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    interpretation.toOn.Predicate arguments ↔ interpretation.Predicate arguments := by
  cases interpretation <;> exact Iff.rfl

/-- A uniform interpreted application as one at the uniform model. -/
def InterpretedApplication.toOn {owner : ContractBinding imported}
    {environment : RelationEnvironment imported F G}
    (interpreted : InterpretedApplication owner application F G environment) :
    InterpretedApplicationOn owner application (ringModel F G) environment.toOn :=
  ⟨interpreted.binding, interpreted.interpretation.toOn⟩

theorem InterpretedApplication.holds_toOn {owner : ContractBinding imported}
    {invocation : InvocationCoordinate} {environment : RelationEnvironment imported F G}
    (interpreted : InterpretedApplication owner application F G environment)
    (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments (assignment F G) owner invocation) :
    interpreted.toOn.Holds context boundary assignments ↔
      interpreted.Holds context boundary assignments := by
  unfold InterpretedApplicationOn.Holds InterpretedApplication.Holds InterpretedApplication.toOn
  exact exists_congr fun arguments =>
    and_congr Iff.rfl (interpreted.interpretation.holds_toOn arguments)

/-- A uniform contract interpretation as one at the uniform model. -/
def ContractInterpretation.toOn {owner : ContractBinding imported}
    {environment : RelationEnvironment imported F G}
    (interpretation : ContractInterpretation owner F G environment) :
    ContractInterpretationOn owner (ringModel F G) environment.toOn where
  subjects index := (interpretation.subjects index).toOn
  residuals index residual selected := (interpretation.residuals index residual selected).toOn
  decisions := interpretation.decisions

theorem ContractInterpretation.subject_toOn {owner : ContractBinding imported}
    {invocation : InvocationCoordinate} {environment : RelationEnvironment imported F G}
    (interpretation : ContractInterpretation owner F G environment) (context : ProtocolContext)
    (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments (assignment F G) owner invocation) :
    interpretation.toOn.Subject context index boundary assignments ↔
      interpretation.Subject context index boundary assignments :=
  (interpretation.subjects index).holds_toOn context boundary assignments

theorem ContractInterpretation.residual_toOn {owner : ContractBinding imported}
    {invocation : InvocationCoordinate} {environment : RelationEnvironment imported F G}
    (interpretation : ContractInterpretation owner F G environment) (context : ProtocolContext)
    (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments (assignment F G) owner invocation) :
    interpretation.toOn.Residual context index boundary assignments ↔
      interpretation.Residual context index boundary assignments := by
  unfold ContractInterpretationOn.Residual ContractInterpretation.Residual
  exact exists_congr fun residual => exists_congr fun selected =>
    (interpretation.residuals index residual selected).holds_toOn context boundary assignments

theorem ContractInterpretation.accepts_toOn {owner : ContractBinding imported}
    {environment : RelationEnvironment imported F G}
    (interpretation : ContractInterpretation owner F G environment) (context : ProtocolContext)
    (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs) :
    interpretation.toOn.Accepts context index boundary ↔
      interpretation.Accepts context index boundary := Iff.rfl

theorem Logical.relationMeaning_eq_relationMeaningOn (environment : RelationEnvironment imported F G)
    (index : Fin snapshot.relations.length)
    (arguments : Values (assignment F G) (snapshot.relations.get index).inputs) :
    Logical.relationMeaning environment index arguments =
      Logical.relationMeaningOn (ringModel F G) environment.toOn index arguments := by
  unfold Logical.relationMeaning Logical.relationMeaningOn
  rw [closedMeanings_eq_closedMeaningsOn]
  rcases (snapshot.relations.get index).formula with _ | name <;> rfl

end Uniform

end Zkc.Source.Structured
