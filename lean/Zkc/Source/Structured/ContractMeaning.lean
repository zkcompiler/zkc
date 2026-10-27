module

public import Zkc.Source.Structured.ContractBoundary
public import Zkc.Source.Structured.OpaqueRegistry

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Structured

variable {snapshot : Snapshot} {imported : Imported snapshot}
variable {application : RelationApplication} {relation : RelationBinding snapshot application}
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- One registered interpretation environment per imported subject/experiment.
Every opaque declaration resolves to its family instance before evidence.
Formula meanings ignore this environment and remain actual helper invocation. -/
abbrev RelationEnvironment {snapshot : Snapshot} (_imported : Imported snapshot) (F G : Type) :=
  RegisteredRelations (assignment F G) snapshot.relations

/-- Invocation at the relation ABI uses the exact retained formula symbol and
admitted helper table; it is not an externally chosen predicate. -/
def FormulaBinding.invokeRelation (binding : FormulaBinding imported relation)
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    Closed (Values (assignment F G) relation.declaration.outputs) :=
  invoke (closedMeanings imported.program.payload.definitions)
    ⟨binding.original.name, .math, relation.declaration.inputs, relation.declaration.outputs⟩ arguments

/-- Reuse the existing exact-body association law at the relation ABI. The
caller supplies only a typed view of the actual retained raw body. -/
theorem FormulaBinding.invokeRelation_body_view (binding : FormulaBinding imported relation)
    (body : Region dialect relation.declaration.inputs relation.declaration.outputs)
    (exactRaw : binding.definition.raw = body.erase)
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    binding.invokeRelation arguments = body.denote
      (meaning F G (closedMeanings imported.program.payload.definitions)) arguments.get :=
  (BodyIn.of_mem (List.get_mem ..) binding.signature_eq exactRaw).invoke
    imported.program.payload.linked arguments

/-- Opaque meanings are fixed by the admitted registry. Formula meanings are
fixed by actual invocation; domain/predicate data describe a proposed local law,
whose proof is required separately by the obligation record. -/
inductive RelationInterpretation (imported : Imported snapshot)
    {application : RelationApplication} (relation : RelationBinding snapshot application)
    (F G : Type) [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (environment : RelationEnvironment imported F G) where
  | formula (binding : FormulaBinding imported relation)
      (booleanOutput : relation.declaration.outputs = [.boolean])
      (domain predicate : Values (assignment F G) relation.declaration.inputs → Prop)
      (decidablePredicate : DecidablePred predicate)
  | opaque (noFormula : relation.declaration.formula = none)
      (opaqueKind : relation.declaration.isOpaque = true)

namespace RelationInterpretation
variable {environment : RelationEnvironment imported F G}

def Holds (interpretation : RelationInterpretation imported relation F G environment)
    (arguments : Values (assignment F G) relation.declaration.inputs) : Prop :=
  match interpretation with
  | .formula binding booleanOutput _ _ _ => binding.invokeRelation arguments =
      .done (booleanOutput.symm ▸ (Values.cons true .nil))
  | .opaque _ _ => environment.meanings relation.index arguments

/-- This local formula obligation includes explicit preconditions/domain. It
never claims that a refused invocation is a completed false result. -/
def FormulaLaw : RelationInterpretation imported relation F G environment → Prop
  | .formula binding booleanOutput domain predicate decidablePredicate =>
    ∀ arguments, domain arguments → binding.invokeRelation arguments =
      .done (booleanOutput.symm ▸ (Values.cons (@decide (predicate arguments)
        (decidablePredicate arguments)) .nil))
  | .opaque _ _ => True

def Domain (interpretation : RelationInterpretation imported relation F G environment)
    (arguments : Values (assignment F G) relation.declaration.inputs) : Prop :=
  match interpretation with
  | .formula _ _ domain _ _ => domain arguments
  | .opaque .. => True

def Predicate (interpretation : RelationInterpretation imported relation F G environment)
    (arguments : Values (assignment F G) relation.declaration.inputs) : Prop :=
  match interpretation with
  | .formula _ _ _ predicate _ => predicate arguments
  | .opaque _ _ => environment.meanings relation.index arguments

/-- A formula-domain proof is used at the actual arguments when translating
invocation truth to mathematical truth. A vacuous domain supplies no such use. -/
theorem holds_iff_predicate (interpretation : RelationInterpretation imported relation F G environment)
    (law : interpretation.FormulaLaw)
    (arguments : Values (assignment F G) relation.declaration.inputs)
    (domain : interpretation.Domain arguments) :
    interpretation.Holds arguments ↔ interpretation.Predicate arguments := by
  cases interpretation with
  | «opaque» => rfl
  | formula binding booleanOutput admissible predicate decidablePredicate =>
    change binding.invokeRelation arguments = .done (booleanOutput.symm ▸ Values.cons true .nil) ↔ predicate arguments
    rw [law arguments domain]
    let := decidablePredicate
    constructor
    · intro same
      have values := PIR.Process.done.inj same
      have uncast := congrArg (fun value => booleanOutput ▸ value) values
      have cancel {types : List Ty} (eq : types = [.boolean])
          (values : Values (assignment F G) [.boolean]) : eq ▸ (eq.symm ▸ values) = values := by
        cases eq; rfl
      simp only [cancel] at uncast
      have booleans := congrArg (fun value : Values (assignment F G) [.boolean] => value.get .here) uncast
      exact of_decide_eq_true booleans
    · intro truth
      simp [truth]

end RelationInterpretation

structure InterpretedApplication (owner : ContractBinding imported) (application : RelationApplication)
    (F G : Type) [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (environment : RelationEnvironment imported F G) where
  binding : ApplicationBinding owner application
  interpretation : RelationInterpretation imported binding.relation F G environment

namespace InterpretedApplication
variable {owner : ContractBinding imported} {invocation : InvocationCoordinate}
variable {environment : RelationEnvironment imported F G}

/-- Argument existence is visible. The existential here only packages the unique
ordered read result; it does not choose a fresh witness for this clause. -/
def Holds (interpreted : InterpretedApplication owner application F G environment)
    (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments (assignment F G) owner invocation) : Prop :=
  ∃ arguments, interpreted.binding.read context boundary assignments = some arguments ∧
    interpreted.interpretation.Holds arguments

end InterpretedApplication

/-- Every retained clause receives an interpretation, including every residual.
All clauses share the same boundary and the same parameter/witness assignments. -/
structure ContractInterpretation (owner : ContractBinding imported) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (environment : RelationEnvironment imported F G) where
  subjects : (index : Fin owner.contract.clauses.length) →
    InterpretedApplication owner (owner.clause index).subject F G environment
  residuals : (index : Fin owner.contract.clauses.length) →
    (residual : RelationApplication) → (owner.clause index).residual = some residual →
    InterpretedApplication owner residual F G environment
  decisions : (index : Fin owner.contract.clauses.length) →
    (selector : ContractSelector) → (owner.clause index).decision = some selector →
    { typed : BoundarySelector owner.protocol.signature .boolean // typed.erase = selector }

namespace ContractInterpretation
variable {owner : ContractBinding imported} {invocation : InvocationCoordinate}
  {environment : RelationEnvironment imported F G}
  (interpretation : ContractInterpretation owner F G environment) (context : ProtocolContext)

def Subject (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments (assignment F G) owner invocation) : Prop :=
  (interpretation.subjects index).Holds context boundary assignments

def Residual (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments (assignment F G) owner invocation) : Prop :=
  ∃ residual, ∃ selected : (owner.clause index).residual = some residual,
    (interpretation.residuals index residual selected).Holds context boundary assignments

def Accepts (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs) : Prop :=
  ∃ selector, ∃ selected : (owner.clause index).decision = some selector,
    (interpretation.decisions index selector selected).val.read context boundary = some true

end ContractInterpretation

end Zkc.Source.Structured
