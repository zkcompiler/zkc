import ZkcSecurity.Tools.PairConstruction
import ZkcSecurity.Tools.SigmaReadback
import ZkcSecurity.Claims.SubjectABI
import ZkcSecurity.Claims.PrimitiveDependencies
import Zkc.Source.Structured.UnitViews
import Mathlib.Algebra.Ring.Int.Defs

set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

noncomputable section

namespace TestsSecurity.RetainedOpaqueTargets
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims

private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def input : ContractClause :=
  ⟨.input, "honest", ⟨"Truth", [⟨.input, 0, "P", false⟩]⟩, none, none⟩
private def target (role : String) : ContractClause :=
  ⟨.target, "truth", ⟨"Truth", [⟨.input, 0, role, false⟩]⟩, none, some ⟨.output, 0, "V", false⟩⟩
private def declaration : Relation :=
  ⟨"Truth", .publicDef, "example.boolean/0", "truth", "1", [.boolean], [.boolean],
    ["statement"], none, [.index, .natural "7"]⟩
private def formulaDeclaration : Relation :=
  { declaration with
    kind := "zkc.language.formula/0"
    key := "identity"
    revision := "0"
    formula := some "identity"
    staticArguments := [] }
private def original (relation : Relation) (role : String := "V") : Snapshot :=
  ⟨digest, "main", [], [relation], [],
    [.function ⟨"identity", .math, .privateDef, [.boolean], [.boolean], none, [], none,
      .block [] (.ret [0])⟩,
     .function ⟨"main", .protocol, .publicDef, [.boolean, .service scalarServiceContract], [.boolean],
      some ⟨["P", "V"], [["P", "V"], ["V"]], [["V"]]⟩, [], some (.protocol ⟨"main", []⟩),
      .block [] (.ret [0])⟩],
    [⟨"main", [input, target role]⟩], blsRows, {}⟩
private abbrev identityHelper : Helper := ⟨"identity", .math, [.boolean], [.boolean]⟩
private def identityBody : Region dialect identityHelper.inputs identityHelper.outputs :=
  .ret (.cons .here .nil)
private def mainSignature : ProtocolSignature :=
  ⟨"main", ["P", "V"], [.boolean, .service scalarServiceContract], [.boolean],
    [[0, 1], [1]], [[1]]⟩
private def mainBody : Region protocolDialect mainSignature.inputs mainSignature.outputs :=
  .ret (.cons .here .nil)
namespace OpaqueUnit
structured_views (original declaration)
  helpers [identity := identity]
  protocols [main := main]
end OpaqueUnit
namespace FormulaUnit
structured_views (original formulaDeclaration)
  helpers [identity := identity]
  protocols [main := main]
end FormulaUnit
private abbrev imported := OpaqueUnit.imported
private abbrev formulaImported := FormulaUnit.imported
private def policy : Policy :=
  ⟨"main", "P", "V", 0, "suite", [1], [0], [], "zkc.framed/0", ""⟩
private def producer : Participant :=
  { source := digest, candidate := digest, policy, symbol := "producer",
    inputs := [.data .boolean, .transcript "suite"],
    outputs := [.transcript "suite"], instructions := [], returned := [1] }
private def validator : Participant :=
  { source := digest, candidate := digest, policy, symbol := "validator",
    inputs := [.data .boolean, .transcript "suite"],
    outputs := [.data .boolean, .transcript "suite"], instructions := [], returned := [0, 1] }
private def artifacts : AuthoredPair.Artifacts := ⟨producer, validator⟩
private def selected : AuthoredPair.Selection (original declaration) :=
  (AuthoredPair.select _ artifacts "truth").toOption.get (by decide +kernel)
private def formulaSelected : AuthoredPair.Selection (original formulaDeclaration) :=
  (AuthoredPair.select _ artifacts "truth").toOption.get (by decide +kernel)
private def model := ringModel Int Int
private def instanceMeaning : OpaqueInstance model.Value :=
  ⟨[.boolean], [.boolean], ["statement"], fun arguments => arguments.get .here = true⟩
private def family : OpaqueFamily model.Value :=
  ⟨declaration.opaqueIdentity.family, fun arguments =>
    if arguments = declaration.staticArguments then some instanceMeaning else none⟩
private def registeredFamilies : OpaqueRegistry model.Value := ⟨[family], by decide +kernel⟩

/-- The actual pair builder selects both opaque input and target clauses. -/
def subject : HonestPair.Subject model (original declaration) imported selected := by
  bind_authored_subject "truth" with_registry registeredFamilies exports digest, digest, digest

-- The builder also works before choosing concrete mathematical carriers.
private def familiesOn (selectedModel : DomainModel) : OpaqueRegistry selectedModel.Value :=
  ⟨[⟨declaration.opaqueIdentity.family, fun arguments =>
    if arguments = declaration.staticArguments then
      some ⟨[.boolean], [.boolean], ["statement"], fun values => values.get .here = true⟩
    else none⟩], by simp⟩
def genericSubject (selectedModel : DomainModel) :
    HonestPair.Subject selectedModel (original declaration) imported selected := by
  bind_authored_subject "truth" with_registry (familiesOn selectedModel) exports digest, digest, digest

private def formulaSubject : HonestPair.Subject model (original formulaDeclaration)
    formulaImported formulaSelected := by
  bind_authored_subject "truth" exports digest, digest, digest
private def formula : FormulaBinding formulaImported formulaSubject.target.application.relation := by bind_contract

private def inputs (value : Bool) : subject.Inputs := .cons (some value) (.cons none .nil)
private def statement (value : Bool) : subject.validatorArtifacts.Statement model := .cons value .nil
private def noWitness : subject.validatorSubject.Witness := fun _ _ => none

theorem opaque_relation (value : Bool) : subject.Relation (inputs value) ↔ value = true := by
  change (∃ arguments : Values model.Value [.boolean],
    some (.cons value .nil) = some arguments ∧ arguments.get .here = true) ↔ _
  simp only [Option.some.injEq]
  constructor
  · rintro ⟨arguments, rfl, truth⟩; exact truth
  · exact fun truth => ⟨.cons value .nil, rfl, truth⟩

-- A valid selector read does not turn a registered opaque relation into a
-- formula. Formula-specific automation must leave this library fact intact.
private def opaqueArguments (value : Bool) : Values model.Value [.boolean] := .cons value .nil

example (value : Bool) (related : subject.Relation (inputs value)) : value = true := by
  have read : subject.target.application.read {} (subject.boundary (inputs value))
      (subject.assignments (inputs value)) = some (opaqueArguments value) := rfl
  fail_if_success
    prepare_sigma_relation for subject reading read
  exact (opaque_relation value).mp related

theorem opaque_domain (value : Bool) (witness : subject.validatorSubject.Witness) :
    subject.validatorSubject.Holds (statement value) witness ↔ value = true := by
  apply (subject.validatorSubject.holds_iff_of_read _ witness (.cons value .nil) (by rfl)).trans
  rfl

-- The actual input clause remains a separate, mandatory honest-input condition.
theorem opaque_input : ¬ subject.inputClause (inputs false) ⟨0, by decide⟩ rfl := by
  change ¬ ∃ arguments : Values model.Value [.boolean],
    some (.cons false .nil) = some arguments ∧ arguments.get .here = true
  rintro ⟨arguments, same, truth⟩
  cases Option.some.inj same
  exact Bool.false_ne_true truth

example : ¬ subject.HonestInput (inputs false) := fun honest => opaque_input (honest.2.1 _ rfl)
example : subject.validatorSubject.Holds (statement true) noWitness := (opaque_domain true _).mpr rfl
example : subject.validatorSubject.FalseStatement (statement false) := by
  rintro ⟨witness, truth⟩
  exact Bool.false_ne_true ((opaque_domain false witness).mp truth)

-- The formula path retains the complete invocation, not a mathematical fallback.
theorem formula_equivalence (value : Bool) (witness : formulaSubject.validatorSubject.Witness) :
    formulaSubject.validatorSubject.Holds (.cons value .nil) witness ↔
      formula.invokeRelationOn model (.cons value .nil) = .done (.cons true .nil) :=
  formulaSubject.validatorSubject.holds_iff_of_read _ witness _ (by rfl)

-- An admitted partial Math helper really stops on an out-of-range read.
private def partialDeclaration : Relation :=
  ⟨"PartialTruth", .publicDef, "zkc.language.formula/0", "partial", "0",
    [.vector scalarDomain, .index], [.boolean], ["statement", "statement"], some "partial", []⟩
private def stoppedOriginal : Snapshot :=
  { (original formulaDeclaration) with
    relations := [formulaDeclaration, partialDeclaration]
    definitions := [.function ⟨"partial", .math, .privateDef,
      [.vector scalarDomain, .index], [.boolean], none, [⟨1, 0, 0⟩], none,
      .block [.instruction (.boundedAt scalarDomain) [0, 1] [.field scalarDomain] [] "",
        .instruction (.fieldEqual scalarDomain) [0, 0] [.boolean] [] ""] (.ret [0])⟩] ++
      (original formulaDeclaration).definitions }
private abbrev partialHelper : Helper :=
  ⟨"partial", .math, [.vector scalarDomain, .index], [.boolean]⟩
private def partialBody : Region dialect partialHelper.inputs partialHelper.outputs :=
  .letOp (.boundedAt scalarDomain) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.fieldEqual scalarDomain) (.cons .here (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)
namespace StoppedUnit
structured_views stoppedOriginal
  helpers [identity := identity, partialRead := (partialHelper, partialBody)]
  protocols [main := main]
end StoppedUnit
private def stoppedRelation : RelationBinding stoppedOriginal ⟨"PartialTruth", []⟩ := by bind_contract
private def stoppedFormula : FormulaBinding StoppedUnit.imported stoppedRelation := by bind_contract
theorem stopped_formula :
    ¬ (RelationMeaning.formula stoppedFormula : RelationMeaning StoppedUnit.imported
      stoppedRelation model.Value OpaqueRegistry.empty).HoldsOn rfl (.cons [] (.cons 0 .nil)) := by
  intro impossible
  cases impossible

example : checkRetainedMeaning subject.meaning = .ok () := rfl
example : checkRetainedMeaning formulaSubject.meaning =
    checkDefaultRelation formulaImported.program.payload.definitions formula.definition.helper := rfl

-- Each identity coordinate and the complete ordered ABI must resolve exactly.
example : (registeredFamilies.resolve { declaration with kind := "other/0" }).isNone = true := by decide +kernel
example : (registeredFamilies.resolve { declaration with key := "other" }).isNone = true := by decide +kernel
example : (registeredFamilies.resolve { declaration with revision := "2" }).isNone = true := by decide +kernel
example : (registeredFamilies.resolve { declaration with staticArguments := [.natural "7", .index] }).isNone = true := by decide +kernel
example : (registeredFamilies.resolve { declaration with staticArguments := [.index, .natural "8"] }).isNone = true := by decide +kernel
example : (registeredFamilies.resolve { declaration with inputs := [.index] }).isNone = true := by decide +kernel
example : (registeredFamilies.resolve { declaration with outputs := [.index] }).isNone = true := by decide +kernel
example : (registeredFamilies.resolve { declaration with purposes := ["witness"] }).isNone = true := by decide +kernel
example : (OpaqueRegistry.empty (Value := model.Value)).check [declaration] = false := by decide +kernel

-- A registry with the same identity but a different body defines a different request.
private def otherInstance : OpaqueInstance model.Value := { instanceMeaning with holds := fun _ => False }
private def otherRegistry : OpaqueRegistry model.Value :=
  ⟨[{ family with instantiate := fun _ => some otherInstance }], by decide +kernel⟩
private def otherBinding : OpaqueRegistry.Binding otherRegistry subject.target.application.relation.declaration :=
  (otherRegistry.resolve _).get (by decide +kernel)

example : True := by
  fail_if_success
    have : RelationMeaning imported subject.target.application.relation model.Value subject.relations.registry :=
      .opaque otherBinding
  trivial

-- The selected proof cannot replace the registered predicate, even at the same ABI.
example : True := by
  fail_if_success
    have : OpaqueRegistry.Binding registeredFamilies declaration :=
      { instantiation := otherInstance, selected := rfl, inputs := rfl, outputs := rfl,
        purposes := rfl, opaqueKind := rfl, noFormula := rfl }
  trivial

example : True := by
  fail_if_success
    have : HonestPair.Subject model (original declaration) imported selected := by
      bind_authored_subject "truth" exports digest, digest, digest
  trivial

-- An available source port at the wrong role still fails the publication policy.
namespace WrongSelectorUnit
structured_views (original declaration "P")
  helpers [identity := identity]
  protocols [main := main]
end WrongSelectorUnit
private abbrev wrongImported := WrongSelectorUnit.imported
example : True := by
  fail_if_success
    have : RetainedTarget wrongImported policy [.boolean] := by bind_target "truth"
  trivial

#print axioms subject
#print axioms genericSubject
#print axioms opaque_relation
#print axioms opaque_domain
#print axioms opaque_input
#print axioms formula_equivalence
#print axioms stopped_formula
#print axioms Zkc.Source.Structured.RelationMeaning.unique_meaning
#print axioms Zkc.Construction.RetainedTarget.holds_formula_iff
end TestsSecurity.RetainedOpaqueTargets
