import Zkc.Source.Structured.ContractElaboration
import Mathlib.Algebra.Ring.Int.Defs

open Zkc.Source Zkc.Source.Structured
open Zkc.Source.Structured.ContractElaboration

namespace Tests.ContractElaborationControls
set_option smartUnfolding false

private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def predicate (changed : Bool) : Function :=
  ⟨"predicate", .math, .privateDef, [.boolean, .boolean], [.boolean], none, [], none,
    .block [.instruction (if changed then .booleanNotEqual else .booleanEqual)
      [0, 1] [.boolean] [] ""] (.ret [0])⟩
private def root : Function :=
  ⟨"main", .protocol, .publicDef, [.boolean, .boolean], [.boolean],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["V"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [] (.ret [0])⟩
private def other : Function := { root with name := "other", origin := some (.protocol ⟨"other", []⟩) }
private def spare : Function :=
  { predicate false with name := "spare", body := .block [] (.ret [0]) }
private def relation : Relation :=
  ⟨"Equal", .publicDef, "zkc.language.formula/0", "equality", "0",
    [.boolean, .boolean], [.boolean], ["statement", "witness"], some "predicate"⟩
private def opaqueDeclaration : Relation :=
  { relation with name := "Opaque", kind := "opaque", formula := none }
private def subject : RelationApplication :=
  ⟨"Equal", [⟨.input, 0, "V"⟩, ⟨.input, 1, "P"⟩]⟩
private def clause : ContractClause :=
  ⟨.target, "claim", subject, none, some ⟨.output, 0, "V"⟩⟩
private def secondClause : ContractClause := { clause with name := "second" }
private def snapshot (changed reordered : Bool) : Snapshot :=
  ⟨digest, "main", [], if reordered then [opaqueDeclaration, relation] else [relation, opaqueDeclaration], [],
    if reordered then [.function other, .function spare, .function (predicate changed), .function root]
    else [.function root, .function (predicate changed), .function spare, .function other],
    if reordered then [⟨"other", []⟩, ⟨"main", [secondClause, clause]⟩]
    else [⟨"main", [clause, secondClause]⟩, ⟨"other", []⟩], blsRows⟩

private noncomputable def formulaBody (changed : Bool) : Region dialect [.boolean, .boolean] [.boolean] :=
  if changed then
    .letOp .booleanNotEqual (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
  else
    .letOp .booleanEqual (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
private noncomputable def checkedFormula (changed : Bool) : CheckedDefinition :=
  ⟨"predicate", .math, [.boolean, .boolean], [.boolean], (formulaBody changed).erase,
    formulaBody changed, (formulaBody changed).elaborate_erase⟩
private def spareBody : Region dialect [.boolean, .boolean] [.boolean] := .ret (.cons .here .nil)
private def checkedSpare : CheckedDefinition :=
  ⟨"spare", .math, [.boolean, .boolean], [.boolean], spareBody.erase,
    spareBody, spareBody.elaborate_erase⟩
private def rootBody : Region protocolDialect [.boolean, .boolean] [.boolean] :=
  .ret (.cons .here .nil)
private def checkedRoot (name : String) : CheckedProtocol :=
  ⟨⟨name, ["P", "V"], [.boolean, .boolean], [.boolean], [[0, 1], [0, 1]], [[1]]⟩,
    rootBody.erase, rootBody, rootBody.elaborate_erase⟩
private noncomputable def payload (changed reordered : Bool) : UnitPayload :=
  ⟨if reordered then [checkedSpare, checkedFormula changed] else [checkedFormula changed, checkedSpare],
    if reordered then [checkedRoot "other", checkedRoot "main"]
    else [checkedRoot "main", checkedRoot "other"],
    ⟨if reordered then 1 else 0, by cases reordered <;> decide⟩,
    by cases reordered <;> cases changed <;> decide +kernel,
    by cases reordered <;> cases changed <;> decide +kernel,
    by cases reordered <;> cases changed <;> rfl,
    by cases reordered <;> cases changed <;> decide +kernel,
    by cases reordered <;> cases changed <;> decide +kernel⟩

noncomputable def imported : Imported (snapshot false false) :=
  ⟨⟨snapshot false false, payload false false⟩, by rfl⟩
noncomputable def reordered : Imported (snapshot false true) :=
  ⟨⟨snapshot false true, payload false true⟩, by rfl⟩
noncomputable def changed : Imported (snapshot true false) :=
  ⟨⟨snapshot true false, payload true false⟩, by rfl⟩

noncomputable def owner : ContractBinding imported := by bind_contract
noncomputable def reorderedOwner : ContractBinding reordered := by bind_contract
noncomputable def changedOwner : ContractBinding changed := by bind_contract
noncomputable def namedOther : ContractBinding imported := ContractBinding.ofName imported "other"
theorem named_owner_exact : namedOther.protocol.name = "other" := rfl
noncomputable def application : ApplicationBinding owner subject := by bind_contract
noncomputable def reorderedApplication : ApplicationBinding reorderedOwner subject := by bind_contract
noncomputable def changedApplication : ApplicationBinding changedOwner subject := by bind_contract
noncomputable def formula : FormulaBinding imported application.relation := by bind_contract
noncomputable def reorderedFormula : FormulaBinding reordered reorderedApplication.relation := by bind_contract
noncomputable def changedFormula : FormulaBinding changed changedApplication.relation := by bind_contract

-- These equalities concern actual admitted subjects after changing table order.
theorem owner_reordered : owner.protocol.name = reorderedOwner.protocol.name := rfl
theorem owner_index_moves : owner.ownerIndex.val ≠ reorderedOwner.ownerIndex.val := by decide +kernel
theorem root_index_moves : owner.protocolIndex.val ≠ reorderedOwner.protocolIndex.val := by decide +kernel
theorem relation_index_moves : application.relation.index.val ≠ reorderedApplication.relation.index.val := by decide +kernel
theorem helper_index_moves : formula.helperIndex.val ≠ reorderedFormula.helperIndex.val := by decide +kernel
theorem named_clause_reordered :
    owner.clause (owner.namedClause "claim") = reorderedOwner.clause (reorderedOwner.namedClause "claim") := rfl
theorem formula_reordered : formula.original = reorderedFormula.original := rfl
theorem helper_reordered : formula.definition = reorderedFormula.definition := rfl
theorem selectors_reordered : eraseSelectors application.selectors = eraseSelectors reorderedApplication.selectors := rfl

theorem formula_adequate : formula.Realizes (F := Int) (G := Int) rfl (fun _ => True)
    (fun args => args.get .here = args.get (.there .here)) := by
  intro args _
  cases args with
  | cons first rest =>
    cases rest with
    | cons second rest => cases rest; rfl

-- Same name and ABI still bind; the old mathematical law becomes false.
theorem changed_same_abi : changedFormula.definition.helper = formula.definition.helper := rfl
theorem changed_rejects_old_law : ¬ changedFormula.Realizes (F := Int) (G := Int)
    rfl (fun _ => True) (fun args => args.get .here = args.get (.there .here)) := by
  intro oldLaw
  have impossible := oldLaw (.cons false (.cons false .nil)) trivial
  cases impossible

example : True := by
  fail_if_success
    have ambiguous : RelationBinding
        { snapshot false false with relations := [relation, relation] } subject := by bind_contract
  fail_if_success
    have oldLaw : changedFormula.Realizes (F := Int) (G := Int)
        rfl (fun _ => True) (fun args => args.get .here = args.get (.there .here)) := formula_adequate
  -- The tactic does not solve semantic goals, even a trivial predicate.
  fail_if_success bind_contract
  trivial

-- Missing and duplicate names, including identical duplicates, are refused.
example : uniqueIndex? ["a", "b"] id "missing" = none := rfl
example : uniqueIndex? ["a", "a"] id "a" = none := rfl
example : uniqueIndex? ["b", "a"] id "a" = some ⟨1, by decide⟩ := rfl
example : originalFunction? (snapshot false false) none = none := rfl
example : originalFunction? (snapshot false false) (some "missing") = none := rfl
example : originalFunction? { snapshot false false with
    definitions := [.function (predicate false), .function (predicate false)] }
    (some "predicate") = none := rfl

-- An ABI or helper-kind change is rejected before an Imported binding exists.
example : checkFormulaLinks { snapshot false false with
    definitions := [.function { predicate false with inputs := [.boolean, .index] }] } =
    .error "structured-relation-formula" := rfl
example : checkFormulaLinks { snapshot false false with
    definitions := [.function { predicate false with outputs := [.index] }] } =
    .error "structured-relation-formula" := rfl
example : checkFormulaLinks { snapshot false false with
    definitions := [.function { predicate false with kind := .local }] } =
    .error "structured-relation-formula" := rfl

-- A different valid participant copy binds to that copy, never to the old one.
noncomputable def otherCopy : ApplicationBinding owner
    ⟨"Equal", [⟨.input, 0, "P"⟩, ⟨.input, 1, "P"⟩]⟩ := by bind_contract
theorem changed_role_observed : eraseSelectors otherCopy.selectors ≠ eraseSelectors application.selectors := by
  decide +kernel
example : True := by
  fail_if_success
    have wrongCopy : ApplicationBinding owner
        ⟨"Equal", [⟨.input, 0, "P"⟩, ⟨.input, 1, "P"⟩]⟩ := application
  trivial

private def signature : ProtocolSignature :=
  ⟨"main", ["P", "V"], [.boolean, .index], [.boolean], [[0, 1], [0]], [[1]]⟩

-- Complete type, direction, port, role and scope are required by decoding.
example : (selector? signature .boolean ⟨.input, 0, "V"⟩).isSome = true := rfl
example : (selector? signature .boolean ⟨.input, 1, "P"⟩).isSome = false := rfl
example : (selector? signature .index ⟨.input, 1, "V"⟩).isSome = false := rfl
example : (selector? signature .boolean ⟨.input, 9, "V"⟩).isSome = false := rfl
example : (selector? signature .boolean ⟨.input, 0, "X"⟩).isSome = false := rfl
example : (selector? signature .boolean ⟨.output, 0, "P"⟩).isSome = false := rfl
example : (selector? { signature with roles := ["V", "V"] }
    .boolean ⟨.input, 0, "V"⟩).isSome = false := rfl
example : (selectors? signature [.boolean] []).isSome = false := rfl
example : (selectors? signature [] [⟨.input, 0, "V"⟩]).isSome = false := rfl

-- Invalid requests cannot elaborate to bindings, even at a valid admitted owner.
example : True := by
  fail_if_success
    have missing : RelationBinding (snapshot false false) ⟨"Missing", []⟩ := by bind_contract
  fail_if_success
    have missingOwner : ContractBinding imported := ContractBinding.ofName imported "Missing"
  fail_if_success
    have missingClause := owner.namedClause "Missing"
  fail_if_success
    have wrongRole : ApplicationBinding owner ⟨"Equal", [⟨.input, 0, "X"⟩, ⟨.input, 1, "P"⟩]⟩ := by bind_contract
  fail_if_success
    have missingArgument : ApplicationBinding owner ⟨"Equal", []⟩ := by bind_contract
  fail_if_success
    have unavailableOutput : ApplicationBinding owner ⟨"Equal", [⟨.output, 0, "P"⟩, ⟨.input, 1, "P"⟩]⟩ := by bind_contract
  trivial

noncomputable def opaqueRelation : RelationBinding (snapshot false false) ⟨"Opaque", []⟩ := by bind_contract
example : True := by
  fail_if_success
    have missingFormula : FormulaBinding imported opaqueRelation := by bind_contract
  trivial

end Tests.ContractElaborationControls
