import Zkc.Source.Structured.ContractObligations
import Zkc.Source.Structured.ContractEntry
import Mathlib.Algebra.Ring.Int.Defs

open Zkc.Source Zkc.Source.Structured

namespace Tests.StructuredContracts
set_option smartUnfolding false

private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def predicate : Function :=
  ⟨"predicate", .math, .privateDef, [.boolean, .boolean], [.boolean], none, [], none,
    .block [.instruction .booleanEqual [0, 1] [.boolean] [] ""] (.ret [0])⟩
private def root : Function :=
  ⟨"main", .protocol, .publicDef, [.boolean, .boolean], [.boolean, .boolean],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["V"], ["V"]]⟩, [], none,
    .block [.instruction .booleanEqual [0, 1] [.boolean] [] ""] (.ret [0, 1])⟩
private def caller : Function :=
  ⟨"caller", .protocol, .publicDef, [.boolean, .boolean], [.boolean, .boolean],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["P"], ["P"]]⟩, [], none,
    .block [.instruction (.protocolApply "main" ["V", "P"]) [1, 0] [.boolean, .boolean] [] "invoke"]
      (.ret [0, 1])⟩
private def relation : Relation :=
  ⟨"Equal", .publicDef, "zkc.language.formula/0", "equality", "0", [.boolean, .boolean], [.boolean],
    ["statement", "witness"], some "predicate"⟩
private def subject : RelationApplication := ⟨"Equal", [⟨.input, 0, "V"⟩, ⟨.input, 1, "P"⟩]⟩
private def copiedSubject : RelationApplication := ⟨"Equal", [⟨.input, 0, "P"⟩, ⟨.input, 1, "P"⟩]⟩
private def clause : ContractClause := ⟨.target, "claim", subject, none, some ⟨.output, 0, "V"⟩⟩
private def copiedClause : ContractClause := ⟨.target, "copiedClaim", copiedSubject, none, some ⟨.output, 0, "V"⟩⟩
private def residual : RelationApplication :=
  ⟨"Equal", [⟨.output, 0, "V"⟩, ⟨.output, 1, "V"⟩]⟩
private def continuation : ContractClause :=
  ⟨.continuation, "carry", subject, some residual, some ⟨.output, 0, "V"⟩⟩
private def snapshot : Snapshot :=
  ⟨digest, "main", [], [relation], [], [.function root, .function predicate, .function caller],
    [⟨"main", [clause, continuation, copiedClause]⟩, ⟨"caller", []⟩], blsRows⟩
private def admits (snapshot : Snapshot) := (check snapshot).isOk
private def withClause (changed : ContractClause) : Snapshot :=
  { snapshot with contracts := [⟨"main", [changed]⟩, ⟨"caller", []⟩] }
private def withRelation (changed : Relation) : Snapshot := { snapshot with relations := [changed] }

private def admissionControls : List (String × Bool) := [
    ("valid-complete-owner-table", admits snapshot == true),
    ("missing-owner-table", admits { snapshot with contracts := [] } == false),
    ("duplicate-owners", admits { snapshot with contracts := snapshot.contracts ++ snapshot.contracts } == false),
    ("nonprotocol-owner", admits { snapshot with contracts := [⟨"predicate", [clause]⟩] } == false),
    ("duplicate-clauses", admits { snapshot with contracts := [⟨"main", [clause, clause]⟩] } == false),
    ("target-without-decision", admits (withClause { clause with decision := none }) == false),
    ("input-decision", admits (withClause { clause with decision := some ⟨.input, 0, "V"⟩ }) == false),
    ("unavailable-decision-role", admits (withClause { clause with decision := some ⟨.output, 0, "P"⟩ }) == false),
    ("decision-out-of-range", admits (withClause { clause with decision := some ⟨.output, 2, "V"⟩ }) == false),
    ("unknown-subject", admits (withClause { clause with subject := ⟨"Missing", subject.selectors⟩ }) == false),
    ("unknown-selector-role", admits (withClause { clause with subject := ⟨"Equal", [⟨.input, 0, "X"⟩, ⟨.input, 1, "P"⟩]⟩ }) == false),
    ("input-with-decision", admits (withClause { clause with kind := .input }) == false),
    ("output-without-output-selector", admits (withClause { clause with kind := .output }) == false),
    ("continuation-without-residual", admits (withClause { clause with kind := .continuation }) == false),
    ("target-with-residual", admits (withClause { clause with residual := some subject }) == false),
    ("formula-missing-link", admits (withRelation { relation with formula := none }) == false),
    ("formula-protocol-helper", admits (withRelation { relation with formula := some "main" }) == false),
    ("formula-missing-helper", admits (withRelation { relation with formula := some "missing" }) == false),
    ("formula-input-abi", admits (withRelation { relation with inputs := [.boolean], purposes := ["statement"] }) == false),
    ("opaque-with-formula-link", admits (withRelation { relation with kind := "opaque" }) == false)]

#eval do
  let mut failed := 0
  for (name, passed) in admissionControls do
    if !passed then
      IO.println s!"FAIL: {name}"
      failed := failed + 1
  if failed != 0 then throw (IO.userError s!"{failed} contract admission controls failed")
  IO.println s!"structured contracts: {admissionControls.length} admission controls passed"

private def refusal {α : Type} (result : Except String α) (expected : String) : Bool :=
  match result with | .error code => code == expected | .ok _ => false
private def signature : ProtocolSignature :=
  ⟨"main", ["P", "V"], [.boolean, .boolean], [.boolean, .boolean], [[0, 1], [0, 1]], [[1], [1]]⟩

private def runDiagnostics : IO Unit := do
  let controls : List (String × Bool) := [
    ("owners", refusal (checkContracts {snapshot with contracts := []} [signature]) "structured-contract-owners"),
    ("table-limit", refusal (checkContracts {snapshot with contracts := List.replicate 129 ⟨"main", []⟩} [signature]) "structured-contract-limit"),
    ("clause-limit", refusal (checkContracts {snapshot with contracts := [⟨"main", List.replicate 513 clause⟩]} [signature]) "structured-contract-limit"),
    ("duplicate", refusal (checkContracts {snapshot with contracts := [⟨"main", [clause, clause]⟩]} [signature]) "structured-contract-duplicate"),
    ("name", refusal ({clause with name := ""}.check snapshot signature) "structured-contract-name"),
    ("name-limit", refusal ({clause with name := String.ofList (List.replicate 513 'a')}.check snapshot signature) "structured-contract-name"),
    ("name-space", ({clause with name := "two words"}.check snapshot signature).isOk),
    ("name-dot", ({clause with name := "claim.part"}.check snapshot signature).isOk),
    ("name-unicode", ({clause with name := "증명"}.check snapshot signature).isOk),
    ("port", refusal ((⟨.input, 99, "P"⟩ : ContractSelector).resolve signature) "structured-contract-port"),
    ("role-copy", refusal ((⟨.output, 0, "P"⟩ : ContractSelector).resolve signature) "structured-contract-role"),
    ("service", refusal ((⟨.input, 0, "P"⟩ : ContractSelector).resolve
      {signature with inputs := [.service scalarServiceContract]}) "structured-contract-service"),
    ("unknown-relation", refusal ((⟨"missing", []⟩ : RelationApplication).check snapshot signature) "structured-contract-relation"),
    ("arguments", refusal ((⟨"Equal", []⟩ : RelationApplication).check snapshot signature) "structured-contract-arguments"),
    ("selector-limit", refusal ((⟨"Equal", List.replicate 513 ⟨.input, 0, "P"⟩⟩ : RelationApplication).check snapshot signature) "structured-contract-limit"),
    ("direction", refusal ({clause with kind := .output}.check snapshot signature) "structured-contract-direction"),
    ("residual", refusal ({clause with kind := .continuation}.check snapshot signature) "structured-contract-residual"),
    ("decision", refusal ({clause with decision := none}.check snapshot signature) "structured-contract-decision"),
    ("decision-type", refusal (clause.check snapshot {signature with outputs := [.field scalarDomain]}) "structured-contract-decision"),
    ("formula", refusal (checkFormulaLinks (withRelation {relation with formula := none})) "structured-relation-formula"),
    ("formula-input-abi", refusal (checkFormulaLinks { snapshot with
      definitions := [.function {predicate with inputs := [.boolean, .index]}] }) "structured-relation-formula"),
    ("formula-output-abi", refusal (checkFormulaLinks { snapshot with
      definitions := [.function {predicate with outputs := [.boolean, .boolean]}] }) "structured-relation-formula"),
    ("formula-nonmath", refusal (checkFormulaLinks { snapshot with
      definitions := [.function {predicate with kind := .local}] }) "structured-relation-formula")]
  for (name, passed) in controls do
    if !passed then throw (IO.userError s!"contract diagnostic failed: {name}")
  IO.println s!"structured contracts: {controls.length} exact diagnostic controls passed"

#eval runDiagnostics

private def arr (values : List Lean.Json) := Lean.Json.arr values.toArray
private def wire : List Lean.Json := [.str "zkc.structured-source/0", .str "original",
  .str digest, .str "main", arr [], arr [], arr [], arr [], arr [], arr [arr [], arr []]]
private def selectorWire : Lean.Json := arr [.str "input", Lean.toJson (0 : Nat), .str "P"]
private def applicationWire := arr [.str "Equal", arr [selectorWire]]
private def clauseWire := arr [.str "target", .str "claim", applicationWire, .null,
  arr [.str "output", Lean.toJson (0 : Nat), .str "V"]]
private def relationWire : List Lean.Json := [.str "relation", .str "Equal", .str "public",
  .str "zkc.language.formula/0", .str "equality", .str "0", arr [arr [.str "bool"]],
  arr [arr [.str "bool"]], arr [.str "statement"], .str "predicate"]

private def runWire : IO Unit := do
  let controls : List (String × Bool) := [
    ("ten", (Format.snapshot (arr wire)).isOk),
    ("nine-refused", refusal (Format.snapshot (arr (wire.take 9))) "structured-envelope"),
    ("eleven-refused", refusal (Format.snapshot (arr (wire ++ [Lean.Json.null]))) "structured-envelope"),
    ("formula-field", (Format.relation (arr relationWire)).isOk),
    ("relation-missing", refusal (Format.relation (arr (relationWire.take 9))) "structured-relation"),
    ("relation-extra", refusal (Format.relation (arr (relationWire ++ [Lean.Json.null]))) "structured-relation"),
    ("formula-type", refusal (Format.relation (arr (relationWire.set 9 (.bool true)))) "structured-string"),
    ("formula-empty", refusal (Format.relation (arr (relationWire.set 9 (.str "")))) "structured-string"),
    ("selector", (Format.contractSelector selectorWire).isOk),
    ("selector-shape", refusal (Format.contractSelector (arr [.str "input", Lean.toJson (0 : Nat), .str "P", .null])) "structured-contract-selector"),
    ("selector-direction", refusal (Format.contractSelector (arr [.str "other", Lean.toJson (0 : Nat), .str "P"])) "structured-contract-direction"),
    ("application-shape", refusal (Format.relationApplication (arr [.str "Equal"])) "structured-contract-application"),
    ("clause", (Format.contractClause clauseWire).isOk),
    ("clause-shape", refusal (Format.contractClause (arr [])) "structured-contract-clause"),
    ("clause-kind", refusal (Format.contractClause (arr [.str "unknown", .str "claim", applicationWire, .null, .null])) "structured-contract-kind"),
    ("owner-shape", refusal (Format.protocolContract (arr [.str "main", arr [], .null])) "structured-contract"),
    ("owner", (Format.protocolContract (arr [.str "main", arr [clauseWire]])).isOk)]
  for (name, passed) in controls do
    if !passed then throw (IO.userError s!"strict contract wire failed: {name}")
  IO.println s!"structured contracts: {controls.length} strict wire controls passed"

#eval runWire

noncomputable section

private def formulaBody : Region dialect [.boolean, .boolean] [.boolean] :=
  .letOp .booleanEqual (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
private def checkedFormula : CheckedDefinition :=
  ⟨"predicate", .math, [.boolean, .boolean], [.boolean], formulaBody.erase, formulaBody,
    formulaBody.elaborate_erase⟩
private def rootBody : Region protocolDialect [.boolean, .boolean] [.boolean, .boolean] :=
  .letOp (.mark "") .nil .nil
    (.letOp (.calculate .booleanEqual rfl) (.cons .here (.cons (.there .here) .nil)) .nil
      (.ret (.cons .here (.cons (.there .here) .nil))))
private def checkedRoot : CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], [.boolean, .boolean], [.boolean, .boolean], [[0, 1], [0, 1]], [[1], [1]]⟩,
    rootBody.erase, rootBody, rootBody.elaborate_erase⟩
private def callerBody : Region protocolDialect [.boolean, .boolean] [.boolean, .boolean] :=
  .letOp (.mark "invoke") .nil .nil
    (.letOp (.protocolApply checkedRoot.signature [1, 0] "invoke")
      (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here (.cons (.there .here) .nil))))
private def checkedCaller : CheckedProtocol :=
  ⟨⟨"caller", ["P", "V"], [.boolean, .boolean], [.boolean, .boolean], [[0, 1], [0, 1]], [[0], [0]]⟩,
    callerBody.erase, callerBody, callerBody.elaborate_erase⟩
private def payload : UnitPayload :=
  ⟨[checkedFormula], [checkedRoot, checkedCaller], ⟨0, by decide⟩, by decide +kernel,
    by decide +kernel, by rfl, by decide +kernel, by decide +kernel⟩
set_option smartUnfolding false in
private def imported : Imported snapshot := ⟨⟨snapshot, payload⟩, by rfl⟩
private def owner : ContractBinding imported := ⟨⟨0, by decide⟩, ⟨0, by decide +kernel⟩, rfl⟩
private def invocation : InvocationCoordinate := ⟨0, []⟩
private def selectedRelation : RelationBinding snapshot subject := ⟨⟨0, by decide⟩, rfl⟩
private def formula : FormulaBinding imported selectedRelation :=
  ⟨predicate, by exact List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, ⟨0, by decide +kernel⟩, rfl⟩

-- Wrong same-typed helper symbols cannot satisfy the retained formula equation.
example : relation.formula ≠ some "otherPredicate" := by decide
example : owner.contract = snapshot.contracts[0] := rfl
example : owner.clause ⟨0, by decide⟩ = clause := rfl
example : formula.preconditions = [] := rfl
example : formula.definition.name = "predicate" := rfl

private def verifierInput : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.input .here, ⟨1, by decide +kernel⟩, by decide +kernel⟩
private def proverInput : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.input .here, ⟨0, by decide +kernel⟩, by decide +kernel⟩
private def decision : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.output .here, ⟨1, by decide +kernel⟩, by decide +kernel⟩
private def wrongDecision : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.output (.there .here), ⟨1, by decide +kernel⟩, by decide +kernel⟩
private def values : BoundaryValuation (fun _ => Bool) owner.protocol.inputs owner.protocol.outputs :=
  ⟨fun self => .cons (some (self == 0)) (.cons (some false) .nil),
   fun _ => .cons (some true) (.cons (some false) .nil)⟩

example : verifierInput.read {} values = some false := rfl
example : proverInput.read {} values = some true := rfl
example : verifierInput.erase ≠ proverInput.erase := by decide +kernel
example : decision.read {} values = some true := rfl
example : wrongDecision.read {} values = some false := rfl
example : decision.erase ≠ wrongDecision.erase := by decide +kernel
private def explicitBoundaryParameters : LogicalAssignments (fun _ => Bool) owner invocation where
  parameters _ selector :=
    (AssignmentSource.boundary (Value := fun _ => Bool) (owner := owner) selector).read {} values
      (⟨fun _ _ => none, fun _ _ => none⟩ : LogicalAssignments (fun _ => Bool) owner invocation)
  witnesses _ _ := none
example : explicitBoundaryParameters.parameters .boolean proverInput = some true := rfl
example : explicitBoundaryParameters.parameters .boolean verifierInput = some false := rfl
example : explicitBoundaryParameters.witnesses .boolean proverInput = none := rfl

-- Shared witness assignment is a function of the exact selector, not a new
-- existential per clause. Independent witnesses can satisfy incompatible claims.
example : (∃ w : Bool, w = false) ∧ (∃ w : Bool, w = true) := ⟨⟨false, rfl⟩, ⟨true, rfl⟩⟩
example : ¬ ∃ w : Bool, w = false ∧ w = true := by
  rintro ⟨w, rfl, impossible⟩
  cases impossible
example (assignments : LogicalAssignments (fun _ => Bool) owner invocation) :
    ¬ (assignments.witnesses .boolean proverInput = some false ∧
       assignments.witnesses .boolean proverInput = some true) := by
  rintro ⟨first, second⟩
  rw [first] at second
  cases second

-- Identical repeated selector occurrences read identical components.
example : readSelectors (owner := owner) (invocation := invocation) {} values (⟨fun _ _ => none, fun _ _ => none⟩)
    [] (.cons verifierInput (.cons verifierInput .nil)) =
    .cons (some false) (.cons (some false) .nil) := rfl

private def callerOwner : ContractBinding imported := ⟨⟨1, by decide⟩, ⟨1, by decide⟩, rfl⟩
private def application : CheckedApplication owner [.boolean, .boolean] where
  caller := callerOwner
  roles := [1, 0]
  site := "invoke"
  operands := .cons (.there .here) (.cons .here .nil)
  occurrence := .next (.mark "invoke") .nil .nil _ (.here _)
  substitution := by unfold ValidSubstitution; decide +kernel

private def callerEnvironment (role : Nat) : Environment (Component (fun _ : Ty => Bool)) [.boolean, .boolean] :=
  (Values.cons (some false) (.cons (some (role == 0)) .nil)).get
private def callerReturned (_role : Nat) : Values (Component (fun _ : Ty => Bool)) [.boolean, .boolean] :=
  .cons (some true) (.cons (some false) .nil)

-- Both the role map and operand permutation come from the actual checked call.
example : verifierInput.read (({} : ProtocolContext).enter application.site application.roles)
    (application.boundary {} callerEnvironment callerReturned) = some true := rfl
example : decision.read (({} : ProtocolContext).enter application.site application.roles)
    (application.boundary {} callerEnvironment callerReturned) = some true := rfl
example : wrongDecision.read (({} : ProtocolContext).enter application.site application.roles)
    (application.boundary {} callerEnvironment callerReturned) = some false := rfl
example : roleSubstitution application.roles 1 = 0 := rfl
example : application.operands.get (.here : Var [Ty.boolean, Ty.boolean] Ty.boolean) = .there .here := rfl

-- The exported generic equation operates on this checked occurrence, without
-- assuming a whole caller-process theorem or reading an inspector sidecar.
example : verifierInput.read (({} : ProtocolContext).enter application.site application.roles)
    (application.boundary {} callerEnvironment callerReturned) =
    Participant.restrict true (callerEnvironment 0 (.there .here)) :=
  application.input_substitution {} callerEnvironment callerReturned verifierInput .here rfl

private def witnessInput : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.input (.there .here), ⟨0, by decide⟩, by decide⟩
private def subjectBinding : ApplicationBinding owner subject :=
  ⟨selectedRelation, .cons verifierInput (.cons witnessInput .nil), rfl⟩
private def residualRelation : RelationBinding snapshot residual := ⟨⟨0, by decide⟩, rfl⟩
private def residualFormula : FormulaBinding imported residualRelation :=
  ⟨predicate, List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl, rfl, rfl, rfl,
    ⟨0, by decide⟩, rfl⟩
private def residualBinding : ApplicationBinding owner residual :=
  ⟨residualRelation, .cons decision (.cons wrongDecision .nil), rfl⟩
private def equalArguments (args : Values (assignment Int Int) [.boolean, .boolean]) : Prop :=
  args.get .here = args.get (.there .here)
private def environment : RelationEnvironment imported Int Int := ⟨fun _ _ => False⟩
private def subjectMeaning : InterpretedApplication owner subject Int Int environment :=
  ⟨subjectBinding, .formula formula rfl (fun _ => True) equalArguments
    (fun arguments => inferInstanceAs (Decidable (arguments.get .here = arguments.get (.there .here))))⟩
private def residualMeaning : InterpretedApplication owner residual Int Int environment :=
  ⟨residualBinding, .formula residualFormula rfl (fun _ => True) equalArguments
    (fun arguments => inferInstanceAs (Decidable (arguments.get .here = arguments.get (.there .here))))⟩
private def copiedRelation : RelationBinding snapshot copiedSubject := ⟨⟨0, by decide⟩, rfl⟩
private def copiedFormula : FormulaBinding imported copiedRelation :=
  ⟨predicate, List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl, rfl, rfl, rfl,
    ⟨0, by decide⟩, rfl⟩
private def copiedBinding : ApplicationBinding owner copiedSubject :=
  ⟨copiedRelation, .cons proverInput (.cons witnessInput .nil), rfl⟩
private def copiedMeaning : InterpretedApplication owner copiedSubject Int Int environment :=
  ⟨copiedBinding, .formula copiedFormula rfl (fun _ => True) equalArguments
    (fun arguments => inferInstanceAs (Decidable (arguments.get .here = arguments.get (.there .here))))⟩
private def contractMeaning : ContractInterpretation owner Int Int environment where
  subjects index := by
    rcases index with ⟨i, bound⟩
    match i with
    | 0 | 1 => exact subjectMeaning
    | 2 => exact copiedMeaning
    | n + 3 => simp [owner, ContractBinding.contract, snapshot] at bound; omega
  residuals index application selected := by
    rcases index with ⟨i, bound⟩
    match i with
    | 0 | 2 => cases selected
    | 1 => cases Option.some.inj selected; exact residualMeaning
    | n + 3 => simp [owner, ContractBinding.contract, snapshot] at bound; omega
  decisions index selector selected := by
    rcases index with ⟨i, bound⟩
    match i with
    | 0 | 1 | 2 => cases Option.some.inj selected; exact ⟨decision, rfl⟩
    | n + 3 => simp [owner, ContractBinding.contract, snapshot] at bound; omega

private theorem subjectLaw : subjectMeaning.interpretation.FormulaLaw := by
  intro arguments _
  cases arguments with
  | cons a rest => cases rest with
    | cons b rest => cases rest; cases a <;> cases b <;> rfl
private theorem residualLaw : residualMeaning.interpretation.FormulaLaw := by
  intro arguments _
  cases arguments with
  | cons a rest => cases rest with
    | cons b rest => cases rest; cases a <;> cases b <;> rfl

private def assignments : LogicalAssignments (assignment Int Int) owner invocation :=
  ⟨fun _ _ => none, fun type _ => match type with | .boolean => some false | _ => none⟩
private def accountingBoundary : ContractBoundaryValues owner Int Int :=
  ⟨fun _ => .cons (some false) (.cons (some false) .nil),
   fun _ => .cons (some true) (.cons (some false) .nil)⟩
private def continuationIndex : Fin owner.contract.clauses.length := ⟨1, by decide⟩

-- Scope is in the assignment type. Reusing identical raw port/role spellings
-- at another owner or invocation cannot silently identify their values.
example : True := by
  fail_if_success have wrong : LogicalAssignments (assignment Int Int) callerOwner invocation := assignments
  fail_if_success have wrong : LogicalAssignments (assignment Int Int) owner ⟨1, []⟩ := assignments
  trivial

private def noIterations : application.Iterations := fun index => Fin.elim0 index
example : application.childInvocation invocation noIterations =
    ⟨0, [.application 1 [1]]⟩ := rfl
private def explicitInstantiation : AssignmentInstantiation (assignment Int Int) application where
  parameters type _ := match type with
    | .boolean => .supplied true
    | _ => .unavailable
  witnesses _ _ := .unavailable
private def callerAssignments : LogicalAssignments (assignment Int Int) callerOwner invocation :=
  ⟨fun _ _ => none, fun _ _ => none⟩
private def callerBoundary : ContractBoundaryValues callerOwner Int Int :=
  ⟨fun _ => .cons (some false) (.cons (some false) .nil),
    fun _ => .cons (some false) (.cons (some false) .nil)⟩
example : (explicitInstantiation.apply noIterations {} callerBoundary callerAssignments).parameters
    .boolean verifierInput = some true := rfl
example : (explicitInstantiation.apply noIterations {} callerBoundary callerAssignments).witnesses
    .boolean verifierInput = none := rfl

private def executionInput : ComponentInput owner Int Int :=
  ⟨{}, 1, .cons (some false) (.cons (some false) .nil)⟩
example : decision.read {} (executionInput.boundary (.returned (.cons (some true) (.cons (some false) .nil)))) =
    some true := rfl
example : decision.read {} (executionInput.boundary (.stopped .refused)) = none := rfl
example : proverInput.read {} (executionInput.boundary (.returned (.cons (some true) (.cons (some false) .nil)))) =
    none := rfl
example : ¬ executionInput.returnedEvent (fun _ => True) (.stopped .reject) := by exact id

private def markHandler : PIR.Handler (observedInterface Int Int) Unit String
  | .mark site, state => ⟨.returned (), state, [site]⟩
  | .action _, state => ⟨.stopped .refused, state, []⟩
private def refusingHandler : PIR.Handler (observedInterface Int Int) Unit String
  | _, state => ⟨.stopped .refused, state, []⟩

-- These outcomes are computed from the admitted body and its actual masks,
-- not supplied as a sidecar result to the acceptance theorem.
example : (executionInput.process.run markHandler ()).outcome =
    .returned (.cons (some true) (.cons (some false) .nil)) := rfl
example : decision.read {} (executionInput.boundary (executionInput.process.run markHandler ()).outcome) =
    some true := rfl
example : (executionInput.process.run refusingHandler ()).outcome = .stopped .refused := rfl
example : decision.read {} (executionInput.boundary (executionInput.process.run refusingHandler ()).outcome) =
    none := rfl
example : let input := { executionInput with self := 0 }
    decision.read {} (input.boundary (input.process.run markHandler ()).outcome) = none := rfl
example : ¬ executionInput.returnedEvent (fun boundary => decision.read {} boundary = some true)
    (executionInput.process.run refusingHandler ()).outcome := by exact id

private def applicationEnvironment : Environment (Component (assignment Int Int)) [.boolean, .boolean] :=
  (Values.cons (some false) (.cons (some false) .nil)).get
private def applicationProcess := protocolOperation (imported.program.payload.tables Int Int) 0
  (.protocolApply owner.protocol.signature application.roles application.site)
  (application.operands.eval applicationEnvironment) .nil (imported.program.payload.protocolTable Int Int) {}
private def childContext : ProtocolContext := ({} : ProtocolContext).enter application.site application.roles

example : (application.componentInput {} 0 applicationEnvironment).process = applicationProcess :=
  application.componentInput_process {} 0 applicationEnvironment rfl
example : (applicationProcess.run markHandler ()).outcome =
    .returned (.cons (some true) (.cons (some false) .nil)) := rfl
example : verifierInput.read childContext (application.boundaryOfOutcome {} 0 applicationEnvironment
    (applicationProcess.run markHandler ()).outcome) = some false :=
  application.boundaryOfOutcome_input {} 0 applicationEnvironment _ verifierInput .here rfl rfl
example : decision.read childContext (application.boundaryOfOutcome {} 0 applicationEnvironment
    (applicationProcess.run markHandler ()).outcome) = some true := rfl
example : wrongDecision.read childContext (application.boundaryOfOutcome {} 0 applicationEnvironment
    (applicationProcess.run markHandler ()).outcome) = some false := rfl
example : (applicationProcess.run refusingHandler ()).outcome = .stopped .refused := rfl
example : decision.read childContext (application.boundaryOfOutcome {} 0 applicationEnvironment
    (applicationProcess.run refusingHandler ()).outcome) = none :=
  application.boundaryOfOutcome_stopped_output {} 0 applicationEnvironment .refused decision .here rfl
example : decision.read childContext (application.boundaryOfOutcome {} 1 applicationEnvironment
    (applicationProcess.run markHandler ()).outcome) = none :=
  application.boundaryOfOutcome_other_output {} 1 applicationEnvironment _ decision .here rfl (by decide)

-- Even an otherwise coherent assignment cannot fabricate the stopped callee's
-- actual output read required by this retained residual application.
example : ¬ contractMeaning.Residual childContext continuationIndex
    (application.boundaryOfOutcome {} 0 applicationEnvironment
      (applicationProcess.run refusingHandler ()).outcome) assignments := by
  rintro ⟨selected, selected_eq, arguments, read, _⟩
  have same : residual = selected := Option.some.inj selected_eq
  subst selected
  change none = some arguments at read
  cases read

private theorem accepts : contractMeaning.Accepts {} continuationIndex accountingBoundary :=
  ⟨⟨.output, 0, "V"⟩, rfl, rfl⟩
private theorem residualFalse :
    ¬ contractMeaning.Residual {} continuationIndex accountingBoundary assignments := by
  rintro ⟨application, selected, arguments, read, holds⟩
  have equal : residual = application := Option.some.inj selected
  subst application
  have values : arguments = .cons true (.cons false .nil) := Option.some.inj read.symm
  subst arguments
  have impossible : false = true := by
    change (PIR.Proc.done (.cons false .nil) : Closed (Values (assignment Int Int) [.boolean])) =
      .done (.cons true .nil) at holds
    exact congrArg (fun values => values.get .here) (PIR.Proc.done.inj holds)
  cases impossible

-- Formula meaning is pinned to the actual helper: the selected boundary's
-- false result cannot be replaced by an externally asserted true relation.
example : ¬ residualMeaning.Holds {} accountingBoundary assignments := by
  intro holds
  exact residualFalse ⟨residual, rfl, holds⟩

private def selectedResidual : SelectedApplication owner Int Int environment :=
  contractMeaning.select (.residual continuationIndex residual rfl)
private def residualUse : ApplicationUse selectedResidual {} accountingBoundary assignments :=
  ⟨.cons true (.cons false .nil), rfl⟩
private def refutationRequest : ContractRequest owner Int Int environment invocation {} accountingBoundary assignments :=
  .relation selectedResidual residualUse .refutation
private theorem refutationProof : refutationRequest.Proof :=
  ⟨⟨residualLaw, trivial⟩, by change ¬ (true = false); decide⟩
example : ¬ selectedResidual.interpreted.Holds {} accountingBoundary assignments :=
  refutationRequest.resolve refutationProof

-- Consume the same formula translation at the actual checked application's
-- observed outcome, with its entered role context and exact output order.
private def observedApplicationBoundary := application.boundaryOfOutcome {} 0 applicationEnvironment
  (applicationProcess.run markHandler ()).outcome
private def observedResidualUse :
    ApplicationUse selectedResidual childContext observedApplicationBoundary assignments :=
  ⟨.cons true (.cons false .nil), rfl⟩
private theorem observedResidualRefutation :
    ¬ selectedResidual.interpreted.Holds childContext observedApplicationBoundary assignments :=
  (ContractRequest.relation selectedResidual observedResidualUse .refutation).resolve
    ⟨⟨residualLaw, trivial⟩, by change ¬ (true = false); decide⟩
example : True := by
  fail_if_success have fabricated :
      ApplicationUse selectedResidual childContext observedApplicationBoundary assignments :=
    ⟨.cons true (.cons true .nil), rfl⟩
  trivial

-- An external terminal reads an explicitly fixed complete table and the exact
-- returned port. A correct local refutation does not close this terminal.
private def externalTerminal : ExternalTerminal owner Int Int where
  parameterTypes := [.vector scalarDomain, .index]
  parameters := .cons (.supplied [2, 7, 2]) (.cons (.supplied 1) .nil)
  outputTypes := [.boolean]
  nonempty := by decide
  outputs := .cons ⟨wrongDecision, rfl⟩ .nil
  meaning parameters outputs := parameters.get .here = [2, 7, 2] ∧
    parameters.get (.there .here) = 1 ∧ outputs.get .here = true
private def selectedRequests : ContractRequests owner Int Int environment invocation {} accountingBoundary assignments :=
  .both (.one refutationRequest) (.one (.terminal externalTerminal))
example : ¬ selectedRequests.Proof := by
  rintro ⟨_, parameters, outputs, parameterRead, outputRead, _, _, terminal⟩
  have actual : outputs = .cons false .nil := Option.some.inj outputRead.symm
  subst outputs
  cases terminal
private def availabilityOnly : ExternalTerminal owner Int Int :=
  { externalTerminal with meaning := fun _ _ => True }
-- This explicitly weak terminal establishes availability, even when the real
-- terminal's required Boolean is false. It still cannot hold after refusal.
example : availabilityOnly.Holds {} accountingBoundary assignments :=
  ⟨.cons [2, 7, 2] (.cons 1 .nil), .cons false .nil, rfl, rfl, trivial⟩
example : ¬ availabilityOnly.Holds childContext
    (application.boundaryOfOutcome {} 0 applicationEnvironment
      (applicationProcess.run refusingHandler ()).outcome) assignments :=
  availabilityOnly.not_holds_stopped application {} 0 applicationEnvironment .refused assignments
example : (AssignmentSource.supplied (Value := assignment Int Int) (owner := callerOwner)
    (type := .index) 1).read {} callerBoundary callerAssignments = some 1 := rfl
example : (AssignmentSource.supplied (Value := assignment Int Int) (owner := callerOwner)
    (type := .vector scalarDomain) [2, 7, 2]).read {} callerBoundary callerAssignments = some [2, 7, 2] := rfl
example : (AssignmentSource.unavailable (Value := assignment Int Int) (owner := callerOwner)
    (type := .vector scalarDomain)).read {} callerBoundary callerAssignments = none := rfl

private def falseDomainMeaning : InterpretedApplication owner subject Int Int environment :=
  ⟨subjectBinding, .formula formula rfl (fun _ => False) equalArguments
    (fun arguments => inferInstanceAs (Decidable (arguments.get .here = arguments.get (.there .here))))⟩
private def falseDomainSelected : SelectedApplication owner Int Int environment :=
  ⟨.subject ⟨0, by decide⟩, falseDomainMeaning⟩
private def falseDomainUse : ApplicationUse falseDomainSelected {} accountingBoundary assignments :=
  ⟨.cons false (.cons false .nil), rfl⟩
example : falseDomainMeaning.interpretation.FormulaLaw := by intro _ impossible; cases impossible
example : ¬ falseDomainUse.Translation := fun proof => proof.domain

private def sharedBoundary : ContractBoundaryValues owner Int Int :=
  ⟨fun role => .cons (some (role == 0)) (.cons (some false) .nil),
    fun _ => .cons (some true) (.cons (some false) .nil)⟩
private def sharedAssignments (witness : Bool) : LogicalAssignments (assignment Int Int) owner invocation :=
  ⟨fun _ _ => none, fun type _ => match type with | .boolean => some witness | _ => none⟩
private theorem readBooleanPair (head : Bool) (tail : Option Bool) :
    RoleFamily.sequence (Value := assignment Int Int) (types := [.boolean, .boolean])
      (.cons (some head) (.cons tail .nil)) =
      tail.map (fun value => .cons head (.cons value .nil)) := by
  cases tail <;> rfl

-- Two actual retained clauses can each hold with separate witnesses, at the
-- same boundary. Their shared witness key cannot satisfy both simultaneously.
example : (∃ a : LogicalAssignments (assignment Int Int) owner invocation, (contractMeaning.subjects ⟨0, by decide⟩).Holds {} sharedBoundary a) ∧
    (∃ a : LogicalAssignments (assignment Int Int) owner invocation, (contractMeaning.subjects ⟨2, by decide⟩).Holds {} sharedBoundary a) :=
  ⟨⟨sharedAssignments false, .cons false (.cons false .nil), rfl, rfl⟩,
    ⟨sharedAssignments true, .cons true (.cons true .nil), rfl, rfl⟩⟩
example (a : LogicalAssignments (assignment Int Int) owner invocation) :
    ¬ ((contractMeaning.subjects ⟨0, by decide⟩).Holds {} sharedBoundary a ∧
      (contractMeaning.subjects ⟨2, by decide⟩).Holds {} sharedBoundary a) := by
  rintro ⟨⟨left, leftRead, leftHolds⟩, ⟨right, rightRead, rightHolds⟩⟩
  change RoleFamily.sequence (.cons (some false) (.cons (a.witnesses .boolean witnessInput) .nil)) =
    some left at leftRead
  change RoleFamily.sequence (.cons (some true) (.cons (a.witnesses .boolean witnessInput) .nil)) =
    some right at rightRead
  rw [readBooleanPair] at leftRead rightRead
  cases value : a.witnesses .boolean witnessInput with
  | none => rw [value] at leftRead; cases leftRead
  | some w =>
    rw [value] at leftRead rightRead
    cases Option.some.inj leftRead
    cases Option.some.inj rightRead
    cases w with
    | false => cases rightHolds
    | true => cases leftHolds

-- An admitted formula may have explicit preconditions and may refuse outside
-- them. Its semantic link preserves that refusal, even with a Boolean result.
private def lookupFormula : Function :=
  ⟨"lookupPredicate", .math, .privateDef, [.vector scalarDomain, .index], [.boolean],
    none, [⟨1, 0, 0⟩], none,
    .block [.instruction (.boundedAt scalarDomain) [0, 1] [.field scalarDomain] [] "",
      .instruction (.fieldEqual scalarDomain) [0, 0] [.boolean] [] ""] (.ret [0])⟩
private def lookupRelation : Relation :=
  ⟨"Lookup", .publicDef, "zkc.language.formula/0", "lookup", "0",
    [.vector scalarDomain, .index], [.boolean], ["parameter", "statement"], some "lookupPredicate"⟩
private def partialSnapshot : Snapshot :=
  { snapshot with
    relations := [relation, lookupRelation]
    definitions := snapshot.definitions ++ [.function lookupFormula] }
private def lookupBody : Region dialect [.vector scalarDomain, .index] [.boolean] :=
  .letOp (.boundedAt scalarDomain) (.cons .here (.cons (.there .here) .nil)) .nil
    (.letOp (.fieldEqual scalarDomain) (.cons .here (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))
private def checkedLookup : CheckedDefinition :=
  ⟨"lookupPredicate", .math, [.vector scalarDomain, .index], [.boolean],
    lookupBody.erase, lookupBody, lookupBody.elaborate_erase⟩
private def partialPayload : UnitPayload :=
  ⟨[checkedFormula, checkedLookup], [checkedRoot, checkedCaller], ⟨0, by decide⟩,
    by decide +kernel, by decide +kernel, by rfl, by decide +kernel, by decide +kernel⟩
private def partialImported : Imported partialSnapshot := ⟨⟨partialSnapshot, partialPayload⟩, by rfl⟩
private def lookupApplication : RelationApplication := ⟨"Lookup", []⟩
private def lookupSelected : RelationBinding partialSnapshot lookupApplication := ⟨⟨1, by decide⟩, rfl⟩
private def partialBinding : FormulaBinding partialImported lookupSelected :=
  ⟨lookupFormula, by simp [partialSnapshot, snapshot], rfl, rfl, rfl, rfl, rfl,
    ⟨1, by decide⟩, rfl⟩

example : partialBinding.preconditions = [⟨1, 0, 0⟩] := rfl
example : partialBinding.invokeRelation (F := Int) (G := Int) (.cons [] (.cons 0 .nil)) =
    .halt .refused := rfl
example : partialBinding.invokeRelation (F := Int) (G := Int) (.cons [7] (.cons 0 .nil)) =
    .done (.cons true .nil) := rfl
example : ¬ partialBinding.Realizes (F := Int) (G := Int) rfl (fun _ => True) (fun _ => True) := by
  intro total
  have contradiction := total (.cons [] (.cons 0 .nil)) trivial
  cases contradiction

private def nonemptyFirst (arguments : Values (assignment Int Int) [.vector scalarDomain, .index]) : Prop :=
  ∃ first rest, arguments = .cons (first :: rest) (.cons 0 .nil)
example : partialBinding.Realizes (F := Int) (G := Int) rfl nonemptyFirst (fun _ => True) := by
  rintro arguments ⟨first, rest, rfl⟩
  change (PIR.Proc.done (Values.cons (decide (first = first)) .nil) :
    Closed (Values (assignment Int Int) [.boolean])) = _
  simp only [decide_true]
  rfl

-- Changing only a same-symbol, same-ABI formula body invalidates the old
-- adequacy theorem. Header/name matching cannot make old meaning reusable.
private def changedPredicate : Function := { predicate with
  body := .block [.instruction .booleanNotEqual [0, 1] [.boolean] [] ""] (.ret [0]) }
private def changedSnapshot : Snapshot := { snapshot with
  definitions := [.function root, .function changedPredicate, .function caller] }
private def changedBody : Region dialect [.boolean, .boolean] [.boolean] :=
  .letOp .booleanNotEqual (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
private def changedChecked : CheckedDefinition :=
  ⟨"predicate", .math, [.boolean, .boolean], [.boolean], changedBody.erase, changedBody,
    changedBody.elaborate_erase⟩
private def changedPayload : UnitPayload :=
  ⟨[changedChecked], [checkedRoot, checkedCaller], ⟨0, by decide⟩,
    by decide +kernel, by decide +kernel, by rfl, by decide +kernel, by decide +kernel⟩
private def changedImported : Imported changedSnapshot := ⟨⟨changedSnapshot, changedPayload⟩, by rfl⟩
private def changedRelation : RelationBinding changedSnapshot subject := ⟨⟨0, by decide⟩, rfl⟩
private def changedFormula : FormulaBinding changedImported changedRelation :=
  ⟨changedPredicate, List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl, rfl, rfl, rfl,
    ⟨0, by decide⟩, rfl⟩
example : changedFormula.definition.helper = formula.definition.helper := rfl
example : changedFormula.invokeRelation (F := Int) (G := Int) (.cons false (.cons false .nil)) =
    .done (.cons false .nil) := rfl
example : ¬ changedFormula.Realizes (F := Int) (G := Int) rfl (fun _ => True)
    (fun args => args.get .here = args.get (.there .here)) := by
  intro oldLaw
  have contradiction := oldLaw (.cons false (.cons false .nil)) trivial
  cases contradiction

private def opaqueSnapshot : Snapshot := { snapshot with relations := [{ relation with kind := "opaque", formula := none }] }
private def opaqueImported : Imported opaqueSnapshot := ⟨⟨opaqueSnapshot, payload⟩, by rfl⟩
private def opaqueOwner : ContractBinding opaqueImported := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
private def opaqueEnvironment : RelationEnvironment opaqueImported Int Int where
  meanings index := by
    rcases index with ⟨index, bound⟩
    match index with
    | 0 => exact fun args => args.get .here = args.get (.there .here)
    | _ + 1 => simp [opaqueSnapshot] at bound
private def opaqueSubjectRelation : RelationBinding opaqueSnapshot subject := ⟨⟨0, by decide⟩, rfl⟩
private def opaqueResidualRelation : RelationBinding opaqueSnapshot residual := ⟨⟨0, by decide⟩, rfl⟩
private def opaqueSubject : RelationInterpretation opaqueImported opaqueSubjectRelation Int Int opaqueEnvironment :=
  .opaque rfl (by decide)
private def opaqueResidual : RelationInterpretation opaqueImported opaqueResidualRelation Int Int opaqueEnvironment :=
  .opaque rfl (by decide)
-- The same declaration at subject and residual occurrences has one meaning.
example (args : Values (assignment Int Int) [.boolean, .boolean]) :
    opaqueSubject.Holds args ↔ opaqueResidual.Holds args := Iff.rfl
example (args : Values (assignment Int Int) [.boolean, .boolean]) :
    ¬ (opaqueSubject.Holds args ∧ ¬ opaqueResidual.Holds args) := fun both => both.2 both.1

end
end Tests.StructuredContracts
