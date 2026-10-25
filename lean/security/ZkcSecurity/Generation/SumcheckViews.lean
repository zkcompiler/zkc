module

public import ZkcSecurity.Generation.RoundDescriptors
public import ZkcSecurity.Generation.SubjectABI

@[expose] public section

/-! Source-driven validator presentation construction for installed table rounds.
Only admitted pair and module identities are configured. Input positions, all
round occurrences, captures and source continuations come from the artifacts.
The output invokes the generic checked view constructor; it contains no guessed
presentation and no protocol-name dispatch. Unsupported layouts stay unresolved.
-/
set_option autoImplicit false
namespace ZkcSecurity.Generation.SumcheckViews
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck
open ZkcTools.StructuredSource.Constructed (literal)

structure Output where
  moduleName : String
  subjectModule : String
  validatorModule : String
  roundsModule : String

def inputType : ValueSort → Except String String
  | .data .boolean => .ok "Bool"
  | .data .index => .ok "Nat"
  | .data (.field _) => .ok "F"
  | .data (.vector _) => .ok "List F"
  | .data (.group _) => .ok "G"
  | .data (.service _) => .error "component-view-service-input"
  | .data (.sequence _) | .data (.product ..) => .error "component-view-aggregate-input"
  | .transcript _ => .ok "Domain.History (uniformCarriers F G)"
  | .indices => .ok "List Nat"

def encodedInput (sort : ValueSort) (name : String) : Except String String := do
  match sort with
  | .data ty => SubjectABI.encoded ty name
  | .transcript suite => pure (".transcript " ++ literal suite ++ " " ++ name)
  | .indices => pure (".indices " ++ name)

def source (producer validator : Participant) (output : Output) : Except String String := do
  let rounds ← RoundDescriptors.discover producer validator
  let patterns ← rounds.mapM fun descriptor => do
    let some pattern := descriptor.pattern? producer validator | throw "component-view-round-pattern"
    pure pattern
  let some first := patterns.head? | throw "component-view-no-rounds"
  if !patterns.all (fun pattern => pattern.plan.field == first.plan.field) then
    throw "component-view-multiple-fields-requires-domain-family"
  let histories := validator.inputs.zipIdx.filter fun (sort, _) =>
    match sort with | .transcript _ => true | _ => false
  let [(_, historyIndex)] := histories | throw "component-view-single-history-input"
  let names := (List.range validator.inputs.length).map SubjectABI.inputName
  let binders ← (validator.inputs.zip names).mapM fun (sort, name) => do
    pure (" (" ++ name ++ " : " ++ (← inputType sort) ++ ")")
  let encoded ← (validator.inputs.zip names).mapM fun (sort, name) => encodedInput sort name
  let arguments := " ".intercalate names
  let history := names[historyIndex]!
  let view := output.validatorModule
  let field := literal first.plan.field
  let suite := literal first.suite
  let mut text := "module\n\npublic import " ++ output.subjectModule ++
    "\npublic import " ++ view ++ "\npublic import " ++ output.roundsModule ++
    "\npublic import ZkcSecurity.Realizations.Sumcheck.ValidatorHelpers\n" ++
    "public import ZkcSecurity.Families.Sumcheck.CompiledValidatorOrigins\n" ++
    "public import ZkcSecurity.Families.Sumcheck.CompiledValidatorExecution\n" ++
    "public import Zkc.Source.Structured.BodyBindings\n" ++
    "public meta import ZkcSecurity.Tools.ComponentView\n\n" ++
    "@[expose] public section\nnoncomputable section\n\n" ++
    "/-! Generated from the retained pair by ZkcSecurity.Generation.SumcheckViews.\n" ++
    "The generic constructor infers the full presentation and proves its bridge.\n" ++
    "All source guards, complete returns and exact stopped outcomes are retained.\n" ++
    "Regenerate; do not hand edit. -/\n" ++
    "set_option autoImplicit false\nset_option maxRecDepth 20000\n" ++
    "set_option maxHeartbeats 8000000\n" ++
    "set_option backward.isDefEq.respectTransparency false\n" ++
    "set_option linter.unusedSimpArgs false\n" ++
    "namespace " ++ output.moduleName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Construction\n" ++
    "open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent\n" ++
    "open ZkcSecurity.Families.Sumcheck.TableComponent.Execution\n" ++
    "open ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution\n" ++
    "open ZkcSecurity.FiatShamir.DomainReduction\n" ++
    "open ZkcSecurity.Realizations.Sumcheck\n" ++
    "open " ++ output.roundsModule ++ "\n\n" ++
    "abbrev program := " ++ output.subjectModule ++ ".imported.program\n" ++
    "abbrev context := " ++ output.subjectModule ++ ".subject.selection.context\n" ++
    "abbrev field := " ++ field ++ "\n" ++
    "abbrev suite := " ++ suite ++ "\n" ++
    "theorem context_suite : context.suite = suite := rfl\n\n" ++
    "theorem helper_bodies : DomainHelpers.Bodies program := by\n  bind_structured_bodies\n\n" ++
    "variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]\n" ++
    "  [DecidableEq F] [DecidableEq G]\n\n" ++
    "def inputs" ++ String.join binders ++ " : Domain.Environment (uniformCarriers F G) :=\n  [" ++
    ", ".intercalate encoded ++ "]\n\n"
  for index in List.range rounds.length do
    let round := "round" ++ toString index
    text := text ++ "theorem " ++ round ++ "_field : " ++ round ++ ".plan.field = field := rfl\n" ++
      "theorem " ++ round ++ "_connection : CompiledValidator.RoundConnection (F := F) (G := G)\n" ++
      "    " ++ round ++ ".plan.field program context " ++ round ++ ".plan.toPlan " ++ round ++ ".schedule := by\n" ++
      "  apply CompiledValidator.connectionOfOrigins " ++ round ++ ".plan program context " ++
      round ++ ".bases " ++ round ++ ".origins_checked\n" ++
      "  intro point challenge\n" ++
      "  exact DomainHelpers.append (F := F) (G := G) program helper_bodies.sumcheck point challenge\n\n"
  text := text ++ "noncomputable def assembled" ++ String.join binders ++ " :\n" ++
    "    {presented : PIR.Process (Nominal.signature F field) (Domain.Result (uniformCarriers F G)) //\n" ++
    "      Bridge (Nominal.interface (G := G) field) (fun _ _ => True) " ++ history ++ "\n" ++
    "        (Domain.participant (ringModel F G) program context " ++ view ++ ".artifact\n" ++
    "          (inputs " ++ arguments ++ ")) presented} := by\n" ++
    "  have emptyLaw := DomainHelpers.empty (F := F) (G := G) program helper_bodies.sumcheck\n"
  let mut rules : List String := []
  let mut fields : List String := []
  for index in List.range rounds.length do
    let round := "round" ++ toString index
    let rule := round ++ "Rule"
    rules := rules ++ [rule]
    fields := fields ++ [round ++ "_field"]
    text := text ++ "  have " ++ rule ++ " := sourceLoopBind (B := Domain.Result (uniformCarriers F G))\n" ++
      "    " ++ round ++ ".plan.field program context " ++ round ++ ".plan.toPlan " ++ round ++ ".schedule\n" ++
      "    " ++ round ++ "_connection _ _ (" ++ round ++ ".validator_block F G program context rfl)\n" ++
      "  dsimp only [" ++ round ++ ".validatorCapture, " ++ round ++ ".descriptor] at " ++ rule ++ "\n" ++
      "  simp only [" ++ round ++ "_field, field, context_suite, suite, Nat.reduceAdd, CompiledValidator.carried] at " ++ rule ++ "\n"
  text := text ++ "  construct_component_view [" ++ ", ".intercalate rules ++ "]\n" ++
    "    normalizing (\n" ++
    "      try (\n        rw [" ++ view ++ ".participant_eq]\n" ++
    "        simp only [" ++ view ++ ".view, Domain.View.participant, " ++ view ++ ".inputSorts,\n" ++
    "          " ++ view ++ ".outputSorts, " ++ view ++ ".returned, inputs, field, suite, context_suite,\n" ++
    "          Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, List.map_cons, List.map_nil,\n" ++
    "          beq_self_eq_true, ite_true]\n" ++
    "        unfold_component_bodies [" ++ view ++ ".view])\n" ++
    "      try simp only [List.length_nil, List.length_range, Nat.zero_add] at *\n" ++
    "      repeat first\n" ++
    "        | fail_if_no_progress (simp (disch := omega) only [ValidatorHelpers.terminal_all program helper_bodies])\n" ++
    "        | fail_if_no_progress (\n" ++
    "            normalize_table_validator [emptyLaw] unfolding\n" ++
    "              [CompiledValidator.carried, " ++ ", ".intercalate fields ++ ", field, suite, context_suite,\n" ++
    "                List.length_nil, List.length_range, Nat.zero_add]\n" ++
    "            try simp_all only [ite_true, ite_false])\n" ++
    "        | fail_if_no_progress (conv => arg 4; simp only [PIR.Process.bind_assoc]))\n" ++
    "    solving rfl\n    finishing trivial\n\n" ++
    "project_checked_view assembled as presented with bridge\n\n" ++
    "end " ++ output.moduleName ++ "\n"
  pure text

end ZkcSecurity.Generation.SumcheckViews
