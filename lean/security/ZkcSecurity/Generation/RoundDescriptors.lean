module

public import ZkcSecurity.Families.Sumcheck.RoundDescriptor
public import ZkcTools.StructuredSource.Constructed

@[expose] public section

/-! Lean-owned discovery and printing of small actual-pair round descriptors.
The caller selects modules and a pair, never instruction offsets, captures,
helpers, templates, or proof scripts. Full generated block equalities remain
kernel obligations; recognition alone does not establish a correspondence. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.RoundDescriptors
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck
open ZkcTools.StructuredSource.Constructed (literal)

structure Output where
  moduleName : String
  producerModule : String
  validatorModule : String
  contextModule : String
  contextExpression : String

/-- Discover all top-level loops, including private prefix results in captures.
Nested or unrecognized loops are refused rather than silently omitted. -/
def loops (artifact : Participant) : List RoundDescriptor.Loop := Id.run do
  let mut found := []
  let mut capture := artifact.inputs.length
  for (instruction, index) in artifact.instructions.zipIdx do
    match instruction.operation with
    | .loop site maximum yielded =>
        found := found ++ [⟨index, capture, site, maximum, yielded,
          instruction.operands, instruction.results⟩]
    | _ => pure ()
    capture := capture + instruction.results.length
  return found

def query? (body : List Zkc.Construction.Instruction) : Option Template :=
  match body.filterMap (fun instruction => match instruction.operation with
      | .challenge _ _ template => some template | _ => none) with
  | [template] => some template
  | _ => none

/-- Pair by exact source query template, including its ordered apply/repeat
path. Reordering roles or confusing two same-typed calls cannot select a round. -/
def discover (producer validator : Participant) : Except String (List RoundDescriptor.Descriptor) := do
  let producers := loops producer
  let validators := loops validator
  if producers.isEmpty || producers.length != validators.length then
    throw "round-descriptors-loop-count"
  let mut used : List Nat := []
  let mut found := []
  for left in producers do
    let some query := query? (left.instruction producer).body |
      throw "round-descriptors-producer-query"
    let [right] := validators.filter (fun loop =>
      query? (loop.instruction validator).body == some query) |
      throw "round-descriptors-query-match"
    if used.contains right.index then throw "round-descriptors-duplicate-query"
    let descriptor : RoundDescriptor.Descriptor := ⟨left, right⟩
    if !(decide (descriptor.Matches producer validator)) then
      throw "round-descriptors-family-mismatch"
    used := right.index :: used
    found := found ++ [descriptor]
  return found

def roundSource (descriptor : RoundDescriptor.Descriptor) (number : Nat)
    (output : Output) : String := Id.run do
  let left := output.producerModule
  let right := output.validatorModule
  let leftBody := left ++ ".bodyStep" ++ toString descriptor.producer.index ++ "Body"
  let rightBody := right ++ ".bodyStep" ++ toString descriptor.validator.index ++ "Body"
  let mut text := "namespace round" ++ toString number ++ "\n\n" ++
    "def descriptor : RoundDescriptor.Descriptor := " ++ literal descriptor ++ "\n\n" ++
    "abbrev producerIndex := descriptor.producer.index\n" ++
    "abbrev validatorIndex := descriptor.validator.index\n" ++
    "abbrev producerCapture := descriptor.producer.capture\n" ++
    "abbrev validatorCapture := descriptor.validator.capture\n" ++
    "abbrev producerYielded := descriptor.producer.yielded\n" ++
    "abbrev validatorYielded := descriptor.validator.yielded\n" ++
    "abbrev maximum := descriptor.producer.maximum\n" ++
    "abbrev producerLoop := descriptor.producer.instruction " ++ left ++ ".artifact\n" ++
    "abbrev validatorLoop := descriptor.validator.instruction " ++ right ++ ".artifact\n\n" ++
    "theorem checked : descriptor.Matches " ++ left ++ ".artifact " ++ right ++
    ".artifact := by decide +kernel\n\n" ++
    "def pattern : RoundDescriptor.Pattern :=\n" ++
    "  (descriptor.pattern? " ++ left ++ ".artifact " ++ right ++
    ".artifact).get (by decide +kernel)\n\n" ++
    "abbrev plan := pattern.plan\nabbrev suite := pattern.suite\n\n" ++
    "theorem occurrences :\n" ++
    "    RoundDescriptor.templatesAt producerLoop.body [4, 8, 11, 14] =\n" ++
    "      some (RoundDescriptor.occurrences plan) ∧\n" ++
    "    RoundDescriptor.templatesAt validatorLoop.body [3, 7, 13, 16] =\n" ++
    "      some (RoundDescriptor.occurrences plan) := by decide +kernel\n\n"
  for (role, body, family, capture) in [
      ("producer", leftBody, "ReadbackRound.producerBlock plan", "producerCapture"),
      ("validator", rightBody, "CompiledRound.block plan.toPlan", "validatorCapture")] do
    let arguments := if role == "validator" then " plan.field " else " "
    text := text ++ "theorem " ++ role ++ "_block\n" ++
      "    (F G : Type) [Field F] [AddCommGroup G] [Module F G]\n" ++
      "    [DecidableEq F] [DecidableEq G] (program : Structured.Program) (context : Context)\n" ++
      "    (selectedSuite : context.suite = suite) :\n" ++
      "    " ++ body ++ " (ringModel F G) program context =\n" ++
      "      " ++ family ++ " program context" ++ arguments ++ capture ++ " := by\n" ++
      "  unfold " ++ (if role == "producer" then "ReadbackRound.producerBlock" else "CompiledRound.block") ++
      "\n  rw [selectedSuite]\n  rfl\n\n" ++
      "theorem " ++ role ++ "_actual_block\n" ++
      "    (F G : Type) [Field F] [AddCommGroup G] [Module F G]\n" ++
      "    [DecidableEq F] [DecidableEq G] (program : Structured.Program) (context : Context)\n" ++
      "    (selectedSuite : context.suite = suite) :\n" ++
      "    Domain.evaluate (ringModel F G) program context " ++ role ++ "Loop.body =\n" ++
      "      " ++ family ++ " program context" ++ arguments ++ capture ++ " := by\n" ++
      "  funext env\n  exact (" ++ body ++ "_eq (ringModel F G) program context env).trans\n" ++
      "    (congrFun (" ++ role ++ "_block F G program context selectedSuite) env)\n\n"
  text := text ++ "noncomputable abbrev context : Context := " ++ output.contextExpression ++ "\n\n" ++
    "def bases : RoundDescriptor.OriginBases := RoundDescriptor.originBases plan context\n\n" ++
    "theorem origins_checked : bases.Valid plan context := by decide +kernel\n\n" ++
    "def sites (index : Nat) : ReadbackRound.Sites plan context index :=\n" ++
    "  RoundDescriptor.OriginBases.sites origins_checked index\n\n" ++
    "def schedule : TableComponent.Nominal.Schedule plan.field :=\n" ++
    "  RoundDescriptor.OriginBases.schedule origins_checked\n\n" ++
    "end round" ++ toString number ++ "\n\n"
  return text

def source (producer validator : Participant) (output : Output) : Except String String := do
  let descriptors ← discover producer validator
  let rounds := String.join ((descriptors.zipIdx).map fun (descriptor, index) =>
    roundSource descriptor index output)
  pure ("module\n\npublic import " ++ output.producerModule ++
    "\npublic import " ++ output.validatorModule ++
    "\npublic import " ++ output.contextModule ++
    "\npublic import ZkcSecurity.Families.Sumcheck.RoundDescriptor\n\n" ++
    "@[expose] public section\nnoncomputable section\n\n" ++
    "/-! Generated by ZkcSecurity.Generation.RoundDescriptors from the retained pair.\n" ++
    "Small structural descriptors and applications of installed family blocks;\n" ++
    "all actual bodies, loop headers and occurrences are kernel checked.\n" ++
    "Regenerate; do not hand edit. -/\n" ++
    "set_option autoImplicit false\nset_option maxRecDepth 20000\n" ++
    "set_option maxHeartbeats 8000000\n" ++
    "namespace " ++ output.moduleName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Construction\n" ++
    "open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent\n\n" ++
    rounds ++ "end " ++ output.moduleName ++ "\n")

end ZkcSecurity.Generation.RoundDescriptors
