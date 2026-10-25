module

public import Zkc.Source.Structured.MathematicsAliases
public import ZkcTools.StructuredSource.Bindings.Inputs

@[expose] public section

/-! An untrusted printer for a small source mathematics dependency graph.
Only selected target metadata, exact bodies and dependency equations are
emitted. Arithmetic and finite-sum proofs remain authored in ordinary modules.
The supported graph has at most one distinct direct callee and one fold per
body; ambiguity refuses. Repeated edge names receive a deterministic unused
suffix within the dependency path. -/

namespace ZkcTools.StructuredSource.MathematicsAliases
open Zkc.Source Zkc.Source.Structured
open ZkcTools.StructuredSource.Presentation

structure Output where
  moduleName : String
  sourceModule : String

def one {α : Type} (reason : String) : List α → Except String α
  | [value] => .ok value
  | _ => .error ("source-mathematics-" ++ reason)

def definition (program : Program) (helper : Helper) : Except String CheckedDefinition :=
  match Structured.MathematicsAliases.definition? program.payload.definitions helper with
  | some selected => .ok selected
  | none => .error "source-mathematics-helper-association"

def target (program : Program) (name : String) : Except String CheckedDefinition := do
  let owner ← one "target-owner" (program.snapshot.contracts.filter (·.owner == program.payload.entry.name))
  let clause ← one "target-clause" (owner.clauses.filter (fun clause => clause.name == name && clause.kind == .target))
  let relation ← one "target-relation" (program.snapshot.relations.filter (·.name == clause.subject.relation))
  unless relation.kind == "zkc.language.formula/0" do throw "source-mathematics-formula-kind"
  let some name := relation.formula | throw "source-mathematics-formula-reference"
  definition program ⟨name, .math, relation.inputs, relation.outputs⟩

def declaration (path : String) (selected : CheckedDefinition) : String :=
  "abbrev " ++ path ++ ".helper : Helper := " ++ helperText selected.helper ++ "\n" ++
  "def " ++ path ++ ".body : Region dialect " ++ path ++ ".helper.inputs " ++ path ++ ".helper.outputs :=\n  " ++
    Bindings.helperRegionText selected.body ++ "\n" ++
  "theorem " ++ path ++ ".association : BodyIn imported.program.payload.definitions " ++ path ++ ".helper " ++
    path ++ ".body := by bind_structured_bodies\n\n"

def foldText (spec : FoldSpec) : String :=
  "⟨⟨" ++ ", ".intercalate [quoted spec.domain.name, typesText spec.domain.inputs,
    quoted spec.domain.field, positionText spec.domain.container.index, boolText spec.domain.indices] ++
    "⟩, " ++ ", ".intercalate [typesText spec.state, typesText spec.captures, quoted spec.step,
    quoted spec.predicate, if spec.kind == .math then ".math" else ".local"] ++ "⟩"

/-- Avoid repeated namespace components without changing unambiguous edge names. -/
def childPath (path edge : String) : String :=
  let components := path.splitOn "."
  let candidates := edge :: (List.range (components.length + 1)).map
    (fun index => edge ++ "Dependency" ++ toString index)
  path ++ "." ++ (candidates.find? fun candidate => !components.contains candidate).getD edge

def graph (program : Program) : Nat → String → CheckedDefinition → Except String String
  | 0, _, _ => .error "source-mathematics-dependency-depth"
  | fuel + 1, path, selected => do
    if selected.raw.operations.any (fun | .map _ => true | _ => false) then
      throw "source-mathematics-map-dependency"
    let mut text := declaration path selected
    let calls := Structured.MathematicsAliases.calls selected.raw
    unless calls.isEmpty do
      let helper ← one "callee-ambiguity" calls
      let callee ← definition program helper
      let calleePath := childPath path "callee"
      text := text ++ (← graph program fuel calleePath callee) ++
        "theorem " ++ path ++ ".calls : MathematicsAliases.calls " ++ path ++ ".body.erase = [" ++
        calleePath ++ ".helper] := by kernel_rfl\n\n"
    let folds := Structured.MathematicsAliases.folds selected.raw
    unless folds.isEmpty do
      let spec ← one "fold-ambiguity" folds
      unless spec.predicate.isEmpty do throw "source-mathematics-filtered-fold"
      let step ← definition program spec.stepHelper
      let stepPath := childPath path "foldStep"
      text := text ++ "def " ++ path ++ ".fold : FoldSpec := " ++ foldText spec ++ "\n" ++
        "theorem " ++ path ++ ".fold_selected : MathematicsAliases.folds " ++ path ++ ".body.erase = [" ++
        path ++ ".fold] := by kernel_rfl\n\n" ++
        (← graph program fuel stepPath step) ++
        "theorem " ++ path ++ ".fold_step : " ++ path ++ ".fold.stepHelper = " ++
        stepPath ++ ".helper := by kernel_rfl\n\n"
    return text

def source (program : Program) (targetName : String) (output : Output) : Except String String := do
  unless !targetName.isEmpty && targetName.toList.all (fun c => c.isAlphanum || c == '_') do
    throw "source-mathematics-target-spelling"
  let selected ← target program targetName
  let final ← match Structured.MathematicsAliases.finalMath? program.payload.entry.raw with
    | none => pure "theorem entry_final_absent : MathematicsAliases.finalMath? imported.program.payload.entry.raw = none := by kernel_rfl\n\n"
    | some helper => do
      let finalDefinition ← definition program helper
      pure <| (← graph program program.payload.definitions.length (targetName ++ ".entryFinal") finalDefinition) ++
        "theorem " ++ targetName ++ ".entry_final : MathematicsAliases.finalMath? imported.program.payload.entry.raw =\n" ++
        "    some " ++ targetName ++ ".entryFinal.helper := by kernel_rfl\n\n"
  return "module\n\npublic import " ++ output.sourceModule ++
    "\npublic import Zkc.Source.Structured.MathematicsAliases\n\n@[expose] public section\n\n" ++
    "/-! Generated from the selected admitted target and dependency paths.\n" ++
    "Synthetic paths assert no compiler origin metadata. All associations and\n" ++
    "selection equations are independently checked by the Lean kernel. -/\n" ++
    "set_option maxRecDepth 50000\nset_option maxHeartbeats 16000000\n" ++
    "noncomputable section\n" ++
    "namespace " ++ output.moduleName ++ "\nopen Zkc.Source Zkc.Source.Structured\n" ++
    "abbrev imported := " ++ output.sourceModule ++ ".imported\n" ++
    "abbrev original := " ++ output.sourceModule ++ ".program.snapshot\n" ++
    "def owner : ContractBinding imported := by bind_contract\n" ++
    "abbrev clause := owner.clause (owner.namedClause " ++ quoted targetName ++ ")\n" ++
    "theorem target_kind : clause.kind = .target := by kernel_rfl\n" ++
    "def relation : RelationBinding original clause.subject := by bind_contract\n" ++
    "def formula : FormulaBinding imported relation := by bind_contract\n\n" ++
    (← graph program program.payload.definitions.length targetName selected) ++
    "theorem " ++ targetName ++ ".selected : formula.definition.helper = " ++ targetName ++ ".helper := by kernel_rfl\n\n" ++
    final ++ "end " ++ output.moduleName ++ "\n"

end ZkcTools.StructuredSource.MathematicsAliases
