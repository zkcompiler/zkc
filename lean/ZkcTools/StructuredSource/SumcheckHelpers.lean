module

public import ZkcTools.StructuredSource.Presentation
public import ZkcExamples.Structured.OriginalSumcheckChecks

@[expose] public section

/-! Candidate discovery for the installed Sumcheck implementation templates.
Private realization names come from actual dependency edges. Selection is
untrusted: every emitted association checks membership, full ABI and body.
No root name, historical ordinal or generated-name prefix selects a helper. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.SumcheckHelpers
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcTools.StructuredSource.Presentation

def one {α : Type} (label : String) : List α → Except String α
  | [value] => .ok value
  | _ => .error ("sumcheck-helper-association-" ++ label)

def lookup (definitions : List CheckedDefinition) (helper : Helper) :
    Except String CheckedDefinition :=
  one helper.name (definitions.filter (·.helper == helper))

def children (definitions : List CheckedDefinition) (helper : Helper) :
    Except String (List CheckedDefinition) := do
  (← lookup definitions helper).helpers.mapM (lookup definitions)

structure Selection where
  collection : MultilinearCollectBodies.Bindings
  restriction : MultilinearPrefixBodies.Bindings

def analyze (definitions : List CheckedDefinition) : Except String Selection := do
  let first ← children definitions MapFirstBodies.firstHelper
  let collection ← one "collection" (first.filter fun definition =>
    definition.raw.operations.any fun op => match op with | .collect _ => true | _ => false)
  let spec ← one "collection-operation" (collection.raw.operations.filterMap fun op =>
    match op with | .collect spec => some spec | _ => none)
  let computation ← one "collection-callback" (← children definitions spec.bodyHelper)
  let wrapper ← children definitions MapPrefixBodies.foldWrapperHelper
  let fold ← one "prefix-fold" (wrapper.filter fun definition =>
    definition.raw.operations.any fun op => match op with | .fold _ => true | _ => false)
  let terminal ← children definitions SumcheckHelperBodies.checkTableHelper
  let values ← one "values-realization" (terminal.filter fun definition =>
    definition.helpers.contains MapPrefixBodies.valuesHelper)
  return ⟨⟨collection.name, spec.domain.name, spec.body, computation.name⟩,
    ⟨fold.name, values.name⟩⟩

def source (definitions : List CheckedDefinition) (table : String) : Except String String := do
  let selected ← analyze definitions
  let c := selected.collection
  let p := selected.restriction
  return "abbrev collectBindings : MultilinearCollectBodies.Bindings :=\n  ⟨" ++
    ", ".intercalate ([c.collection, c.domain, c.callback, c.computation].map quoted) ++ "⟩\n\n" ++
    "abbrev prefixBindings : MultilinearPrefixBodies.Bindings :=\n  ⟨" ++
    ", ".intercalate ([p.fold, p.values].map quoted) ++ "⟩\n\n" ++
    "theorem first_bodies : MapFirstContracts.Bodies " ++ table ++ " collectBindings := by\n  bind_structured_bodies\n\n" ++
    "theorem prefix_bodies : MapPrefixContracts.Bodies " ++ table ++ " prefixBindings := by\n  bind_structured_bodies\n\n" ++
    "theorem producer_bodies : SumcheckUnitContracts.Bodies " ++ table ++ " where\n" ++
    "  first := ⟨collectBindings, first_bodies⟩\n" ++
    String.join (["sums", "empty", "append", "values", "width", "«variables»"].map fun field =>
      "  " ++ field ++ " := by bind_structured_bodies\n") ++ "\n" ++
    "theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies " ++ table ++ " :=\n" ++
    "  ⟨prefixBindings, { first := ⟨collectBindings, first_bodies⟩\n" ++
    "                     restriction := prefix_bodies\n" ++
    "                     check := by bind_structured_bodies\n" ++
    "                     checkTable := by bind_structured_bodies }⟩\n\n"

end ZkcTools.StructuredSource.SumcheckHelpers
