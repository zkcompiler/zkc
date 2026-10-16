module

public import Zkc.Source.Structured.Formation
public import Zkc.Source.Structured.PreparationAdmission

@[expose] public section

/-! Source helper lowering and bounded declaration ordering. Formed records and
raw formation are available separately to semantic consumers. -/

namespace Zkc.Source.Structured

def checkDefinition (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (definition : Definition) : Except String CheckedDefinition := do
  let kind ← match definition.kind with
    | .protocol => throw "structured-helper-kind"
    | .math => pure HelperKind.math
    | .local => pure HelperKind.local
  let raw ← match definition with
    | .function f =>
      (lowerBlock snapshot domains summaries f.kind 64 f.inputs
        (f.preconditions.map fun bound => (bound.index, bound.container)) .function f.body).run' {}
    | .finite f => do
      let spec ← resolveFold snapshot domains .local f.domain f.step f.predicate
        f.inputs f.outputs (List.range f.inputs.length) []
      let raw : RawRegion Ty Op := .letOp (.fold spec) (List.range f.inputs.length)
        f.outputs .nil (.ret (List.range f.outputs.length))
      pure raw
    | .realization declaration => do
      declaration.validate snapshot
      pure declaration.raw
    | .map declaration => do
      declaration.validate snapshot
      pure declaration.raw
  formDefinition definition kind raw

/-- The retained declaration determines every derived operand and result index. -/
theorem checkDefinition_realization_raw {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {declaration : RealizationDeclaration} {checked : CheckedDefinition}
    (accepted : checkDefinition snapshot domains summaries (.realization declaration) = .ok checked) :
    checked.raw = declaration.raw := by
  cases validated : declaration.validate snapshot with
  | error error => simp [checkDefinition, Definition.kind, validated, Except.bind, Except.pure, pure, bind] at accepted
  | ok value =>
    cases value
    apply formDefinition_raw
    simpa only [checkDefinition, Definition.kind, validated, Except.bind, Except.pure, pure, bind] using accepted

/-- Map derivation retains the complete ordered input tuple and its sole result. -/
theorem checkDefinition_map_raw {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {declaration : MapDeclaration} {checked : CheckedDefinition}
    (accepted : checkDefinition snapshot domains summaries (.map declaration) = .ok checked) :
    checked.raw = declaration.raw := by
  cases validated : declaration.validate snapshot with
  | error error => simp [checkDefinition, Definition.kind, validated, Except.bind, Except.pure, pure, bind] at accepted
  | ok value =>
    cases value
    apply formDefinition_raw
    simpa only [checkDefinition, Definition.kind, validated, Except.bind, Except.pure, pure, bind] using accepted

structure OrderedDefinition where
  definition : CheckedDefinition
  depth : Nat

/-- Kahn ordering over the stored definitions. The recursion bound is the number
of declarations, not evaluation fuel. Shared dependencies are never expanded. -/
def orderDefinitions : Nat → List CheckedDefinition → List OrderedDefinition →
    Except String (List OrderedDefinition)
  | _, [], ordered => .ok ordered
  | 0, _ :: _, _ => .error "structured-helper-cycle"
  | remaining + 1, pending, ordered => do
    let ready := pending.find? fun definition =>
      definition.dependencies.all fun name => ordered.any (·.definition.name == name)
    let some next := ready | throw "structured-helper-cycle"
    let dependencies : List OrderedDefinition ← next.dependencies.mapM fun name =>
      requireSome (ordered.find? (·.definition.name == name)) "structured-helper-resolution"
    let depth : Nat := (dependencies.map (·.depth + 1)).foldl max 0
    if depth > 64 then throw "structured-reference-depth"
    orderDefinitions remaining (pending.filter (·.name != next.name))
      (ordered ++ [⟨next, depth⟩])

end Zkc.Source.Structured
