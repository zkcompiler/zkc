module

public import Zkc.Source.Structured.Vocabulary

@[expose] public section

/-! Conservative identity summaries for the shared Math helper table. These
summaries transfer exact returned-input identities, not equality of values or
extents. Formation and bound checks still inspect every original definition. -/

namespace Zkc.Source.Structured

structure IdentitySummary where
  name : String
  outputs : List (Option Nat)

abbrev IdentitySummaries := List IdentitySummary

/-- Each known result names an operand's original SSA position. No arithmetic,
fold result, or changing loop state is identified with an input. -/
def resultIdentities (summaries : IdentitySummaries) (descriptor : Descriptor)
    (operands : List Nat) (resultCount : Nat) : List (Option Nat) :=
  match descriptor with
  | .call name =>
    match summaries.find? (·.name == name) with
    | some summary =>
      (List.range resultCount).map fun result =>
        (summary.outputs[result]?.bind id).bind fun input => operands[input]?
    | none => List.replicate resultCount none
  | .select _ =>
    match operands with
    | [_, left, right] =>
      if left == right && resultCount == 1 then [some left]
      else List.replicate resultCount none
    | _ => List.replicate resultCount none
  | _ => List.replicate resultCount none

def Function.identitySummary (summaries : IdentitySummaries) (function : Function) :
    IdentitySummary :=
  let .block instructions terminal := function.body
  let origins := instructions.foldl (fun origins instruction =>
    let .instruction descriptor operands results _ _ := instruction
    let forwarded := (resultIdentities summaries descriptor operands results.length).map fun input =>
      input.bind fun index => origins[index]?.bind id
    forwarded ++ origins) ((List.range function.inputs.length).map some)
  let outputs := match terminal with
    | .ret refs => refs.map fun index => origins[index]?.bind id
    | _ => List.replicate function.outputs.length none
  ⟨function.name, outputs⟩

def Function.identityDependencies (function : Function) : List String :=
  let .block instructions _ := function.body
  instructions.filterMap fun (.instruction descriptor _ _ _ _) =>
    match descriptor with | .call name => some name | _ => none

/-- Summarize each helper once after its Math callees. The declaration count
only bounds this static ordering; shared calls are never expanded. Cycles are
refused, and non-Math or missing callees remain for ordinary admission to reject. -/
def summarizeIdentities : Nat → List Function → IdentitySummaries →
    Except String IdentitySummaries
  | _, [], summaries => .ok summaries
  | 0, _ :: _, _ => .error "structured-helper-cycle"
  | remaining + 1, pending, summaries => do
    let ready := pending.find? fun function => function.identityDependencies.all fun name =>
      !(pending.any (·.name == name)) || summaries.any (·.name == name)
    let some next := ready | throw "structured-helper-cycle"
    summarizeIdentities remaining (pending.filter (·.name != next.name))
      (next.identitySummary summaries :: summaries)

def Snapshot.identitySummaries (snapshot : Snapshot) : Except String IdentitySummaries :=
  let functions := snapshot.definitions.filterMap fun definition =>
    match definition with
    | .function function => if function.kind == .math then some function else none
    | .finite _ => none
  summarizeIdentities functions.length functions []

end Zkc.Source.Structured
