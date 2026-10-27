module

public import ZkcTools.StructuredSource.Methods.SumcheckRoot
public import Zkc.Construction.SourceDelivery

@[expose] public section

/-! Proposals for construction bindings, obtained from admitted source paths and
the actual artifact's SSA frame. This analysis grants no simulation authority.
Generated full body equations and structural certificates are checked separately. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Call where
  application : String
  library : String
  query : Template
  delivery : Template
  messages : List Template
  deriving Repr

structure Loop where
  instruction : Nat
  offset : Nat
  site : String
  maximum : Nat
  count : Nat
  initial : List Nat
  yielded : List Nat
  body : List Zkc.Construction.Instruction
  call : Call
  deriving Repr

structure Layout where
  context : Zkc.Construction.Context
  calls : List Call
  loops : List Loop
  arity : Nat
  deriving Repr

def unique {α : Type} (label : String) : List α → Except String α
  | [value] => .ok value
  | _ => .error ("construction-binding-" ++ label)

/-- Enumerate source applications, in source order. This installation supports
a straight root and a single repeated library; effects in other regions refuse. -/
def sourceCalls (program : Program) (context : Zkc.Construction.Context) : Except String (List Call) := do
  let some root := SourceOccurrences.root program.snapshot context
    | throw "construction-binding-source-root"
  let all := SourceDelivery.templates program.snapshot context
  let mut calls := []
  for instruction in root.body.topLevelInstructions do
    match instruction with
    | .instruction (.protocolApply library roles) _ _ [] application =>
        unless roles == context.roles do throw "construction-binding-call-roles"
        let queries := all.filter fun template =>
          template.steps.head? == some (⟨"apply", context.entry, application⟩ : Step) &&
          template.querySite?.isSome
        let query ← unique "source-query" queries
        let pair ← unique "source-delivery" (context.draws.filterMap fun (draw, delivery) =>
          if query.querySite? == some draw then SourceDelivery.resolve program.snapshot context draw delivery else none)
        unless pair.1 == query do throw "construction-binding-query-association"
        let [⟨"apply", _, _⟩, ⟨"repeat", owner, _⟩] := query.steps
          | throw "construction-binding-call-path"
        unless owner == library do throw "construction-binding-library-association"
        let messages := all.filter fun template => template.steps == query.steps && template.messageSite?.isSome
        unless messages.length == 3 do throw "construction-binding-family-message-abi"
        calls := calls ++ [⟨application, library, query, pair.2, messages⟩]
    | .instruction (.protocolRepeat ..) .. => throw "construction-binding-root-repeat"
    | _ => pure ()
  unless !calls.isEmpty do throw "construction-binding-no-call"
  return calls

def templates (body : List Zkc.Construction.Instruction) : List Template :=
  body.filterMap fun instruction => match instruction.operation with
    | .observe _ template | .challenge _ _ template => some template
    | _ => none

/-- Traverse forward SSA. A loop is associated by its full source-qualified
templates, never by its instruction count, name, or position in a fixed layout. -/
def analyzeWithContext (program : Program) (context : Zkc.Construction.Context)
    (artifact : Participant) : Except String Layout := do
  let calls ← sourceCalls program context
  let mut offset := artifact.inputs.length
  let mut loops := []
  for (instruction, index) in artifact.instructions.zipIdx do
    match instruction.operation with
    | .loop site maximum yielded =>
        let retained := templates instruction.body
        let call ← unique "loop-source-association" (calls.filter fun call =>
          retained.contains call.query && retained.contains call.delivery &&
          call.messages.all retained.contains)
        unless retained.all (fun template => template == call.query || call.messages.contains template) do
          throw "construction-binding-unclaimed-template"
        let count :: initial := instruction.operands | throw "construction-binding-loop-operands"
        unless (count :: initial).all (· < offset) do throw "construction-binding-forward-reference"
        loops := loops ++ [⟨index, offset, site, maximum, count, initial, yielded, instruction.body, call⟩]
    | _ =>
        unless instruction.body.isEmpty do throw "construction-binding-unclaimed-region"
        unless instruction.operands.all (· < offset) do throw "construction-binding-forward-reference"
    offset := offset + instruction.results.length
  unless loops.map (·.call.application) == calls.map (·.application) do
    throw "construction-binding-call-order"
  unless artifact.returned.all (· < offset) do throw "construction-binding-return-reference"
  return ⟨context, calls, loops, offset⟩

def analyze (program : Program) (artifact : Participant) : Except String Layout := do
  let some context := exportContext program.snapshot artifact
    | throw "construction-binding-export-context"
  analyzeWithContext program context artifact

end ZkcTools.ConstructionBindings
