module

public import Zkc.Construction.ConnectionMathFrames
public import Zkc.Construction.ConnectionTargetPrefix

@[expose] public section

/-! Finite connection evidence for an inlined closed mathematical region.
The indices retain the exact typed source body, ordered source locations,
physical extent, target instruction spine and complete return selection.

This carrier does not turn a mathematical reference law into a lowering law.
Only operation and region constructors can build evidence; there is no
whole-body semantic-equation constructor. Both selected arms are explicit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ConnectionMathRegion
open Zkc.Source Zkc.Source.Structured ConnectionCalculations ConnectionMathFrames
abbrev TargetBlock := ConnectionTargetPrefix.TargetBlock

def sourceRegions (operation : Calculation) : Regions dialect operation.op.regions := by
  cases operation <;> exact .nil

/-- Source variables in a closed arm occupy the ordered capture row. -/
def arguments (count : Nat) : List Original.Location := allocated 0 count

/-- An exact actual declaration and its lexical dependency prefix. Suffix
freshness prevents a later declaration from replacing its name. -/
structure Declaration (definitions : List CheckedDefinition) (definition : CheckedDefinition) where
  before : List CheckedDefinition
  after : List CheckedDefinition
  declarations : definitions = before ++ definition :: after
  fresh : after.all (fun other => other.name != definition.name) = true

theorem Declaration.member {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (association : Declaration definitions definition) : definition ∈ definitions := by
  rw [association.declarations]
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-- A concrete index makes the existing nonempty-table obligation available. -/
def Declaration.index {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (association : Declaration definitions definition) : Fin definitions.length :=
  ⟨association.before.length, by
    have length := congrArg List.length association.declarations
    simp only [List.length_append, List.length_cons] at length
    omega⟩

/-- The parameter table is the actual lexical source prefix. Physical source
slots are immutable; a result tuple is appended physically and prepended in the
typed source environment. Selected arms receive only their explicit captures.
The closed-arm formation check remains a separate all-arm obligation. -/
inductive Alignment (definitions : List CheckedDefinition) :
    {inputs outputs : List Ty} → Region dialect inputs outputs →
    List Original.Location → Nat → TargetBlock → List Nat → Nat → Type 1 where
  | returned {inputs outputs : List Ty} (positions : Operands inputs outputs)
      (locations : List Original.Location) (size : Nat) (references : List Nat)
      (selected : operandReferences locations positions = some references) :
      Alignment definitions (.ret positions) locations size
        (fun _ => Domain.View.empty) references size
  | stopped {inputs outputs : List Ty} (reason : PIR.Stop)
      (locations : List Original.Location) (size : Nat) (references : List Nat) (finalSize : Nat) :
      Alignment definitions (Region.stop (Γ := inputs) (out := outputs) reason) locations size
        (fun _ _ => .halt reason) references finalSize
  | calculation {inputs outputs : List Ty} (operation : Calculation)
      (operands : Operands inputs operation.op.arguments)
      {next : Region dialect (operation.op.results ++ inputs) outputs}
      (locations : List Original.Location) (size : Nat) (references : List Nat)
      (selected : operandReferences locations operands = some references)
      (inputData : operation.op.arguments.all Domain.localType = true)
      (outputData : operation.op.results.all Domain.localType = true)
      {rest : TargetBlock} {yielded : List Nat} {finalSize : Nat}
      (tail : Alignment definitions next
        (allocated size operation.op.results.length ++ locations)
        (size + operation.op.results.length) rest yielded finalSize) :
      Alignment definitions
        (.letOp operation.op operands (sourceRegions operation) next)
        locations size (fun model => Domain.View.sequence
          (Domain.View.calculation model operation references (operation.op.results.map .data))
          (rest model)) yielded finalSize
  | selected {inputs captures results outputs : List Ty}
      (program : Program)
      (condition : Var inputs .boolean) (captured : Operands inputs captures)
      (yes no : Region dialect captures results)
      {next : Region dialect (results ++ inputs) outputs}
      (locations : List Original.Location) (size selector : Nat) (references : List Nat)
      (selected : operandReferences locations (.cons condition captured) = some (selector :: references))
      (captureData : captures.all Domain.localType = true)
      (resultData : results.all Domain.localType = true)
      (yesRegion noRegion : InstructionRegion)
      (yesInputs : yesRegion.inputs = captures.map ValueSort.data)
      (noInputs : noRegion.inputs = captures.map ValueSort.data)
      (formed : checkClosedArms .math (Domain.closedOperationMatches program)
        (results.map ValueSort.data) yesRegion noRegion = .ok ())
      {yesBody noBody rest : TargetBlock} {yesSize noSize finalSize : Nat} {yielded : List Nat}
      (yesConnected : Alignment definitions yes (arguments captures.length) captures.length
        yesBody yesRegion.yielded yesSize)
      (noConnected : Alignment definitions no (arguments captures.length) captures.length
        noBody noRegion.yielded noSize)
      (tail : Alignment definitions next (allocated size results.length ++ locations)
        (size + results.length) rest yielded finalSize) :
      Alignment definitions
        (.letOp (.branch captures results) (.cons condition captured) (.cons yes (.cons no .nil)) next)
        locations size (fun model => Domain.View.sequence
          (Domain.View.mathBranch program selector references (results.map ValueSort.data)
            yesRegion noRegion (yesBody model) (noBody model)) (rest model)) yielded finalSize
  | invoke {inputs outputs : List Ty}
      (linked : DeclarationsLinked [] definitions) (definition : CheckedDefinition)
      (member : definition ∈ definitions)
      (operands : Operands inputs definition.inputs)
      {next : Region dialect (definition.outputs ++ inputs) outputs}
      (locations : List Original.Location) (size : Nat) (references : List Nat)
      (selected : operandReferences locations operands = some references)
      (inputData : definition.inputs.all Domain.localType = true)
      (outputData : definition.outputs.all Domain.localType = true)
      {spine : ConnectionTargetPrefix.Prefix} {rest : TargetBlock}
      {returned yielded : List Nat} {middleSize finalSize : Nat}
      (head : Alignment definitions definition.body (references.map Original.Location.data)
        size spine.block returned middleSize)
      (tail : Alignment definitions next (returned.map Original.Location.data ++ locations)
        middleSize rest yielded finalSize) :
      Alignment definitions (.letOp (.invoke definition.helper) operands .nil next)
        locations size (spine.plug rest) yielded finalSize
  | finiteFold {inputs outputs : List Ty}
      (program : Program) (after : List CheckedDefinition)
      (split : program.payload.definitions = definitions ++ after)
      (domain step predicate : String) (spec : FoldSpec)
      (fresh : after.all (fun definition => (Op.fold spec).helpers.all
        (fun helper => definition.name != helper.name)) = true)
      (resolved : Domain.resolveFiniteFold program domain step predicate
        (spec.arguments.map ValueSort.data) (spec.state.map ValueSort.data) = .ok spec)
      (operands : Operands inputs spec.arguments)
      {next : Region dialect (spec.state ++ inputs) outputs}
      (locations : List Original.Location) (size : Nat) (references : List Nat)
      (selected : operandReferences locations operands = some references)
      (inputData : spec.arguments.all Domain.localType = true)
      (outputData : spec.state.all Domain.localType = true)
      {rest : TargetBlock} {yielded : List Nat} {finalSize : Nat}
      (tail : Alignment definitions next (allocated size spec.state.length ++ locations)
        (size + spec.state.length) rest yielded finalSize) :
      Alignment definitions (.letOp (.fold spec) operands .nil next)
        locations size (fun model => Domain.View.sequence
          (Domain.View.finiteFold model program domain step predicate references (spec.state.map .data))
          (rest model)) yielded finalSize
  | bind {inputs intermediate outputs : List Ty} {body : Region dialect inputs intermediate}
      {next : Region dialect (intermediate ++ inputs) outputs}
      {locations : List Original.Location} {size middleSize finalSize : Nat}
      {spine : ConnectionTargetPrefix.Prefix} {rest : TargetBlock}
      {intermediateReferences yielded : List Nat}
      (intermediateData : intermediate.all Domain.localType = true)
      (head : Alignment definitions body locations size spine.block intermediateReferences middleSize)
      (tail : Alignment definitions next
        (intermediateReferences.map Original.Location.data ++ locations)
        middleSize rest yielded finalSize) :
      Alignment definitions (.bind body next) locations size
        (spine.plug rest) yielded finalSize

end Zkc.Construction.ConnectionMathRegion
