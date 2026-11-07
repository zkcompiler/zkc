module

public import Zkc.Construction.DomainCorrespondence
public import Zkc.Construction.ConnectionFiniteFold
public import Zkc.Construction.LayoutPermutation

@[expose] public section

/-! Embedded computations use the original finite-domain and helper semantics.
The callback is checked source; tests do not supply an opaque success equation. -/
set_option autoImplicit false
set_option smartUnfolding false
namespace Tests.EmbeddedMath
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := [⟨"range", [.index, .index], [.range 0 1], 0⟩]
  relations := []
  bindings := []
  definitions := [
    .function ⟨"sum", .math, .privateDef, [.index, .index, .index, .index], [.index], none, [], none,
      .block [.instruction .indexWrappingAdd [0, 1] [.index] [] ""] (.ret [0])⟩,
    .function ⟨"skip", .math, .privateDef, [.index, .index, .index], [.boolean], none, [], none,
      .block [.instruction (.booleanConstant false) [] [.boolean] [] ""] (.ret [0])⟩,
    .function ⟨"main", .protocol, .publicDef, [.boolean], [.boolean],
      some ⟨["P"], [["P"]], [["P"]]⟩, [], some (.protocol ⟨"main", []⟩), .block [] (.ret [0])⟩]
  contracts := [⟨"main", []⟩]
  catalogue := ⟨[], [], []⟩

private def program : Program := (Structured.check snapshot).toOption.get (by decide +kernel)
private def model : DomainModel := ringModel Int Int

example : (Domain.resolveFiniteFold program "range" "sum" ""
    [.data .index, .data .index, .data .index] [.data .index]).isOk = true := by decide +kernel

/-- The original callback sees each actual induction and its previous carry. -/
example : Domain.finiteFold model program "range" "sum" "" [.data .index]
    [.data (.index 2), .data (.index 5), .data (.index 10)] =
      .returned [.data (.index 19)] := by rfl

example : Domain.finiteFold model program "range" "sum" "skip" [.data .index]
    [.data (.index 2), .data (.index 5), .data (.index 10)] =
      .returned [.data (.index 10)] := by rfl

example : Domain.finiteFold model program "range" "sum" "" [.data .index]
    [.data (.index 2), .data (.index 2), .data (.index 10)] =
      .returned [.data (.index 10)] := by rfl

/-- Even an empty interval must pass the source domain's machine-index checks. -/
example : Domain.finiteFold model program "range" "sum" "" [.data .index]
    [.data (.index indexLimit), .data (.index indexLimit), .data (.index 10)] =
      .stopped .refused := by rfl

example : (Domain.resolveFiniteFold program "missing" "sum" ""
    [.data .index, .data .index, .data .index] [.data .index]).isOk = false := by decide +kernel

example : (Domain.resolveFiniteFold program "range" "sum" ""
    [.data .index, .data .index, .data .boolean] [.data .boolean]).isOk = false := by decide +kernel

example : (Domain.resolveFiniteFold program "range" "sum" "sum"
    [.data .index, .data .index, .data .index] [.data .index]).isOk = false := by decide +kernel

/-- Empty traversal still needs the exact callback declaration. -/
example : Domain.finiteFold model program "range" "missing" "" [.data .index]
    [.data (.index 2), .data (.index 2), .data (.index 10)] =
      .stopped .refused := by rfl

private def region : InstructionRegion := ⟨[.data .index, .data .index], [], [1, 0]⟩
private def computation : Zkc.Construction.Instruction := ⟨.mathCompute, [1, 0], [.data .index, .data .index], [region]⟩

/-- Both the operand and return permutation matter, even at equal types. -/
example (domainModel : DomainModel) (original : Program) (context : Context) :
    Domain.step domainModel original context computation [.data (.index 3), .data (.index 9)] =
      .done [.data (.index 3), .data (.index 9), .data (.index 3), .data (.index 9)] := rfl

example : checkClosedStep .local (fun _ _ _ _ => true) [.data .boolean]
    ⟨.mathCompute, [0], [.data .boolean],
      [⟨[.data .boolean], [⟨.guard "hidden", [0], [], []⟩], [0]⟩]⟩ =
      .error "construction-math-operation" := rfl

example : LayoutPermutation.reindexInstructions (· + 1) 1 [computation] =
    [{ computation with operands := [2, 1] }] := by decide +kernel

example (domainModel : DomainModel) (original : Program) (context : Context) :
    Domain.Correspondence.Step (model := domainModel) (program := original) (context := context) computation
      (Domain.View.mathCompute original [1, 0] [.data .index, .data .index] region Domain.View.empty) :=
  Domain.Correspondence.mathCompute [1, 0] [.data .index, .data .index] region Domain.Correspondence.empty

private def spec : FoldSpec :=
  (Domain.resolveFiniteFold program "range" "sum" ""
    [.data .index, .data .index, .data .index] [.data .index]).toOption.get (by decide +kernel)

/-- The common connection works for every domain input, including refused
finite-index bounds; it does not assume that the selected callback is reached. -/
private noncomputable def connected (lower upper initial : Nat) :=
  ConnectionFiniteFold.simulation model program "range" "sum" "" spec
    (by kernel_rfl) (.cons lower (.cons upper (.cons initial .nil)))
    (by kernel_rfl) (by kernel_rfl)
    [.data (.index initial), .data (.index lower), .data (.index upper)] [1, 2, 0]
    (by rfl)

/-- Callback semantics and refusal are both taken from the admitted source. -/
example : Domain.View.finiteFold model program "range" "sum" "" [1, 2, 0]
    [.data .index] [.data (.index 10), .data (.index 2), .data (.index 5)] =
      .done [.data (.index 10), .data (.index 2), .data (.index 5), .data (.index 19)] := rfl

example : Domain.View.finiteFold model program "range" "sum" "" [1, 2, 0]
    [.data .index] [.data (.index 10), .data (.index indexLimit), .data (.index indexLimit)] =
      .halt .refused := rfl

#print axioms connected

end Tests.EmbeddedMath
