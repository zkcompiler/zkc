import Zkc.Source.Structured.ContractInstantiation
import Mathlib.Algebra.Ring.Int.Defs

open Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredContractInvocation
set_option smartUnfolding false

private def leaf : Function :=
  ⟨"leaf", .protocol, .publicDef, [.boolean, .boolean], [.boolean],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["V"]]⟩, [], some (.protocol ⟨"leaf", []⟩),
    .block [.instruction .booleanEqual [0, 1] [.boolean] [] ""] (.ret [0])⟩
private def caller : Function :=
  ⟨"main", .protocol, .publicDef, [.index, .boolean], [],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], []⟩, [], some (.protocol ⟨"main", []⟩),
    .block [.instruction (.protocolRepeat 0 2 ["P", "V"] []) [0, 1] []
      [.region [.index, .boolean] [] (.block [
        .instruction (.protocolApply "leaf" ["V", "P"]) [1, 1] [.boolean] [] "call"] (.yield []))]
      "loop"] (.ret [])⟩
private def snapshot : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], [],
    [.function leaf, .function caller], [⟨"leaf", []⟩, ⟨"main", []⟩], blsRows, {}⟩
noncomputable section
private def leafBody : Region protocolDialect [.boolean, .boolean] [.boolean] :=
  .letOp (.mark "") .nil .nil
    (.letOp (.calculate .booleanEqual rfl) (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
private def checkedLeaf : CheckedProtocol :=
  ⟨⟨"leaf", ["P", "V"], [.boolean, .boolean], [.boolean], [[0, 1], [0, 1]], [[1]]⟩,
    leafBody.erase, leafBody, leafBody.elaborate_erase⟩
private def spec : RepeatSpec := ⟨[], [.boolean], [0, 1], [], 2⟩
private def actualOperands : Operands [.index, .boolean] checkedLeaf.inputs :=
  .cons (.there .here) (.cons (.there .here) .nil)
private def callback : Region protocolDialect [.index, .boolean] [] :=
  .letOp (.mark "call") .nil .nil
    (.letOp (.protocolApply checkedLeaf.signature [1, 0] "call") actualOperands .nil (.ret .nil))
private def callerBody : Region protocolDialect [.index, .boolean] [] :=
  .letOp (.mark "loop") .nil .nil
    (.letOp (.repeat spec "loop") (.cons .here (.cons (.there .here) .nil))
      (.cons callback .nil) (.ret .nil))
private def checkedCaller : CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], [.index, .boolean], [], [[0, 1], [0, 1]], []⟩,
    callerBody.erase, callerBody, callerBody.elaborate_erase⟩
private def payload : UnitPayload :=
  ⟨[], [checkedLeaf, checkedCaller], ⟨1, by decide⟩, by decide +kernel, by decide +kernel,
    by rfl, by decide +kernel, by decide +kernel⟩
private def imported : Imported snapshot := ⟨⟨snapshot, payload⟩, by rfl⟩
private def owner : ContractBinding imported := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
private def callerOwner : ContractBinding imported := ⟨⟨1, by decide⟩, ⟨1, by decide⟩, rfl⟩
private def call : CheckedApplication owner [.index, .boolean] where
  caller := callerOwner
  roles := [1, 0]
  site := "call"
  operands := actualOperands
  occurrence := .next (.mark "loop") .nil .nil _
    (.repeatBody spec "loop" _ callback (.ret .nil)
      (.next (.mark "call") .nil .nil _ (.here (.ret .nil))))
  substitution := by unfold ValidSubstitution; decide +kernel
private def parent : InvocationCoordinate := ⟨0, []⟩
private def first : call.Iterations := by
  intro index
  have same : index = ⟨0, by decide⟩ := by
    apply Fin.ext
    change index.val = 0
    have bound := index.isLt
    change index.val < 1 at bound
    omega
  subst index
  exact ⟨0, by decide⟩
private def second : call.Iterations := by
  intro index
  have same : index = ⟨0, by decide⟩ := by
    apply Fin.ext
    change index.val = 0
    have bound := index.isLt
    change index.val < 1 at bound
    omega
  subst index
  exact ⟨1, by decide⟩
private def input0 : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.input .here, ⟨1, by decide⟩, by decide⟩
private def input1 : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.input (.there .here), ⟨1, by decide⟩, by decide⟩
private def otherRole : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.input .here, ⟨0, by decide⟩, by decide⟩
private def environment (self : Nat) : Environment (Component (assignment Int Int)) [.index, .boolean] :=
  (Values.cons (some 0) (.cons (some (self == 0)) .nil)).get
private def returned (_ : Nat) : Values (Component (assignment Int Int)) [.boolean] := .cons (some true) .nil

example : call.occurrence.position = [1, 0, 1] := rfl
example : call.occurrence.repeats = [([1], 2)] := rfl
example : call.childInvocation parent first ≠ call.childInvocation parent second := by decide +kernel
-- Equal SSA operands induce equal runtime reads for the same role only.
example : input0.read (({} : ProtocolContext).enter call.site call.roles) (call.boundary {} environment returned) =
    input1.read (({} : ProtocolContext).enter call.site call.roles) (call.boundary {} environment returned) := rfl
example : input0.read (({} : ProtocolContext).enter call.site call.roles) (call.boundary {} environment returned) =
    some true := rfl
example : otherRole.read (({} : ProtocolContext).enter call.site call.roles) (call.boundary {} environment returned) =
    some false := rfl

-- Logical slots are not automatically identified by those aliased SSA operands.
private def choices : LogicalAssignments (assignment Int Int) owner (call.childInvocation parent first) where
  parameters type selector := match type with
    | .boolean => some (selector.port.index == 0)
    | _ => none
  witnesses _ _ := none
example : choices.parameters .boolean input0 = some true := rfl
example : choices.parameters .boolean input1 = some false := rfl
example : True := by
  fail_if_success have wrong : LogicalAssignments (assignment Int Int) owner (call.childInvocation parent second) := choices
  trivial

-- The labels reject accidental reuse, but explicitly copying a logical choice
-- is legal. Neither label nor this copy proves that either iteration was reached.
private def copiedChoices : LogicalAssignments (assignment Int Int) owner (call.childInvocation parent second) :=
  ⟨choices.parameters, choices.witnesses⟩
example : copiedChoices.parameters .boolean input0 = choices.parameters .boolean input0 := rfl

-- Explicitly supplied logical values need not have a matching caller port type.
private def extraValue : AssignmentSource (assignment Int Int) callerOwner (.vector scalarDomain) :=
  .supplied [3, 4, 3]
private def callerAssignments : LogicalAssignments (assignment Int Int) callerOwner parent :=
  ⟨fun _ _ => none, fun _ _ => none⟩
private def callerBoundary : BoundaryValuation (assignment Int Int) callerOwner.protocol.inputs [] :=
  ⟨fun _ => .cons (some 2) (.cons (some false) .nil), fun _ => .nil⟩
example : extraValue.read {} callerBoundary callerAssignments = some [3, 4, 3] := rfl

end
end Tests.StructuredContractInvocation
