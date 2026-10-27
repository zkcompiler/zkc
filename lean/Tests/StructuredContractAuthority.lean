import Zkc.Source.Structured.ContractObligations
import Mathlib.Algebra.Ring.Int.Defs

open Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredContractAuthority
set_option smartUnfolding false
noncomputable section

private def root : Function :=
  ⟨"main", .protocol, .publicDef, [.vector scalarDomain, .field scalarDomain], [.boolean],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["V"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [.instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0])⟩
private def subject : RelationApplication := ⟨"Initial", [⟨.input, 0, "P"⟩, ⟨.input, 1, "V"⟩]⟩
private def snapshot : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [],
    [⟨"Initial", .publicDef, "opaque", "sum", "0", [.vector scalarDomain, .field scalarDomain],
      [.boolean], ["parameter", "statement"], none, []⟩], [], [.function root],
    [⟨"main", [⟨.input, "initial_sum", subject, none, none⟩]⟩], blsRows, {}⟩
private def body : Region protocolDialect [.vector scalarDomain, .field scalarDomain] [.boolean] :=
  .letOp (.mark "") .nil .nil
    (.letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret (.cons .here .nil)))
private def checked : CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], [.vector scalarDomain, .field scalarDomain], [.boolean], [[0, 1], [0, 1]], [[1]]⟩,
    body.erase, body, body.elaborate_erase⟩
private def payload : UnitPayload :=
  ⟨[], [checked], ⟨0, by decide⟩, by decide +kernel, by decide +kernel,
    by rfl, by decide +kernel, by decide +kernel⟩
private def imported : Imported snapshot := ⟨⟨snapshot, payload⟩, by rfl⟩
private def owner : ContractBinding imported := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
private def invocation : InvocationCoordinate := ⟨0, []⟩
private def tableP : BoundarySelector owner.protocol.signature (.vector scalarDomain) :=
  ⟨.input .here, ⟨0, by decide⟩, by decide⟩
private def tableV : BoundarySelector owner.protocol.signature (.vector scalarDomain) :=
  ⟨.input .here, ⟨1, by decide⟩, by decide⟩
private def claimV : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  ⟨.input (.there .here), ⟨1, by decide⟩, by decide⟩
private def boundary : ContractBoundaryValues owner Int Int :=
  ⟨fun role => .cons (some (if role = 0 then [1] else [2])) (.cons (some 1) .nil),
    fun _ => .cons none .nil⟩
private def emptyAssignments : LogicalAssignments (assignment Int Int) owner invocation :=
  ⟨fun _ _ => none, fun _ _ => none⟩

-- The choice is explicit in the statement: a fixed table or an authored read
-- of one participant's runtime table. There is no default authority conversion.
private def choose (source : AssignmentSource (assignment Int Int) owner (.vector scalarDomain)) :
    LogicalAssignments (assignment Int Int) owner invocation where
  parameters type _ := match type with
    | .vector _ => source.read {} boundary emptyAssignments
    | _ => none
  witnesses _ _ := none
private def fixed := choose (.supplied [2])
private def proverRuntime := choose (.boundary tableP)
private def registry : OpaqueRegistry (assignment Int Int) :=
  ⟨[⟨⟨"opaque", "sum", "0"⟩, fun arguments =>
    if arguments = [] then some ⟨[.vector scalarDomain, .field scalarDomain], [.boolean],
      ["parameter", "statement"], fun args => (args.get .here).sum = args.get (.there .here)⟩
    else none⟩], by simp⟩
private def environment : RelationEnvironment imported Int Int :=
  .ofChecked registry (by decide +kernel)
private def relation : RelationBinding snapshot subject := ⟨⟨0, by decide⟩, rfl⟩
private def interpreted : InterpretedApplication owner subject Int Int environment :=
  ⟨⟨relation, .cons tableP (.cons claimV .nil), rfl⟩, .opaque rfl (by decide)⟩
private def selected : SelectedApplication owner Int Int environment :=
  ⟨.subject ⟨0, by decide⟩, interpreted⟩
private def fixedUse : ApplicationUse selected {} boundary fixed :=
  ⟨.cons [2] (.cons 1 .nil), rfl⟩
private def request : ContractRequest owner Int Int environment invocation {} boundary fixed :=
  .relation selected fixedUse .refutation
private theorem requested : request.Proof :=
  ⟨⟨trivial, trivial⟩, by change ¬ ((2 : Int) = 1); decide⟩

example : tableP.read {} boundary = some [1] := rfl
example : tableV.read {} boundary = some [2] := rfl
example : claimV.read {} boundary = some 1 := rfl
example : fixed.parameters (.vector scalarDomain) tableP = some [2] := rfl
example : proverRuntime.parameters (.vector scalarDomain) tableP = some [1] := rfl
example : interpreted.Holds {} boundary proverRuntime := ⟨.cons [1] (.cons 1 .nil), rfl, rfl⟩
example : ¬ interpreted.Holds {} boundary fixed := request.resolve requested
example : fixed.witnesses (.vector scalarDomain) tableP = none := rfl
example : True := by
  fail_if_success have detached : ApplicationUse selected {} boundary fixed :=
    ⟨.cons [1] (.cons 1 .nil), rfl⟩
  trivial

end
end Tests.StructuredContractAuthority
