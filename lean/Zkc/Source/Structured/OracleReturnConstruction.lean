module

public import Zkc.Source.RegionReturnProjection
public import Zkc.Source.Structured.ReceiverMetadata
public import Zkc.Source.Structured.OracleQueryDerivation
public meta import Zkc.Source.RegionReturnProjection
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Common return-proof construction for straight-line oracle regions. Local
mathematical and provider laws determine replies; the constructor selects the
actual typed source operations and composes their continuations. Unsupported
operations and mathematical implications remain goals, never axioms. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProtocol

/-- Install a helper equation at its actual active source call. The helper,
arguments and captured table come from the operation; its mark is not a
mathematical premise. -/
theorem localCallFromLaw (model : DomainModel) {self owner : Nat} {context : ProtocolContext}
    {ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model)}
    {helpers : ProtocolCalculation.Tables model.toCarriers (Interface model)}
    {table : ProtocolTable (ProtocolValue model.toCarriers) (Interface model)}
    (helper : Helper) (localKind : helper.kind = .local)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) helper.inputs) (site : String)
    {process : PIR.Process (Interface model) (Values (Component (ProtocolValue model.toCarriers)) helper.outputs)}
    (active : context.roles owner = self)
    (law : owned model self self ordinary helper arguments = process) :
    ((algebra model self ordinary helpers).meaning table context self).operation
      (.localCall helper localKind owner site) arguments .nil = process := by
  change owned model self (context.roles owner) ordinary helper arguments = process
  rw [active]
  exact law

theorem guardActive (model : DomainModel) {self owner : Nat} {context : ProtocolContext}
    {ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model)}
    {helpers : ProtocolCalculation.Tables model.toCarriers (Interface model)}
    {table : ProtocolTable (ProtocolValue model.toCarriers) (Interface model)}
    (active : context.roles owner = self) (flag : Bool) (site : String) :
    ((algebra model self ordinary helpers).meaning table context self).operation (.guard owner site)
      (.cons (concrete model .boolean flag) .nil) .nil =
      (if flag then .done .nil else .halt .reject) := by
  change ((Participant.guard (services := services) (Value := model.Value) self (context.roles owner)
    ((concrete model .boolean flag).bind ProtocolValue.toConcrete)).interpret (actions model)).bind _ = _
  cases flag <;> simp [active, concrete, Participant.guard, PIR.Process.interpret, PIR.Process.bind]

end Zkc.Source.Structured.OracleProtocol

/-- The supplied laws are facts, not a source traversal. Structural source
operations use their common semantics; checked operations introduce their
successful condition before constructing the continuation. -/
macro "derive_oracle_returns" "[" laws:Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic =>
  `(tactic|
    (repeat' first
      | (project_step Zkc.Source.Structured.ProtocolOp.mark
         apply PIR.Process.ReturnsUnder.call
         exact Zkc.Source.Structured.ReceiverForwarding.mark _ _ _ _ _ _ _
         apply PIR.Process.ReturnsUnder.done)
      | (project_step Zkc.Source.Structured.ProtocolOp.restrict
         apply PIR.Process.ReturnsUnder.ofEquation
         exact Zkc.Source.Structured.OracleProtocol.restrictActive _ (by assumption) _
         apply PIR.Process.ReturnsUnder.done)
      | (project_step Zkc.Source.Structured.ProtocolOp.restrict
         apply PIR.Process.ReturnsUnder.done)
      | (project_step Zkc.Source.Structured.ProtocolOp.assemble
         apply PIR.Process.ReturnsUnder.ofEquation
         apply Zkc.Source.Structured.OracleProtocol.assembleSecond
         first | assumption | exact Ne.symm (by assumption)
         assumption
         apply PIR.Process.ReturnsUnder.done)
      | (project_step Zkc.Source.Structured.ProtocolOp.assemble
         apply PIR.Process.ReturnsUnder.done)
      | (project_step Zkc.Source.Structured.ProtocolOp.calculate [Zkc.Source.Structured.Op.indexEqual]
         apply PIR.Process.ReturnsUnder.ofEquation
         exact Zkc.Source.Structured.OracleProtocol.compareIndex _ _ _
         apply PIR.Process.ReturnsUnder.done)
      | (project_step Zkc.Source.Structured.ProtocolOp.calculate
         apply PIR.Process.ReturnsUnder.done)
      | (project_checked Zkc.Source.Structured.ProtocolOp.calculate
         solve_by_elim (maxDepth := 4) only [$laws,*]
         intro)
      | (project_step Zkc.Source.Structured.ProtocolOp.calculate
         apply PIR.Process.ReturnsUnder.ofEquation
         solve_by_elim (maxDepth := 4) only [$laws,*]
         apply PIR.Process.ReturnsUnder.done)
      | (project_checked Zkc.Source.Structured.ProtocolOp.localCall
         apply Zkc.Source.Structured.OracleProtocol.localCallFromLaw
         assumption
         solve_by_elim (maxDepth := 4) only [$laws,*]
         intro)
      | (project_checked Zkc.Source.Structured.ProtocolOp.guard
         exact Zkc.Source.Structured.OracleProtocol.guardActive _ (by assumption) _ _
         intro)
      | (project_step Zkc.Source.Structured.ProtocolOp.localCall
         apply PIR.Process.ReturnsUnder.ofEquation
         apply Zkc.Source.Structured.OracleProtocol.localCallFromLaw
         assumption
         solve_by_elim (maxDepth := 4) only [$laws,*]
         apply PIR.Process.ReturnsUnder.done)
      | (project_step Zkc.Source.Structured.ProtocolOp.oracle
         solve_by_elim (maxDepth := 4) only [$laws,*])
     first
     | project_return
     | apply Zkc.Source.Region.ReturnsSatisfying.stop))
