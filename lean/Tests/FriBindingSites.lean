import Mathlib.Tactic.FinCases
import Zkc.Source.Structured.ContractCalls
import Tests.FriBindingSitesView
import Tests.FriBindingAssociation

/-! The two distinct source calls use the same installed low-degree
declaration and, inside it, the same receiver binding component. -/
namespace Tests.FriBindingSites
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriSourceViews

abbrev doubleProgram := FriBindingSitesView.program

/-- The root has two calls. Keep their typed occurrence witnesses and SSA
operands, rather than identifying an occurrence by the spelling of its label. -/
def outer (i : Fin 2) : CallOccurrence doubleProgram.payload.entry.body :=
  (callInventory doubleProgram.payload.entry.body)[i.val]'(by
    have arity : (callInventory doubleProgram.payload.entry.body).length = 2 := by kernel_rfl
    simpa only [arity] using i.isLt)

abbrev binding := FriSourceCalls.binding

theorem rootCalls (i : Fin 2) : (outer i).callSite.signature = protocol5Signature := by
  fin_cases i <;> kernel_rfl

theorem selectedBinder : binding.signature = protocol2Signature := by kernel_rfl

theorem helperClosure : doubleProgram.payload.definitions = unit.definitions := by kernel_rfl

theorem protocols : doubleProgram.payload.protocols = [protocol0Definition, protocol1Definition, protocol2Definition,
    protocol3Definition, protocol4Definition, protocol5Definition, doubleProgram.payload.entry] := by kernel_rfl

/-- A changed root may extend the immutable protocol table, but the captured
implementation of its previously linked binder is identical in both units. -/
theorem sameBinder (model : DomainModel) :
    invokeProtocol (doubleProgram.payload.oracleProtocolTable model 1) protocol2Signature =
      invokeProtocol (verifierTable model) protocol2Signature := by
  unfold UnitPayload.oracleProtocolTable UnitPayload.oracleCalculations
  rw [helperClosure]
  let shared := [protocol0Definition, protocol1Definition, protocol2Definition]
  let suffix := [protocol3Definition, protocol4Definition, protocol5Definition]
  have member : protocol2Signature ∈ shared.map CheckedProtocol.signature :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact (ProtocolClosure.prefix_agrees (verifierAlgebra model).denote doubleProgram.payload.protocolsLinked
    shared (suffix ++ [doubleProgram.payload.entry]) protocols protocol2Signature member).symm.trans
    (ProtocolClosure.prefix_agrees (verifierAlgebra model).denote unit.protocolsLinked
      shared (suffix ++ [runDefinition]) rfl protocol2Signature member)

def binderContext (i : Fin 2) : ProtocolContext :=
  binding.childContext ((outer i).callSite.childContext {})

example : (binderContext 0).applicationPrefix ≠ (binderContext 1).applicationPrefix := by decide +kernel

private theorem placement (i : Fin 2) :
    (binderContext i).roles 1 = 1 ∧ 1 ≠ (binderContext i).roles 0 := by
  fin_cases i <;> decide +kernel

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (OraclePublication.Interface model) S E)
  (original : OracleRuntimeState model snapshot domains math S) (role : original.self = 1)

def CorrespondsAt (site : Fin 2) : Prop :=
  ∀ (handles : FriBindingExecution.Handles) (rest : FriBinding.Committed model)
    (xs : FriScalarLoop.Positions), xs.length = 8 →
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (invokeProtocol (doubleProgram.payload.oracleProtocolTable model 1) protocol2Signature (binderContext site) 1
        (FriBinding.inputs model (handles.attach rest) xs)) (FriBinding.output (handles.attach rest) xs)

include role in
/-- Independent inputs may be used at either of the two actual sites. Only
their context changes. Both applications use the same mathematical proof. -/
theorem bothSites : CorrespondsAt oracles ordinary base publish original 0 ∧
    CorrespondsAt oracles ordinary base publish original 1 := by
  have siteLaw (site : Fin 2) : CorrespondsAt oracles ordinary base publish original site := by
    intro handles rest xs count
    rw [sameBinder]
    exact FriBindingExecution.installed oracles ordinary base publish original role
      (binderContext site) (placement site).1 (placement site).2 handles rest xs count
  exact ⟨siteLaw 0, siteLaw 1⟩

include role in
/-- The same-sort swap is impossible as a returned value of either reached
binder. This uses its actual installed process under any publication handler. -/
theorem excludesSwapped (site : Fin 2)
    (handles : FriBindingExecution.Handles) (rest : FriBinding.Committed model)
    (xs : FriScalarLoop.Positions) (count : xs.length = 8) (distinct : handles.layers ≠ handles.folds)
    (state : OracleProtocol.State model snapshot domains math S) (valid : state.oracle = original) :
    Std.Do.Internal.Ensures (fun result ↦ result.outcome ≠ .returned
      (FriBindingAssociation.swapped.apply (FriBinding.inputs model (handles.attach rest) xs)
        (.cons (OracleProtocol.concrete model .index 8) .nil)))
      ((invokeProtocol (doubleProgram.payload.oracleProtocolTable model 1) protocol2Signature
        (binderContext site) 1 (FriBinding.inputs model (handles.attach rest) xs)).runM
        (OraclePublication.actionM model oracles ordinary base publish) state) := by
  have sites := bothSites oracles ordinary base publish original role
  have atBinder : CorrespondsAt oracles ordinary base publish original site := by
    fin_cases site
    · exact sites.1
    · exact sites.2
  exact (atBinder handles rest xs count).excludes
    (FriBindingAssociation.swap_refused handles rest xs distinct) state valid

end Tests.FriBindingSites
