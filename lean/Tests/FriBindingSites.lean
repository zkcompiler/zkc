import Tests.FriBindingSitesView
import Tests.FriBindingAssociation

/-! The two distinct source calls use the same installed low-degree
declaration and, inside it, the same receiver binding component. -/
namespace Tests.FriBindingSites
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriSourceViews

abbrev doubleProgram := FriBindingSitesView.program

def calls (definition : CheckedProtocol) : List (String × ProtocolSignature × List Nat) :=
  definition.body.erase.operations.filterMap fun op ↦ match op with
    | .protocolApply signature roles site => some (site, signature, roles)
    | _ => none

abbrev leftSite := "label_6c656674"
abbrev rightSite := "label_7269676874"

theorem rootCalls : calls doubleProgram.payload.entry =
    [(leftSite, protocol5Signature, [0, 1]), (rightSite, protocol5Signature, [0, 1])] := by kernel_rfl

theorem nested : ("s4", protocol2Signature, [0, 1]) ∈ calls protocol5Definition := by decide +kernel

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

def binderContext (site : String) := (({} : ProtocolContext).enter site [0, 1]).enter "s4" [0, 1]

example : (binderContext leftSite).applicationPrefix ≠ (binderContext rightSite).applicationPrefix := by decide

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (OraclePublication.Interface model) S E)
  (original : OracleRuntimeState model snapshot domains math S) (role : original.self = 1)

def CorrespondsAt (site : String) : Prop :=
  ∀ (handles : FriBindingExecution.Handles) (rest : FriBinding.Committed model)
    (xs : FriScalarLoop.Positions), xs.length = 8 →
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (invokeProtocol (doubleProgram.payload.oracleProtocolTable model 1) protocol2Signature (binderContext site) 1
        (FriBinding.inputs model (handles.attach rest) xs)) (FriBinding.output (handles.attach rest) xs)

include role in
/-- Independent inputs may be used at either of the two actual sites. Only
their context changes. Both applications use the same mathematical proof. -/
theorem bothSites : CorrespondsAt oracles ordinary base publish original leftSite ∧
    CorrespondsAt oracles ordinary base publish original rightSite := by
  have siteLaw (site : String) : CorrespondsAt oracles ordinary base publish original site := by
    intro handles rest xs count
    rw [sameBinder]
    exact FriBindingExecution.installed oracles ordinary base publish original role
      (binderContext site).applicationPrefix handles rest xs count
  exact ⟨siteLaw leftSite, siteLaw rightSite⟩

include role in
/-- The same-sort swap is impossible as a returned value of either reached
binder. This uses its actual installed process under any publication handler. -/
theorem excludesSwapped (site : String) (atSite : site = leftSite ∨ site = rightSite)
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
    rcases atSite with rfl | rfl
    · exact sites.1
    · exact sites.2
  exact (atBinder handles rest xs count).excludes
    (FriBindingAssociation.swap_refused handles rest xs distinct) state valid

end Tests.FriBindingSites
