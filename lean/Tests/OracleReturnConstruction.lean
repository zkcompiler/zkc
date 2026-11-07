module

public import Zkc.Source.Structured.OracleReturnConstruction
public meta import Zkc.Source.Structured.OracleReturnConstruction

@[expose] public section

/-! New source components use the same constructor without importing either
Sumcheck or FRI. These are partial return statements, not termination claims. -/
set_option autoImplicit false
namespace Tests.OracleReturnConstruction
open Zkc.Source Zkc.Source.Structured
open OracleProtocol (concrete)

def guarded (owner : Nat) (site : String) : Region protocolDialect [.index] [.index] :=
  .letOp (.mark (site ++ ".enter")) .nil .nil
  (.letOp (.calculate (.indexConstant 7) rfl) .nil .nil
  (.letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil
  (.letOp (.guard owner site) (.cons .here .nil) .nil
  (.ret (.cons (.there (.there .here)) .nil)))))

/-- The second component has another comparison, another guard and a different
return layout. Its proof does not add a source rule or syntax traversal. -/
def twoChecks (owner : Nat) : Region protocolDialect [.index, .index] [.index, .index] :=
  .letOp (.calculate (.indexConstant 7) rfl) .nil .nil
  (.letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil
  (.letOp (.guard owner "first") (.cons .here .nil) .nil
  (.letOp (.calculate (.indexConstant 9) rfl) .nil .nil
  (.letOp (.calculate .indexEqual rfl)
    (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil
  (.letOp (.guard owner "second") (.cons .here .nil) .nil
  (.ret (.cons (.there (.there (.there (.there (.there .here)))))
    (.cons (.there (.there (.there (.there .here)))) .nil))))))))

def stopped : Region protocolDialect [] [.index] :=
  .letOp (.calculate (.indexConstant 7) rfl) .nil .nil (.stop .exhausted)

def newHelper : Helper := ⟨"new_checked_component", .local, [.index], [.index]⟩

def otherHelper : Helper := ⟨"another_checked_component", .local, [.index], [.index]⟩

def helperClient (owner : Nat) : Region protocolDialect [.index] [.index, .index] :=
  .letOp (.localCall newHelper rfl owner "compute") (.cons .here .nil) .nil
  (.letOp (.calculate (.indexConstant 7) rfl) .nil .nil
  (.letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil
  (.letOp (.guard owner "check") (.cons .here .nil) .nil
  (.ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))))))

variable (model : DomainModel) {self owner : Nat} (context : ProtocolContext)
  (ordinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
  (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model))
  (table : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
  {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
  {M : Type → Type} [Monad M] [LawfulMonad M] {S E : Type}
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinaryHandler : PIR.MonadHandler M (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler M (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler M (OraclePublication.Interface model) S E)
  (original : OracleRuntimeState model snapshot domains math S)

theorem guarded_spec (active : context.roles owner = self) (site : String) (value : Nat) :
    Region.ReturnsSatisfying (OraclePublication.actionM model oracles ordinaryHandler base publish)
      (fun state ↦ state.oracle = original)
      ((OracleProtocol.algebra model self ordinary helpers).meaning table context self)
      (guarded owner site) (Values.cons (concrete model .index value) .nil).get
      (fun out ↦ value = 7 ∧ out = .cons (concrete model .index value) .nil) := by
  derive_oracle_returns []
  constructor
  · exact of_decide_eq_true (by assumption)
  · rfl

theorem twoChecks_spec (active : context.roles owner = self) (first second : Nat) :
    Region.ReturnsSatisfying (OraclePublication.actionM model oracles ordinaryHandler base publish)
      (fun state ↦ state.oracle = original)
      ((OracleProtocol.algebra model self ordinary helpers).meaning table context self)
      (twoChecks owner) (Values.cons (concrete model .index first)
        (.cons (concrete model .index second) .nil)).get
      (fun out ↦ first = 7 ∧ second = 9 ∧
        out = .cons (concrete model .index second) (.cons (concrete model .index first) .nil)) := by
  derive_oracle_returns []
  exact ⟨of_decide_eq_true (by assumption), of_decide_eq_true (by assumption), rfl⟩

theorem stopped_spec :
    Region.ReturnsSatisfying (OraclePublication.actionM model oracles ordinaryHandler base publish)
      (fun state ↦ state.oracle = original)
      ((OracleProtocol.algebra model self ordinary helpers).meaning table context self)
      stopped (Values.nil (Value := Component (ProtocolValue model.toCarriers))).get
      (fun _ ↦ False) := by
  derive_oracle_returns []

/-- A new helper supplies its semantic equation independently of the source
call's site and role frame. The constructor installs that equation and learns
the checked precondition and subsequent guard; the equation itself is not
inferred or assumed to be mathematical truth by the constructor. -/
theorem helperClient_spec (active : context.roles owner = self) (input output : Nat)
    (admitted : Prop) [Decidable admitted]
    (mathematics : OracleProtocol.owned model self self ordinary newHelper
      (.cons (concrete model .index input) .nil) =
      if admitted then .done (.cons (concrete model .index output) .nil) else .halt .exhausted) :
    Region.ReturnsSatisfying (OraclePublication.actionM model oracles ordinaryHandler base publish)
      (fun state ↦ state.oracle = original)
      ((OracleProtocol.algebra model self ordinary helpers).meaning table context self)
      (helperClient owner) (Values.cons (concrete model .index input) .nil).get
      (fun out ↦ admitted ∧ output = 7 ∧
        out = .cons (concrete model .index input) (.cons (concrete model .index output) .nil)) := by
  derive_oracle_returns [mathematics]
  exact ⟨by assumption, of_decide_eq_true (by assumption), rfl⟩

/-- An existing operation contract uses the same constructor at a projected
return boundary. The companion supplies no traversal or caller-frame proof. -/
theorem helperProjection_spec (input : Nat)
    (law : ((OracleProtocol.algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun action ↦ .call action .done) (.localCall newHelper rfl owner "compute")
      (.cons (concrete model .index input) .nil) .nil
      (.done (.cons (concrete model .index 7) .nil))) :
    Region.ReturnsProjection (OraclePublication.actionM model oracles ordinaryHandler base publish)
      (fun state ↦ state.oracle = original)
      ((OracleProtocol.algebra model self ordinary helpers).meaning table context self)
      (helperClient owner) (Values.cons (concrete model .index input) .nil).get
      (fun out ↦ out.get .here) (concrete model .index input) := by
  derive_oracle_returns [law]

/-- Candidate selection rejects an unrelated same-typed helper contract.
This is a proof-construction control; it is not an execution refusal. -/
theorem helper_selection (input : Nat)
    (_unrelated : ((OracleProtocol.algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun action ↦ .call action .done) (.localCall otherHelper rfl owner "compute")
      (.cons (concrete model .index input) .nil) .nil
      (.done (.cons (concrete model .index 9) .nil)))
    (law : ((OracleProtocol.algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun action ↦ .call action .done) (.localCall newHelper rfl owner "compute")
      (.cons (concrete model .index input) .nil) .nil
      (.done (.cons (concrete model .index 7) .nil))) :
    Region.ReturnsProjection (OraclePublication.actionM model oracles ordinaryHandler base publish)
      (fun state ↦ state.oracle = original)
      ((OracleProtocol.algebra model self ordinary helpers).meaning table context self)
      (helperClient owner) (Values.cons (concrete model .index input) .nil).get
      (fun out ↦ out.get .here) (concrete model .index input) := by
  fail_if_success derive_oracle_returns [_unrelated]
  derive_oracle_returns [_unrelated, law]

/-- On every actual returned record, exchanging the two same-typed result
ports violates the proved association. Stops retain their ordinary meaning. -/
theorem wrong_result_order (active : context.roles owner = self)
    (state : OracleProtocol.State model snapshot domains math S) (kept : state.oracle = original) :
    Std.Do.Internal.Ensures
      (fun record ↦ record.outcome ≠ .returned
        (Values.cons (concrete model .index 7) (.cons (concrete model .index 9) .nil)))
      (((twoChecks owner).denote
        ((OracleProtocol.algebra model self ordinary helpers).meaning table context self)
        (Values.cons (concrete model .index 7) (.cons (concrete model .index 9) .nil)).get).runM
        (OraclePublication.actionM model oracles ordinaryHandler base publish) state) := by
  apply (twoChecks_spec model context ordinary helpers table oracles ordinaryHandler base publish original
    active 7 9 state kept).weaken
  rintro record ⟨_, result⟩ wrong
  have first := congrArg (fun values ↦ values.get .here) (result _ wrong).2.2
  have decoded := congrArg (fun value ↦ value.bind ProtocolValue.toConcrete) first
  simp only [Values.get, concrete, Option.bind_some,
    ProtocolValue.toConcrete_ofConcrete, Option.some.injEq, Nat.reduceEqDiff] at decoded

#print axioms guarded_spec
#print axioms twoChecks_spec
#print axioms stopped_spec
#print axioms helper_selection
#print axioms helperProjection_spec
#print axioms helperClient_spec
#print axioms wrong_result_order
end Tests.OracleReturnConstruction
