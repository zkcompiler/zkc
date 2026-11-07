module

public import ZkcArkLibExamples.Fri.VerifierTerminal
public import ZkcExamples.Structured.FriCheckRound
public import Zkc.Source.Structured.Bindings.Continuation

@[expose] public section

/-! The actual continuation of Check's inner loop evaluates the terminal
polynomial, compares it with the final folded value, then returns the vector
remembered by the outer query. Its two live references come from the
admitted continuation. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierTerminalGuard
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriSourceViews
open FriCheckRound (roundSite coefficientsPort rememberedPort)
open OracleProtocol (concrete withMarks)
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

abbrev Γ := roundSite.context
abbrev stateTypes : List Ty := [.field extension, .index, .index, .field extension]

abbrev terminalMeaning (context : ProtocolContext) :=
  (verifierAlgebra model).meaning (verifierTable model) context 1

private theorem evaluateStep (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (site : String) (cs : List Octic) (shift : Octic) (nonzero : shift ≠ 0)
    {k : Nat} (bound : k ≤ 5) (index : Fin (2 ^ k)) (fits : cs.length < indexLimit)
    (input : FriBinding.Value model (.vector extension))
    (coefficients : input = concrete model (.vector extension) cs) :
    (terminalMeaning context).OperationLaw (fun op ↦ .call op .done) (.localCall helper36Helper rfl 1 site)
      (.cons input (.cons (concrete model (.field extension) shift)
        (.cons (concrete model .index (2 ^ k)) (.cons (concrete model .index index.val) .nil)))) .nil
      (.done (.cons (concrete model (.field extension)
        (terminal (F := Octic) RetainedDomain.root cs shift k index.val)) .nil)) := by
  subst input
  apply RegionMeaning.OperationLaw.identity
  change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model)
    helper36Helper (ProtocolValue.embedComponents
      ((Values.cons (Value := model.Value) (ty := Ty.vector extension) cs
        (.cons shift (.cons (2 ^ k) (.cons index.val .nil)))).present)) = _
  rw [receiver, OracleProtocol.owned_present, VerifierTerminal.installed bound cs fits shift nonzero index]
  rfl

private theorem compareStep (context : ProtocolContext) (value expected : Octic) (flag : Bool)
    (agrees : decide (value = expected) = flag) :
    (terminalMeaning context).OperationLaw (fun op ↦ .call op .done) (.calculate (.fieldEqual extension) rfl)
      (.cons (concrete model (.field extension) value) (.cons (concrete model (.field extension) expected) .nil)) .nil
      (.done (.cons (concrete model .boolean flag) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change ProtocolCalculation.strict model (OracleProtocol.demand model) 1 (FriIndexCollections.helpers model)
    (.fieldEqual extension) (ProtocolValue.embedComponents (.cons (some value) (.cons (some expected) .nil))) rfl = _
  erw [ProtocolCalculation.strict_embed]
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (concrete model .boolean (decide (value = expected))) .nil) = _
  rw [agrees]
  rfl

private theorem rejects (context : ProtocolContext) (receiver : context.roles 1 = 1) (site : String) :
    (terminalMeaning context).OperationLaw (fun op ↦ .call op .done) (.guard 1 site)
      (.cons (concrete model .boolean false) .nil) .nil (.halt .reject) := by
  apply RegionMeaning.OperationLaw.identity
  change ((Participant.guard (services := services) (Value := model.Value) 1 (context.roles 1)
    ((concrete model .boolean false).bind ProtocolValue.toConcrete)).interpret (OracleProtocol.actions model)).bind _ = _
  simp [receiver, OracleProtocol.concrete, Participant.guard, PIR.Process.interpret, PIR.Process.bind]

def finalValues (expected : Octic) (pos rows : Nat) (shift : Octic) :
    Values (FriBinding.Value model) stateTypes :=
  .cons (concrete model (.field extension) expected) (.cons (concrete model .index pos)
    (.cons (concrete model .index rows) (.cons (concrete model (.field extension) shift) .nil)))

/-- A complete equation for the reached suffix of the installed inner repeat.
Only the coefficient vector needs a mathematical representation. Every other
old SSA value is arbitrary, including the remembered outer-loop vector. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (env : Environment (FriBinding.Value model) Γ)
    (cs : List Octic) (coefficients : env coefficientsPort = concrete model (.vector extension) cs)
    (shift : Octic) (nonzero : shift ≠ 0) {k : Nat} (bound : k ≤ 5)
    (index : Fin (2 ^ k)) (fits : cs.length < indexLimit) (expected : Octic) :
    roundSite.next.denote (terminalMeaning context) (env.prepend (finalValues expected index.val (2 ^ k) shift)) =
      withMarks (roundSite.continuationMarks context)
        (if terminal (F := Octic) RetainedDomain.root cs shift k index.val = expected then
          .done (.cons (env rememberedPort) .nil) else .halt .reject) := by
  by_cases same : terminal (F := Octic) RetainedDomain.root cs shift k index.val = expected
  · rw [ite_eq_left same]
    derive_process using
      (first
       | apply evaluateStep context receiver _ cs shift nonzero bound index fits _ coefficients
       | exact compareStep context _ _ true (by simp only [same, decide_true])
       | apply OracleProtocol.guardTrue model)
  · rw [ite_eq_right same]
    derive_process using
      (first
       | apply evaluateStep context receiver _ cs shift nonzero bound index fits _ coefficients
       | exact compareStep context _ _ false (by simp only [same, decide_false])
       | apply rejects context receiver)

end ZkcSecurity.ArkLib.Fri.VerifierTerminalGuard
