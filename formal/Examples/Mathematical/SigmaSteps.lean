import Zkc.Source.Mathematical.ProtocolLaws
import Zkc.Source.Mathematical.ProtocolAdmission

/-! Observable prefix laws for an admitted query/pure/message sequence.

FreshReceive exposes the actual continuation and the environment fixed before
the wire reply. It does not equate received data with the sender's expression.
-/

set_option autoImplicit false
namespace Examples.Mathematical.SigmaSteps
open Zkc.Source
open Zkc.Source.Mathematical hiding Capability Program Signature interface
open Zkc.Source.Mathematical.Protocol

variable {vocabulary : Vocabulary}

def FreshReceive (meaning : Graph.Interpretation vocabulary.toAlgebra) (self sender site : Nat)
    (path : List LocatedExecution.Frame) (results : List (Port Nat vocabulary.Ty))
    (execution : PIR.Proc (interface self vocabulary meaning.Value)
      (Values (Component meaning.Value self) results)) : Prop :=
  ∃ (parties : List Nat) (capabilities : List (Capability Nat vocabulary.Service))
    (scope : List (Signature Nat vocabulary)) (Γ : List (Port Nat vocabulary.Ty))
    (ty : vocabulary.Ty) (schema : vocabulary.Wire ty) (finish : Nat)
    (condition : CallCondition (vocabulary := vocabulary) capabilities scope)
    (calls : CheckedCallMeaning (capabilities := capabilities) meaning self scope condition)
    (next : Program parties vocabulary capabilities scope
      (⟨messageRoles parties sender self, ty⟩ :: Γ) results (site + 1) finish)
    (valid : next.CallsSatisfy condition) (env : Environment meaning.Value self Γ),
    execution = .call (.receive ⟨path, site⟩ schema sender) (fun reply =>
      next.denoteChecked meaning self calls path valid (env.push (fun _ => reply)))

variable {parties : List Nat} {capabilities : List (Capability Nat vocabulary.Service)}
  {scope : List (Signature Nat vocabulary)}

/-- Evaluate one pure region after the query reply and before the send. The
captured environment is exactly the input environment extended by that reply. -/
def commitmentValue (meaning : Graph.Interpretation vocabulary.toAlgebra)
    {Γ captures outputs : List (Port Nat vocabulary.Ty)} {service : vocabulary.Service}
    (capture : Operands (⟨[0], vocabulary.serviceResult service⟩ :: Γ) captures)
    (region : Graph.Region parties vocabulary.toAlgebra captures outputs)
    {ty : vocabulary.Ty} (value : Reference (outputs ++ ⟨[0], vocabulary.serviceResult service⟩ :: Γ) ⟨[0], ty⟩)
    (env : Environment meaning.Value 0 Γ) (nonce : meaning.Value (vocabulary.serviceResult service)) :
    meaning.Value ty :=
  value.read (Environment.prepend (env.push (fun _ => nonce))
    (region.denote meaning 0 (fun ref => (Operands.eval (env.push (fun _ => nonce)) capture).get ref))) (by simp)

def QueryPureSend (meaning : Graph.Interpretation vocabulary.toAlgebra)
    {Γ : List (Port Nat vocabulary.Ty)} (env : Environment meaning.Value 0 Γ)
    (results : List (Port Nat vocabulary.Ty)) (path : List LocatedExecution.Frame)
    (rawCaptures : List Nat) (rawGraph : Graph.Raw vocabulary.Op vocabulary.Count)
    (execution : PIR.Proc (interface 0 vocabulary meaning.Value)
      (Values (Component meaning.Value 0) results)) : Prop :=
  ∃ (parties : List Nat) (signature : Capability Nat vocabulary.Service)
    (arguments : Inputs Γ (vocabulary.serviceArguments signature.service))
    (available : 0 ∈ Inputs.available parties arguments)
    (captures outputs : List (Port Nat vocabulary.Ty))
    (capture : Operands (⟨[0], vocabulary.serviceResult signature.service⟩ :: Γ) captures)
    (region : Graph.Region parties vocabulary.toAlgebra captures outputs)
    (ty : vocabulary.Ty) (schema : vocabulary.Wire ty)
    (value : Reference (outputs ++ ⟨[0], vocabulary.serviceResult signature.service⟩ :: Γ) ⟨[0], ty⟩)
    (rest : meaning.Value (vocabulary.serviceResult signature.service) → Unit →
      PIR.Proc (interface 0 vocabulary meaning.Value) (Values (Component meaning.Value 0) results)),
    Graph.inputIndices (algebra := vocabulary.toAlgebra) arguments = [] ∧
    Graph.operandIndices capture = rawCaptures ∧ region.erase = rawGraph ∧ value.operand.index = 0 ∧
    execution = .call (.query ⟨path, 0⟩ signature.root signature.service
      (Inputs.read parties arguments env available)) (fun nonce =>
        .call (.send ⟨path, 1⟩ schema 1 (commitmentValue meaning capture region value env nonce)) (rest nonce))

theorem prefix_fresh_receive {Γ results finish captures graph wire tail}
    (program : Program parties vocabulary capabilities scope Γ results 0 finish)
    (erasure : program.erase = .query 0 0 0 [] (.pure captures graph (.message 1 wire 0 1 0 tail)))
    (meaning : Graph.Interpretation vocabulary.toAlgebra)
    {condition : CallCondition (vocabulary := vocabulary) capabilities scope}
    (calls : CheckedCallMeaning (capabilities := capabilities) meaning 1 scope condition)
    (path : List LocatedExecution.Frame) (valid : program.CallsSatisfy condition)
    (env : Environment meaning.Value 1 Γ) :
    FreshReceive meaning 1 0 1 path results (program.denoteChecked meaning 1 calls path valid env) := by
  cases program <;> simp only [Program.erase, Raw.query.injEq, reduceCtorEq] at erasure
  case query owner participates capability permitted arguments available next =>
    obtain ⟨_, rfl, _, _, nextEq⟩ := erasure
    cases next <;> simp only [Program.erase, Raw.pure.injEq, reduceCtorEq] at nextEq
    case pure region capture next =>
      obtain ⟨_, _, nextEq⟩ := nextEq
      cases next <;> simp only [Program.erase, Raw.message.injEq, reduceCtorEq] at nextEq
      case message schema sender receiver sending receiving different value next =>
        obtain ⟨_, _, rfl, rfl, _, _⟩ := nextEq
        refine ⟨parties, capabilities, scope, _, _, schema, finish, condition, calls, next, valid,
          Environment.prepend (env.push (fun absent => by simp at absent))
            (region.denote meaning 1 (fun ref =>
              (Operands.eval (env.push (fun absent => by simp at absent)) capture).get ref)), ?_⟩
        simp only [Program.denoteChecked, Nat.one_ne_zero, dite_false, dite_true]

theorem prefix_pure_send {Γ results finish captures graph wire tail}
    (program : Program parties vocabulary capabilities scope Γ results 0 finish)
    (erasure : program.erase = .query 0 0 0 [] (.pure captures graph (.message 1 wire 0 1 0 tail)))
    (meaning : Graph.Interpretation vocabulary.toAlgebra)
    {condition : CallCondition (vocabulary := vocabulary) capabilities scope}
    (calls : CheckedCallMeaning (capabilities := capabilities) meaning 0 scope condition)
    (path : List LocatedExecution.Frame) (valid : program.CallsSatisfy condition)
    (env : Environment meaning.Value 0 Γ) :
    QueryPureSend meaning env results path captures graph
      (program.denoteChecked meaning 0 calls path valid env) := by
  cases program <;> simp only [Program.erase, Raw.query.injEq, reduceCtorEq] at erasure
  case query owner participates capability permitted arguments available next =>
    obtain ⟨_, rfl, _, argumentsEq, nextEq⟩ := erasure
    cases next <;> simp only [Program.erase, Raw.pure.injEq, reduceCtorEq] at nextEq
    case pure region capture next =>
      obtain ⟨capturesEq, graphEq, nextEq⟩ := nextEq
      cases next <;> simp only [Program.erase, Raw.message.injEq, reduceCtorEq] at nextEq
      case message schema sender receiver sending receiving different value next =>
        obtain ⟨_, _, rfl, rfl, valueEq, _⟩ := nextEq
        refine ⟨parties, _, arguments, available, _, _, capture, region, _, schema, value,
          (fun nonce _ => next.denoteChecked meaning 0 calls path valid
            (Environment.push (Environment.prepend (env.push (fun _ => nonce))
              (region.denote meaning 0 (fun ref => (Operands.eval (env.push (fun _ => nonce)) capture).get ref)))
              (fun _ => commitmentValue meaning capture region value env nonce))),
          argumentsEq, capturesEq, graphEq, valueEq, ?_⟩
        simp only [Program.denoteChecked, dite_true, commitmentValue]

end Examples.Mathematical.SigmaSteps
