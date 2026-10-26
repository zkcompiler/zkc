module

public import Zkc.Executable.DomainCompleteness
public import Zkc.Executable.DomainNormalization
public import Zkc.Executable.DomainByteLaws

@[expose] public section

/-! Honest success certificates over the canonical Process and its actual
scalar handler. These are explicit no-stop proof obligations, separate from
budget sufficiency and from arbitrary-input transport. They contain no
constructed instruction recursion and assume no execution equality. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

/-- A successful Process path for a deterministic scalar oracle. The query
case inspects the actual mapped handler's reply, including handler refusal.
The receive case inspects the actual scalar decoder and supplied proof head.
A protocol-specific honest proof must establish every reached obligation. -/
def Passes {A : Type} (key : Origin → Origin) (initial : History F G)
    (oracle : History F G → F) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A → Proof F G →
      (A → Proof F G → Prop) → Prop
  | .done value, proof, holds => holds value proof
  | .halt _, _, _ => False
  | .call (.receive ty ..) next, proof, holds =>
      match proof with
      | [] => False
      | payload :: unread => match Value.decode ty (.data payload) with
        | none => False
        | some value => Passes key initial oracle (next value) unread holds
  | .call (.query history origin) next, proof, holds =>
      Domain.drawRequest origin = true ∧
        match DomainAdapter.query (m := Id) key initial oracle history origin with
        | .stopped _ => False
        | .returned value => Passes key initial oracle (next value) proof holds
  | .call (.localService ..) _, _, _ => False
  | .call (.send ..) next, proof, holds |
    .call (.observe ..) next, proof, holds |
    .call (.checkpoint ..) next, proof, holds => Passes key initial oracle (next ()) proof holds

/-- Success is an actual returned outcome with its exact unread proof, rather
than a statement only about accepting runs or an implication from success. -/
theorem Passes.run {A : Type} (key : Origin → Origin) (initial : History F G)
    (oracle : History F G → F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (holds : A → Proof F G → Prop)
    (passes : Passes key initial oracle process proof holds) :
    ∃ value unread, holds value unread ∧
      DomainAdapter.run (m := Id) key initial oracle process proof = (.returned value, unread) := by
  induction process generalizing proof with
  | done value => exact ⟨value, proof, passes, rfl⟩
  | halt => exact False.elim passes
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => exact False.elim passes
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) with
              | none => simp only [Passes, decoded] at passes
              | some value =>
                  obtain ⟨result, rest, property, executed⟩ := ih value unread
                    (by simpa only [Passes, decoded] using passes)
                  exact ⟨result, rest, property, by simpa only [DomainAdapter.run,
                    DomainAdapter.runK, decoded] using executed⟩
      | send | observe | checkpoint => exact ih () proof passes
      | localService => exact False.elim passes
      | query history origin =>
          simp only [Passes] at passes
          obtain ⟨draw, passes⟩ := passes
          cases replied : DomainAdapter.query (m := Id) key initial oracle history origin with
          | stopped reason => simp only [replied] at passes
          | returned value =>
              obtain ⟨result, rest, property, executed⟩ := ih value proof
                (by simpa only [replied] using passes)
              exact ⟨result, rest, property, by simpa only [DomainAdapter.run,
                DomainAdapter.runK, draw, ite_true, replied, bind, Id.instMonad] using executed⟩

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Combine independently established real success and Code budget bounds.
The continuation's output scope can select different SSA slots in a normalized
schedule. Every returned value is nominal until the caller applies its ABI. -/
theorem metered_success (program : Structured.Program) (context : Context)
    (key : Origin → Origin) (initial : History F G) (oracle : History F G → F)
    (cost : String → List (Value F G) → Nat) (budget : Nat)
    (lowered : Lowered) (env : Environment F G) (proof : Proof F G)
    (holds : Environment F G → Proof F G → Prop)
    (fits : Sufficient program context cost budget lowered env proof)
    (passes : Passes key initial oracle
      (observation program context (Code.instructions lowered.code) lowered.returned env) proof holds) :
    ∃ value unread, holds value unread ∧
      metered (m := Id) program context key initial oracle cost budget lowered env proof =
        (.returned value, unread) := by
  obtain ⟨value, unread, property, executed⟩ := Passes.run key initial oracle _ proof holds passes
  refine ⟨value, unread, property, ?_⟩
  exact (metered_sufficient (m := Id) program context cost budget key initial oracle lowered env proof fits).trans
    ((run_observation (m := Id) program context key initial oracle (Code.instructions lowered.code)
      lowered.returned env proof).symm.trans executed)

end Zkc.Executable.DomainVM
