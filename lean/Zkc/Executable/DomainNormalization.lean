module

public import Zkc.Executable.DomainSoundness
public import Zkc.Construction.DomainCalculations

@[expose] public section

/-! Canonical normalization observations. SSA checkpoint frames are private to
an instruction schedule; the outcome, readback and every nonadministrative
action remain observable. No interpreter for constructed instructions is
introduced by this projection. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

/-- Relate exactly the live positions named by two scopes. In particular this
is an equality of complete nominal values: suites and occurrence coordinates
are retained, and unsupported scalar readback is not assigned a default. -/
def ScopeRelation (left right : Environment F G) (leftRefs rightRefs : List Nat) : Prop :=
  Domain.read left leftRefs = Domain.read right rightRefs

theorem ScopeRelation.refl (env : Environment F G) (refs : List Nat) :
    ScopeRelation env env refs refs := rfl

def readback (refs : List Nat) (env : Environment F G) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G)) (Environment F G) :=
  match Domain.read env refs with
  | some values => .done values
  | none => .halt .refused

theorem ScopeRelation.readback {left right : Environment F G} {leftRefs rightRefs : List Nat}
    (related : ScopeRelation left right leftRefs rightRefs) :
    readback leftRefs left = readback rightRefs right := by
  unfold DomainVM.readback
  rw [related]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def outcome (program : Structured.Program) (context : Context)
    (instructions : List Instruction) (returned : List Nat) (env : Environment F G) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G)) (Environment F G) :=
  (Domain.evaluate (Structured.ringModel F G) program context instructions env).bind (readback returned)

def observation (program : Structured.Program) (context : Context)
    (instructions : List Instruction) (returned : List Nat) (env : Environment F G) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G)) (Environment F G) :=
  (outcome program context instructions returned env).interpret Original.forgetCheckpoints

variable {m : Type → Type} [Monad m]
variable (program : Structured.Program) (context : Context)
  (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- Handling this observation preserves the complete scalar proof suffix.
Only administrative checkpoint operations are projected. -/
theorem run_observation (instructions : List Instruction) (returned : List Nat)
    (env : Environment F G) (proof : Proof F G) :
    DomainAdapter.run key initial challenge (observation program context instructions returned env) proof =
      DomainAdapter.runK key initial challenge
        (Domain.evaluate (Structured.ringModel F G) program context instructions env) proof
        (fun final unread => pure
          (match Domain.read final returned with
          | some values => .returned values
          | none => .stopped .refused, unread)) := by
  unfold DomainAdapter.run observation
  rw [DomainAdapter.runK_forgetCheckpoints]
  simp only [outcome, DomainAdapter.runK_bind]
  congr 1
  funext final unread
  unfold readback
  cases Domain.read final returned <;> rfl

/-- Every Code budget preserves the canonical action prefix and readback
observation, including helper and loop/yield charge exhaustion. -/
theorem metered_prunes_observation (lowered : Lowered) (env : Environment F G) (proof : Proof F G) :
    Prunes Stopped (metered program context key initial challenge cost budget lowered env proof)
      (DomainAdapter.run key initial challenge
        (observation program context (Code.instructions lowered.code) lowered.returned env) proof) := by
  rw [run_observation]
  exact metered_prunes program context key initial challenge cost budget lowered env proof

/-- A static sufficient Code budget has the full canonical readback
observation. Checkpoint projection preserves the handler's exact unread proof
and actions, including a query followed by a false returned Boolean. -/
theorem metered_static_observation {lowered : Lowered} {total : Nat}
    (static : lowered.total? = some total) (sufficient : total ≤ budget)
    (env : Environment F G) (proof : Proof F G) :
    metered program context key initial challenge cost budget lowered env proof =
      DomainAdapter.run key initial challenge
        (observation program context (Code.instructions lowered.code) lowered.returned env) proof := by
  rw [run_observation]
  exact metered_static program context key initial challenge cost budget static sufficient env proof

end Zkc.Executable.DomainVM
