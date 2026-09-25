import Zkc.Protocols.Sumcheck.Framed
import Zkc.Semantics.Preparation

set_option autoImplicit false

namespace Tests.ConstructionSequencing

open PIR Zkc.Protocols

def polynomial : Zkc.Polynomial.Quadratic Nat 1 :=
  .node (.constant 0) (.constant 1) (.constant 0)
def initial := Sumcheck.Framed.initial "sequencing" polynomial 1 () 0
def send (_ : Unit) : AlgebraicRounds.Message Nat × Unit := (⟨0, 1, 0⟩, ())
def react (_ : Unit) (_ : Nat) : Unit := ()

/-- Deterministic schedule discriminator, not a cryptographic random oracle. -/
def query : AlgebraicRounds.Construction.Query Nat Nat := fun frames attempts =>
  (.returned frames.length, attempts + 1)

def first : Proc (AlgebraicRounds.interface Nat) Nat :=
  (Sumcheck.Source.rounds 1 ⟨1, []⟩).bind (fun accumulator => .done accumulator.claim)
def next (value : Nat) : Proc (AlgebraicRounds.interface Nat) (Nat × Nat) :=
  .call .challenge (fun r => .done (value, r))

def run := ((first.bind next).interpret AlgebraicRounds.Construction.framed).run
  (AlgebraicRounds.Framed.handler send react query) initial

theorem separately_constructed :
    run = ((first.interpret AlgebraicRounds.Construction.framed).run
      (AlgebraicRounds.Framed.handler send react query) initial).follow
        (fun value state => ((next value).interpret AlgebraicRounds.Construction.framed).run
          (AlgebraicRounds.Framed.handler send react query) state) :=
  Proc.run_interpret_bind _ _ _ _ _

def reset (state : AlgebraicRounds.Framed.State Nat Unit Nat) :=
  { state with frames := Sumcheck.Framed.root "sequencing" polynomial 1, position := 0 }

def resetRun := ((first.interpret AlgebraicRounds.Construction.framed).run
  (AlgebraicRounds.Framed.handler send react query) initial).follow
    (fun value state => ((next value).interpret AlgebraicRounds.Construction.framed).run
      (AlgebraicRounds.Framed.handler send react query) (reset state))

theorem transcript_reset_changes_result :
    run.outcome = .returned (4, 6) ∧ resetRun.outcome = .returned (4, 3) := by decide +kernel

/-- A rebase may change private state only when the actual following run ignores it. -/
theorem unused_state_can_be_rebased (value state : Nat) :
    (Execution.mk (.returned value) state ([] : List Nat)).follow
        (fun v _ => ⟨.returned v, 0, []⟩) =
      (Execution.mk (.returned value) state ([] : List Nat)).follow
        (fun v s => (fun (_ : Nat) => ⟨.returned v, 0, []⟩) (s + 1)) :=
  Execution.follow_rebase _ _ (fun s => s + 1) (fun _ _ => rfl)

theorem staging_square (source : Proc (AlgebraicRounds.interface Nat) Nat) :
    (source.interpret AlgebraicRounds.Construction.framed).interpret
        (PIR.Preparation.externalCalls (K := Nat) (V := Nat)) =
      source.interpret (fun op =>
        (AlgebraicRounds.Construction.framed op).interpret
          (PIR.Preparation.externalCalls (K := Nat) (V := Nat))) :=
  Proc.interpret_interchange _ _ _ (fun _ => rfl) source

def received : Proc (AlgebraicRounds.interface Nat) (AlgebraicRounds.Message Nat) :=
  .call .message .done

theorem construction_identity_matters :
    ((received.interpret AlgebraicRounds.Construction.framed).run
      (AlgebraicRounds.Framed.handler send react query) initial).state.frames ≠
    ((received.interpret AlgebraicRounds.Construction.fresh).run
      (AlgebraicRounds.Framed.handler send react query) initial).state.frames := by decide +kernel

end Tests.ConstructionSequencing
