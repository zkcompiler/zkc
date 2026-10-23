module

public import Zkc.Semantics.Continuation

@[expose] public section

/-! Statement/witness relations and explicit terminal adequacy.

Quantitative reduction composition is owned by `Zkc.Obligations` and its
security interpretation. Ordinary implication hypotheses suffice for a
relation-only argument; this module does not duplicate a reduction contract.
-/

set_option autoImplicit false

namespace PIR.Relation

/-- A protocol instance fixes the statement/witness interpretation. -/
structure Family where
  Statement : Type
  Witness : Type
  holds : Statement → Witness → Prop

def Valid (family : Family) (statement : family.Statement) : Prop :=
  ∃ witness, family.holds statement witness

variable {R A : Type}

/-- This law concerns the actual terminal decision, not a finished phase. -/
structure TerminalContract (residual : R → Prop)
    (verify : R → Continuation.Terminal A) : Prop where
  sound : ∀ r a, verify r = .accepted a → residual r

/-- A concrete scalar terminal: reaching the end of a round sequence supplies
    an actual residual scalar; acceptance additionally checks its target. -/
def scalarTerminal {F : Type} [DecidableEq F] (target actual : F) :
    Continuation.Terminal Unit := if actual = target then .accepted () else .rejected

theorem scalar_contract {F : Type} [DecidableEq F] (target : F) :
    TerminalContract (fun actual => actual = target) (scalarTerminal target) := by
  refine ⟨?_⟩
  intro actual a accepted
  by_cases h : actual = target
  · exact h
  · simp [scalarTerminal, h] at accepted

end PIR.Relation
