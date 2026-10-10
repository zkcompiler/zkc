import Zkc.Semantics.Continuation

/-! Statement/witness relations and soundness contracts for protocol reductions.

`ReductionContract.then` composes implications for the actual intermediate
result and accumulates explicit bad events by disjunction. It supplies neither
witness reconstruction nor completeness, sampling, or a probability bound.
Those require separate laws of the selected execution and adversary model.
`terminal_sound` additionally consumes a sound terminal decision; finishing a
phase or producing residual claims is insufficient for acceptance.
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

variable {S R A : Type}

/-- Completeness and soundness directions must be requested separately.
    `bad` is the explicit exceptional event of a reduction execution. A
    probability theorem, not this predicate, must bound its probability. -/
structure ReductionContract (input : S → Prop) (residual : R → Prop)
    (source : S) (result : R) (bad : Prop) : Prop where
  sound : residual result → input source ∨ bad

theorem ReductionContract.then {T : Type} {input : S → Prop} {middle : R → Prop}
    {last : T → Prop} {s : S} {r : R} {t : T} {bad₁ bad₂ : Prop}
    (first : ReductionContract input middle s r bad₁)
    (next : ReductionContract middle last r t bad₂) :
    ReductionContract input last s t (bad₁ ∨ bad₂) := by
  refine ⟨?_⟩
  intro accepted
  rcases next.sound accepted with intermediate | bad
  · rcases first.sound intermediate with valid | bad
    · exact Or.inl valid
    · exact Or.inr (Or.inl bad)
  · exact Or.inr (Or.inr bad)

/-- This law concerns the actual terminal decision, not a finished phase. -/
structure TerminalContract (residual : R → Prop)
    (verify : R → Continuation.Terminal A) : Prop where
  sound : ∀ r a, verify r = .accepted a → residual r

theorem terminal_sound {input : S → Prop} {residual : R → Prop}
    {source : S} {result : R} {bad : Prop}
    (reduction : ReductionContract input residual source result bad)
    (verify : R → Continuation.Terminal A) (terminal : TerminalContract residual verify)
    (a : A) (accepted : verify result = .accepted a) : input source ∨ bad :=
  reduction.sound (terminal.sound result a accepted)

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
