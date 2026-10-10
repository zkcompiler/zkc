import Zkc.Semantics.RelationComposition

/-! Exact realization of a selected acceptance-and-output relation.

The input binds the actual verifier source, proof and configuration where they
matter. Each instance chooses its quantifier partition: fixed statement and
environment in the input, exposed results in the output, and existential
assignments in the witness. A derived challenge placed in the witness must be
constrained to the actual selected derivation; existentially choosing an
interactive challenge does not express its experiment's probability law.
Outputs and internal witness types may depend on that input. Soundness
quantifies over every satisfying witness, not just an honest assignment. This
contract does not equate executions, establish input coverage, prove protocol
security or discharge a residual obligation returned as an output.
-/

namespace Zkc.Realization

variable {I : Type} {O : I → Type} {W : (i : I) → O i → Type}

/-- Both directions concern the same selected input and exposed output. -/
structure Acceptance (accepts : (i : I) → O i → Prop)
    (constraints : (i : I) → (o : O i) → W i o → Prop) : Prop where
  sound : ∀ i o w, constraints i o w → accepts i o
  complete : ∀ i o, accepts i o → ∃ w, constraints i o w

namespace Acceptance

variable {accepts : (i : I) → O i → Prop}
  {constraints : (i : I) → (o : O i) → W i o → Prop}

theorem adequacy (realization : Acceptance accepts constraints) (i : I) (o : O i) :
    (∃ w, constraints i o w) ↔ accepts i o :=
  ⟨fun ⟨w, hw⟩ => realization.sound i o w hw, realization.complete i o⟩

/-- Connect the actual source input through an explicit binding function. The
source predicate is stated independently and must agree at that binding. -/
theorem bindInput {S : Type} (realization : Acceptance accepts constraints)
    (bind : S → I) (sourceAccepts : (s : S) → O (bind s) → Prop)
    (bound : ∀ s o, sourceAccepts s o ↔ accepts (bind s) o) :
    Acceptance sourceAccepts (fun s o w => constraints (bind s) o w) where
  sound s o w hw := (bound s o).mpr (realization.sound (bind s) o w hw)
  complete s o ho := realization.complete (bind s) o ((bound s o).mp ho)

/-- A following consumer sees the actual returned output, which cannot be
existentially hidden separately on the two sides of the connection. -/
theorem followedBy (realization : Acceptance accepts constraints)
    (consumer : (i : I) → O i → Prop) (i : I) :
    (∃ o w, constraints i o w ∧ consumer i o) ↔
      ∃ o, accepts i o ∧ consumer i o := by
  constructor
  · rintro ⟨o, w, hw, hc⟩
    exact ⟨o, realization.sound i o w hw, hc⟩
  · rintro ⟨o, ho, hc⟩
    obtain ⟨w, hw⟩ := realization.complete i o ho
    exact ⟨o, w, hw, hc⟩

/-- Different component outputs share meaning through a selected connector.
Their internal constraint witnesses may use unrelated representations. -/
theorem connected {P : I → Type} {V : (i : I) → P i → Type}
    {otherAccepts : (i : I) → P i → Prop}
    {otherConstraints : (i : I) → (p : P i) → V i p → Prop}
    (left : Acceptance accepts constraints)
    (right : Acceptance otherAccepts otherConstraints)
    (connect : (i : I) → O i → P i → Prop) (i : I) :
    PIR.Relation.Connected (fun o => ∃ w, constraints i o w) (connect i)
        (fun p => ∃ v, otherConstraints i p v) ↔
      PIR.Relation.Connected (accepts i) (connect i) (otherAccepts i) :=
  PIR.Relation.Connected.congr (connect i) (left.adequacy i) (right.adequacy i)

end Acceptance
end Zkc.Realization
