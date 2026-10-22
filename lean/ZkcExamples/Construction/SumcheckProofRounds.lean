module

public import ZkcExamples.Construction.SumcheckProof
public import ZkcExamples.Structured.SumcheckSourceVerifier

@[expose] public section

/-! The compiled Sumcheck verifier read through the source rounds.

`SumcheckProof` is generated from the Entry's exports. With an admitted round
count and a decoded verifier table, its original validator is the source rounds
followed by the multilinear terminal check
(`SumcheckSourceVerifier.verifier_checked`), so the compiled verifier is the
Fiat–Shamir transform of that process (`compiled_transform_rounds`).
-/

namespace ZkcExamples.Construction.SumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- With an admitted round count and a decoded verifier table, the compiled
verifier is the Fiat–Shamir transform of the source rounds followed by the
multilinear terminal check of the final point and claim. -/
theorem compiled_transform_rounds {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (rounds : Nat) (admitted : rounds ≤ 2) (values : List F) (claim : F)
    (handle : Nat) (table : Zkc.Polynomial.Multilinear.Table F rounds)
    (decoded : Zkc.Polynomial.Multilinear.ofList? rounds values = some table)
    (vectorBound : values.length < indexLimit) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge (helperTable program F G) participant.returned participant.instructions
          (inputs values claim rounds ++ [.transcript initial]) proof =
      transform context challenge
        (((PIR.repeatN rounds (ZkcExamples.Structured.SumcheckVerifierLaws.roundPlain (G := G)
            ZkcExamples.Structured.SumcheckSourceVerifier.childContext (some handle)) (some [], some claim)).bind
          (fun pc => match pc.1, pc.2 with
            | some point, some value => .done (some (decide (point.length = rounds ∧
                Zkc.Polynomial.Multilinear.extension rounds table
                  (Zkc.Polynomial.coordinates rounds point) = value)))
            | _, _ => .halt .incomplete)).interpret CommonAdapter.project) initial proof := by
  rw [compiled_transform challenge values claim rounds handle initial proof]
  unfold verifier process
  rw [show verifierInputs (F := F) (G := G) values claim rounds handle =
      ZkcExamples.Structured.SumcheckSourceVerifier.sourceRootInputs (some values) (some claim) (some rounds)
        (some handle) from rfl,
    ZkcExamples.Structured.SumcheckSourceVerifier.verifier_checked rounds admitted values (some claim)
    (some handle) table decoded vectorBound]
  congr 2
  rw [PIR.Process.bind_assoc]
  congr 1
  funext pc
  rcases pc with ⟨_ | point, _ | value⟩ <;> rfl

end ZkcExamples.Construction.SumcheckProof
