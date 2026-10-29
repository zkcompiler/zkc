module

public import ZkcSecurity.FiatShamir.OccurrenceReading
public import ZkcExamples.Construction.ComposedSumcheckProof

@[expose] public section

/-! The second source client consumes its stored complete connection. The
all-input endpoint includes both applications and arbitrary capability labels;
the independent nominal field-reading laws remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.OccurrenceReading
open Zkc.Source Zkc.Construction
open ZkcSecurity.FiatShamir
open ZkcExamples.Construction
variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Exact source/compiler scalar reading for arbitrary raw inputs and replies. -/
theorem sumcheck_reading {m : Type → Type} [Monad m] [LawfulMonad m]
    (oracle : History F G → m F) (left right : List F) (leftClaim rightClaim : F)
    (count handle : Nat) (initial : History F G) (proof : Proof F G) :
    ComposedSumcheckProof.compiledVerifier oracle left right leftClaim rightClaim count initial proof =
      transform ComposedSumcheckProof.context oracle
        (ComposedSumcheckProof.verifier left right leftClaim rightClaim count handle) initial proof :=
  ComposedSumcheckProof.compiled_transform oracle left right leftClaim rightClaim count handle initial proof

#print axioms sumcheck_reading
#print axioms OccurrenceReading.reading
#print axioms OccurrenceReading.charged
#print axioms OccurrenceReading.cost

end TestsSecurity.OccurrenceReading
