module

public import ZkcExamples.Executable.SumcheckCompleteness

@[expose] public section

/-! Native byte regressions with symbolic field values, codec and oracle.
The same three budgets cover the actual zero-, one- and two-round verifier. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Tests.SumcheckNativeConsumer
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Executable
open ZkcExamples.Construction.SumcheckDomainConnection

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (oracle : History F G → F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
  (encode : F → List UInt8)
  (roundtrip : ∀ value, decode SumcheckProof.coordinate (encode value) = some (.field "bls12-381.fr" value))
  (bounded : ∀ value, (encode value).length ≤ proofLimit)
  (binding : List UInt8) (bindingLength : binding.length = 32) (initial : History F G)

def honestRun (budget : Nat) (values : List F) (rounds : Nat) : Bool :=
  validate (m := Id) installed SumcheckProof.validator ZkcExamples.Construction.SumcheckProof.context
    oracle decode budget binding ZkcExamples.Construction.SumcheckProof.acceptancePosition
    (ZkcExamples.Construction.SumcheckProof.inputs values values.sum rounds) initial
    (SumcheckCompleteness.honestBytes encode binding (SumcheckCompleteness.honestRounds oracle initial values rounds))

include roundtrip bounded bindingLength

theorem selected_honest (rounds : Fin 3) (values : List F) (shaped : values.length = 2 ^ rounds.val) :
    honestRun oracle decode encode binding initial (72 + 59 * rounds.val) values rounds.val = true := by
  exact SumcheckCompleteness.honest_accepted oracle decode encode roundtrip bounded _ binding bindingLength
    values rounds.val (by rw [SumcheckProof.maximum_eq]; exact Nat.le_of_lt_succ rounds.isLt)
    shaped initial (by rw [SumcheckCharges.charge_eq])

theorem zero_honest (value : F) :
    honestRun oracle decode encode binding initial 72 [value] 0 = true :=
  selected_honest oracle decode encode roundtrip bounded binding bindingLength initial 0 [value] (by simp)

theorem one_honest (low high : F) :
    honestRun oracle decode encode binding initial 131 [low,high] 1 = true :=
  selected_honest oracle decode encode roundtrip bounded binding bindingLength initial 1 [low,high] (by simp)

theorem two_honest (a b c d : F) :
    honestRun oracle decode encode binding initial 190 [a,b,c,d] 2 = true :=
  selected_honest oracle decode encode roundtrip bounded binding bindingLength initial 2 [a,b,c,d] (by simp)

omit encode roundtrip bounded bindingLength in
/-- Header rejection precedes any decoding or oracle computation. -/
theorem wrong_header (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (bytes : List UInt8)
    (wrong : bytes.take 40 ≠ magic ++ binding) :
    validate (m := Id) installed SumcheckProof.validator ZkcExamples.Construction.SumcheckProof.context
      oracle decode budget binding ZkcExamples.Construction.SumcheckProof.acceptancePosition
      (ZkcExamples.Construction.SumcheckProof.inputs values claim rounds) initial bytes = false := by
  simp only [validate, ite_eq_right wrong]
  rfl

omit encode roundtrip bounded binding bindingLength in
/-- Budget zero exhausts before the first helper, on arbitrary public inputs
and proof bytes. The observation retains the native stop class. -/
theorem zero_budget (values : List F) (claim : F) (rounds : Nat) (bytes : List UInt8) :
    Run.observe (execute (m := Id) installed SumcheckProof.validator
      ZkcExamples.Construction.SumcheckProof.context oracle decode 0
      (ZkcExamples.Construction.SumcheckProof.inputs values claim rounds) initial bytes) =
        (.stopped .exhausted, true) := by
  have exactRun := SumcheckProof.executable_metered (m := Id) oracle decode 0 values claim rounds initial bytes
  rw [SumcheckCharges.lowered_eq] at exactRun
  simpa [SumcheckCharges.lowered, SumcheckShape.code, DomainVM.metered, DomainVM.meteredK,
    DomainVM.meteredStep, Functor.map, Pure.pure, Id.instMonad] using exactRun

end Tests.SumcheckNativeConsumer
