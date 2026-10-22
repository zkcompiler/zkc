module

public import ZkcArkLib.Sumcheck.Bridge
public import ZkcArkLib.Sumcheck.Domain
public import Zkc.Specification

@[expose] public section

namespace ZkcSecurity.ArkLib.Sumcheck
open _root_.Interaction.Oracle OracleSpec OracleComp
open _root_.Sumcheck.Interaction
open Zkc.Protocols.Sumcheck.Common
open scoped BigOperators ENNReal

variable {F : Type} [Field F]

def noAccess : PFunctor := ⟨Empty, Empty.elim⟩
def noImplementation : QueryImpl (ofPFunctor noAccess) Id := fun query => nomatch query

/-- The public polynomial is a fixed mathematical statement oracle. It has no
native cryptographic-provider assumption or unproved commitment realization. -/
noncomputable def statementOracle (coefficients : Coefficients F) :
    VirtualOracle (ofPFunctor noAccess) (MultivariateRound.polynomialFamily F 2 2) :=
  ⟨fun query => pure ((MultivariateRound.polynomialFamily F 2 2).behaviorOfRealizations
    (fun _ => oracleStatement coefficients) query)⟩

theorem statementOracle_realized (coefficients : Coefficients F) :
    (statementOracle coefficients).eval noImplementation =
      (MultivariateRound.polynomialFamily F 2 2).behaviorOfRealizations
        (fun _ => oracleStatement coefficients) := by
  rfl

theorem statementOracle_answers (coefficients : Coefficients F) (first second : F) :
    (statementOracle coefficients).eval noImplementation ⟨(), ![first, second]⟩ =
      evaluate coefficients first second := by
  exact statement_evaluate coefficients first second

theorem closed_statement (coefficients : Coefficients F) (claim : F) :
    MultivariateRound.closedRelation F 2 2 (boolEmbedding F) 0
      ⟨⟨claim, Fin.elim0⟩, (statementOracle coefficients).eval noImplementation⟩ ↔
      (polynomial coefficients).booleanSum = claim := by
  change (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ 2,
    MvPolynomial.eval (Fin.append Fin.elim0 point ∘ Fin.cast (by decide))
      (statement coefficients)) = claim ↔ _
  simp only [Fin.append_left_nil _ _ rfl, Function.comp_def, Fin.cast_eq_self]
  rw [statement_sum]

variable [DecidableEq F] [SampleableType F] [Fintype F]

/-- ArkLib's soundness theorem, transported to the actual admitted PIR verifier
under reached-query uniform sampling and arbitrary causal coefficient messages. -/
theorem soundness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (coefficients : Coefficients F)
    (claim : F) (service : Nat) (prover : Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    Pr{let result ← execution program coefficients claim service prover}[
      result.outcome = PIR.Outcome.returned (some true)] ≤ 4 / (Fintype.card F : ENNReal) := by
  have bound := Native.execute_soundness 2 2 F (boolEmbedding F) 2 0 rfl noAccess
    (statementOracle coefficients) ⟨claim, Fin.elim0⟩ noImplementation
    (nativeProver (strategy prover)) (oracleStatement coefficients)
    (statementOracle_realized coefficients)
    (fun h => falseClaim ((closed_statement coefficients claim).mp h).symm)
  have roundBound : (2 : ENNReal) * 2 = 4 := by norm_num
  have nativeBound : prEvent (nativeAcceptance booleanDomain noAccess (statementOracle coefficients)
      noImplementation claim prover) ≤ 4 / (Fintype.card F : ENNReal) := by
    simpa only [nativeAcceptance, prEvent_norm, booleanDomain, Nat.cast_ofNat, roundBound] using bound
  rw [native_game (booleanDomain (F := F)) noAccess (statementOracle coefficients)
    noImplementation coefficients claim prover booleanDomain_sum (statementOracle_answers coefficients),
    ← execution_game certificate coefficients claim service prover] at nativeBound
  simpa only [prEvent_norm] using nativeBound

/-- Arbitrary private probabilistic choice of a causal strategy, made without
access to the verifier's fresh challenge draws. `ProbComp` supplies a normalized
private mixture; an additional failure monad requires its own transport law. -/
theorem randomized_soundness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (coefficients : Coefficients F)
    (claim : F) (service : Nat) (provers : ProbComp (Strategy F))
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    Pr{let result ← (provers >>= execution program coefficients claim service)}[
      result.outcome = PIR.Outcome.returned (some true)] ≤ 4 / (Fintype.card F : ENNReal) :=
  prEvent_bind_le_of_forall_le provers (execution program coefficients claim service) _
    (fun prover => soundness certificate coefficients claim service prover falseClaim)

/-- Typed property selection is separate from program conformance. -/
noncomputable def soundnessProperty (coefficients : Coefficients F) (claim : F)
    (service : Nat) (provers : ProbComp (Strategy F)) : Zkc.Verification.Property (Verifier F) where
  assumptions _ := claim ≠ (polynomial coefficients).booleanSum
  conclusion program :=
    Pr{let result ← (provers >>= execution program coefficients claim service)}[
      result.outcome = PIR.Outcome.returned (some true)] ≤ 4 / (Fintype.card F : ENNReal)

theorem soundnessConsumer (wiring : Wiring) (coefficients : Coefficients F) (claim : F)
    (service : Nat) (provers : ProbComp (Strategy F)) :
    Zkc.Verification.Consumer (VerifierContract wiring)
      (soundnessProperty coefficients claim service provers) :=
  ⟨fun _ certificate falseClaim =>
    randomized_soundness certificate coefficients claim service provers falseClaim⟩

end ZkcSecurity.ArkLib.Sumcheck
