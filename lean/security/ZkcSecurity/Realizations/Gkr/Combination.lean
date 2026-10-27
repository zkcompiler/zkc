module

public import ZkcSecurity.Families.Gkr.Combination
public import ZkcSecurity.Realizations.Gkr.Rounds

public section
noncomputable section

namespace ZkcSecurity.Realizations.Gkr.Combination
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Construction
open Zkc.Obligations ZkcSecurity.Obligations
open ZkcSecurity.Families.Gkr
open ZkcExamples.Structured
open Zkc.Source.Structured
open OracleComp OracleSpec

variable {F G : Type} [Field F] [DecidableEq F] {width : Nat}

structure Invocation (F : Type) (width : Nat) where
  add : Zkc.Protocols.Gkr.Wiring F width
  mul : Zkc.Protocols.Gkr.Wiring F width
  state : GkrVerifier.State F
  left : List F
  right : List F
  claim : F
  first : F
  coefficients : List F

@[expose] def gateClaim (below : Table F width) (runtime : Invocation F width) : Prop :=
  runtime.claim = GkrVerifier.wiringValue
    (extension (width + width + width) runtime.add
      (coordinates (width + width + width) (runtime.state.2.1 ++ runtime.left ++ runtime.right)))
    (extension (width + width + width) runtime.mul
      (coordinates (width + width + width) (runtime.state.2.1 ++ runtime.left ++ runtime.right)))
    (extension width below (coordinates width runtime.left))
    (extension width below (coordinates width runtime.right))

@[expose] def component (below : Table F width) (ctx : ProtocolContext) (handle : Nat) :
    ComponentInterface (Actions F G) (Event F G)
    (Invocation F width) (GkrVerifier.State F) where
  Parameters := Unit
  Input := Invocation F width
  InputWitness := Unit
  Output := Evaluation F width
  OutputWitness := Unit
  input := .exact fun runtime _ => gateClaim below runtime
  output := evaluationRelation below
  body runtime := GkrVerifier.lineCheck ctx handle width runtime.add runtime.mul
    runtime.state runtime.left runtime.right runtime.claim runtime.first runtime.coefficients
  Scope _ runtime _ := runtime.left.length = width ∧ runtime.right.length = width ∧
    runtime.coefficients.length = width + 1 ∧ runtime.coefficients.headD 0 = runtime.first
  inputView _ runtime _ := some runtime
  outputView _ _ _ result := some ⟨coordinates width result.2.1, result.2.2⟩

/-- This frame law is independent of claim truth, received coefficients and
the sampler. A stopping branch never supplies a returned state. -/
theorem returns (below : Table F width) (ctx : ProtocolContext) (handle : Nat)
    (runtime : Invocation F width) (leftSize : runtime.left.length = width)
    (rightSize : runtime.right.length = width)
    (interaction : PIR.Interaction (Actions F G)) (phase : interaction.Phase) :
    PIR.Boundary.Returns interaction
      (fun result _ => result.1 = runtime.state.1 + 1 ∧ result.2.1.length = width)
      ((component below ctx handle).body runtime) phase := by
  change PIR.Boundary.Returns _ _ (GkrVerifier.lineCheck _ _ _ _ _ _ _ _ _ _ _) _
  unfold GkrVerifier.lineCheck
  split
  · intro t delivered
    exact ⟨rfl, by simp only [linePoints_length, leftSize, rightSize, min_self]⟩
  · trivial

/-- Successful execution of the same combination body for a delivered honest
line polynomial. Query and delivery equations preserve actual handler state
and observations; they do not presume a successful verifier result. -/
theorem honest {H E : Type} (below : Table F width) (ctx : ProtocolContext) (handle : Nat)
    (runtime : Invocation F width) (leftSize : runtime.left.length = width)
    (rightSize : runtime.right.length = width) (head : runtime.coefficients.headD 0 = runtime.first)
    (gate : gateClaim below runtime)
    (polynomial : coefficientPolynomial runtime.coefficients =
      linePolynomial width below (coordinates width runtime.left) (coordinates width runtime.right))
    (handler : PIR.Handler (Actions F G) H E) (initial queried final : H) (challenge : F)
    (queryEvents deliveryEvents : List E)
    (query : handler (.query (GkrVerifier.lineChallengeSite ctx) "bls12-381.fr" (.cons handle .nil)) initial =
      ⟨.returned challenge, queried, queryEvents⟩)
    (delivery : handler (.send (ty := GkrVerifier.scalar) (GkrVerifier.lineDeliverySite ctx)
      (ctx.roles 0) challenge) queried = ⟨.returned (), final, deliveryEvents⟩) :
    ∃ result, ((component below ctx handle).body runtime).run handler initial =
      ⟨.returned result, final, queryEvents ++ deliveryEvents⟩ ∧
      result.1 = runtime.state.1 + 1 ∧ result.2.1.length = width ∧
      result.2.2 = extension width below (coordinates width result.2.1) := by
  have endpoints := Families.Gkr.Combination.honest_endpoints below _ _ _ polynomial
  have checked : runtime.claim = GkrVerifier.wiringValue
      (extension (width + width + width) runtime.add
        (coordinates (width + width + width) (runtime.state.2.1 ++ runtime.left ++ runtime.right)))
      (extension (width + width + width) runtime.mul
        (coordinates (width + width + width) (runtime.state.2.1 ++ runtime.left ++ runtime.right)))
      runtime.first runtime.coefficients.sum := by
    rw [← head, endpoints.1, endpoints.2]
    exact gate
  refine ⟨(runtime.state.1 + 1, linePoints runtime.left runtime.right challenge,
    powerSum runtime.coefficients challenge), ?_, rfl, ?_, ?_⟩
  · change (GkrVerifier.lineCheck _ _ _ _ _ _ _ _ _ _ _).run _ _ = _
    rw [GkrVerifier.lineCheck, ite_eq_left checked]
    simp only [PIR.Process.run, query, PIR.Execution.follow, GkrVerifier.lineDelivery, delivery,
      List.append_nil]
  · simp only [linePoints_length, leftSize, rightSize, min_self]
  · simpa only [coordinates_linePoints _ _ _ leftSize rightSize] using
      Families.Gkr.Combination.honest_evaluation below _ _ _ polynomial challenge

variable [Fintype F] [SampleableType F]

/-- The received polynomial is fixed before the actual line challenge. Every
coefficient list of the source's length is admitted, including false ones. -/
noncomputable opaque soundness (below : Table F width) (ctx : ProtocolContext) (handle : Nat) (context : Context)
    (charge : History F G → Event F G → ENNReal)
    (covers : ∀ history,
      (width : ENNReal) / Fintype.card F ≤ charge history
        (.challenge (context.query (GkrVerifier.lineChallengeSite ctx) (.draw "bls12-381.fr")))) :
    SoundnessContract (component (G := G) below ctx handle) context.interface (boundedEscape charge) := by
  intro _ runtime history scope inputNo
  have wrong : ¬ gateClaim below runtime := by
    intro correct
    exact (ReadbackHolds.some.mp inputNo) ⟨(), correct⟩
  change Derivation _ _ _ _ (GkrVerifier.lineCheck _ _ _ _ _ _ _ _ _ _ _)
  unfold GkrVerifier.lineCheck
  apply Derivation.guard
  intro checked
  let start := coordinates width runtime.left
  let finish := coordinates width runtime.right
  have different := Families.Gkr.Combination.different below start finish _ _ runtime.claim
    runtime.first runtime.coefficients scope.2.2.2 wrong checked
  have degree : (coefficientPolynomial runtime.coefficients).natDegree ≤ width :=
    (coefficientPolynomial_natDegree _).trans (by rw [scope.2.2.1]; omega)
  let bad := fun t : F => (coefficientPolynomial runtime.coefficients).eval t =
    (linePolynomial width below start finish).eval t
  refine Derivation.query rfl bad ?_ ?_
  · exact (ZkcSecurity.Algebra.Polynomial.agreement_uniform_le _ _ different degree
      (linePolynomial_natDegree below start finish)).trans (by simpa only [max_self] using covers history)
  · intro raw reply decoded outside
    cases Option.some.inj decoded
    unfold GkrVerifier.lineDelivery
    apply Derivation.send rfl
    apply Derivation.done
    refine ⟨_, rfl, ?_⟩
    rintro ⟨_, equal⟩
    apply outside
    change powerSum runtime.coefficients raw =
      extension width below (coordinates width (linePoints runtime.left runtime.right raw)) at equal
    simpa only [bad, start, finish, coefficientPolynomial_eval, linePolynomial_eval,
      coordinates_linePoints _ _ _ scope.1 scope.2.1] using equal

end ZkcSecurity.Realizations.Gkr.Combination
