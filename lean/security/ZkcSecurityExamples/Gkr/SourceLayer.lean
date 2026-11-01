module

public import ZkcSecurityExamples.Gkr.HonestProducerObserved
public import ZkcSecurityExamples.Gkr.SourceRounds
public import ZkcSecurity.Bindings.Source.OccurrenceProperties

@[expose] public section

/-! GKR layer mathematics on the occurrence-preserving source presentation.
Both Sumcheck applications use the shared degree-two residual contract. The
line law is fixed by all received coefficients before its actual query. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.SourceLayer
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Source ZkcSecurity.Families.Gkr ZkcSecurity.Examples.Components
open ZkcExamples.Structured OracleComp OracleSpec
open HonestProducerObservedLayers
variable {F G : Type} [Field F] [DecidableEq F] {width : Nat}

def No (circuit : Families.Gkr.Circuit F width) (remaining : Nat)
    (state : Nat × List F × F) : Prop :=
  state.2.1.length = width ∧ state.2.2 ≠ extension width (circuit.wires remaining state.1)
    (coordinates width state.2.1)

variable [Fintype F] [SampleableType F]
attribute [local instance] ZkcSecurity.FiatShamir.OccurrenceReading.rawSampleable

def coefficients (ctx : ProtocolContext) (site : String) (start count : Nat)
    (first : F) (tail : List F) (price : ENNReal)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ result => result.headD 0 = first ∧ result.length = tail.length+1+count)
      history (validatorCoefficients ctx site start count (first :: tail)) := by
  induction count generalizing start tail history with
  | zero => exact .done ⟨rfl,rfl⟩
  | succ count ih =>
    rw [validatorCoefficients]
    simp only [Occurrence.iterations, GkrVerifier.lineCoefficient,
      PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
    apply Derivation.send rfl
    apply Derivation.receive rfl
    intro _ value _
    apply Derivation.send rfl
    exact (ih (start+1) (tail ++ [value]) _).consequence fun _ result shape =>
      ⟨shape.1, by have sized := shape.2; simp only [List.length_append, List.length_singleton] at sized; omega⟩

def line (below : Table F width) (ctx : ProtocolContext) (handle : Nat)
    (add mul : Zkc.Protocols.Gkr.Wiring F width) (state : Nat × List F × F)
    (left right : List F) (claim first : F) (received : List F)
    (leftSize : left.length = width) (rightSize : right.length = width)
    (size : received.length = width+1) (head : received.headD 0 = first)
    (wrong : claim ≠ GkrVerifier.wiringValue
      (extension (width+width+width) add (coordinates (width+width+width) (state.2.1 ++ left ++ right)))
      (extension (width+width+width) mul (coordinates (width+width+width) (state.2.1 ++ left ++ right)))
      (extension width below (coordinates width left)) (extension width below (coordinates width right)))
    (price : ENNReal) (covers : (width : ENNReal) / Fintype.card F ≤ price)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ result => result.1 = state.1+1 ∧ result.2.1.length = width ∧
        result.2.2 ≠ extension width below (coordinates width result.2.1)) history
      (((GkrVerifier.lineCheck ctx handle width add mul state left right claim first received).interpret
        CommonAdapter.embed).interpret Occurrence.actions) := by
  unfold GkrVerifier.lineCheck
  split
  next checked =>
    have different := Families.Gkr.Combination.different below (coordinates width left)
      (coordinates width right) _ _ claim first received head wrong checked
    have degree : (coefficientPolynomial received).natDegree ≤ width :=
      (coefficientPolynomial_natDegree _).trans (by rw [size]; omega)
    simp only [PIR.Process.interpret, GkrVerifier.lineDelivery, CommonAdapter.embed,
      Occurrence.actions, PIR.Process.bind]
    refine Derivation.query rfl
      (fun (t : F) => (coefficientPolynomial received).eval t =
        (linePolynomial width below (coordinates width left) (coordinates width right)).eval t)
      (PublicUniform.bound price _ _ _ _
        ((ZkcSecurity.Algebra.Polynomial.agreement_uniform_le _ _ different degree
          (linePolynomial_natDegree below _ _)).trans (by simpa only [max_self] using covers)) history) ?_
    intro raw reply decoded outside
    cases Option.some.inj decoded
    apply Derivation.send rfl
    apply Derivation.done
    refine ⟨rfl, by simp only [linePoints_length,leftSize,rightSize,min_self], ?_⟩
    intro equal
    apply outside
    simpa only [coefficientPolynomial_eval, linePolynomial_eval,
      coordinates_linePoints _ _ _ leftSize rightSize] using equal
  next => exact .halt .reject

def rejected (circuit : Families.Gkr.Circuit F width) (remaining : Nat)
    (ctx : ProtocolContext) (sites : Sites) (handle : Nat) (state : Nat × List F × F)
    (wrong : No circuit (remaining+1) state) (price : ENNReal)
    (roundBound : 2 / (Fintype.card F : ENNReal) ≤ price)
    (lineBound : (width : ENNReal) / Fintype.card F ≤ price)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ result => No circuit remaining result) history
      (validatorLayer ctx handle width sites circuit.add circuit.mul state) := by
  have mismatch : state.2.2 ≠ GkrRoundsReference.total
      (Circuit.factors circuit remaining state.1 (coordinates width state.2.1)) := by
    rw [← Circuit.layer_identity circuit]
    exact wrong.2
  let root := Circuit.factors circuit remaining state.1 (coordinates width state.2.1)
  unfold validatorLayer
  apply (SourceRounds.residual (G := G) (GkrVerifier.leftContext ctx) sites.left handle 0 width
    (n := width) root state.2.2 (Circuit.factors_admissible circuit _ _ _) mismatch price roundBound history).bind
  intro reached left leftNo
  let leftState : Rounds.State F width := Classical.choose leftNo
  have facts := Classical.choose_spec leftNo
  have anchored := facts.1
  have allowed := facts.2.1
  have leftWrong := facts.2.2.1
  have projected := facts.2.2.2
  have leftLength : left.1.length = width := by
    rw [← projected]
    have length : leftState.point.length + width = width + width := anchored.1
    change leftState.point.length = width
    omega
  have right := SourceRounds.residual (F := F) (G := G) (GkrVerifier.rightContext ctx)
    sites.right handle 0 width (n := 0)
  rw [Nat.zero_add] at right
  apply (right leftState.reference left.2 allowed (by
    have claimEq := congrArg Prod.snd projected
    exact claimEq ▸ leftWrong) price roundBound reached).bind
  intro afterRight right rightNo
  have terminal := Rounds.terminal _ right rightNo
  have gateWrong : right.2 ≠ GkrVerifier.wiringValue
      (extension (width+width+width) (circuit.add state.1)
        (coordinates (width+width+width) (state.2.1 ++ left.1 ++ right.1)))
      (extension (width+width+width) (circuit.mul state.1)
        (coordinates (width+width+width) (state.2.1 ++ left.1 ++ right.1)))
      (extension width (circuit.wires remaining (state.1+1)) (coordinates width left.1))
      (extension width (circuit.wires remaining (state.1+1)) (coordinates width right.1)) := by
    have evaluation := Circuit.factors_evaluation circuit remaining state.1 (coordinates width state.2.1)
      (coordinates width left.1) (coordinates width right.1)
    dsimp only at evaluation
    rw [← coordinates_three _ _ _ wrong.1 leftLength terminal.1,
      point_coordinates width _ _ leftLength terminal.1] at evaluation
    intro equal
    apply terminal.2
    rw [anchored.2, show leftState.point = left.1 from congrArg Prod.fst projected]
    exact equal.trans evaluation.symm
  simp only [PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
  apply Derivation.receive rfl
  intro _ first _
  apply (coefficients ctx sites.coefficients 0 width first [] price _).bind
  intro beforeLine received shape
  exact (line (circuit.wires remaining (state.1+1)) ctx handle (circuit.add state.1)
    (circuit.mul state.1) state left.1 right.1 right.2 first received leftLength terminal.1
    (by simpa only [List.length_nil, Nat.zero_add, Nat.add_comm] using shape.2) shape.1 gateWrong price lineBound beforeLine).consequence
      (fun _ result holds => ⟨holds.2.1, by simpa only [holds.1] using holds.2.2⟩)

#print axioms rejected
end ZkcSecurity.Realizations.Gkr.SourceLayer
