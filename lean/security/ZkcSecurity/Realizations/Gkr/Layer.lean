module

public import ZkcSecurity.Realizations.Gkr.Combination

public section
noncomputable section

/-! A complete actual GKR layer exports a reusable component. The left call
retains a width-dimensional residual; the right call consumes that same
restricted reference. The line component produces the next layer claim.
-/

namespace ZkcSecurity.Realizations.Gkr.Layer
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Construction
open Zkc.Obligations ZkcSecurity.Obligations
open ZkcSecurity.Families.Gkr
open ZkcSecurity.Realizations.Gkr.Circuit
open ZkcSecurity.Examples.Components
open ZkcExamples.Structured
open Zkc.Source.Structured
open OracleComp OracleSpec

variable {F G : Type} [Field F] [DecidableEq F] {width : Nat}

@[expose] def relation (circuit : Circuit F width) (remaining : Nat) :
    ClaimRelation (GkrVerifier.State F) Unit where
  Holds state _ := state.2.1.length = width ∧ state.2.2 = extension width (circuit.wires remaining state.1)
    (coordinates width state.2.1)
  No state := state.2.1.length = width ∧ state.2.2 ≠ extension width (circuit.wires remaining state.1)
    (coordinates width state.2.1)
  no_excludes _ _ wrong correct := wrong.2 correct.2

@[expose] def component (circuit : Circuit F width) (remaining : Nat)
    (ctx : ProtocolContext) (handle : Nat) :
    ComponentInterface (Actions F G) (Event F G) (GkrVerifier.State F) (GkrVerifier.State F) where
  Parameters := Unit
  Input := GkrVerifier.State F
  InputWitness := Unit
  Output := GkrVerifier.State F
  OutputWitness := Unit
  input := relation circuit (remaining + 1)
  output := relation circuit remaining
  body := GkrVerifier.layerStep ctx handle width circuit.add circuit.mul
  Scope _ state _ := state.2.1.length = width
  inputView _ state _ := some state
  outputView _ _ _ result := some result

/-- The inter-layer seam routes the actual returned index, point and claim.
Its mathematical map and runtime map coincide here by a checked square. -/
def connection (circuit : Circuit F width) (remaining : Nat) (ctx : ProtocolContext) (handle : Nat) :
    Connection (component (G := G) circuit (remaining + 1) ctx handle)
      (component circuit remaining ctx handle) where
  parameters := id
  route _ result := result
  map := id
  square _ _ _ _ _ defined := defined

omit [DecidableEq F] in
theorem connection_sound (circuit : Circuit F width) (remaining : Nat) :
    (relation circuit (remaining + 1)).SoundLink (relation circuit (remaining + 1)) id :=
  ClaimRelation.SoundLink.id _

omit [DecidableEq F] in
theorem connection_honest (circuit : Circuit F width) (remaining : Nat) :
    (relation circuit (remaining + 1)).HonestLink (relation circuit (remaining + 1)) id :=
  ClaimRelation.HonestLink.id _

variable [Fintype F] [SampleableType F]

/-- The coefficient loop establishes length and its retained constant term
independently of the input claim. All received field values remain arbitrary. -/
noncomputable def coefficients (ctx : ProtocolContext) (context : Context)
    (charge : History F G → Event F G → ENNReal) (first : F)
    (count : Nat) (tail : List F) (history : History F G) :
    Derivation context.interface (boundedEscape charge)
      (fun _ result => result.headD 0 = first ∧ result.length = tail.length + 1 + count)
      history (PIR.repeatN count (GkrVerifier.lineCoefficient ctx) (first :: tail)) := by
  induction count generalizing tail history with
  | zero => exact .done ⟨rfl, rfl⟩
  | succ count ih =>
    rw [PIR.repeatN]
    change Derivation context.interface (boundedEscape charge) _ _ (.call (.receive GkrVerifier.scalar
      (GkrVerifier.lineCoefficientSite ctx) (ctx.roles 0)) _)
    apply Derivation.receive rfl
    intro _ value _
    exact (ih (tail ++ [value]) _).consequence fun _ result shape =>
      ⟨shape.1, by have sized := shape.2; simp only [List.length_append, List.length_singleton] at sized; omega⟩

noncomputable opaque soundness (circuit : Circuit F width) (remaining : Nat)
    (ctx : ProtocolContext) (handle : Nat) (context : Context)
    (charge : History F G → Event F G → ENNReal)
    (roundCharge : ∀ inner, inner = GkrVerifier.leftContext ctx ∨ inner = GkrVerifier.rightContext ctx →
      ∀ history, 2 / (Fintype.card F : ENNReal) ≤ charge history
        (.challenge (context.query (GkrVerifier.challengeSite inner) (.draw "bls12-381.fr"))))
    (lineCharge : ∀ history, (width : ENNReal) / Fintype.card F ≤ charge history
      (.challenge (context.query (GkrVerifier.lineChallengeSite ctx) (.draw "bls12-381.fr")))) :
    SoundnessContract (component (G := G) circuit remaining ctx handle)
      context.interface (boundedEscape charge) := by
  intro _ state history pointLength inputNo
  have wrong : state.2.2 ≠ GkrRoundsReference.total
      (factors circuit remaining state.1 (coordinates width state.2.1)) := by
    rw [← layer_identity circuit]
    exact (ReadbackHolds.some.mp inputNo).2
  let root := factors circuit remaining state.1 (coordinates width state.2.1)
  have left := Rounds.residual (G := G) handle width (GkrVerifier.leftContext ctx) context
    (n := width) root state.2.2 (factors_admissible circuit _ _ _) wrong charge
    (roundCharge _ (.inl rfl)) history
  change Derivation _ _ _ _ ((GkrVerifier.rounds _ _ _ _).bind _)
  apply left.bind
  intro reached leftResult leftNo
  change Rounds.Residual (n := width) root leftResult at leftNo
  let leftState : Rounds.State F width := Classical.choose leftNo
  have facts : Rounds.Anchored root leftState ∧
      GkrRoundsReference.admissible leftState.reference ∧
      leftState.claim ≠ GkrRoundsReference.total leftState.reference ∧
      Rounds.project leftState = leftResult := Classical.choose_spec leftNo
  have anchored := facts.1
  have allowed := facts.2.1
  have leftWrong := facts.2.2.1
  have projected := facts.2.2.2
  have leftLength : leftResult.1.length = width := by
    rw [← projected]
    have length : leftState.point.length + width = width + width := anchored.1
    change leftState.point.length = width
    omega
  unfold GkrVerifier.layerAfterLeft
  have right := Rounds.residual (F := F) (G := G) handle width (GkrVerifier.rightContext ctx) context (n := 0)
  rw [Nat.zero_add] at right
  apply (right leftState.reference leftResult.2 allowed (by
      have claimEq : leftState.claim = leftResult.2 := congrArg Prod.snd projected
      exact claimEq ▸ leftWrong)
    charge (roundCharge _ (.inr rfl)) reached).bind
  intro afterRight rightResult rightNo
  have terminal := Rounds.terminal _ rightResult rightNo
  have gateWrong : rightResult.2 ≠ GkrVerifier.wiringValue
      (extension (width + width + width) (circuit.add state.1)
        (coordinates (width + width + width) (state.2.1 ++ leftResult.1 ++ rightResult.1)))
      (extension (width + width + width) (circuit.mul state.1)
        (coordinates (width + width + width) (state.2.1 ++ leftResult.1 ++ rightResult.1)))
      (extension width (circuit.wires remaining (state.1 + 1)) (coordinates width leftResult.1))
      (extension width (circuit.wires remaining (state.1 + 1)) (coordinates width rightResult.1)) := by
    have evaluation := factors_evaluation circuit remaining state.1 (coordinates width state.2.1)
      (coordinates width leftResult.1) (coordinates width rightResult.1)
    dsimp only at evaluation
    rw [← coordinates_three _ _ _ pointLength leftLength terminal.1,
      point_coordinates width _ _ leftLength terminal.1] at evaluation
    intro equal
    apply terminal.2
    rw [anchored.2, show leftState.point = leftResult.1 from congrArg Prod.fst projected]
    exact equal.trans evaluation.symm
  unfold GkrVerifier.layerAfterRight
  apply Derivation.receive rfl
  intro _ first _
  unfold GkrVerifier.layerAfterConstant
  apply (coefficients ctx context charge first width [] _).bind
  intro beforeLine received shape
  let invocation : Combination.Invocation F width :=
    ⟨circuit.add state.1, circuit.mul state.1, state, leftResult.1, rightResult.1,
      rightResult.2, first, received⟩
  have line := Combination.soundness (G := G) (circuit.wires remaining (state.1 + 1)) ctx handle context charge
    lineCharge
  let interaction : PIR.Interaction (Actions F G) :=
    ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
  have framed := (line () invocation beforeLine ⟨leftLength, terminal.1, by
      change received.length = width + 1
      have sized := shape.2
      simp only [List.length_nil] at sized
      omega, shape.1⟩
    (ReadbackHolds.some.mpr (by rintro ⟨_, correct⟩; exact gateWrong correct))).frameReturns
      interaction (fun result => result.1 = state.1 + 1 ∧ result.2.1.length = width) ()
      (Combination.returns _ ctx handle invocation leftLength terminal.1 interaction ())
  exact framed.consequence fun _ result holds => by
        obtain ⟨evaluation, defined, wrong⟩ := holds.1
        cases Option.some.inj defined
        apply ReadbackHolds.some.mpr
        refine ⟨holds.2.2, ?_⟩
        intro correct
        apply wrong
        exact ⟨(), by simpa only [holds.2.1] using correct⟩

end ZkcSecurity.Realizations.Gkr.Layer
