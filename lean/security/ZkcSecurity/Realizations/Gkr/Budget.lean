module

public import ZkcSecurity.Realizations.Gkr.RootSource
public import ZkcSecurity.FiatShamir.CostComposition

@[expose] public section

/-! Pathwise query costs of the current source validator. Invalid statements
halt in admission. Admitted statements use the same body equation as rejection;
all replies and stopped branches remain in the cost bound. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 500000
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.Budget
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcExamples.Structured ZkcSecurity.FiatShamir
variable {F G A : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem repeat_cost (context : Context) (price stepCost : ENNReal)
    (step : A → PIR.Process (Actions F G) A)
    (bounded : ∀ value history, Typed.ChargedCostBound context.interface (fun _ _ => price)
      (step value) history stepCost) (count : Nat) (value : A) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (PIR.repeatN count step value) history (count * stepCost) := by
  induction count generalizing value history with
  | zero => trivial
  | succ count ih =>
      rw [PIR.repeatN]
      convert CostComposition.bind _ _ stepCost (count * stepCost)
        (bounded value history) (fun next reached => ih next reached) using 1
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

omit [Field F] [DecidableEq F] in
private theorem output_cost (ctx : ProtocolContext) (handle : Nat) (context : Context)
    (price : ENNReal) (point : List F) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (GkrVerifier.outputRound ctx handle point) history price := by
  simp only [GkrVerifier.outputRound, GkrVerifier.outputDelivery, Typed.ChargedCostBound,
    Context.interface, Payload.ofValue]
  exact ⟨0, by simp, fun _ => trivial⟩

private theorem round_cost (ctx : ProtocolContext) (handle : Nat) (context : Context)
    (price : ENNReal) (state : List F × F) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (GkrVerifier.round ctx handle state) history price := by
  simp only [GkrVerifier.round, GkrVerifier.roundFirst, GkrVerifier.roundSecond,
    Typed.ChargedCostBound, Context.interface]
  intro m0 c0 d0 m1 c1 d1 m2 c2 d2
  unfold GkrVerifier.roundCheck
  split
  · simp only [GkrVerifier.roundChallenge, Typed.ChargedCostBound,
      Context.interface, Payload.ofValue]
    exact ⟨0, by simp, fun _ => trivial⟩
  · trivial

omit [Field F] [DecidableEq F] in
private theorem coefficient_cost (ctx : ProtocolContext) (context : Context)
    (price : ENNReal) (line : List F) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (GkrVerifier.lineCoefficient ctx line) history 0 := by
  simp only [GkrVerifier.lineCoefficient, Typed.ChargedCostBound, Context.interface]
  intro _ _ _
  trivial

private theorem line_cost (ctx : ProtocolContext) (handle width : Nat) (context : Context)
    (price : ENNReal) (add mul : Zkc.Protocols.Gkr.Wiring F width)
    (state : GkrVerifier.State F) (left right : List F) (claim first : F)
    (coefficients : List F) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (GkrVerifier.lineCheck ctx handle width add mul state left right claim first coefficients) history price := by
  unfold GkrVerifier.lineCheck
  split
  · simp only [GkrVerifier.lineDelivery, Typed.ChargedCostBound, Context.interface, Payload.ofValue]
    exact ⟨0, by simp, fun _ => trivial⟩
  · trivial

private theorem layer_cost (ctx : ProtocolContext) (handle width : Nat) (context : Context)
    (price : ENNReal) (add mul : Nat → Zkc.Protocols.Gkr.Wiring F width)
    (state : GkrVerifier.State F) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (GkrVerifier.layerStep ctx handle width add mul state) history ((2 * width + 1) * price) := by
  unfold GkrVerifier.layerStep GkrVerifier.layerAfterLeft GkrVerifier.rounds
  have first := repeat_cost context price price (GkrVerifier.round (GkrVerifier.leftContext ctx) handle)
    (round_cost _ _ context price) width ([], state.2.2) history
  convert CostComposition.bind _ _ (width * price) (width * price + price) first ?_ using 1
  · ring
  · intro left reached
    have second := repeat_cost context price price (GkrVerifier.round (GkrVerifier.rightContext ctx) handle)
      (round_cost _ _ context price) width ([], left.2) reached
    apply CostComposition.bind _ _ (width * price) price second
    intro right reached
    simp only [GkrVerifier.layerAfterRight, Typed.ChargedCostBound, Context.interface]
    intro payload first decoded
    unfold GkrVerifier.layerAfterConstant
    have coefficients := repeat_cost (F := F) (G := G) context price 0
      (GkrVerifier.lineCoefficient (F := F) (G := G) ctx)
      (coefficient_cost (F := F) (G := G) ctx context price) width [first]
      (reached ++ [Event.message
        (context.message (GkrVerifier.lineConstantSite ctx) (ctx.roles 0) context.validator) payload])
    simp only [mul_zero] at coefficients
    have rest := CostComposition.bind _ _ 0 price coefficients (fun line reached =>
      line_cost ctx handle width context price (add state.1) (mul state.1)
        state left.1 right.1 right.2 first line reached)
    simpa only [zero_add] using rest

/-- An exact structural query bound for any admitted mathematical verifier. -/
theorem verifier_cost (ctx : ProtocolContext) (handle layers width : Nat) (context : Context)
    (price : ENNReal) (outputs inputs : Zkc.Polynomial.Multilinear.Table F width)
    (add mul : Nat → Zkc.Protocols.Gkr.Wiring F width) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (GkrVerifier.verifier ctx handle layers width outputs inputs add mul) history
      ((width + layers * (2 * width + 1)) * price) := by
  unfold GkrVerifier.verifier
  have initial := repeat_cost context price price (GkrVerifier.outputRound ctx handle)
    (output_cost ctx handle context price) width [] history
  convert CostComposition.bind _ _ (width * price) (layers * ((2 * width + 1) * price)) initial ?_ using 1
  · ring
  · intro point reached
    unfold GkrVerifier.afterOutputs
    have layersCost := repeat_cost context price ((2 * width + 1) * price)
      (GkrVerifier.layerStep ctx handle width add mul)
      (layer_cost ctx handle width context price add mul) layers
      (0, point, Zkc.Polynomial.Multilinear.extension width outputs
        (Zkc.Polynomial.coordinates width point)) reached
    have result := CostComposition.bind _
      (fun final => PIR.Process.done (GkrVerifier.decision width inputs final))
      (layers * ((2 * width + 1) * price)) 0
      layersCost (fun _ _ => trivial)
    simpa only [add_zero] using result

section SourceBound
variable [AddCommGroup G] [Module F G] [DecidableEq G]
attribute [local irreducible] Source.body Source.actualVerifier

/-- Every raw statement has at most forty reached source queries. Admission
failures halt before querying; no table-shape premise is exported. -/
theorem source_cost (runtime : Source.Invocation F) (context : Context)
    (price : ENNReal) (history : History F G) :
    Typed.ChargedCostBound context.interface (fun _ _ => price)
      (Source.body runtime) history (40 * price) := by
  by_cases admitted : runtime.Admitted
  · rw [Source.admitted_binding runtime admitted]
    apply CostComposition.mono (verifier_cost {} runtime.handle runtime.layers runtime.width
      context price runtime.outputTable runtime.encoding.circuit.inputs
      runtime.encoding.circuit.add runtime.encoding.circuit.mul history)
    have widthBound : runtime.width ≤ 4 := admitted.2.2.1
    have layersBound : runtime.layers ≤ 4 := admitted.2.2.2.1
    have countBound : runtime.width + runtime.layers * (2 * runtime.width + 1) ≤ 40 := by
      calc
        _ ≤ 4 + 4 * (2 * 4 + 1) := Nat.add_le_add widthBound
          (Nat.mul_le_mul layersBound (Nat.add_le_add_right (Nat.mul_le_mul_left 2 widthBound) 1))
        _ = 40 := rfl
    apply mul_le_mul' _ le_rfl
    exact_mod_cast countBound
  · obtain ⟨reason, stopped⟩ := Source.invalid_verifier_stops (G := G) runtime admitted
    have stoppedBody : Source.body (G := G) runtime = .halt reason := by
      unfold Source.body
      exact stopped
    rw [stoppedBody]
    trivial
end SourceBound

end ZkcSecurity.Realizations.Gkr.Budget
