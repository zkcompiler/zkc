module

public import ZkcSecurityExamples.Gkr.CanonicalVerifier
public import ZkcSecurityExamples.Gkr.SourceAdmission
public import ZkcSecurity.Bindings.Source.OccurrenceProperties
public meta import ZkcSecurityTools.SourceProperties.Loops

@[expose] public section

/-! Pathwise cost of the actual occurrence validator, for arbitrary replies
and incoming source histories. Source iteration boundaries are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.Budget
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open ZkcSecurity.Source ZkcSecurity.FiatShamir ZkcExamples.Structured
open HonestProducerOccurrences HonestProducerObservedLayers HonestProducerObserved
variable {F G : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem output_step (ctx : ProtocolContext) (handle : Nat) (point : List F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (((GkrVerifier.outputRound ctx handle point).interpret CommonAdapter.embed).interpret Occurrence.actions)
      history price := by
  simp only [GkrVerifier.outputRound,GkrVerifier.outputDelivery,PIR.Process.interpret,
    CommonAdapter.embed,Occurrence.actions,PIR.Process.bind,Typed.ChargedCostBound,PublicProperties.interface]
  exact ⟨0,by simp,fun _ => trivial⟩

private theorem round_step (ctx : ProtocolContext) (handle : Nat) (value : List F × F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (((GkrVerifier.round ctx handle value).interpret CommonAdapter.embed).interpret Occurrence.actions)
      history price := by
  simp only [GkrVerifier.round,GkrVerifier.roundFirst,GkrVerifier.roundSecond,PIR.Process.interpret,
    CommonAdapter.embed,Occurrence.actions,PIR.Process.bind,Typed.ChargedCostBound,PublicProperties.interface]
  intro a x dx b y dy c z dz
  unfold GkrVerifier.roundCheck
  split
  · simp only [GkrVerifier.roundChallenge,PIR.Process.interpret,CommonAdapter.embed,
      Occurrence.actions,PIR.Process.bind,Typed.ChargedCostBound,PublicProperties.interface]
    exact ⟨0,by simp,fun _ => trivial⟩
  · trivial

theorem rounds (ctx : ProtocolContext) (site : String) (handle start count : Nat) (value : List F × F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (validatorRounds ctx handle site start count value) history (count * price) := by
  install_source_loop_cost per_iteration price using_rules [round_step ctx handle]

omit [Field F] [DecidableEq F] in
theorem coefficients (ctx : ProtocolContext) (site : String) (start count : Nat) (values : List F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (validatorCoefficients ctx site start count values) history 0 := by
  have step : ∀ (values : List F) reached,
      Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
        (((GkrVerifier.lineCoefficient (G := G) ctx values).interpret CommonAdapter.embed).interpret Occurrence.actions)
        reached 0 := by
    intro values reached payload value decoded
    trivial
  install_source_loop_cost per_iteration 0 using_rules [step]

private theorem line_step (ctx : ProtocolContext) (handle width : Nat)
    (add mul : Zkc.Protocols.Gkr.Wiring F width) (value : Nat × List F × F)
    (left right : List F) (claim first : F) (received : List F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (((GkrVerifier.lineCheck ctx handle width add mul value left right claim first received).interpret
        CommonAdapter.embed).interpret Occurrence.actions) history price := by
  unfold GkrVerifier.lineCheck
  split
  · simp only [GkrVerifier.lineDelivery,PIR.Process.interpret,CommonAdapter.embed,
      Occurrence.actions,PIR.Process.bind,Typed.ChargedCostBound,PublicProperties.interface]
    exact ⟨0,by simp,fun _ => trivial⟩
  · trivial

theorem layer (ctx : ProtocolContext) (sites : HonestProducerObservedLayers.Sites) (handle width : Nat)
    (add mul : Nat → Zkc.Protocols.Gkr.Wiring F width) (value : Nat × List F × F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (validatorLayer ctx handle width sites add mul value) history ((2*width+1)*price) := by
  unfold validatorLayer
  convert CostComposition.bind _ _ (width*price) (width*price+price)
    (rounds _ sites.left handle 0 width _ price history) ?_ using 1
  · ring
  · intro left reached
    apply CostComposition.bind _ _ (width*price) price (rounds _ sites.right handle 0 width _ price reached)
    intro right afterRight
    change ∀ payload first, _ → _
    intro payload first decoded
    simpa only [zero_add, PIR.Process.bind, PIR.Process.interpret] using CostComposition.bind _ _ 0 price
      (coefficients ctx sites.coefficients 0 width [first] price _)
      (fun received beforeLine => line_step ctx handle width (add value.1) (mul value.1)
        value left.1 right.1 right.2 first received price beforeLine)

omit [Field F] [DecidableEq F] in
theorem output (ctx : ProtocolContext) (site : String) (handle start count : Nat) (point : List F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (validatorOutput ctx handle site start count point) history (count*price) := by
  install_source_loop_cost per_iteration price using_rules [output_step ctx handle]

theorem layers (ctx : ProtocolContext) (sites : HonestProducerObserved.Sites) (handle : Nat)
    (encoding : CircuitEncoding F) (start count : Nat) (value : Nat × List F × F)
    (price : ENNReal) (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (validatorLayers ctx handle sites encoding start count value) history
      (count*((2*encoding.width+1)*price)) := by
  install_source_loop_cost per_iteration ((2 * encoding.width + 1) * price)
    using_rules [layer ctx sites.layer handle encoding.width encoding.circuit.add encoding.circuit.mul]

theorem validator (ctx : ProtocolContext) (sites : HonestProducerObserved.Sites) (handle : Nat)
    (encoding : CircuitEncoding F) (outputs : List F) (price : ENNReal)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (HonestProducerObserved.validator ctx handle sites encoding outputs) history
      ((encoding.width+encoding.layers*(2*encoding.width+1))*price) := by
  unfold HonestProducerObserved.validator
  convert CostComposition.bind _ _ (encoding.width*price) (encoding.layers*((2*encoding.width+1)*price))
    (output ctx sites.output handle 0 encoding.width [] price history) ?_ using 1
  · ring
  · intro point reached
    apply (CostComposition.map_iff _ _ _).mpr
    exact layers ctx sites handle encoding 0 encoding.layers _ price reached

end ZkcSecurity.Realizations.Gkr.Budget
