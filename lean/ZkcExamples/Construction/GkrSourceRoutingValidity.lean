module
public import ZkcExamples.Construction.GkrSourceRoutingData
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace ZkcExamples.Construction.GkrSourceRouting
open Zkc.Source Zkc.Source.Structured Zkc.Construction

theorem template0_valid : SourceOccurrences.valid snapshot context template0 = true := by decide +kernel

theorem template1_valid : SourceOccurrences.valid snapshot context template1 = true := by decide +kernel

theorem template2_valid : SourceOccurrences.valid snapshot context template2 = true := by decide +kernel

theorem template3_valid : SourceOccurrences.valid snapshot context template3 = true := by decide +kernel

theorem template4_valid : SourceOccurrences.valid snapshot context template4 = true := by decide +kernel

theorem template5_valid : SourceOccurrences.valid snapshot context template5 = true := by decide +kernel

theorem template6_valid : SourceOccurrences.valid snapshot context template6 = true := by decide +kernel

theorem template7_valid : SourceOccurrences.valid snapshot context template7 = true := by decide +kernel

theorem template8_valid : SourceOccurrences.valid snapshot context template8 = true := by decide +kernel

theorem template9_valid : SourceOccurrences.valid snapshot context template9 = true := by decide +kernel

theorem template10_valid : SourceOccurrences.valid snapshot context template10 = true := by decide +kernel

theorem template11_valid : SourceOccurrences.valid snapshot context template11 = true := by decide +kernel

theorem template12_valid : SourceOccurrences.valid snapshot context template12 = true := by decide +kernel

theorem template13_valid : SourceOccurrences.valid snapshot context template13 = true := by decide +kernel

theorem template14_valid : SourceOccurrences.valid snapshot context template14 = true := by decide +kernel

theorem template15_valid : SourceOccurrences.valid snapshot context template15 = true := by decide +kernel

theorem delivery0_valid : SourceDelivery.checked snapshot context template0 template1 = true := by decide +kernel

theorem delivery1_valid : SourceDelivery.checked snapshot context template5 template6 = true := by decide +kernel

theorem delivery2_valid : SourceDelivery.checked snapshot context template10 template11 = true := by decide +kernel

theorem delivery3_valid : SourceDelivery.checked snapshot context template14 template15 = true := by decide +kernel

theorem templates_valid : ∀ template ∈ templates, SourceOccurrences.valid snapshot context template = true := by
  intro template member
  simp only [templates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | member | member | member | member | member | member | member | member | member | member | member | member | member | member | member
  · subst template; exact template0_valid
  · subst template; exact template1_valid
  · subst template; exact template2_valid
  · subst template; exact template3_valid
  · subst template; exact template4_valid
  · subst template; exact template5_valid
  · subst template; exact template6_valid
  · subst template; exact template7_valid
  · subst template; exact template8_valid
  · subst template; exact template9_valid
  · subst template; exact template10_valid
  · subst template; exact template11_valid
  · subst template; exact template12_valid
  · subst template; exact template13_valid
  · subst template; exact template14_valid
  · subst template; exact template15_valid


theorem deliveries_valid : ∀ candidate ∈ deliveries,
    Original.deliveryValid snapshot context candidate.draw candidate.message = true := by
  intro candidate member
  simp only [deliveries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | member | member | member
  · subst candidate; exact delivery0_valid
  · subst candidate; exact delivery1_valid
  · subst candidate; exact delivery2_valid
  · subst candidate; exact delivery3_valid

theorem delivery_candidates (site : String) :
    deliveries.filter (fun candidate =>
      Original.deliveryValid snapshot context candidate.draw candidate.message &&
        candidate.message.qualify (candidate.message.event[2]?.getD "") == site &&
        context.draws.contains (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), site)) =
    deliveries.filter (fun candidate =>
        candidate.message.qualify (candidate.message.event[2]?.getD "") == site &&
        context.draws.contains (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), site)) := by
  apply List.filter_congr
  intro candidate member
  simp only [deliveries_valid candidate member, Bool.true_and]

theorem output_delivery_candidates :
    deliveries.filter (fun candidate =>
        candidate.message.qualify (candidate.message.event[2]?.getD "") == "label_6f75747075745f64656c6976657279_0" &&
        context.draws.contains (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), "label_6f75747075745f64656c6976657279_0")) =
    [⟨template0, template1⟩] := by cbv

theorem left_delivery_candidates :
    deliveries.filter (fun candidate =>
        candidate.message.qualify (candidate.message.event[2]?.getD "") == "apply_14_label_6c656674_label_64656c6976657279_0" &&
        context.draws.contains (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), "apply_14_label_6c656674_label_64656c6976657279_0")) =
    [⟨template5, template6⟩] := by cbv

theorem right_delivery_candidates :
    deliveries.filter (fun candidate =>
        candidate.message.qualify (candidate.message.event[2]?.getD "") == "apply_16_label_7269676874_label_64656c6976657279_0" &&
        context.draws.contains (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), "apply_16_label_7269676874_label_64656c6976657279_0")) =
    [⟨template10, template11⟩] := by cbv

theorem line_delivery_candidates :
    deliveries.filter (fun candidate =>
        candidate.message.qualify (candidate.message.event[2]?.getD "") == "label_6c696e655f64656c6976657279_0" &&
        context.draws.contains (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), "label_6c696e655f64656c6976657279_0")) =
    [⟨template14, template15⟩] := by cbv

theorem round_delivery_candidates (side : Side) :
    deliveries.filter (fun candidate =>
        candidate.message.qualify (candidate.message.event[2]?.getD "") ==
          ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side) &&
        context.draws.contains (candidate.draw.qualify (candidate.draw.event[2]?.getD ""),
          ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side))) =
    [match side with | .left => ⟨template5, template6⟩ | .right => ⟨template10, template11⟩] := by
  cases side <;> cbv

theorem delivery_labels_unique :
    (!(context.draws.map Prod.fst).Nodup || !(context.draws.map Prod.snd).Nodup) = false := by cbv

end ZkcExamples.Construction.GkrSourceRouting
