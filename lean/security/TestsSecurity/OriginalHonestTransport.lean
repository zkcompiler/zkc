module

import ZkcSecurity.FiatShamir.OriginalReadback

/-! Controls at the original/readback seam. Existing InterleavedReadback tests
cover unequal query histories/origins and missing typed replies; existing
OriginalProducerBinding tests cover unequal nominal delivery origins. -/
set_option autoImplicit false
namespace TestsSecurity.OriginalHonestTransport
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir

variable {carriers : Structured.Carriers} {A B C D : Type}

/-- Independent simulations can change both return types and insert distinct
physical frames. The conclusion still retains both complete return relations. -/
theorem full_returns_at_exact_checkpoints (Post : A → B → Prop)
    (returnsP : A → C → Prop) (returnsV : B → D → Prop)
    (a : A) (b : B) (c : C) (d : D) (post : Post a b)
    (returnedP : returnsP a c) (returnedV : returnsV b d)
    (producerFrame validatorFrame : Domain.Environment carriers) :
    Readback (fun targetP targetV => ∃ sourceP sourceV,
      Post sourceP sourceV ∧ returnsP sourceP targetP ∧ returnsV sourceV targetV)
      (.call (.checkpoint producerFrame) (fun _ => .done c))
      (.call (.checkpoint validatorFrame) (fun _ => .done d)) :=
  Readback.original
    (liveP := fun _ _ => True) (liveV := fun _ _ => True)
    (.checkpoint producerFrame trivial (.done returnedP))
    (.checkpoint validatorFrame trivial (.done returnedV)) (.done post)

/-- A physical checkpoint cannot conceal an added false guard after a
successfully returning original producer, for any proposed return relation. -/
theorem false_guard_after_checkpoint (returns : A → C → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop)
    (value : A) (frame : Domain.Environment carriers) :
    ¬ Nonempty (Original.Simulation returns live (.done value)
      (.call (.checkpoint frame) (fun _ => .halt .refused))) := by
  rintro ⟨simulation⟩
  generalize continuationEq : (fun _ : Unit =>
    (PIR.Process.halt .refused : PIR.Process (Domain.effects carriers) C)) = continuation at simulation
  cases simulation with
  | checkpoint frame related next =>
    have stopped := congrFun continuationEq ()
    cases stopped
    cases next

/-- Matching source/target refusal certificates are valid simulations, but
their matching stops cannot provide the successful-source readback premise. -/
theorem matching_refusals_do_not_complete (Post : A → B → Prop) :
    ¬ Readback (carriers := carriers) Post (.halt .refused) (.halt .refused) := by
  intro aligned
  cases aligned

#print axioms Readback.original_left
#print axioms Readback.original_right
#print axioms Readback.original
#print axioms full_returns_at_exact_checkpoints
#print axioms false_guard_after_checkpoint
#print axioms matching_refusals_do_not_complete

end TestsSecurity.OriginalHonestTransport
