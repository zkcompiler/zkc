import M0

/-!
Axiom closure report. `run.py` elaborates this file with `lake env lean
Axioms.lean` after the library is built and parses the `#print axioms`
messages; the frozen findings require every statement below to rest on the
standard Lean axioms at most (`propext`, `Classical.choice`, `Quot.sound`)
and never on `sorryAx`.
-/

#print axioms M0.decode_encode
#print axioms M0.parse_canonical
#print axioms M0.decode_canonical
#print axioms M0.encode_injective
#print axioms M0.encode_prefix_free
#print axioms M0.encodeChecked_injective
#print axioms M0.Join_cons
#print axioms M0.PCClass.join_assoc
#print axioms M0.PCClass.join_comm
#print axioms M0.PCClass.join_idem
#print axioms M0.PCClass.join_invalid_left
#print axioms M0.PCClass.join_invalid_right
#print axioms M0.PCClass.join_staticPublic_left
#print axioms M0.Publish_idem
#print axioms M0.class_fold_topological_order_independent
#print axioms M0.magnitude_eq_quadratic
#print axioms M0.evaluation_deterministic
#print axioms M0.evaluation_completed_mono
#print axioms M0.schnorr_denotation_eq_closed_form
#print axioms M0.attemptedWhenever_sound
#print axioms M0.mustEnv_sound_evalCore
#print axioms M0.must_when_true_sound
#print axioms M0.must_when_false_sound
#print axioms M0.impossible_when_true_cannot_evaluate_true
#print axioms M0.impossible_when_false_cannot_evaluate_false
#print axioms M0.terminalContractDecision_correct
