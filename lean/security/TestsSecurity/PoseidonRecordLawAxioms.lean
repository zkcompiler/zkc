module

public import TestsSecurity.PoseidonRecordLaw

@[expose] public section

/-! Selected transitive axiom checks and complete endpoint types. -/

open ZkcSecurity.Commitment.PoseidonRows.Monitored

#print axioms targets_bound
#print axioms miss_good
#print axioms goodHistory_snoc
#print axioms associate_fresh
#print axioms record_invariant
#print axioms register_invariant
#print axioms run_invariant
#print axioms run_association
#print axioms run_goodHistory
#print axioms run_call_count
#print axioms run_calls_le
#print axioms potential_step
#print axioms bad_probability_le
#print axioms opening_agrees
#print axioms batch_agrees
#print axioms disagreement_implies_bad
#print axioms extraction_disagreement_le
#print axioms randomized_extraction_disagreement_le
#print axioms TestsSecurity.PoseidonRecordLaw.late_capacity_not_good
#print axioms TestsSecurity.PoseidonRecordLaw.nonvacuous_recorded_batch
#print axioms TestsSecurity.PoseidonRecordLaw.actual_mixed_probability

#check @run_association
#check @run_goodHistory
#check @extraction_disagreement_le
#check @randomized_extraction_disagreement_le
