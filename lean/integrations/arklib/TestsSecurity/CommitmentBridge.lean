import ZkcSecurity.Commitment.Soundness
import ZkcSecurity.Commitment.Merkle
import ZkcSecurity.Commitment.HashedLeaves
import ZkcSecurity.Examples.CommittedOpeningBound

/-! Axiom closures of the commitment bridge.

* `ZkcSecurity.Commitment.soundness_weighted` and `soundness`: a verifier with committed tables,
  read concretely with roots and authenticated openings in the joint random-oracle experiment,
  accepts a false statement with probability at most the charges of a typed certificate of its
  ideal reading plus one charge per hash call.
* `ZkcSecurity.Commitment.MerkleTrees.scheme` and `LeafHashing.scheme`: Merkle trees with raw
  leaves (VCVio's extractor) and with hashed leaves satisfy the two laws of an extractable table
  commitment.
* `ZkcSecurity.Examples.CommittedOpening.intendedBound`: the intended bound of the committed-opening
  experiment holds for the straight-line extractor.
-/

#print axioms ZkcSecurity.Commitment.soundness_weighted
#print axioms ZkcSecurity.Commitment.soundness
#print axioms ZkcSecurity.Commitment.trace
#print axioms ZkcSecurity.Commitment.runTable_escape
#print axioms ZkcSecurity.Commitment.run_table
#print axioms ZkcSecurity.Commitment.bad_transcript_resample
#print axioms ZkcSecurity.Commitment.bad_hash_resample
#print axioms ZkcSecurity.Commitment.extract_checkpoint_eq
#print axioms ZkcSecurity.Commitment.responseInjective_of_good
#print axioms ZkcSecurity.Commitment.good_of_forall_not_bad
#print axioms ZkcSecurity.Commitment.beforeFirst_update
#print axioms ZkcSecurity.Commitment.run_simulateQ_withLogging
#print axioms ZkcSecurity.Commitment.MerkleTrees.opening_agrees
#print axioms ZkcSecurity.Commitment.MerkleTrees.extract_append
#print axioms ZkcSecurity.Commitment.LeafHashing.opening_agrees
#print axioms ZkcSecurity.Commitment.LeafHashing.extract_append_changed
#print axioms ZkcSecurity.Commitment.LeafHashing.extractLabel_of_climbs
#print axioms ZkcSecurity.Examples.CommittedOpening.intendedBound
#print axioms ZkcSecurity.Examples.CommittedOpening.trace
