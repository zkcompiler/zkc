module

public import TestsSecurity.PoseidonRows

@[expose] public section

/-! # Selected deterministic adapter axiom evidence

This checks only the listed roots and their imported proof dependencies. It is not a package
declaration audit, probability proof, native refinement check, or source security receipt.
-/

#print axioms ZkcSecurity.Commitment.PoseidonRows.normalize_repeat
#print axioms ZkcSecurity.Commitment.PoseidonRows.normalize_prefix
#print axioms ZkcSecurity.Commitment.PoseidonRows.normalize_pairwise
#print axioms ZkcSecurity.Commitment.PoseidonRows.Good.capacity_forward
#print axioms ZkcSecurity.Commitment.PoseidonRows.Good.parent_forward
#print axioms ZkcSecurity.Commitment.PoseidonRows.SpongeTrace.recover
#print axioms ZkcSecurity.Commitment.PoseidonRows.recover_sound
#print axioms ZkcSecurity.Commitment.PoseidonRows.SpongeTrace.evaluates
#print axioms ZkcSecurity.Commitment.PoseidonRows.decoder_consistent
#print axioms ZkcSecurity.Commitment.PoseidonRows.macroLog_append
#print axioms ZkcSecurity.Commitment.PoseidonRows.extract_stable
#print axioms ZkcSecurity.Commitment.PoseidonRows.raw_opening_agrees
#print axioms ZkcSecurity.Commitment.PoseidonRows.raw_batch_agrees
#print axioms ZkcSecurity.Commitment.PoseidonRows.directExtract_eq
#print axioms ZkcSecurity.Commitment.PoseidonRows.directCheckpoint_frozen
#print axioms ZkcSecurity.Commitment.PoseidonRows.directCheckpoint_update
#print axioms ZkcSecurity.Commitment.PoseidonRows.direct_checkpoint_opening_agrees
#print axioms ZkcSecurity.Commitment.PoseidonRows.checkpoint_batch_agrees
#print axioms ZkcSecurity.Commitment.PoseidonRows.width_eight_alias
#print axioms ZkcSecurity.Commitment.PoseidonRows.flatten_overwrite
#print axioms TestsSecurity.PoseidonRows.multiblock_nine
#print axioms TestsSecurity.PoseidonRows.multiblock_sixteen
#print axioms TestsSecurity.PoseidonRows.public_permutation_outside_log

#check @ZkcSecurity.Commitment.PoseidonRows.direct_checkpoint_opening_agrees
#check @ZkcSecurity.Commitment.PoseidonRows.checkpoint_batch_agrees
#check @ZkcSecurity.Commitment.PoseidonRows.SpongeTrace.evaluates
