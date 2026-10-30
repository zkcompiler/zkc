import ZkcSecurity.Transformations.Commitment.Soundness
import ZkcSecurity.Transformations.Commitment.Merkle
import ZkcSecurity.Transformations.Commitment.HashedLeaves
import ZkcSecurityExamples.CommittedOpeningBound
import ZkcSecurity.Transformations.Commitment.Opening
import ZkcArkLibExamples.CommittedFri
import ZkcTools.DeclarationAudit

/-! Axiom closures of the commitment bridge: every declaration of its modules, including
the theorems below, passes the declaration audit.

* `ZkcSecurity.Commitment.soundness_weighted` and `soundness`: a verifier with committed tables,
  read concretely with roots and authenticated openings in the joint random-oracle experiment,
  accepts a false statement with probability at most the charges of a typed certificate of its
  ideal reading plus one charge per hash call.
* `ZkcSecurity.Commitment.MerkleTrees.scheme` and `LeafHashing.scheme`: Merkle trees with raw
  leaves (VCVio's extractor) and with hashed leaves satisfy the two laws of an extractable table
  commitment.
* `ZkcSecurity.Examples.CommittedOpening.intendedBound`: the intended bound of the committed-opening
  experiment holds for the straight-line extractor.
* `ZkcSecurity.Examples.CommittedOpeningBridge.soundness`: the general theorem applies to the
  smallest committed-table verifier, with all of its premises discharged.
* `ZkcSecurity.Commitment.run_costBound` and `run_queryBound`: the concrete reading of a verifier
  with committed tables inherits a bound charged on the verifier's paths.
* `ZkcSecurity.Examples.CommittedFri.soundness`: `fri::LowDegree` with committed words, whose
  ideal reading is the verifier with every word in the clear (`withTables_verifier`).
-/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcSecurity.Transformations.Commitment, `ZkcSecurityExamples.CommittedOpening,
     `ZkcSecurityExamples.CommittedOpeningBound, `ZkcSecurity.Transformations.Commitment.Opening,
     `ZkcArkLibExamples.CommittedFri]
    "COMMITMENT-BRIDGE-AUDIT-PASS"
