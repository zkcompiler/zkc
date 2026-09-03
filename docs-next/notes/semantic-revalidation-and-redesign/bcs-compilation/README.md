# BCS-style compilation of oracle proofs: entry contract

> **Kind:** entry contract (design program, prerequisite for the
> kernel-scope decision the peer review named)
> **State:** Drafted 2026-09-03; no lane has run it; nothing selected.
> **Authority:** None.

## 1. The question

An interactive oracle proof becomes a succinct argument by committing every
oracle string with a vector commitment, answering the verifier's queries with
openings, and fixing the challenges by Fiat--Shamir. The peer review asked how
that compilation enters the kernel: as a construction the kernel owns, as a
composition of things it already owns, or as something outside it. The
kernel already owns the parts: an Oracle with `PublicBinding` publication
(the commitment-opening profile), Query and Answer occurrences, the
canonical-framed Fiat--Shamir construction, and a Compiler whose transitions
are checked changes that re-admit their result under a new identity. The
question is whether their composition is the compilation, exactly, and what
a theorem about the compilation binds to.

## 2. The lane's deliverables

1. **One finite oracle-proof-shaped Core.** A two-round folding protocol in
   the retained fixtures' style: the Prover publishes two `LogicalAccess`
   Oracles, the Verifier draws two Fresh challenges and queries each Oracle at
   challenge-derived indices, one Check consumes the answers, and the
   terminals follow the migrated Terminal contract. Admit it and issue its six
   views.
2. **The commitment step as a transition.** Elaborate every `LogicalAccess`
   Oracle into a `PublicBinding` Oracle under the commitment-opening profile
   with the Query and Answer occurrences becoming opening occurrences, using
   the indexed-core elaboration the repository already carries where it
   applies; admit the result as a new Core with a new identity; record the
   exact change as a Compiler transition with its re-admission, and show that
   the source Core's views and the target Core's views relate by the exact
   map the transition declares.
3. **The Fiat--Shamir step.** Form the canonical-framed construction over the
   target Core and check it with the existing same-Core construction checker;
   record the transcript declaration, required-influence, and
   challenge-transition views.
4. **Identity and cone.** Measure what rotates at each step and confirm that
   nothing in the Interaction kernel changes: the compilation is a composition
   of admitted subjects and transitions, not a new constructor.
5. **Theorem coordinates.** For a BCS-style soundness statement (state
   restoration or round-by-round soundness of the oracle proof, binding of the
   commitment, the Fiat--Shamir transform's loss), write down the exact
   coordinates an applicability judgment would carry under the named-premise
   intake: which premise binds to which owner coordinate, at which step, and
   which premises the family transport profile owns.
6. **Verdict.** Fits (the composition is the compilation and every theorem
   premise has a coordinate), bends (a named reopening condition is needed),
   or breaks (a named boundary), with the exact missing coordinate for any
   premise that has none.

## 3. Package and note

`evaluation/bcs-compilation-probe/` with a check, frozen findings, and the
usual registrations; the record is this directory's `README.md`, extended by
the lane with its evidence and its `## Handoff`. Owner pages are not edited;
underdetermined text becomes a `CannotAnswer` finding with a proposed delta.

## 4. Acceptance

`Affirmative` only when steps 1 to 4 close and step 5 assigns a coordinate to
every premise of the chosen statement; otherwise `CannotAnswer` with the list.
An affirmative result establishes that the compilation is expressible as a
composition of admitted subjects; it establishes no soundness, no binding, no
random-oracle property, and no implementation correspondence.

## 5. Order

After the migration text is reviewed, because step 1 uses the migrated
Terminal contract and views; independent of the family-instance decision,
which it does not constrain.
