# Evidence and assurance records

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `evidence`
> **Authority:** None during the transition. Existing status, formalization,
> test, and evaluation records retain their current bounded roles.

## Purpose

`evidence/` owns how exact observations, receipts, comparisons, and
conformance records are bound to subjects and interpreted as deliberately
limited support for claims.

This is a system domain for evidence objects, claim scope, and future
admission-policy language, not a generic document-kind bucket. A domain may
define what behavior must be preserved; evidence defines what a particular
record demonstrates about it.

## Owns

- evidence kinds and record schemas;
- exact subject, revision, issuer, input, environment, and procedure binding;
- provenance, reproduction, and drift information;
- facets and grades for structural, operational, formal, backend, and
  cross-implementation conformance;
- residual trust, exclusions, failures, and unattempted scope;
- formalization receipts and source-reading records as evidence objects;
- execution, benchmark, replay, parity, and conformance records;
- evidence-policy vocabulary, record validity, and future admission machinery;
  and
- the evidence catalog supporting the global status page.

Evidence files may remain beside executable evaluation assets when that keeps
reproduction honest. This domain can index and govern them without forcing all
records into one physical directory.

## Does not own

- intended protocol, relation, judgment, compiler, endpoint, or realization
  semantics;
- theorem truth merely because a source or declaration is cited;
- global current capability claims, which belong to project status;
- concrete release or reliance decisions made by evidence consumers;
- future work order;
- a generic “verified” label spanning unrelated facets; or
- broader conclusions than the record's exact subject and procedure support.

## Dependencies

Evidence depends on the owning domain for the claim being tested. Each record
must identify that semantic authority and the exact subject. It may also depend
on external tools, theorem libraries, hardware, providers, or upstream
implementations, all of which remain attributed and pinned where possible.

No semantic domain depends on the presence of an evidence record for artifact
meaning or identity. A release or admission policy may require evidence, but
that is an explicit consumer policy, not backward semantic authority.

## Consumers and outputs

- global status cites bounded evidence records under its reporting policy;
- maintainers use reproduction and drift results to find conformance gaps;
- decisions may cite evidence without turning observations into semantics;
- users assess claim scope and residual trust; and
- guides link to reproducible procedures rather than restating results.

## Bridge ownership

`evidence/` owns the transition from raw test output, abstract execution result,
attributed operational run, source reading, formal receipt, event log, or
benchmark measurement to an evidence record. The producing domain owns the raw
result and the semantic property being observed. The relying project, user, or
release policy owns the concrete decision to accept that record for a claim.

## Minimum record contract

Every evidence record should state:

```text
claim or facet
exact subject and identity or revision
issuer or recorder
inputs and configuration
environment and external pins
procedure
observed result
covered and uncovered facets
residual trust and non-claims
reproduction path
```

Missing fields narrow or invalidate the claim; they are not filled by
assumption.

## Candidate internal topics

- claim and evidence taxonomy;
- record schema and provenance;
- formalization receipts;
- reference and differential evidence;
- endpoint and backend conformance;
- execution and replay records;
- benchmarks and performance observations;
- future admission, aggregation, and status routing; and
- reproduction and drift checking.

## Open boundary questions

- Should the domain be renamed `assurance/` to avoid collision with evidence as
  a local document kind?
- Which conformance grades are cross-domain evidence concepts and which remain
  domain-specific obligations?
- Can future evidence admission be standardized without implying that an
  accepted record proves its subject universally?
- How should global status derive concise claims from records without creating
  a second manually synchronized evidence inventory?
