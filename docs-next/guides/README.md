# Guides

> **Document kind:** Area index
> **Document state:** Scaffold
> **Provisional owner:** `guides`
> **Authority:** Guides are always non-normative and are not current-status
> authority.

## Purpose

`guides/` owns reader journeys: tutorials, task-oriented workflows, examples,
tool usage, integration guidance, and conceptual introductions that cross one
or more semantic domains.

Guides optimize for learning and successful action. They do not become a
parallel specification because their examples are easier to read.

## Owns

- getting-started and build workflows;
- protocol authoring, sealing, analysis, compilation, projection, realization,
  and execution journeys;
- tool-oriented references where the tool interface is the reader's question;
- worked examples and tutorials;
- concrete integration guides and time-sensitive ecosystem surveys; and
- audience-specific reading paths.

## Does not own

- schemas, identities, judgments, refusals, or boundary contracts;
- current capability or compatibility claims;
- architecture decisions or future work order;
- evidence conclusions; or
- definitions copied from semantic owners.

## Dependencies and consumers

Guides may depend on every domain and on global project status. Each technical
claim links to the current owner. Commands and examples identify the version or
checkout assumptions needed to reproduce them.

Readers, contributors, integrators, and operators consume guides. Semantic
domains do not depend on guide wording.

## Placement rule

Place a page here when its primary organizing principle is an audience goal or
multi-domain task. Place a domain-specific explanatory page beside its owning
domain when its primary purpose is to explain one semantic subject.

Do not create mirrored guide hierarchies under every domain. Use links and a
small number of intentional reader journeys.

## Candidate guide families

- orientation and conceptual model;
- build and development setup;
- author, seal, and inspect a protocol;
- analyze a property judgment;
- run checked protocol compilation;
- project and inspect endpoints;
- emit, deploy, invoke, and reproduce a run;
- understand evidence and claim scope; and
- integrate relation producers, formal systems, proving libraries, and zkVMs.

## Open boundary questions

- Which existing overview material is a project explanation and which is a
  beginner guide?
- Should command reference remain within task guides or become generated tool
  documentation?
- Which ecosystem pages are stable integration guides versus time-sensitive
  surveys that need explicit freshness metadata?
