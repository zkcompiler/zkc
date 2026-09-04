# Stage 3 comparative case dossiers

> **Document kind:** Temporary research index
> **Document state:** Completed Stage 3.2 portfolio; absorbed into convergence
> **Authority:** None. A dossier supplies evidence and design pressure; it does
> not select the Stage 3 semantic model, canonical PIR schema, or relation
> ontology.
> **Disposition:** Preserve only reviewed conclusions and primary-source
> rationale in the final Stage 3 convergence record, then delete this directory
> before `docs-next/` authority cutover.

## Purpose

This directory studies mature systems at the exact seams relevant to Stage 3:
semantic subject, closed schema, carrier encoding, validation, identity,
versioning, composition, and interface ownership. The portfolio is selected by
design pressure rather than ecosystem coverage.

Each dossier must:

1. use primary specifications, official documentation, papers, or source
   repositories;
2. distinguish source fact from design inference and zkc transfer hypothesis;
3. describe both a system's strengths and its difficult-to-reverse choices;
4. state the installed constraints that made those choices rational;
5. identify where the analogy to interactive zero-knowledge Protocols ends;
   and
6. produce constraints or falsifiers for equal-resolution Stage 3 candidates,
   not a precedent to copy.

## Portfolio

| Dossier | Systems and pressure | State |
|---|---|---|
| [IR carrier and schema contracts](ir-carrier-and-schema.md) | MLIR, StableHLO/VHLO, SPIR-V, WebAssembly Core and Component Model, and zkInterface: semantic authority, closed schema, validation, physical canonicality, versioning, composition, and interface separation | Complete |
| [Protocol theory](protocol-theory.md) | Interactive protocols, IOPs, Fiat--Shamir, transcripts, relation separation, and three meanings of composition | Complete |
| [Formal protocols and composition](formal-protocols-and-composition.md) | Sigma protocols, IOP composition, UC, SSProve, VCVio, and ArkLib: typed interfaces, denotation, maps, theorem premises, and non-transferable models | Complete |
| [ZK systems](zk-systems.md) | zkInterface, Noir ACIR/Brillig, Halo 2, Marlin, STARK/AIR and Winterfell, Plonky3, Nova, and HyperNova: layer boundaries, transcripts, plans, relation grounding, recursion, and path-dependent choices | Complete |

The portfolio is closed for Stage 3.2. A question that can be answered by an
existing dossier should extend that dossier rather than create a duplicate
ecosystem survey.
