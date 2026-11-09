# Shared program and proof packages

Packages 1 and 2 implement the selected architecture in
`/ethereum/wonjae/archives/zkc/unified-proof-architecture-2026-11-09/`.

The shared package owns the existing generic Region/Process definitions exactly
once. Their existing declaration namespaces are retained during this extraction;
there are no compatibility modules or declaration aliases. Module names express
ownership. Renaming every mathematical declaration is not required to establish
this dependency boundary.

Actual protocol adoption, the construction engine, and the broader family library
migration are outside these two packages. The goal includes full execution and
probability interpretation, Process-facing properties, and local compositional
interfaces and model clients. Work is in progress; no completion is claimed here.
