# zkc formal library

This optional Lean package contains independent semantic models and proofs.
It does not establish correspondence with native `.zkc`, MLIR or Rust execution.
The [formal reference](docs/README.md) owns model documentation;
[support](docs/support.md) records exact theorem scope and premises.

## Use

The main Lake package depends on pinned Mathlib. `import Zkc` exposes the small
execution, interaction, contract and observation foundation; use narrow imports
for other capabilities. The [architecture](docs/architecture.md) describes areas
and dependencies, and [support](docs/support.md) locates APIs by their claims.

External-dependent proofs live in the optional [ArkLib package](integrations/arklib/README.md).
Main-library imports never require that package or its build objects.
[Downstream clients](clients) demonstrate use from a separate Lake package.
The model-specific [artifact](docs/design/artifact-reference.md) and
[interactive](docs/design/interactive-reference.md) tools have their own admitted
formats and proof boundaries; they do not accept native programs as formal proofs.

## Build and validate

The [toolchain](lean-toolchain) pins Lean; the [manifest](lake-manifest.json)
pins the main dependency closure.
The [Nix environment](../docs/development/README.md) supplies that exact toolchain and
can build both packages from source in a network-isolated build phase:

```sh
nix build .#formal
nix build '.#formal^library'  # sources and compiled library objects
nix build .#arklib          # optional package and standalone consumer checks
```

For interactive development inside `nix develop .#formal`, prepare the pinned
dependencies and use the optional Lake recipes:

```sh
just fetch-lean          # prepare the main package's pinned dependencies
just build-lean          # lake build: every library and executable the package declares
just test-lean           # the structural, tool and consumer checks over it
just test-lean-integration   # the optional ArkLib package and its consumers
```

What `lake build` builds is `lakefile.toml`'s default targets, and
`test_checks.py` fails if a declared library or executable is not one of them,
so neither this page nor a workflow keeps its own list. What `just test-lean`
runs is discovered by [the shared test driver](../tests/run.py) from
`checks/*.py` and `consumers/*/check.py`, with fixture-helper controls supplied
by the driver. The recipe builds the formal prerequisites before running it.

Build the optional library separately from `formal/integrations/arklib` with
`lake build`. The main build checks every maintained library/test/example module;
public root imports do not determine audit coverage. The declaration audit
inspects types and proof/definition bodies, including private and generated
versions, and permits only `propext`, `Classical.choice` and `Quot.sound`.
The independent `Tools.Interactive` and `Tools.Artifact` consumers, including their
`Tools.Crypto` dependencies, are included explicitly in the declaration audit and
compiled as `interactive-protocol` and `artifact-reference`. The crypto modules
provide bounded, independent Keccak/Merkle reference computations.
The importable [requirement-certificate transport](Tools/RequirementChecker/Transport.lean)
is also audited; its separate `requirement-checker` wrapper owns the process entry.
Other tool IO wrappers
are compiled separately. These checks do not certify Lean's
kernel, its native code generator or the adequacy of a theorem's statement.
The maintained tool controls include isolated forbidden-axiom, import-header,
input-capacity and executable-selection regressions. The
[build workflow](../.github/workflows/ci.yml) runs documentation and source/harness
checks automatically on pull requests and pushes to main. Formal builds, audits,
consumers and tool controls belong to its manual optional package checks;
the `fresh` scope reproduces both formal packages without a restored project
cache. See [workflow scopes and reports](../docs/development/maintenance.md#workflow-scopes-and-reports)
for orchestration boundaries.
Passing quick checks does not establish any of these formal results, and a
workflow definition is not evidence of a hosted run.

For fresh builds, run from `formal/` and choose new output directories:

```sh
python3 checks/check_foundation.py --output /tmp/zkc-foundation
python3 reproduce.py --dependency-cache .lake/packages --output /tmp/zkc-main
python3 reproduce.py --with-arklib --dependency-cache .lake/packages \
  --integration-dependency-cache integrations/arklib/.lake/packages \
  --output /tmp/zkc-with-arklib
```

The copied foundation builds without external package imports or prior objects.
The command first parses headers in the configured root Lake environment, so
the invoking checkout still needs its declared package resolution. The full
reproducer copies current build inputs and materializes exact Git sources
without their Lean objects. It builds declared targets, audits
dependencies/axioms, and builds standalone clients.
Omit cache options to fetch the manifest URLs. The installed Lean/Std toolchain
remains trusted. Source drift causes failure; historical snapshots are not inputs.

The [original-source artifact reference](docs/design/artifact-reference.md) explains
`Tools.Artifact` and its explicit public cryptographic reply assumptions.
Executable consumers and framing lemmas have separate assurance
scopes; neither imports an implicit Fiat–Shamir security theorem.


## Development

[Design choices](docs/README.md#design-and-tools) explain the model's adopted
structure. [Correspondence maps](docs/README.md#definitions-and-proofs) identify
prose clauses, Lean declarations and remaining obligations. The
[native connection boundary](docs/native-connection.md) states the distinction
between these laws and a future implementation claim.
