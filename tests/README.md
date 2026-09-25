# Tests

The C++, Rust and Lean builds are independent. Cross-language tests live here
because no single build owns their comparisons. Each selects the compiler,
runtime and reference tools needed for its contract. `harness/` checks the
testing and development machinery without needing compiled project tools;
`groth16/tests/` checks the fixture reproducer itself.

```sh
just test            # all main suites, including resource-boundary cases
just test-harness    # command wiring, configuration and reporting controls
just test-cross      # all pytest cases here, including harness controls
just test-compiler   # the CTest suite, which needs no other build
just test-install    # a separate project built against the installed package
just test-groth16 W  # snarkjs interoperability against a generated workdir
just test-bench      # correctness controls in the separate benchmark workspaces
```

A test never looks inside another build's directory. It names the tool it needs
and `support/toolchain.py` resolves it, so no invocation carries an executable
path and none can supply the wrong Lean reference. That is what lets one command
run the cross-language cases. A missing required tool fails the selected test.
Optional integrations have explicit entry points; they are not implied by a
successful main-suite run.

## Selecting checks

Start with the changed contract's tests and relevant lint. For tooling-only
changes, `just test-harness` needs no project builds; documentation-only changes
use `just test-docs`. With the required tools already built, narrower selections
are available directly:

```sh
uv run --no-sync --locked pytest tests/harness/test_doctor.py
ctest --test-dir build/compiler -R '^selector-ownership$' --output-on-failure
cargo test -p zkc-runtime --lib --all-features
```

Rebuild affected tools before testing their behavior. Pytest accepts a file,
`::test_name` or `-k` selection; CTest accepts a test-name regex; Cargo accepts a
package, test target and name filter. Lean modules can be rebuilt individually
with `lake build Module.Name` from `formal/`.

Broaden verification when the change crosses a boundary, a failure exposes a
wider issue, or a release needs integration evidence. `just test` includes
expensive resource-boundary cases; `test-cross` and `test-rust` also build all
three components first. Cold Nix builds, benchmark correctness suites and
optional upstream integrations are separate decisions, not routine additions
after focused checks pass. Reuse unchanged validation evidence and record its
source revision rather than repeating it after unrelated edits.

## Execution owners

| Surface | Execution owner | Scope |
|---|---|---|
| `tests/**/test_*.py` | pytest, through `just test-cross` | Cross-language regressions, harness controls and Groth16 reproducer unit controls |
| `tests/harness/` | `just test-harness` | Fast checks without C++, Rust or Lean project builds; also included by normal pytest discovery |
| `compiler/test/*.cpp` and `*.py` | CTest, through `just test-compiler [profile]` | Native API and compiler process contracts; the requirements helper is driven by Python |
| Root Cargo workspace | `just test-rust` | Rust unit/integration/example controls, all features enabled |
| `formal/Tests/` | Lake, through `just build-lean` | Compiled examples, proof obligations, guards and executable assertions |
| `formal/checks/` and `formal/consumers/` | `just test-lean` | Package audits, CLI controls and independently built consumers |
| Ordered artifact drivers | `just test-artifact` | Generated fixtures followed by host/reference/differential/baseline comparisons |
| Installed CMake SDK | `just test-install` | Independent consumer configuration, linking and execution |
| Separate benchmark Cargo workspaces | `just test-bench` | Correctness tests; measurement commands remain `just bench` |
| Optional external integrations | `just test-groth16 W`, `just test-lean-integration`, `nix build .#llzk` | Explicit fixture/dependency/toolchain requirements |
| Sanitizers and source reconstruction | `just test-sanitize`, `just test-lean-fresh` | Separate validation modes, not substitutes for ordinary tests |

`tests/run.py` executes selected scopes against existing outputs. Just adds the
build prerequisites for ordinary developer commands; direct driver calls do
not build them. Pytest uses strict configuration/marker validation and the
main scope has no implicit `slow` exclusion. It includes expensive cases and
is not a promise of quick CI. Resource requirements are in the
[development guide](../docs/development/README.md).

The three Rust Groth16 cases marked `ignore` require reproduced fixtures and
are explicitly included by `just test-groth16 W`. The optional historical Lean
identity replay is included only when `--baseline` names a preserved executable;
a missing or nonexecutable explicit path is an error. Ordinary handwritten
identity controls still run independently of that snapshot.

`just test-docs` runs [check_docs.py](check_docs.py) over reference, root/formal
and component guides. Its scope and limits
are described in the [documentation guide](../docs/development/documentation.md).

Within `nix flake check`, the style check owns Python lint and documentation
validation; the project check owns the integration scopes. This avoids running
the same lint and documentation checks twice in separate derivations.

## Organization and evidence

A test sits under the thing it constrains, not under the mechanism it uses.

| Directory | What it constrains |
|---|---|
| `execution/` | What a source computes: regions, storage backends, tables, the vector service, structured local control and the local vocabulary |
| `admission/` | What admission refuses, by phase and at an endpoint, and where the two implementations disagree |
| `physical/` | A physical plan against the Lean producer it is compared with, and what physical admission rejects |
| `protocol/` | An authored protocol: composition, the frontend, relation authoring, capacity, generic correspondence, polynomial domains, storage release, callable expansion and requirement certificates |
| `kernels/` | The numerical, oracle and matrix kernels, extension fields and vector scatter |
| `identity/` | What an identity encodes, against handwritten expected trees |
| `artifact/` | What a compiled artifact proves, compared against the independent reference |
| `harness/` | Tool and report selection, command forwarding, suite discovery, subprocess failures and grouped-case reporting |
| `support/` | The vocabulary these tests share with each other and with the compiler's own tests: tool resolution, what a test does to a tool and keeps of it, the Lean reference driver, source and explicit-binding construction, the canonical matrix wire encoder, and the cases and candidates two implementations are compared on |
| [`fixtures/`](fixtures/README.md) | Shared inputs and expected results; the fixture guide maps their consumers and update rules |
| `consumer/` | A small CMake project that builds against the installed compiler package, so the exported package is checked and not only produced |
| `groth16/` | The Circom and snarkjs fixture generator, its pinned pipeline and the preserved known-answer vectors |

A test names the tool it needs and states what it requires of it through
`support/journal.py`: `run` for a step that must succeed or refuse for a named
reason, `attempt` and `check` for a step it is judging and wants to keep looking
past. `tests/run.py` allocates an exclusive directory under
`build/reports/runs/` (or the selected `ZKC_REPORTS_DIR`), prints its path,
and passes it to the scope's children through that same setting. `run.json`
records the scope's running, passing, failed or interrupted state. JUnit output
and command evidence belong to that run. Direct pytest and compiler Python
tests also allocate exclusive case directories under the selected root's
`tests/`; full test identities distinguish identical basenames and parameter
labels. Repeated and parallel invocations retain separate evidence. This does
not isolate native build directories or dependency stores: serialize builds of
the same profile/package, or use separate checkouts and output directories.

A subprocess terminated by a signal is a failure, even when its earlier output
contains the expected refusal code. Named refusals require both the diagnostic
and a positive failure exit status. Timeout records retain partial output and
diagnostics. Completed command records are appended without rewriting the
entire history on every invocation. Records include the working directory and
the selected timeout. Spawn failures, timeouts, interruptions and caller aborts
remain distinct from domain exits.

[`scripts/processes.py`](../scripts/processes.py) owns process lifecycle; callers
own execution budgets. Journal defaults to 120 seconds per command. Artifact
drivers accept `--timeout`; the resource-limit driver keeps its 180-second
default. The artifact-reference driver's multi-step reference subprocess has
a separate `--reference-timeout` (900 seconds), while the reference's own leaf
calls retain Journal's budget. These are limits, not performance measurements.
Build and whole-suite commands have no blanket Journal timeout.

On POSIX, cancellation forwards the initiating signal to the owned process
group. Ctrl-C therefore gives children SIGINT first, followed by SIGTERM and
SIGKILL if they do not exit. Timeouts start with SIGTERM. Each stage has its own
grace period. Journal allows one second; the
development and suite wrappers allow five seconds for nested runners to finish
their cleanup. The intermediate artifact-reference driver allows three seconds
when running its Python reference subprocess. The direct child is waited for,
and partial captured output is
retained. CTest writes `ctest.xml` under its unique run directory; interrupted
pytest runs retain their completed-test JUnit entries and summary when the
child can finish its interrupt handler. Descendants that deliberately detach from that group, supervisor
SIGKILL, and Windows process-tree cleanup are outside this contract. Compiler
and proof results are not inferred from cancellation output.

Artifact drivers require a new output directory and refuse an existing one,
including an empty directory. Give each differential shard its own output.
Normal test commands do not delete old reports. `just clean-reports` is an
explicit removal operation; use it only when no run is writing that root.

Keep independent expected values and independent implementations. A C++ parser
control, a Rust runtime control and a Lean correspondence comparison may use
the same source while enforcing different obligations. Share fixture builders
and execution plumbing where appropriate; do not replace those checks with
one comparison that all consumers can get wrong together. Fixture files with
the same bytes may still represent distinct named cases.

Differential comparison is the evidence these tests supply: the same admitted
source, run by an executable Lean reference and by the native path, must agree on
the complete outcome, the residual state, the selected observations and the
failure behavior. That is finite evidence about the implemented subset, not a
correspondence theorem.
