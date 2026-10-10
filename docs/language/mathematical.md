# Author mathematical protocols

The `.zkc` language combines total mathematical helpers, ordered local functions,
static libraries and explicit participant messages. It emits Protocol IR
for the existing participant compiler and runtime. The
[source profile](../spec/language/README.md) defines syntax,
permissions, role semantics and bounds. Static protocol composition, managed
randomness, bounded repetition and conditional participant completion are supported.
Relations, specification clauses and explicit run/proof Entries are supported.
The common Host supports authenticated packages, named inputs/results and
independent proof calls through the [CLI and Rust API](../runtime/entries.md).

For a complete small example, read [algebra.zkc](../../compiler/test/fixtures/language/algebra.zkc)
and [transfer.zkc](../../compiler/test/fixtures/language/transfer.zkc). The two
helpers compute different field expressions; P sends their results to V, which
uses its own input component and the values actually received.

From the repository root, using the compiler selected by your build:

```sh
zkc-compile language-check --source-format=zkc --entry=transfer::Demo \
  --module=algebra=compiler/test/fixtures/language/algebra.zkc \
  --module=transfer=compiler/test/fixtures/language/transfer.zkc
```

Use the same options with `language-emit` to print checked original MLIR,
`language-interface` for the selected Entry's named port layout, or
`language-bundle` for the selected run bundle or proof deployment, or
`language-package` for the immutable package containing original, interface,
artifact and compilation options. These Entry commands check source, target
admission and source correspondence. `language-check` also accepts no `--entry`
to check definitions alone; the report identifies that narrower scope.
The application CLI offers `zkc check` with the same behavior and optional
[project inputs](README.md#project-inputs). Module and Asset capture is explicit. `--no-simplify` and `--release-storage` select
existing downstream compiler options for bundle production.

`--asset=NAME=FORMAT=FILE` adds explicitly captured relation data. Supported
formats are `r1cs-json`, `r1cs-binary`, `air-json`, `ring-json` and
`relation-bundle-json`; the compiler validates even unused assets with the
native bounded readers. Capture alone does not attach a relation to a protocol
or add runtime inputs; source names an asset through a relation declaration or
an asset domain.

A bundle uses the existing [native runtime](../runtime/bundles.md). Its entry is
the encoded protocol symbol recorded in the source interface. Runtime inputs
are supplied using the bundle's physical input layout. For the transfer example,
P supplies x and c; V supplies its own c. The
[participant execution control](../../crates/zkc-test-drivers/src/language_native.rs)
also demonstrates direct independent runners, changed receive values and the
existing joint host with independently supplied role inputs.
Use the named Entry Host for application code. The lower-level bundle interface
remains available for direct runtime consumers.

## Select a proof job

[Schnorr source](../../compiler/test/fixtures/language/schnorr.zkc) defines the
participant equations, a discrete-log relation and a target clause. Its Entry
chooses P and V, public inputs, the acceptance result and a transcript suite:

```text
proof Proof = Schnorr<G> {
  prover P;
  verifier V;
  public { base, point };
  accept accepted;
  target knowledge;
  construction fiat_shamir("merlin3.bls12-381.fr64be/0", challenges);
}
```

The compiler finds the actual draws of `challenges` through composition and
repetition. It checks each delivery before constructing participant transcripts.
Use `construction authored;` for an authored noninteractive job. `target` is
optional and adds no execution guard. An Entry alias such as `proof Release = Proof;`
inherits the whole configuration. The [Entry contract](../spec/language/entries.md#entry-jobs)
defines exact selection and refusal rules.

A proof Entry can select `complete result.ready;` for bounded attempts. Setup
slots select application-authorized inputs. The [Entry guide](../runtime/entries.md) owns
package admission, CLI calls, operational defaults and generated Rust bindings.

## Local code and reusable types

```text
module example;
domain Fr = field("bls12-381.fr");

struct Pair<T: Type> { pub left: T, pub right: T }
math fn square<F: Field>(x: F) -> F { return x * x; }
fn choose(x: Fr, go: bool) -> Pair<Fr> {
  let squared = square(x);
  let selected = if go {
    squared
  } else {
    x
  };
  return Pair<Fr>{left: x, right: selected};
}
protocol Transfer roles(P, V)(x: Fr @P, go: bool @P) -> (result: Pair<Fr> @V) {
  let pair = choose(x, go);
  let received = send P -> V(pair);
  return received;
}
run Demo = Transfer;
```

`math fn` describes total algebra. `fn` describes ordered work, including control
and resources. The compiler infers P as the owner of `choose` from its P-only
arguments. The protocol sends its result. The receiver obtains its actual
received components. The record becomes two ordered payload leaves, which the
interface maps back to named fields.

Generic libraries declare the permissions they use. A mathematical parameter
needs `Copy + Drop`; a protocol message also needs `Share + Wire`. A plain `Type`
parameter promises none. These permissions are independent. Components select
interface implementations statically and can seal an associated representation.
Library clients need neither its representation nor a runtime dispatch table.

Blocks use lexical names. `if` and `match` produce their final expression;
`let mut` and whole-name assignment describe changing state. The compiler derives
captures and loop state, including resource checks. For example:

```text
let mut sum: Fr = 0;
for _ in 0..n {
  sum = sum + x;
}
```

Protocol loops additionally spell `roles(P, V) max N`. Protocol calls use ordinary
call syntax, such as `let result = Round(x, coins);`. Declare the service alongside
data inputs, for example `(x: F @V, coins: Random<F> @V)`.
`let alias = coins;` gives the same service another name.
Defined functions infer effects. Write `!{}` only
when an effect-free interface is an intended contract. Ordinary calls can nest;
all calls in one statement must have uniquely determined participants. Use `@P`
on a binding to resolve ambiguity. Later statements never move an earlier call.
`require condition;` rejects at its inferred participant when false; a shared
condition needs an explicit owner, such as `require @V condition;`.
Nonlinear dimension inference and arbitrary inequality solving remain outside
this source profile.

Defined helpers can omit result types. Defined helpers and protocols infer
catalog and natural preconditions when `where` is absent. A written clause is a
complete contract; `where ()` forbids additional preconditions. Resource
permissions stay explicit. For example:

```text
fn first<T: Type + Copy + Drop, N: nat>(xs: [T; N]) {
  return xs[0];
}
fn pairFirst<T: Type + Copy + Drop>(xs: [T; 2]) {
  return first<_, 2>(xs);
}
```

`first` infers result `T` and condition `1 <= N`; the call infers its `_` as `T`.
An explicit result type remains useful for literals and stable library interfaces.

Local code can apply a scalar helper to whole vectors without writing a loop:
`map affine(each low, each high, r)` checks that `low` and `high` have equal
lengths, then computes every row with bulk vector operations. `r` is shared by
all rows. Unequal lengths end execution like a failed vector kernel; `require`
equal lengths first when a protocol should reject such inputs. The [map contract](../spec/language/definitions.md#checked-pointwise-maps)
states the admitted helpers and refusals.

Type information also flows through nested expressions:

```zkc
fn identity<T: Type>(x: T) -> T { return x; }
fn choose<F: Field>(x: F, b: bool) {
  return identity(if b { 0 } else { x });
}
fn samples<F: Field>(x: F) {
  return identity([0, x]);
}
```

`choose` infers result `F`; `samples` infers `[F; 2]`. Reversing the branches or
array elements does not affect type inference. A statement still needs enough
information on its own: write `let zero: F = 0;` when no expression supplies the
field type. A later use of `zero` does not determine that earlier declaration.
Component choices, protocol role remapping and ambiguous owners stay explicit.

The maintained fixtures cover [arrays](../../compiler/test/fixtures/language/array.zkc),
[variants](../../compiler/test/fixtures/language/variant.zkc),
[static components](../../compiler/test/fixtures/language/component.zkc),
[associated domains](../../compiler/test/fixtures/language/associated_domain.zkc),
and [affine control and stop cleanup](../../compiler/test/fixtures/language/resource_control.zkc).
Generic associated types can declare explicit bounds such as
`where Share(G::Scalar), Wire(G::Scalar)`; selecting a group checks those bounds.
Fixed arrays currently use static numeric indices. Private ingress requires a
validator that this source profile does not yet expose. Zero-leaf messages refuse;
empty values and ports still retain their source obligations and interface rows.

The [retained interface](../spec/formats/entry.md) maps logical names and
schemas to original mathematical ports. Physical placement may differ; the
common Host binds the interface to the actual selected artifact.

## Setup-bound inputs

A setup slot associates protocol inputs with application-owned key authority:

```text
proof Proof = Opening<Kzg> {
  setup pcs { vk, pk, commitment };
  prover P;
  verifier V;
  public { vk, commitment, point };
  accept accepted;
  construction authored;
}
```

Selectors may name whole inputs or visible product fields. Every setup-bearing
input belongs to exactly one slot. Each proof slot includes a public verifier key.
A run can use a block containing only `setup` choices.

The application pins `pcs` with `entry::SetupAuthority` and supplies its verifier-key
bytes in each request's `setups` map. The Host initializes `vk`; the application
omits that value from public and role input maps. `pk` uses explicit authenticated
`ProverMaterial` or a pinned key file. Private key/state values do not acquire
message or arbitrary constructor permissions. The [composed PCS fixture](../../compiler/test/fixtures/language/pcs_setup.zkc)
and [Host client](../../crates/zkc-test-drivers/src/language_native/setups.rs) show two
setup slots executing through ordinary kernels and the common runtime.

## C++ boundaries

- `Zkc::Language`: capture supplied buffers, analyze them, and close an exact
  Entry. It uses the pure Contracts and Relation components and their common
  support; it has no MLIR, runtime or filesystem dependency.
- `Zkc::Translation`: emit unsimplified Protocol IR and independently
  admit and compare actual SSA with the checked source.
- `Zkc::Compiler`: `prepareOriginal` retains immutable bytes, interface,
  comparison and diagnostic mappings; `compileEntry` returns that retained
  original and a tagged `CompiledRun` or `CompiledNativeProof` candidate through
  const accessors. `artifact()` exposes the variant; `bytes()` returns the exact
  selected deployment and `options()` retains compilation choices.
  Only successful compilation can construct `CompiledEntry`; downstream MLIR
  remains caller-accessible and is separate from the immutable original.
  `readInterface` independently checks a supplied interface against original
  MLIR. `CheckedOriginal::interface()` exposes the retained checked view;
  `checkInterface` binds supplied metadata to that original. A structural
  interface view grants no authority to decode private inputs.
- `Zkc::Driver`: read explicit bounded files and render command results.

The logical type and layout APIs are [Language/Types.h](../../compiler/include/zkc/Language/Types.h)
and [Language/Layout.h](../../compiler/include/zkc/Language/Layout.h).
The compilation APIs are [Language/Project.h](../../compiler/include/zkc/Language/Project.h),
[Translation/Language.h](../../compiler/include/zkc/Translation/Language.h), and
[Compiler/Language.h](../../compiler/include/zkc/Compiler/Language.h).
The independent reader is [Compiler/LanguageInterface.h](../../compiler/include/zkc/Compiler/LanguageInterface.h).
Diagnostics retain byte spans; recovery tokens cannot be promoted into checked
state. The compiler never accepts a caller-constructed checked project.
[Diagnostics.h](../../compiler/include/zkc/Language/Diagnostics.h) renders bounded
primary and related spans from captured bytes.
[Inspection.h](../../compiler/include/zkc/Language/Inspection.h) describes completed
public callables without rechecking or specializing them.

Target failures retain their phase and generated coordinates. Admission failures
also identify a related source declaration; later compiler diagnostics use the
operation map established by source comparison when a position matches.
Unsupported future syntax is reserved and refuses explicitly.

The interface's toolchain stamp records the compiler source, installed catalog,
LLVM/MLIR release and LLVM revision when the installation provides it. An absent
revision is explicit. This is provenance, not a binary fingerprint: it cannot
distinguish local patches that preserve all recorded version information.
