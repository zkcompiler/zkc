# Author mathematical protocols

The `.zkc` language combines total mathematical helpers, ordered local functions,
static libraries and explicit participant messages. It emits mathematical MLIR
for the existing participant compiler and runtime. The
[source profile](../spec/profiles/source/mathematical-language.md) defines syntax,
permissions, role semantics and bounds. Static protocol composition, managed
randomness, bounded repetition and conditional participant completion are supported.
Relations, specification clauses and explicit run/proof Entries are supported.
Source-facing Host packaging and named invocation remain under
[frontend migration](../roadmap.md).

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
artifact and compilation options. Every command checks source, target
admission and source correspondence. There is no implicit import discovery or
fallback to the `.pir` parser. `--no-simplify` and `--release-storage` select
existing downstream compiler options for bundle production.

`--asset=NAME=FORMAT=FILE` adds explicitly captured relation data. Supported
formats are `r1cs-json`, `r1cs-binary` and `air-json`; the compiler validates even
unused assets with the native bounded readers. Capture alone does not attach a
relation to a protocol or add runtime inputs.

A bundle uses the existing [native runtime](../runtime/bundles.md). Its entry is
the encoded protocol symbol recorded in the source interface. Runtime inputs
are supplied using the bundle's physical input layout. For the transfer example,
P supplies x and c; V supplies its own c. The
[participant execution control](../../crates/zkc-tools/examples/language_native.rs)
also demonstrates direct independent runners, changed receive values and the
existing joint host with independently supplied role inputs.
There is no protocol-specific runtime or source-facing Host generator here.

## Select a proof job

[Schnorr source](../../compiler/test/fixtures/language/schnorr.zkc) defines the
participant equations, a discrete-log relation and a target clause. Its Entry
chooses P and V, public inputs, the acceptance result and a transcript suite:

```text
entry Proof = Schnorr<G> {
  prover P;
  verifier V;
  public { base, point };
  accept accepted;
  target knowledge;
  construction fiat_shamir("merlin3.bls12-381.fr64be/1") {
    derive challenges;
  }
}
```

The compiler finds the actual draws of `challenges` through composition and
repetition. It checks each delivery before constructing participant transcripts.
Use `construction authored;` for an authored noninteractive job. `target` is
optional and adds no execution guard. An Entry alias such as `entry Release = Proof;`
inherits the whole configuration. The [Entry contract](../spec/profiles/source/mathematical-language.md#entry-jobs)
defines exact selection and refusal rules.

`language-package` wraps the original, source interface and compiled artifact in
one exact publication. Rust `zkc_tools::entry::Package::capture` authenticates the
outer package against an application-supplied digest; native interface binding
and named execution are still being implemented.

`language-bundle` emits the existing native proof deployment for a proof Entry;
its producer and validator use the [shared proof host](../compiler/native-proofs.md).
At this stage invocation still uses native port maps and explicit deployment
pins. Named source inputs and authenticated source packages belong to the ongoing
Host implementation.

## Local code and reusable types

```text
module example;
domain Fr = field("bls12-381.fr");

struct Pair<T: Type> { pub left: T, pub right: T }
math fn square<F: Field>(x: F) -> F { return x * x; }
fn choose(x: Fr, go: bool) -> Pair<Fr> {
  let squared = square(x);
  let selected = if go capture(x, squared) {
    yield squared;
  } else {
    yield x;
  };
  return Pair<Fr>{left: x, right: selected};
}
protocol Transfer roles(P, V)(x: Fr @P, go: bool @P) -> (result: Pair<Fr> @V) {
  local P let pair = choose(x, go);
  let received = send P -> V(pair);
  return (result = received);
}
entry Demo = Transfer;
```

`math fn` describes total algebra. `fn` describes ordered work, including control
and resources. The protocol explicitly chooses P as the owner of `choose` and
sends its result. The receiver obtains its actual received components. The record
becomes two ordered payload leaves, which the interface maps back to named fields.

Generic libraries declare the permissions they use. A mathematical parameter
needs `Copy + Drop`; a protocol message also needs `Share + Wire`. A plain `Type`
parameter promises none. These permissions are independent. Components select
interface implementations statically and can seal an associated representation.
Library clients need neither its representation nor a runtime dispatch table.

Use explicit captures in local `if` and `match`; use `carry` for changing state or
affine resources in a `for` loop. Defined functions infer effects. Write `!{}` only
when an effect-free interface is an intended contract. Local owner inference,
nonlinear dimension inference and arbitrary inequality solving are not required.

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

`language-interface` emits `zkc.language-interface/5`. Schemas retain an exact
logical type identity and kind separately from their display label. A logical port's `native`
indices and recursive `schema` describe its flattened fields, variant payloads and
custody. These indices refer to the original mathematical signature, not a promise
that downstream physical storage uses the same positions. Host adapters must also
consult the selected bundle. This package supplies the schema and existing runtime
path; typed source job construction belongs to the Host package.

## C++ boundaries

- `Zkc::Language`: capture supplied buffers, analyze them, and close an exact
  Entry. It uses the pure Contracts and Relation components and their common
  support; it has no MLIR, runtime or filesystem dependency.
- `Zkc::Translation`: emit unsimplified mathematical MLIR and independently
  admit and compare actual SSA with the checked source.
- `Zkc::CompilerCore`: `prepareOriginal` retains immutable bytes, interface,
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

Target failures retain their phase and generated coordinates. Admission failures
also identify a related source declaration; later compiler diagnostics use the
operation map established by source comparison when a position matches.
Unsupported future syntax is reserved and refuses explicitly.

The interface's toolchain stamp records the compiler source, installed catalog,
LLVM/MLIR release and LLVM revision when the installation provides it. An absent
revision is explicit. This is provenance, not a binary fingerprint: it cannot
distinguish local patches that preserve all recorded version information.
