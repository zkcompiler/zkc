# Protocol source notation

The `.pir` language authors local algorithms, interactions, dependencies and
instances above common PIR. Its [retained source model](../compiler/frontend.md)
adds nominal types, bounded static construction and domain-generic protocol
families; these are checked before lowering into the explicit common carrier.
Portable JSON represents that carrier, rather than all authoring distinctions.
The C++ frontend resolves source declarations and reconstructs bounded static
arguments without changing PIR execution semantics.

Parsing, checking and executable lowering are separate operations; formatting
does not certify validity.

Start with the annotated [committed two-factor source](../../examples/protocols/committed-two-factor.pir)
or [repeated DLEQ source](../../examples/protocols/dleq.pir). Both include complete
local bodies and protocol composition. The [example index](../../examples/protocols/README.md)
separates executable sources from external declarations.
For reusable algorithms with late semantic and physical selection, use the
[generic DLEQ](../../tests/fixtures/generic-dleq.pir) and
[generic committed two-factor](../../tests/fixtures/generic-committed-two-factor.pir)
sources. Their explicit configurations share the same frontend and common IR.

## Daily use

From the repository root, after the [compiler build](../../compiler/README.md#build):

```sh
build/compiler/zkc-compile protocol-admit examples/protocols/dleq.pir
build/compiler/zkc-compile protocol-import examples/protocols/dleq.pir
build/compiler/zkc-compile protocol-compile examples/protocols/dleq.pir > /tmp/dleq-participants.json
build/compiler/zkc-compile protocol-format-check examples/protocols/dleq.pir
build/compiler/zkc-compile --help
```

The table highlights authoring commands; `zkc-compile --help` lists the complete
command set and options. The
[development host contract](../runtime/inputs.md#input-format) defines
`run-protocol` inputs. Artifact producers and validators instead use
`zkc.artifact-inputs/1` from the
[artifact format](../compiler/artifact-format.md#canonical-logical-encoding).

| Command | Result |
|---|---|
| `protocol-analyze FILE` | Retained source declarations, types and uses; reports partial/error states and does not claim admission |
| `protocol-parse FILE` | Tagged syntax inspection, including unresolved declarations; not portable common JSON |
| `protocol-source FILE` | Elaborated, admitted JSON common module or structurally valid construction descriptor |
| `protocol-explain FILE` | Checked requirements, partial configurations and specialization sharing |
| `protocol-inspect FILE` | Machine-readable explanation, actual elaborated source, occurrence spans and selection snapshot |
| `protocol-prepare FILE` | Checked generic specialization retaining source configuration names |
| `protocol-format FILE` | Readable text; preserves comments in text input |
| `protocol-format-check FILE` | Exit 0 if already formatted; exit 1 if formatting would change |
| `protocol-admit FILE` | Declaration admission through the existing source/MLIR checks |
| `protocol-import FILE` | Common MLIR |
| `protocol-project FILE` | Logical participant JSON |
| `protocol-physical-ir FILE` | Physical participant MLIR |
| `protocol-compile FILE` | Physical participant JSON |
| `protocol-construct SOURCE DESCRIPTOR` | Constructed common program and correspondence data |

Text and JSON inputs are detected by content. `-` reads stdin. Output goes to
stdout; errors go to stderr. To format a file, write to a separate path and replace
the original only after success. Redirecting output onto the input path truncates
the input before the tool starts. The formatter has no in-place mode.

Formatting **text** requires complete syntax, but references, types and generic
requirements may still be invalid. `protocol-source`, admission and compilation
continue to reject those errors. JSON-to-text printing requires admitted module
records (or a structurally valid descriptor) and checks its exact parse round trip.
Printed modules start with `carrier module { ... }`. This explicit representation
preserves the carrier's names (`src_`, `lib_`, `client_`,
`__library_operation_`) and origins when read by `protocol-source`, including
when copied into a new file or supplied on stdin. The printer uses that same
public reader and checks exact carrier equality. There is no printer-only trust
flag. An ordinary `module` still reserves generated prefixes.
Construction descriptors use the same closed names and selector interpretation
for carrier text and JSON. Project aliases and origin-group expansion belong to
ordinary authored modules and are not reapplied to a printed carrier.

A carrier module is self-contained: it accepts functions (including portable
generic definitions), bindings, configurations, protocols, instances and entries.
It cannot import modules/assets or declare source-library interfaces, components,
records, constants or exports (`source-carrier-authoring`), and cannot be a child
module or an imported library (`source-carrier-project`). Its functions and
protocols still pass the usual checking and independent PIR admission. This form
does not reconstruct the original library abstraction from a flattened carrier.
`protocol-analyze` supports bounded declaration recovery. Formatting and
accepted emission still require complete syntax; a full editor is outside scope.

```sh
build/compiler/zkc-compile protocol-format examples/protocols/dleq.pir > /tmp/dleq-formatted.pir
build/compiler/zkc-compile protocol-source examples/protocols/dleq.pir > /tmp/dleq-source.json
```

The native Rust hosts and Lean checkers still consume JSON. Generate it with
`protocol-source`, then use it wherever those tools require the original source.
Host inputs, construction candidates and proof files keep their existing formats.
Compiled participant counts additionally support the input-family bindings
described below. `protocol-export` continues to read MLIR.

## Related source forms

The common calls and interaction below combine with the following checked source
features. These links own their detailed syntax and restrictions.

| Form | Reference |
|---|---|
| `interface`, `component`, `link`, `select`, `seal` | [Checked interfaces and static components](components.md#checked-interfaces-and-static-components) |
| `enum`, `match`, finite traversal | [Local alternatives and finite traversal](components.md#local-alternatives-and-finite-traversal) |
| Products, named arguments, tail expressions, `local Role { ... }`, `finish` | [Products, local blocks and distributed outputs](values.md#products-local-blocks-and-distributed-outputs) |
| `mod`, `use`, `pub`, exact source dependencies | [Source projects](projects.md) |
| Static constants and bounded evaluation | [Named static constants](families.md#named-static-constants) |
| Development-host inputs for compiled participants | [Host input contract](../runtime/inputs.md#input-format) |
| Artifact producer/validator inputs | [Artifact input format](../compiler/artifact-format.md#canonical-logical-encoding) |

Struct declarations and construction accept both the parenthesized notation
shown below and braces such as `struct Pair { left: bool, right: bool }` and
`Pair { left: x, right: y }`. Brace construction also permits field shorthand.
Both retain the same nominal source type before common lowering.

## Static source construction

Named natural constants and whole-protocol domain parameters are part of the
[language foundation](families.md#protocol-families):

```text
const ROUNDS: index = 8;
protocol Exchange<F: Field> { /* explicitly owned interactions */ }
configure Small = Exchange(F = koala-bear);
```

Constants are pure bounded source computations, not runtime values. A protocol
family is checked under its declared source requirements, then each selected
concrete program passes independent common admission. Static local calls use
`Helper::<F>(...)`; child dependencies may bind their parent's domains. See the
complete [domain family](../../examples/protocols/domain-family.pir) and the
[polynomial family](../../examples/protocols/folded-contraction-family.pir).

## Module and local algorithms

This complete module admits and compiles with `protocol-source` and
`protocol-compile`. Save it as `/tmp/twice.pir`:

<!-- executable: source -->
```text
module {
  fn Twice<F: Field>(x: F::Element) -> F::Element {
    [sum] let y = field::add(x, x);
    return y;
  }
  fn Four<F: Field>(x: F::Element) -> F::Element {
    [first] let a = Twice(x);
    [second] let b = Twice(a);
    return b;
  }
  configure Calculate = Four(F = "koala-bear");
  protocol Demo {
    roles (P, V);
    inputs (P x: "koala-bear"::Element);
    outputs (V "koala-bear"::Element);
    local [calc] P: let y = Calculate(x);
    message [send_result] result: P(y) -> V(received_y);
    return received_y;
  }
  instance concrete: Demo { roles (P = P, V = V); }
  entry main = concrete;
}
```

```sh
build/compiler/zkc-compile protocol-source /tmp/twice.pir > /tmp/twice-source.json
build/compiler/zkc-compile protocol-compile /tmp/twice.pir > /tmp/twice-participants.json
```

A function has an explicit signature and no participant of its own. `local`
selects its owner; local work can draw randomness, consume resources or fail.
Calls resolve against the complete declaration index, including forward references.
Primitive operations and helper calls use ordinary call syntax but retain distinct
common records and effects. The acyclic helper graph is retained in native MLIR
before checked expansion; see [local composition](../compiler/local-composition.md).

| Form | Meaning |
|---|---|
| `[site] let y = Twice(x);` | One result, with an optional occurrence label |
| `let (a, b) = Helper(x);` | Two ordered results, flat destructuring |
| `control::require(ok);` | Zero-result call; the guard is retained |
| `let y = Twice::<F>(x);` | Explicit static argument |
| `let first = vector::at::<F>(xs) attributes (0);` | Static domain and separate ordered operation attributes |
| `let one: F::Element = field::constant() attributes (1);` | Result annotation constrains a nullary producer |
| `return x;` / `return (x, y);` / `return;` | One, multiple or zero results |

Bindings are immutable unless declared `let mut`. Mutable source bindings
elaborate to SSA values and region results; they are not references or mutable
heap storage. Nested call expressions evaluate operands once, left to right.
Shadowing, wildcard discard and implicit resource copies remain unsupported. Bare calls require zero results.
Source products are first-class values: `(x, y)` can be bound, nested or
projected with `.0` and `.1`; `()` is unit and `(x,)` is a singleton. Their
leaves become ordered common-PIR results. Functions accept explicit `return`
or a tail expression. See [products and local blocks](values.md#products-local-blocks-and-distributed-outputs).
`::<...>` supplies static arguments; `attributes (...)` supplies existing ordered
attribute strings. A natural attribute token abbreviates its decimal string.

Qualified calls such as `field::add` select installed operation contracts.
Exact names such as `Twice` or `"bool.and"` prefer the declared helper or
configuration. With no such declaration, an exact installed operation name can
still be used in a generic body. Named-call resolution happens before argument
type checking, with no overload search. Operators use the separate fixed table
keyed by operand types. Ordinary bodies may use explicit operation
bindings, a selected module profile, or qualified contracts. A qualified contract
with concrete inferred domains creates a shared default binding in the module;
explicit bindings remain the way to select an implementation.
Thus a helper named `"bool.and"` remains callable even beside `bool::and`.
Names that conflict with grammar keywords can be quoted at use sites; the common
printer quotes them automatically. Cross-file declarations use the separate
[project lookup rules](projects.md).
A bare name may contain dots, so `inner.Keep` can be a declaration's own name.
When it is also a path to another declaration, through a module, an import or a
dependency, a call or a clause that names it unquoted (an instance's protocol,
an entry's instance and the like) refuses as ambiguous, and `"inner.Keep"`
names the declaration in scope. Types, static terms, record literals, predicates
and values use the same ambiguity check for their own reference category;
rename a declaration or use an unambiguous import alias to resolve those uses.
A competing path must reach a declaration or member authorized for that category:
an ordinary function followed by an arbitrary suffix is not such a path.

Nominal terms distinguish bound parameters from installed identities. Write `F`
or `G::Scalar` for a scoped parameter or its associated projection, and
`"bls12-381.fr"` for a concrete installed identity. `G.Scalar` is an opaque dotted
root, not an alias for `G::Scalar`; it refuses with `source-name-unresolved`
when no such installed identity exists. Quoting it does not turn it into a
projection. Concrete associated terms such as `"bls12-381.g1"::Scalar` normalize
to the installed associated identity.

Explicit `bind add = field::add("bls12-381.fr");` declarations select operation
bindings for ordinary functions. The two existing BLS profile headings retain
their documented closed-module defaults and bare-type shorthand. They are a
supported convenience feature, not a decoder for replaced call/type syntax.
Generic definitions require an explicit module. A profile does not supply
omitted domains for arbitrary types, and an explicitly authored origin is kept.

## Collections and structured local control

```text
fn Evaluate<F: Field>(coefficients: Vector<F::Element>, point: F::Element,
                      negate: bool) -> F::Element {
  let mut result = field::constant::<F>() attributes (0);
  for i in 0..coefficients.len() {
    result = field::add(field::mul(result, point), coefficients[i]);
  }
  if negate { result = field::neg(result); } else { }
  return result;
}
```

`[a, b, c]` constructs a homogeneous field/group vector or index collection.
Its type follows its elements; annotate an empty literal, for example
`let empty: Vector<F::Element> = [];`. `values[i]` performs checked indexing,
and `values.len()` reads the length of a named collection. Integers in expressions
are index values; field constants still use their typed operation. Boolean
literals are `true` and `false`. Collection syntax does not denote SIMD vectors.

`for i in 0..4` and `for i in start..values.len()` use the same finite operation.
Bounds are read once, the upper bound is exclusive, and inverted ranges do no
iterations. `if` requires a Boolean. An omitted `else` leaves the outer state unchanged.
Only the selected arm executes. Source reassignment requires `let mut` and cannot
change the binding's type. Branch-local bindings do not escape. The frontend
computes region captures, carried state and branch-result merges.

These forms are legal only inside `fn`; protocol `loop` retains its public static
count and role-owned ports. Runtime limits, affine-state rules and supported
construction paths are specified by the [local-control profile](../spec/profiles/compiler/local-control.md).
Neither secret-dependent control nor this syntax establishes constant-time or
zero-knowledge behavior. There are no source-defined operator overloads,
break/continue, unbounded `while`, or protocol-level dynamic
branches. Infix operators are [spellings of installed operations](#bundles-structs-operators-and-checked-structs).

Printing portable source displays explicit `capture`, `carry`, result bindings
and `yield` so it can preserve and check the exact region structure. Explicit
region arguments are immutable; return new state through the declared yields.
Only those explicit regions accept a written `yield`. Text formatting preserves the higher-level source conveniences. The full executable
[polynomial fold example](../../examples/protocols/polynomial-fold.pir) and
[Groth16 source](../../examples/protocols/groth16.pir) show both uses.

## Bundles, structs, operators and checked structs

These four forms are authoring syntax. Source analysis retains their nominal types and resolved uses. Lowering expands
them into the common notation above; they add no record kinds to the
`protocol-source` JSON consumed by later stages. A source that uses them and a
source written out by hand produce the same encoded common records. The
[design](data.md) gives the reasons and every refusal code.

```text
module {
  bundle PairingScalars(F) = (
    ScalarAction(F::PairingG1), ScalarAction(F::PairingG2),
    "="(F::PairingG1::Scalar, F), "="(F::PairingG2::Scalar, F)
  );

  struct VerifyingKey<F: domain Field>(
    input_query: Vector<F::PairingG1::Element>,
    alpha: F::PairingG1::Element,
    beta: F::PairingG2::Element
  );

  checked struct BoundAssignment<F: domain Field>(
    assignment: Vector<F::Element>,
    statement: Vector<F::Element>
  ) constructors (BindAssignment);

  fn Blind<F: PairingField>(vk: VerifyingKey<F>, r: F::Element) -> F::PairingG1::Element
      requires (PairingScalars(F)) {
    let blinded = vk.alpha + -(vk.alpha * r);
    return blinded;
  }
}
```

| Form | Rewritten to |
|---|---|
| `requires (Bundle(T))`, `where T: Bundle` | The bundle's requirements at that position, in declared order, arguments substituted; nested bundles expand recursively; nothing is sorted or deduplicated |
| `p: Struct<F>` as a parameter, input or result | One parameter, input or result per leaf, in declaration order with nested structs depth first, named `p.field` |
| `Struct(field = expr, ...)` | No operation. Initializers run once in written order; the leaves are arranged in declaration order |
| `binding.field` | The leaf value of that name. The lexer reads `binding.field` as one name |
| `a + b`, `a * b`, `a - b`, `-a` | The installed operation spelled by that symbol for those operand constructors, with operands evaluated once, left to right as written |

A bundle is a name for a requirement list. It adds no assumption, and a header
bound cannot name one because a bound also fixes a parameter's sort.

A struct's static parameters use `F: domain Sort`; a struct states no capability,
so functions keep stating theirs. Field types are logical types or other structs.
A struct value may be a parameter, result, `let` binding, protocol input or
output, `local` result, `invoke` argument or result, and a `carry`, loop output,
`yield` or `return` value. Struct identity is nominal, including static
arguments. Bindings are immutable, and a message carries one named value, so
send a struct's fields under their own schemas. A leaf that is an affine
resource keeps the existing rule under its own name: reading `s.coins` uses that
leaf, and passing `s` uses every leaf. Construction infers static arguments as
calls do; a parameter that occurs only under an associated domain, such as
`F::PairingG1`, is written: `Groth16Proof::<F>(a = a, b = b, c = c)`. An entry
protocol with a struct input receives host values under the leaf names, such as
`vk.alpha`.

Operators resolve to installed operation contracts, with operands evaluated once
in written order. The [operator reference](data.md#4-operators) owns the spelling
table, precedence and domain restrictions; notation supplies no additional
algebraic laws or reassociation permission.

A checked struct is constructed only inside its named constructor functions and
is otherwise an ordinary struct, readable by field. A consumer that declares it
therefore receives a value a constructor returned. It carries its run-time
context as fields, and a consumer reads that context from the value. It is
refused as an input of an entry protocol and as the result of an `external`
function, where a value would arrive without its constructor. The rule is
applied to `.pir` text and guards its author against an omitted or mismatched
check; constructor correctness remains the author's obligation.

The [Groth16 source](../../examples/protocols/groth16.pir) uses all four forms
and its [expanded twin](../../tests/fixtures/groth16-expanded.pir) states
the same module without them.

## Types, bounds and static inference

| Authored type | Common logical type |
|---|---|
| `F::Element` / `G::Element` | `field:F` / `group:G`, according to the declared sort |
| `G::Scalar::Element` | `field:G.Scalar` |
| `E::BaseField::Element` | `field:E.BaseField` |
| `Vector<F::Element>` / `Vector<G::Element>` | `vector:F` / `groups:G` |
| `Matrix<F::Element>` | `matrix:F` |
| `Polynomial<F>`, `Table<F>`, `Point<F>`, `Round<F>` | Existing polynomial, multilinear table, point and round constructors |
| `Rng<F>`, `Nonce<F>`, `Transcript<T>` | Existing resource constructors |
| `Commitment<C>`, `Commitments<C>`, `OpeningState<C>`, `OpeningStates<C>`, `Proof<C>`, `ProverKey<C>`, `VerifierKey<C>` | Existing commitment-sorted constructors |
| `bool`, `index`, `Indices` | Domain-independent constructors |

Nominal domains remain distinct even when physical representations agree.
These are finite logical constructors, not arbitrary generic types:
`Vector<Vector<F::Element>>` is unsupported. Physical representations remain
selected later; the JSON `constructor:domain@representation` carrier is unchanged.

`<F: Field>` declares a field-sorted parameter and emits exactly `Field(F)`.
`<F: domain Field>` declares only the sort, with no capability assumption.
`<F: TwoAdicField>` emits that capability; the installed implication supplies
`Field(F)` without adding a stored assumption. Do not strengthen a kind-only
interface during printing or migration.

Bounds describe public promises, never promises inferred from a body. `where`
adds capabilities over declared terms, for example `where G::Scalar: Field`.
`requires (...)` retains ordered multi-argument and equality predicates. Stored
requirements follow header bounds, then `where` predicates, then explicit
requirements, without sorting or deduplication. The common printer uses
kind-only parameters and explicit requirements to preserve that order.
This is a bounded installed capability vocabulary, not Rust's full trait system,
user `impl` blocks or a theorem prover.

For a resolved callee, static inference matches operand types and optional local
result annotations. A partial configuration takes only residual parameters in
base declaration order. Missing arguments must be uniquely determined; write
`Helper::<F>(x)` when inference cannot determine them. Nullary calls need a result
annotation or explicit arguments. Associated projections can be checked but not
inverted: knowing `G::Scalar = F` cannot infer `G`. There is no global solver,
backward inference through later statements, implicit field embedding or backend
search. Inferred calls still undergo signature, requirement and affine checks.

`fn Name(...)` and `fn Name<>(...)` remain distinct ordinary and zero-parameter
generic categories. Generic bodies call generic definitions/configurations;
ordinary closed bodies can also supply concrete residual static arguments.
When constraints provide several equal nominal spellings, inference chooses
among those spellings by fewest projections and then lexical order. It does not
search all equivalent catalog identities. Explicit static arguments retain the
selected term. Reordering operation operands is still a source change; this
choice promises stable inferred arguments, not identical artifacts for rewrites.

Inside a generic definition, nominal terms must be its parameters or their
associated domains. Closed catalog identities belong in configurations or
ordinary functions. Invalid requirement arity and sorts are diagnosed at the
requirement itself. Successful reconstruction does not establish the declared
capability obligations; the existing common checker still checks them.

Protocol-local generic work still needs an explicit `configure`; inference does
not invent configurations or change source identity.

## Roles and interaction

This profile-scoped opening child illustrates the two-factor interaction; its
functions and enclosing module are in the linked complete source:

```text
protocol FactorOpening {
  roles (P, V);
  inputs (
    P state: opening_state,
    P p_point: point,
    V vk: verifier_key,
    V root: commitment,
    V v_point: point
  );
  outputs (V field);
  local [make_opening] P: let (evaluation, proof) = OpenFactor(state, p_point);
  message [evaluation_message] evaluation: P(evaluation) -> V(received_value);
  message [proof_message] opening: P(proof) -> V(received_proof);
  local [check_opening] V: let checked_value = CheckOpening(
    vk, root, v_point, received_value, received_proof
  );
  return (checked_value);
}
```

`roles` is mandatory. `P` and `V` are declared names, not predefined participants;
other names and more than two roles are supported by common-source formation and
projection. A particular construction or host can impose a narrower role profile.

`inputs` records each value's owner and type. `outputs` records result owners and
types in order. `local [site] ROLE: let result = Function(...);` executes one algorithm
using that role's available values. `message [site] SCHEMA: Sender(value) ->
Receiver(binding);` makes the wire action, its schema and receiving binding
explicit. A local call cannot silently read a peer's private values. Admission
checks these facts using the same rules as JSON input.

Header clauses precede the body. `parameters`, `inputs`, `outputs` and
`dependencies` are optional when empty. `roles` is explicit even on declarations.

## Composition and counted loops

A parent declares dependency interfaces, then invokes their selected instances:

```text
dependencies (sumcheck: ProductSumcheck(n = n), opening: FactorOpening());
invoke [open_f] opening(sf, p_point, vk, root_f, v_point) -> (f_value);
invoke [open_g] opening(sg, p_point, vk, root_g, v_point) -> (g_value);
```

The dependency name is a slot, not a local function. Its child protocol retains
its own role-owned work and messages. Arguments/results follow the declared child
signature in order. `n = n` here states agreement between a named child parameter
and a named parent parameter; it is not a runtime assignment or implicit inference.
Repeated child calls keep distinct sites, whether labelled or anonymous.

Loops retain a public count and explicit state:

```text
loop [rounds] n carry (
  left = f, right = g, p_point = pp, v_point = vp, current = claim, random = coins
) -> (residual_f, residual_g, p_end, v_end, claim_end, coins_end) {
  // Round work appears here in the complete source.
  yield (next_f, next_g, next_p, next_v, next_claim, next_random);
}
```

The snippet above omits the round body for explanation; the linked source contains
it. A named count refers to a declared public natural parameter; a decimal count
is a constant. `carry (inner = outer, ...)` initializes block arguments. An
optional `capture (name, ...)` between `carry` and `->` explicitly imports other
available values. `yield` supplies the next carried state; the loop's result names
bind the final state. Nested loops use the same rules. `return` terminates a body;
`stop [site] ROLE reason;` records an owned stop under existing admission rules.

## Instances and external declarations

```text
instance sumcheck: ProductSumcheck {
  parameters (n = 3);
  roles (P = P, V = V);
}
instance opening: FactorOpening {
  roles (P = P, V = V);
}
instance interactive: CommittedTwoFactorArgument {
  parameters (n = 3);
  dependencies (sumcheck = sumcheck, opening = opening);
  roles (P = P, V = V);
}
entry main = interactive;
```

An instance selects natural parameters (fixed values or bounded entry ingress), dependency instances and a
formal-to-actual role mapping. Mappings are explicit; omission never inserts
`P` or `V`. Existing admission checks closure, role compatibility and parameter
agreements. An entry selects an instance. Definitions can be forward-referenced;
resolution happens after parsing the complete module.
Runtime-selected counts use `rounds = ingress(10, P = Select(pn), V = Select(vn))`.
The selector argument lists name actual owned entry ports; see the
[input-family contract](../compiler/interactive-execution.md#input-selected-families) for
bounds and the restricted dependency surface.

A local declaration without a body uses `fn Name(...) -> (...) external;`.
A protocol declaration retains its headers and uses `external;` instead of a
body, inside its braces. This permits interface and composition experiments.
Declaration admission is separate from executable compilation: missing bodies
and unsupported executable types still cause refusal.

## Construction descriptor

Keep a construction in its own document, for example
[dleq.construction.pir](../../examples/protocols/dleq.construction.pir):

```text
construction main {
  producer P;
  validator V;
  public "base_0" = (P p_base_0, V base_0);
  public "base_1" = (P p_base_1, V base_1);
  public "image_0" = (V image_0);
  public "image_1" = (V image_1);
  random coins at (DLEQDraw draw);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
```

`public` binds an ordered label to role/input references. `random` names the
validator RNG input and allowed local-function/draw-site pairs. `accept` selects
the validator result position. The [construction contract](../compiler/artifact-format.md)
defines their meaning and the supported suite. All singleton clauses are required;
`public` can repeat. Parsing and formatting check descriptor shape. Source-relative
roles, public binding, randomness provenance and construction applicability are
checked by `protocol-construct` or `protocol-check-construction` with both inputs.

## Text rules and identity

Labels can be omitted on local operations, `local`, `message`, `invoke`, `loop`
and `stop`. The parser allocates `__site_0`, `__site_1`, … in each declaration,
reserving all its explicit labels, including those later in nested bodies.
Duplicate explicit sites in that scope are errors. Unrelated declarations do not
renumber a declaration's anonymous sites. An added instruction can renumber them.
Use a descriptive label when another declaration selects a particular operation:

```text
[fold] let result = poly::fold::<F>(table, challenge);
// In a configuration of the containing generic function:
// using (fold = "arkworks-msb/poly.fold")
```

Formatting authored text keeps omitted labels omitted. Printing a portable record
shows its allocated sites because that carrier has no explicit/anonymous flag.
Inspection exposes both site names and snapshot-relative structural paths.
These are source references, not globally stable identifiers or proof evidence.

- Bare names start with an ASCII letter or `_`, followed by letters, digits,
  `_`, `.` or `-`. `->` is always an arrow. Double-quoted JSON strings can be used
  for names, labels, profiles, attributes and types; escapes decode exactly once.
  Text strings require valid UTF-8 and paired Unicode surrogate escapes; malformed
  encodings are rejected instead of replaced in public labels.
- Natural numbers use decimal digits without leading zeroes. Operation attributes
  are strings; an unquoted natural attribute is shorthand for its decimal string.
  Qualified types such as `opaque:Trace` can also be quoted as `"opaque:Trace"`.
- Lists accept trailing commas. Statements end with `;`. Whitespace and `//` or
  nested `/* ... */` comments do not enter the parsed representation.
- Formatting uses two-space indentation and breaks long parenthesized lists near
  100 columns. Long identifiers and comments can exceed that width. Comments keep
  their text and token order, but can move onto separate lines. Formatting text
  retains its token spellings; JSON-to-text printing chooses canonical spellings.

Text formatting preserves syntax and token values without elaboration. Common
printing checks equality of the re-elaborated common record, excluding diagnostic
spans, rather than original JSON whitespace or byte encoding. Sites, names, attributes, labels and order within each
declaration/binding/body list are preserved. The module record stores functions,
protocols, instances and entries in separate lists; their interleaving in text has
no additional meaning. Formatting does not rename or reorder them within a list.
Renaming a site remains a source change for exact candidate checking. Under
exact identity the construction binds that whole source, so renaming a site can
change transcript bytes; under normalized identity it does not.
A construction uses normalized identity unless it is written
`construction main identity exact { … }`; `identity normalized` states the
default. The normalized occurrence and binding contract is specified in the
[identity design](../runtime/artifact-identity.md).
Do not assume an arbitrary alpha-renaming or algorithm rewrite preserves a
transcript. Public interfaces, schemas and cryptographic domains remain distinct.

`protocol-import` and `protocol-physical-ir` accept `--locations` to show MLIR
source locations. Local instructions, generic bodies, calls and inserted physical
conversions retain their relevant source locations. Debug locations are omitted
from portable artifacts and do not establish transformation correspondence.

Both compilation commands accept `--implementations=FILE`. A persisted selection
can use the `selection_template` returned by `protocol-inspect`:

```text
["zkc.implementation-selection/1", "<source snapshot SHA-256>",
 [["fold_left", "arkworks-msb/poly.fold"]]]
```

Selection keys name concrete operation bindings. The compiler checks the snapshot
against the elaborated original common record before specialization;
whitespace/comments do not change it, but changes to that record do. Bare
selection lists are also supported, without a source snapshot or freshness
guarantee. Generic `configure … using (…)` clauses instead
select labelled operations within their target definition. Neither mechanism
performs implementation search, and these compiler snapshots do not enter the
protocol transcript.

Inputs are bounded to 1 MiB, token streams to 262,144 tokens, individual parsed
lists to 32,768 entries and text body/comment nesting to 64. Existing JSON and
protocol admission limits apply in addition. An input near these bounds may be
refused if its expanded JSON or printed text exceeds a bound.

Syntax errors show `file:line:column`, a stable error code and a bounded excerpt.
Common-source admission errors point to the offending instruction/declaration
when available, otherwise the module start. Coordinates count source bytes.
Generic definition/configuration errors retain the original record's location;
JSON documents also receive spans. Source maps have a separate allocation budget,
so deeply nested otherwise valid JSON may exceed the authoring metadata limit.
Compilation refuses invalid source. The analysis interface supports bounded
recovery for tooling, and projects support explicit imports. Completion and an
editor language server are outside the current implementation.

## Implementation and validation

Formatting works before semantic admission and preserves comments. Syntax-only
inspection is not portable source; authoring inspection reports resolved calls,
static arguments, result types and requirements. The
[frontend implementation](../compiler/frontend.md) owns retained analysis and
[the source model](../compiler/source-model.md#using-the-model) owns the C++
parsing, checking and programmatic construction APIs. Tooling explanations are
not admission certificates.

The frontend and source checks cover independently written text/model pairs,
codec round-trips, formatting, ownership, exact spans, malformed values and
resource bounds. These are engineering checks, not a parser or security proof.

For native execution, build the tools with `just build`, then run the maintained
frontend integration tests from the repository root:

```sh
uv run --no-sync --locked pytest -q tests/protocol/test_protocol_frontend.py
```

Compiler-only source checks run through CTest:

```sh
ctest --test-dir build/compiler -R '^frontend-' --no-tests=error --output-on-failure
```

Use `just test-sanitize` for the instrumented native suite. Its scope and the
prebuilt-LLVM allocator boundary are owned by the
[development guide](../development/README.md#build-profiles-and-editor-tools).

## Compiled relation declarations

```pir
relation Circuit = r1cs("circuit.r1cs");
derive Core = rank_one(Circuit, public_matrices);
derive Rows = multilinear(Circuit, specialized);
relation Trace = air("trace.air.json");
derive Steps = arithmetic(Trace, specialized, 8);
```

These are module declarations. Parsing/formatting perform no file reads.
`protocol-resolve SOURCE.pir` loads bounded relative dependencies and emits a
self-contained `zkc.relations/1` snapshot; absolute paths, traversal and escaping
symlinks refuse. `protocol-admit` on unresolved declarations refuses.
R1CS accepts binary R1CS v1 or canonical relation JSON; AIR uses its explicit
arithmetic schema. The file path is a locator, not the relation identity.

A view selects a family-specific interface. `Core_Assemble` assembles the ONE,
public and private coordinates. `Core_Products` computes actual A/B/C products;
`Core_Residuals` returns their constraint residuals. A `public_matrices` Products
call takes A, B, C, assignment and checks their exact contents; a `specialized`
call takes assignment only. The multilinear view additionally provides its
challenge/point consumers. `Steps_Evaluate(statement,trace)` evaluates finite
AIR residuals for the selected height. Names are ordinary typed local-function
symbols; a view cannot be retargeted by retaining a generated-looking name.

The native module retains relation symbols and checks generated functions
against those relations. `protocol-materialize SNAPSHOT` explicitly discharges
that ownership into checked ordinary arithmetic, preserving origin identities
and content guards. The independent Lean source checker consumes this ordinary
source, not an implicitly unwrapped relation envelope. `protocol-relation-data
SNAPSHOT VIEW` exports stamped matrix data for an immutable-data view. See
[design and assurance](relations.md) and the executable
[composition example](../../examples/relations/README.md).
