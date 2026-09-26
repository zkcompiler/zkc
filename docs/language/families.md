# Protocol families and static parameters

A protocol family retains choices that are fixed before execution. Public bounds
state what every supported choice must provide; concrete instantiation checks
the selected domains and arguments. [Generic definitions](generics.md) explains
which choices change meaning and which select a physical implementation.

## Protocol families

A protocol may bind static domain parameters, just as a local algorithm does:

```text
module {
  fn Double<F: Field>(x: F::Element) -> F::Element {
    let y = field::add::<F>(x, x);
    return y;
  }

  protocol Exchange<F: Field> {
    roles (Sender, Receiver);
    inputs (Sender x: F::Element);
    outputs (Receiver value: F::Element);
    let y = local Sender { Double(x) };
    message answer: Sender(y) -> Receiver(received);
    finish { value: received };
  }

  configure Small = Exchange(F = koala-bear);
  configure Large = Exchange(F = "bls12-381.fr");
  instance small: Small { roles (Sender = Sender, Receiver = Receiver); }
  instance large: Large { roles (Sender = Sender, Receiver = Receiver); }
  entry main = small;
}
```

`F` is a bound domain; `F::Element` is its element type. `Field` is an explicit
capability requirement, checked through the existing domain and requirement
services. Parameter names must differ from installed concrete domain identities:
the current common carrier uses one spelling namespace for domain terms, so the
source checker refuses a collision rather than capture a quoted literal. A
concrete selection supplies actual domains. It does not choose an arbitrary
backend by rewriting strings in the body.

The [nominal-term rules](reference.md#module-and-local-algorithms) distinguish
quoted installed identities, bound parameters and associated projections.
Domain and bundle parameter names must be undotted; the same rules apply in
types, static arguments, requirements and configurations.
A record named `F` remains a record in a type-head position even inside a
protocol binding domain `F`; specialization does not rename the record.

The configured names `Small` and `Large` become concrete protocol declarations.
The source family remains in the analysis for queries. Explicit static local
calls receive generated closed algorithm configurations. A generic local with
zero domain parameters still writes `Helper::<>` to request this construction.
A preconfigured local must be closed; a family cannot supply additional static
arguments to a partially configured local. These conditions are checked even
before selecting the family. A dependent child may
select its parent's domain using `dependencies(child: Child::<F=F>());`.
An instance can refer to that selected child with `ParentSelection::child` (and
nested dependency projections). This resolves through dependency declarations,
not a generated-name convention:

```text
configure Selected = Parent(F = koala-bear);
instance child: Selected::child { roles (P = Prover); }
instance parent: Selected {
  dependencies (child = child);
  roles (P = Prover);
}
```

Explicit instances preserve ordinary PIR dependency wiring. Direct entry
selection can generate the closed tree as described in
[products and outputs](values.md#products-local-blocks-and-distributed-outputs). Quoted
`"Selected::child"` is one exact name and is not parsed as a projection; ordinary
common-name restrictions still apply (the current owner refuses `::` inside an
exact protocol identity). Generated
identities have the prefix `__stage_<hex UTF-8 root>` followed by `_dep_<hex alias>`
or `_fn_<hex site>` segments. Internally tracked descendants extend that path;
user spellings are never interpreted as generated prefixes. The encoding is
injective and dot-free for the existing independent reader. It is deterministic,
not a claim that renaming source declarations preserves artifact identity.

This route specializes in the source layer and changes no common carrier.
Family bodies are source-checked under abstract domain parameters: local and
child calls, nominal operand/result types, participant ownership, message binds,
loop carries and declared capabilities. Every selected concrete program is
independently admitted. This is not a proof of security or admissibility for all
possible selections. Source/body checking
and concrete common admission remain distinct statuses.

See the maintained [polynomial family](../../examples/protocols/folded-contraction-family.pir)
and [group interaction family](../../examples/protocols/group-agreement-family.pir).
The former reuses vector folding and contraction; the latter uses group-valued
messages. They exercise the same source foundation without requiring a dedicated
protocol-family dialect.

## Named static constants

```text
const N: index = 8;
const LDE_SIZE: index = N * 4;
```

Constants form a bounded, pure natural-expression graph. The supported arithmetic
is `+`, `-`, `*`, `/`, `%`, with explicit overflow, underflow and zero-divisor
refusals. Forward references are permitted; cycles are refused. Each intermediate
value must fit the selected 32-bit natural construction bound. This is a source
construction bound, not a replacement of the runtime's numeric types.

Constants may supply designated natural positions: index expressions, static loop
counts, instance natural parameters, selected numeric operation attributes and
relation-view heights. A runtime lexical binding takes precedence in a runtime
expression. Quoted attribute strings are literals and are never interpolated.
Numeric attribute substitution covers the existing natural slots of
`index.constant`, `vector.splat/powers/at/length_check`, `poly.degree_check`,
`random.vector`, `curve.at`, `matrix.shape_check` and `vector.matvec`. Other
attributes retain their spelling and all slots still pass their operation owner's
checks. Natural expression/dependency depth is bounded at 64, each intermediate
at `2^32-1`, specialization count at 1024 and generation depth at 64. The default
authored/static compiler budget is 262144 cumulative logical units per analysis
invocation, shared by constant evaluation, static selection and syntax copies
across captured modules and specializations. This policy retains the numeric
default but can reject inputs accepted by the earlier independent phase counters.
Library formation, generated source and output have separate accounts; see
[compiler work budgets](../compiler/frontend-budgets.md) for charges, configurable
limits and exclusions. Generated declaration names are bounded at 64 KiB.
Static evaluation cannot access host files, backend state, randomness or witness
values. The dependency loader supplies relation assets explicitly.
