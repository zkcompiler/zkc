# Conformance tests

These are the tests that an implementation of `../LANGUAGE.md` must pass: 502 programs, each
with the outcome that the rules require. The 322 tests of layer A are frozen with that layer.
The tests of the later layers (77 for layer B, 62 for C, 35 for D, 6 for E) are not frozen:
their layers are carried, and an outcome that rests on a pending change says so in its note.

## How the files are read

A file is a list of blocks. A block starts with a line

```text
=== ID | expect | note
```

and the program follows, up to the next such line. The lines before the first block are a
heading.

- **One program per test.** A program is one module. Where a test needs several modules, a line
  `--- file` separates them; the first is the module under test.
- **The library.** A program is checked with the library of `../lib/zkc/`. A module of a test
  whose header is `module zkc::…` stands in place of the library module of that path: this is how
  a change to the library is tested.
- **`// instantiate: m<args>`** asks for that instance to be checked as a root (SP7), for a
  definition that no root of the program reaches.
- **A type bound in a test** (`type F = primitive("bls12-381.fr")`) is a row bound by a module of
  a project: its signature is taken as written and reported (NL9). It is not the test.

`expect` is one of:

| `expect` | Means |
|---|---|
| `accept` | the program is admitted |
| `accept, warn` | admitted, and a report is required (SC8) |
| `accept, unchecked` | admitted, and the tool reports what it did not check: a statement that rests on the formal library (GL5), a definition resolved for names only (SP7) |
| `accept, fmt` | admitted, and the formatter removes a redundant annotation (FM2) |
| `accept, law false` | admitted for execution; a closed law is found false by evaluation, which is an error of the build by policy and changes no role program and no identity (SP10, SX10) |
| `refuse R` | refused, by the rule `R` |
| `refuse R S` | refused; `R` is the rule that this reference names first, and an implementation that reports `S` for the same line also conforms |
| `skip` | not a test yet: the note says which change is pending |

The rule of a refusal is part of the test. Where this reference states the refusal under two
rules, both are given.

The prefix of an identifier says what the program is:

| Prefix | Program |
|---|---|
| `T-`, `S-`, `I-`, `R-`, `V-`, `N-`, `X-` | a program written for the rule or the form that its note names |
| `M-` | a worked program of `../programs/` with one change; the whole changed program is the test |
| `L-` | a module of `../lib/zkc/` with one change, in place of the library module |

## What the tests cover

The outcome stated here is the one that the rules of this reference require, by reading. Besides
the forms and the refusals of each rule, the tests cover:

- the receiver's type without the sender's facts; the range of `a ^ b`; `and` and `or` passing
  facts; a literal typed from the other arm of an `if`, from the other operand and from the
  collection it is appended to; an `if` with a static condition; the loop rule of TY10, with
  collected values as a collection or a tuple; `Ring`, `to_nat` and the view of a field over its
  prime field; a static name of a module and of a section; a nested module without a bound; a
  `where` on a law and on a relation; a `law` of a module; a closed law found false; default
  instances at a bound; specification-only static parameters; operators on a type member and
  the opaque type member of SP12; an asset as naturals and data; types that are empty; a cost
  that is not closed;
- a second case of one alternative, which is refused (`M-OR2`, `N-TY13a`); a `where` conjunct
  on a specification-only parameter, which does not refuse a protocol (`N-SP11c`), and an
  application that gives such a parameter as `spec e = term` (`N-SP11e`, `N-SP11g` to
  `N-SP11i`, `N-GL2c`); what is a ring's (`N-TY6f`, `N-TY6i`); literal expressions (`N-TY6h`);
  types and facts kept separate (`N-TY4b`, `N-TY4c`, `N-TY8e`, `N-TY8f`, `N-TY10f`,
  `N-TY10g`); an alias, which is its definition (`N-TY13b`); a function loop that a run-time
  natural ends (`N-CT4a`);
- the abilities of a simulator, `Runs`, and ceilings. A function named after `by` in a
  `knowledge` or `zero_knowledge` clause is a `def` in every test.

## Counts

By file:

| File | Tests | accept | refuse | not run |
|---|---|---|---|---|
| `layer-a-functions-specification.txt` | 15 | 3 | 12 | 0 |
| `layer-a-interaction.txt` | 46 | 15 | 31 | 0 |
| `layer-a-lexical-grammar.txt` | 24 | 10 | 14 | 0 |
| `layer-a-names-static.txt` | 88 | 30 | 58 | 0 |
| `layer-a-types-facts.txt` | 149 | 62 | 87 | 0 |
| `layer-b.txt` | 77 | 12 | 65 | 0 |
| `layer-c.txt` | 62 | 17 | 45 | 0 |
| `layer-d.txt` | 35 | 11 | 23 | 1 |
| `layer-e.txt` | 6 | 2 | 4 | 0 |
| total | 502 | 162 | 339 | 1 |

By prefix and layer:

| Prefix | A | B | C | D | E | all |
|---|---|---|---|---|---|---|
| `T-` | 67 | 3 | 10 | 9 | 0 | 89 |
| `S-`, `I-` | 27 | 3 | 9 | 7 | 0 | 46 |
| `R-` | 37 | 15 | 17 | 12 | 0 | 81 |
| `V-` | 31 | 5 | 12 | 5 | 0 | 53 |
| `M-` | 48 | 32 | 13 | 0 | 0 | 93 |
| `L-` | 18 | 0 | 0 | 0 | 0 | 18 |
| `N-`, `X-` | 94 | 19 | 1 | 2 | 6 | 122 |

Layer A, by the family of the rule that a test is about (for a refusal, the rule that refuses;
for an acceptance, the rule that its note names):

| Family of the rule a layer-A test is about | Tests |
|---|---|
| LX | 11 |
| GR | 13 |
| NL | 28 |
| SP | 60 |
| TY | 149 |
| HO | 16 |
| EV | 14 |
| GU | 5 |
| CT | 8 |
| RM | 3 |
| FN | 9 |
| SX | 6 |

By the rule that refuses:

| Rule that refuses | layer A | all layers |
|---|---|---|
| CT1 | 1 | 1 |
| CT2 | 4 | 4 |
| CT6 | 1 | 1 |
| EN1 | 0 | 2 |
| EV1 | 3 | 3 |
| EV2 | 1 | 1 |
| EV3 | 3 | 3 |
| EV4 | 0 | 1 |
| EV5 | 2 | 2 |
| FN1 | 1 | 1 |
| FN3 | 1 | 1 |
| FN5 | 5 | 5 |
| GL1 | 0 | 1 |
| GL2 | 0 | 3 |
| GL3 | 0 | 18 |
| GL4 | 0 | 6 |
| GR | 1 | 1 |
| GR2 | 1 | 1 |
| GR6 | 6 | 6 |
| GU2 | 5 | 5 |
| HO1 | 2 | 2 |
| HO2 | 2 | 2 |
| HO3 | 2 | 2 |
| HO5 | 2 | 2 |
| LN2 | 0 | 3 |
| LN3 | 0 | 1 |
| LX2 | 1 | 1 |
| LX3 | 1 | 1 |
| LX4 | 1 | 1 |
| LX5 | 1 | 1 |
| LX7 | 1 | 1 |
| LX8 | 1 | 1 |
| NL1 | 1 | 1 |
| NL2 | 1 | 1 |
| NL3 | 4 | 7 |
| NL6 | 13 | 13 |
| NL9 | 4 | 6 |
| NL10 | 1 | 1 |
| OR2 | 0 | 1 |
| OR3 | 0 | 3 |
| OR4 | 0 | 2 |
| OR8 | 0 | 2 |
| OR9 | 0 | 1 |
| RM1 | 3 | 3 |
| SC1 | 0 | 1 |
| SC2 | 0 | 1 |
| SC3 | 0 | 4 |
| SC4 | 0 | 1 |
| SC5 | 0 | 17 |
| SP3 | 4 | 5 |
| SP4 | 8 | 9 |
| SP5 | 0 | 2 |
| SP6 | 4 | 4 |
| SP8 | 3 | 5 |
| SP9 | 2 | 2 |
| SP10 | 1 | 1 |
| SP11 | 6 | 7 |
| SP12 | 6 | 7 |
| SX2 | 2 | 2 |
| SX3 | 1 | 5 |
| SX4 | 2 | 2 |
| SX6 | 0 | 30 |
| SX8 | 0 | 5 |
| SX9 | 0 | 5 |
| TY1 | 1 | 1 |
| TY2 | 7 | 7 |
| TY4 | 4 | 4 |
| TY5 | 8 | 11 |
| TY6 | 5 | 7 |
| TY7 | 36 | 37 |
| TY8 | 17 | 19 |
| TY10 | 1 | 1 |
| TY13 | 6 | 9 |
| TY15 | 1 | 2 |

## Not tested here

- **Not accept-or-refuse facts.** Trees, sites and parts, the roles that compute, the fields of
  `Run` and the stages are not tests of this format. An implementation is to print them; a
  format for them is not designed.
- **The programs and modules of the later layers.** The programs of the later layers (`fri`,
  `stark`, `product_check`, `spot_check`, `mldsa_signature`, `request_dispatch`,
  `variants_example`) have no `M-` tests, and the modules of layers C and D and the kinds of
  `zkc::polynomial` have no `L-` tests: they are carried and are to be rewritten with their
  layers.
- **How the tests are run.** `../LANGUAGE.md` §11.
