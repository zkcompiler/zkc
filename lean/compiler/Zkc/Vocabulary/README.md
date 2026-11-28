# Vocabulary

The standard vocabulary of the core: the keys of its nominal types, its rows and its laws, and
their table. It is the library `ZkcVocabulary` of the package `zkc_compiler` (`lean/compiler`),
in the namespace `Zkc.Vocabulary`. It imports only the core (`Zkc.Core`), `Init` and `Std`, and
the core does not import it. Each file is a Lean module whose definitions are exposed. The root
module, `Zkc/Vocabulary.lean`, imports every module of the library. `lake exe zkc-audit` audits
it as it audits the core: the axioms of every declaration, the replay of every declaration
through the kernel, and the rules on imports.

A key says everything that tells one type, row or law from another: which field or group, the
elements of a field or those that are not zero, the element and the size of a collection, how
many bytes a hash gives, the type that a law is uniform on. So nothing stands beside a key in a
program, and a key at which a row has no instance has no signature.

| Module | Holds |
|---|---|
| `Keys` | the fields (KoalaBear, its extension of degree four, the scalar field of BLS12-381) with their numbers, and the groups of BLS12-381; the keys of the nominal types (the elements of a field, those that are not zero, the elements of a group); what the group family is at (`Atom`) and what the collection family is at (`Element`); the keys of the rows (of a field, at all its elements or at those that are not zero; of a group; of collections, of a size or of any length; the hashes; the pairing) and of the laws (the uniform one on a type) |
| `Standard` | the table: the signature and the kind of each row at its key, none where the row has no instance there; the literals of each nominal type; the signature of the uniform law on the types that TY15 lists (`bool`, a `fin` of a bound that is not zero, the elements of a field, those that are not zero, the elements of a group, a tuple of such types, and a sized sequence of one or of size zero), and on no other: not `nat`, a sequence of any length, a record or a variant; the law that the domain row of each restricted row decides it (`decided`); and the vocabulary `standard` |
| `Project` | the vocabulary of a package: the name and the static arguments of a primitive that a project binds, its signature over the standard nominal types and the project's own, the bindings of a package, and the standard vocabulary linked with them. A proof about a package reads its vocabulary from here |
| `Encoder` | canonical injective `Core.VocabEncoder` instances for `standard` and `Project.Bindings.vocabulary`, binding each linked project row's canonical primitive signature into its key encoding so distinct project signatures produce distinct proof identities |

## Tests

The tests of the vocabulary are the library `ZkcVocabularyTests` (`Zkc/Tests/Vocabulary/`),
whose checks the kernel runs when they are built; the tests of the core need them, so
`lake test` builds them too, and `lake exe zkc-audit` audits them as it audits the tests of the
core. They state what the reference says, not what the table computes: every expected
signature is written out from the reference's types.

- `Table.lean`: the signature of each row of the field, group and collection families at a
  prime field, at the extension, at a group with a generator and at the target group, at all
  elements and at those that are not zero, of a size and of any length, and at an element that
  is a sized collection; the hashes and the pairing; each place where the reference gives a row
  no instance; the literals of each nominal type; the types at which the uniform law is a law
  and those at which it is not (TY15).
- `Core.lean`: functions over the vocabulary through the core: a row of each family
  elaborated, a key without an instance refused by the rule `row`; the restricted row
  `field.nonzero` accepted after a guard on `field.is_nonzero` of its operand (`x != 0`, and
  `x == 0` negated) and refused without it, through the check of facts; a literal of each
  kind of nominal type elaborated or refused.
- `Outcome.lean`: functions written by names over the standard vocabulary, at the field
  KoalaBear, elaborated and their facts checked through the core, and their outcome: refused by
  elaboration, refused by the check of facts with the whole refusal, or accepted.
- `Ranges.lean`, `Slices.lean`, `Loops.lean`, `Conversions.lean`, `Accepted.lean`, `Encoder.lean`: the
  conformance cases of the reference that a function over the standard vocabulary expresses,
  each by its identifier, with the outcome that the case says: the ranges of arithmetic, of
  conditions, of `and` and of `nonzero` (`Ranges`); reads and slices, at the instance that a
  case names or at its default instances (`Slices`); loops, comprehensions, collected values,
  linear records and empty types (`Loops`); conversions by a fact to `nonzero<F>` and to an
  `index<s>` that a row takes (`Conversions`); accepted cases of other rules whose functions
  apply operations with a domain (`Accepted`); and canonical injectivity and cross-signature
  separation checks for the standard and linked vocabulary encoders (`Encoder`).
