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
| `Standard` | the table: the signature and the kind of each row at its key, none where the row has no instance there; the literals of each nominal type; the signature of the uniform law on a type that is finite and has a value; the law that the domain row of each restricted row decides it (`decided`); and the vocabulary `standard` |
