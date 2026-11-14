# Unicode data

The pinned Unicode data from which the lexer's tables are generated.
[manifest.json](manifest.json) names the Unicode version, the upstream file of the Unicode
Character Database behind each file of the version's directory with its SHA-256 hash, and the
licence. The data is unmodified and distributed under [Unicode License v3](LICENSE.txt).

`../scripts/generate_unicode_tables.py` checks each file against its hash and writes
`Zkc/Frontend/Syntax/UnicodeData.lean`: the identifier classes, the canonical combining classes
and the decompositions and compositions that normalization to NFC needs. The host's Unicode
tables are not used. With `--check` it compares the generated module with the one in the tree.
Which characters an identifier, an operator and a delimiter may have is a rule of the
[reference of the language](../../../language/LANGUAGE.md), not of this directory.

To move to another Unicode version, add its directory, update the manifest, and run the
generator.
