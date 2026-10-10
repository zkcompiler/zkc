# Source text and names

This native contract defines source bytes, identifiers and notation tokens.
[Capture](definitions.md#capture-and-names) owns module admission and identity;
[notation](notation.md) owns the meaning of admitted operator tokens.

## Unicode profile

Source is valid UTF-8. Capture retains the exact supplied bytes and rejects
invalid UTF-8 before lexing. Tokens, source spans, identifier lengths and source
limits use UTF-8 bytes, not scalar counts, grapheme counts or display columns.
Tokenization is independent of imports and the visible notation environment.

Every source identifier uses the Unicode 17.0.0 profile:

| Position | Admitted scalars |
|---|---|
| First | `XID_Start` or ASCII underscore |
| Continuation | `XID_Continue` or subscript digits U+2080 through U+2089 |
| Exclusions at either position | `Default_Ignorable_Code_Point` and `Bidi_Control` |

The whole identifier must already be NFC. Admission checks profile membership
before NFC; it rejects a non-NFC spelling rather than rewriting it. There is no
NFKC or case folding, transliteration, or merging of visually similar names.
`beta_2` and `β₂` are distinct identifiers; the subscript is part of the name,
not indexing or exponentiation. A Unicode 18-only character remains outside the
profile even when a normalization library recognizes it.

These rules apply to module path segments, declarations, fields, alternatives,
parameters, participants, setup slots and Entry selectors, including names
admitted through capture and external source interfaces. A qualified name joins
nonempty identifier segments with `::`. Exact admitted bytes determine equality.
The compiler never normalizes a source buffer, qualified path or capture key.

Decimal literals remain ASCII. Quoted source strings keep their printable ASCII
policy, including strings naming backend operations and domains. Comments begin
with `//` and may contain valid UTF-8; their contents are not identifier-normalized.
Default-ignorable and bidi-control characters outside comments are illegal code
tokens and never whitespace. This is not a whole-buffer comment-content ban or
a guarantee against visually confusable identifiers.

Keywords remain reserved except in explicitly contextual positions. `run`,
`proof`, `operator`, `as`, `primitive`, `notation`, `infixl`, `infixr`, `infix`,
`prefix` and `postfix` have special meanings in their declaration or import
grammar; elsewhere they remain available as ordinary names.

## Mathematical tokens

A custom operator token is exactly one non-ASCII scalar with Unicode general
category `Sm`. It must already be NFC and must not be an identifier character,
default-ignorable character or bidi control. Adjacent symbols form separate
tokens. Existing ASCII tokens, multi-character operators and punctuation retain
their fixed grammar. Word operators, arbitrary ASCII strings, multi-scalar
symbols and combining-mark operators are not admitted. A letter such as `ᵀ`
does not become an operator; use a named function.

`∑` and `∏` are reserved for [finite reduction bindings](notation.md) and cannot
be declared as ordinary operators. Their spelling alone selects no reducer; a
visible library or local `reduction` binding supplies the callable.

Custom delimiters are non-ASCII matching pairs from Unicode 17
`BidiBrackets.txt`. The opener has category `Ps` and the closer `Pe`; both are
NFC and outside identifier, default-ignorable and bidi-control classes. The
generated admitted table fixes the pair; authors cannot choose another closer.
Core `()`, `[]`, `{}`, `<>`, commas and statement punctuation remain reserved.
One opener has one active closer and hole count. A legal token without visible
notation is a visibility error, distinct from an illegal Unicode token.

## Pinned data and normalization

The [source-name manifest](../../../support/unicode/manifest.json) owns the
profile, explicit additions/exclusions, normalizer versions and SHA-256 hashes
of the raw UCD inputs. C++ and Rust derive their classification tables from
these inputs; neither uses locale, host Unicode categories or the normalizer's
character repertoire. Generation checks the raw hashes and works offline.
The manifest, generator and raw inputs contribute to compiler build identity.

NFC uses utf8proc 2.12.0 in C++ and `unicode-normalization` 0.1.25 in Rust.
The pinned source repertoire is checked first, so the C library's newer Unicode
data does not expand source admission. Input byte limits apply before invoking
normalization; generated symbols, nominal preimages and generated Rust names
have separate expansion bounds. The
[SDK guide](../../../compiler/README.md#installed-package-discovery) defines the
external utf8proc dependency without adding MLIR to Language consumers.

Source admission does not widen native operation/domain identities, executable
site IDs, backend service strings, asset keys or hashes. Those retain their
existing ASCII grammars. [Translation](translation.md#source-and-native-names)
defines the explicit encoding at the source/native boundary.
