# Source claims

**Surface version 0 (provisional).** This document records the implemented
author-facing syntax for experimentation. Draft 3.7 has not settled that
surface. The versioned request object and schema are the cross-component
contract; syntax decisions below may change without assigning new security
meaning to a request.

Source claims are versioned wire requests for the optional Lean claim resolver.
The native frontend checks syntax and structural references. It supplies no
security meaning, proof, registry admission, or certification status. A successful
`language-check` means native checking succeeded; it does not mean a claim is
certified. Missing definitions, unregistered identifiers or versions, and missing
proofs are distinguished by the Lean resolver. In particular an unknown version
is exported exactly, never interpreted as version zero.

## Declarations

A named block at module scope attaches claims to one configured proof or closed protocol subject:

```zkc
spec SchnorrClaims for Demo {
  know: knowledge@0(target.knowledge,
    model=models.fiat_shamir@0(level=levels.bytes,statement=statements.fixed,
      oracle=oracles.random@0(construction.provider),queries=2^64),
    accept=out.accepted,stage=executable_bytes,
    guarantee=guarantees.forking@0(challenges=cardinality(G.Scalar),
      extractor=extractors.response_difference@0(),cost=prover_runs(2)));
}
verify SchnorrClaims.know=fs.forking@0();
```

`Demo` resolves using the containing module's ordinary declaration environment,
including qualified paths and imports. It must name a proof declaration or a
closed protocol specialization. For example, `spec InteractiveClaims for
Schnorr<G> { ... }` attaches to that checked protocol and its normalized static
arguments. Equivalent argument spellings match; different specializations do
not. Static arguments use ordinary source checking, with no generic claim
binders. Authored Host Entry functions are not protocol subjects: their control,
outputs and execution count need a separate correspondence before a component
claim can be transported to them.
Blocks and labels are unique within their containing module and block,
respectively. `verify Block.label` selects a local block; each claim has at most
one method plan. The method must be a versioned registry application. Its name
is data; it is never translated to an unchecked Lean declaration string. A
missing plan is legal and does not change the request.

For the built-in knowledge model, `extractor=extractors.response_difference@0()`
selects the registered componentwise response-difference experiment. Version 0
uses that same entry when this argument is omitted. The admitted author library
must provide its typed profile; an unknown extractor/version fails resolution,
and an undefined profile remains incomplete. The profile fixes the transcript
reading, witness layout, challenge site, and fallback sampling before `verify`
selects a proof method. `cost=prover_runs(2)` is the replay guarantee form, not a
checked running-time bound. See the [formal verification contract](../../../lean/docs/spec/verification.md).

An Entry with a configuration block may instead put `spec { ... }` immediately
after that configuration's closing brace. The block's name for `verify` is the
Entry's name:

```zkc
proof Demo=Run {
  prover P;verifier V;public{x};accept accepted;target claim;construction authored;
} spec {
  sound: soundness@0(target.claim,model=models.example@0(),
    accept=out.accepted,stage=executable_bytes,error=0);
}
verify Demo.sound=methods.example@0();
```

Inline and external forms normalize to identical request objects. Attachments
retain their different origins. This Entry form is distinct from the existing
protocol-header `spec { target ... }` construct, which continues to retain
relation applications and acceptance decisions. Claims do not replace, rewrite,
or add executable checks to that construct.

This version deliberately accepts closed subjects without generic claim binders.
The first positional argument has two explicit alternatives:

- `target.NAME` selects exactly one retained target clause on the Entry's
  protocol. Input/output/continuation clauses are not targets. If the proof
  Entry selects a target, a claim must select that same clause.
- `imported_language(languages.guess@0())` supplies exactly one positional
  versioned registry application. The unversioned wrapper accepts no named or
  additional arguments. This alternative requires a proof Entry and **every
  retained clause list in its closed original unit to be empty**. It rejects
  input, output, target and continuation/residual clauses, including those on
  child protocols reached through unlabelled calls or loop bodies. Empty
  specification blocks are allowed; unrelated declarations outside the closed
  unit do not constrain the claim.

For example, a targetless guessing verifier can declare:

```zkc
spec GuessClaims for Proof {
  sound: soundness@0(imported_language(languages.guess@0()),
    model=models.fiat_shamir@0(level=levels.bytes,statement=statements.fixed,
      oracle=oracles.random@0(construction.provider),queries=Q),
    accept=out.accepted,stage=executable_bytes,
    charge=per_site(sites.challenge,1/cardinality(Fr)));
}
```

Language identifiers, versions and argument expression trees are preserved,
including unknown extension identifiers and versions. Lean's typed registry
fixes the imported language independently of evidence; the native frontend
assigns no security meaning to it. The example registry application and charge
remain requests requiring that resolution and a proof. The native structural
check mirrors Endpoint `ImportedLanguage.noClauses`, namely
`art.original.contracts.all (fun contract => contract.clauses.isEmpty) = true`.
It runs after Entry specialization over every emitted protocol, rather than
over only the root or every source declaration. It is also repeated on claim
inspection. It does not replace Lean's check on the actually admitted unit.

Neither alternative admits arbitrary relation applications in claim text or
fabricates a retained clause for a targetless subject.

## Request envelope and expressions

Every property application has one positional target, required named `model`,
`accept` and `stage` arguments, and exactly one quantity argument:

| Argument | Native wire contract |
|---|---|
| `model` | Versioned registry application; model argument schemas belong to Lean |
| `accept` | `out.port` with optional product field path; Boolean result, same selector as the retained target and proof Entry where present; imported-language claims require the checked proof Entry's selector |
| `stage` | `interactive`, `compiled_ideal` or `executable_bytes`; protocol subjects support `interactive` |
| `error` | Scalar expression, including completeness failure bounds when a registered property defines that meaning |
| `charge` | `per_site(sites.path, expression)` or a nonempty list of these with distinct paths |
| `guarantee` | Versioned guarantee application, such as `guarantees.forking@0(...)` |
| `capabilities` | Optional list of distinct versioned capability applications; defaults to `[]` |
| `parameters` | Optional expression carrying property-specific arguments; defaults to `null` |

Unknown envelope fields, duplicate named arguments at any depth, multiple
quantities and positional arguments following named arguments are refused.
Schemas of arguments inside registered applications remain extensible and are
validated by Lean; the native compiler cannot decide whether an arbitrary
extension's named parameter is meaningful. No native list of property, model or
method names constrains extension. The extension fixture exercises a proposed
`user.view_equal@7` property, `user.observer@3` model and
`user.prove_view@11` method; registering their typed meanings belongs to the
Lean integration.

A version is an explicit canonical unsigned 32-bit decimal following `@`.
Versioned identifiers must be applied, even with no arguments. Expressions are
finite trees of canonical arbitrary-size natural literals, identifier paths
(`.` or `::`), applications with positional and named arguments, lists, unary
minus and binary `+`, `-`, `*`, `/`, `^`. Multiplication/division bind above
addition/subtraction; exponentiation binds above multiplication and is left
associative. Parentheses group expressions. There are no strings, floats, raw
Lean expressions, arbitrary JSON objects or native evaluation of these terms.
References to subject parameters and model budget symbols remain proposals for
typed Lean resolution against the admitted subject. Definition-dependent numeric
subtraction and division meanings are likewise owned by the resolver.

The exact unqualified, unversioned application `cardinality(T)` is a
mathematical builtin with one positional domain type reference. The frontend
resolves `T` using ordinary type/name resolution in the claim block's owning
source scope, including imports, visibility, transparent aliases and associated
types. Both `G.Scalar` and `G::Scalar` select the group's associated scalar
domain. The subject protocol's generic parameter names are not introduced into
that lexical scope. Selecting `Run<OtherField>` does not change what an unrelated
`Fr` in the claim owner's module names, and a missing `Fr` never selects a
same-spelled declaration from another module. Conflicting imports remain an
ordinary source import error.

Export substitutes the selected closed Entry's actual type bindings into the
resolved type and requires a closed nominal catalog domain. It writes that
domain's canonical identity into the existing reference expression. For example,
if `Fr=field("bls12-381.fr")` and `G=group("bls12-381.g1")`, then `cardinality(Fr)`,
`cardinality(G.Scalar)` and transparent aliases of either export as:

```json
{"kind":"application","name":"cardinality","version":null,"arguments":[
  {"label":null,"value":{"kind":"reference","name":"bls12-381.fr"}}
]}
```

This reference is a resolved nominal domain identity within this builtin, not
a freely assignable numeric variable. The canonical expression belongs to
`request` identity and strict comparison. The checked authored expression keeps
its spelling, span and resolved `Type` metadata; source attachments identify
that captured spelling. Normalization applies to explicit builtin occurrences
throughout property, model, quantity, capability, parameter and method trees.
`cardinality@19(Missing,x=7)` and `user.cardinality@19(Missing)` remain registry
extension applications with their names, versions and arguments preserved. An
explicit unversioned `cardinality` nested inside an extension still follows the
builtin rule. Malformed versions follow the ordinary expression syntax rules.

Native resolution binds a domain name without evaluating cardinality, proving
finiteness or interpreting a bound, probability or property. Lean must match the
canonical identity to the actual admitted domain interpretation, derive field
cardinalities there and refuse unsupported carriers. A group or other catalog
domain name can be bound natively without thereby receiving a Lean cardinality
meaning. Numeric evidence cannot choose a different size for a source alias.
Lexical resolution alone does not establish that a domain occurs in the admitted
subject; that match is a separate Lean obligation. Source/import correspondence
remains explicit and IR-relative.

A proof Entry's verifier supplies the participant component of `accept`; the
selected port must be available there. A run Entry requires an unambiguous
participant component. Field paths use the same logical projection rules as
retained specification selectors.

Sites use existing `#[site(label)]` annotations. `sites.challenge` selects the
unique authored static site. `sites.wrapper.challenge` traverses an explicitly
labelled protocol call named `wrapper`. Loops retain static occurrences, not
unrolled execution events. Unlabelled calls do not export their descendants.
Site resolution is exact and bounded, and ambiguous paths are refused. Each
`site_bindings` record includes `native_path`, the array of
`nativeSiteName(label, 0)` values for labelled calls followed by the selected
leaf. Query and call sites identify one native operation; aggregate message
labels identify their native leaf family and require admitted layout resolution. A site
binding proposes an occurrence; Lean must check its kind, construction mapping,
and suitability for the registered quantity. Exported membership alone does not
establish a charge theorem.

## Export and comparison API

```sh
build/source-claims/zkc-compile language-check --source-format=zkc \
  --entry=claims::Demo --source-claims \
  --module=claims=compiler/test/fixtures/source-claims/schnorr.zkc
```

The normal `zkc.source-check/0` response gains `source_claims`, a
`zkc.source-claims/0` object with `registry_resolution: "deferred-to-lean"`. `--source-claims` requires an explicit `--subject=NAME` or proof `--entry=NAME`
and is available only on `language-check`. `--subject` is mutually exclusive with
`--entry` and `--entry-kind`. It selects the protocol/proof directly through
`closeSubject`, then uses the same checked original, interface and admission
export. The check response has `scope: "subject"`. Ordinary `--entry` keeps its
Host-function behavior even when its selector names a protocol.

Only matching subject blocks are emitted. Proof aliases retain their own claim
ownership; a proof does not inherit a protocol subject's claims. A protocol
subject's wire `entry` identifies its actual closed Run deployment. Its authored
selector is attachment/provenance, not a replacement for admitted identity.
Other inspection options compose with source-claim export. Raw interface bytes
are retained exactly; parsing and reserializing JSON is not identity preservation.

The [JSON schema](source-claims.schema.json) describes exact output shapes.
All objects reject unknown fields; native comparison also rejects duplicate
keys, noncanonical numeric tokens and any mismatch against the checked source.
JSON object order and whitespace are irrelevant to comparison. Natural
expression values are decimal strings, avoiding floating point truncation.

The APIs are:

- `closeSubject(const CheckedProject &, StringRef, const Limits &)` in
  `zkc/Language/Project.h`: checks a closed protocol/proof selector and refuses
  Host Entry functions, reusing ordinary resolution and closure.
- `inspectSourceClaims(const ClosedEntry &, const Limits &)` in
  `zkc/Language/Inspection.h`: native wire claims without an admission reference.
- `exportSourceClaims(const CheckedOriginal &, const Limits &)` in
  `zkc/Compiler/SourceClaims.h`: the same export with exact original/interface
  references in `admission`.
- `checkSourceClaims` overloads for those two types: strict comparison with that
  API's complete expected export. This is a comparison API, not a standalone
  admission reader for arbitrary requests.

The export separates:

| Field | Role |
|---|---|
| `admission` | Exact SHA256 of original bytes and interface JSON, native original identity, capture/installation identities and protocol symbol |
| `claims[].request` | Subject Entry and stage, property/version/parameters, model expression, retained target reference or imported language, logical acceptance, quantity and capabilities |
| `claims[].attachment` | Module, block declaration, label, AST node address and source byte range |
| `claims[].method` | Optional versioned method application; never part of request meaning |
| `claims[].site_bindings` | Source origins and native label paths for every referenced request site; separate from request meaning |

The retained target reference remains exactly
`{protocol:<closed protocol symbol>, clause:<clause array index>, name:<clause name>}`.
Its relation formula and operands are read from that exact original and its
admitted structured export, not reconstructed from claim text. The imported
alternative is exactly `{protocol:<closed protocol symbol>, language:<versioned
registry application expression>}` with no `clause` or `name` fields. The schema
uses strict `oneOf` object alternatives, each rejecting unknown fields. Native
comparison binds the complete language application, protocol and acceptance to
the checked source; it rejects mixed alternatives and duplicate keys.
`request.subject.stage` uses the frozen wire spellings `interactive`,
`compiled-ideal` and `executable-bytes`.

`attachment.node` is the version-zero address
`{kind:"source-claim", owner:<qualified declaration>, block:<ordinal>, claim:<ordinal>}`.
Ordinals index claim blocks in their owning module or Entry, then claims in the
block. This address is deterministic within the parsed source snapshot and
survives a claim-label rename or whitespace edits; inserting/reordering nodes
requires renewed attachments. `source` uses UTF-8 byte offsets in the named
captured module. Node addresses and source spans are not semantic identity or
a proof of source-to-IR correspondence. A future source AST exporter must use
this scheme or explicitly map it, rather than interpreting it as a global UUID.

To join the admitted structured export, emit the same Entry with
`language-emit`, then run `protocol-structured ORIGINAL.mlir
--symbol=PROTOCOL_SYMBOL`. The claim admission reference's `original_sha256`
and `protocol_symbol` match elements 2 and 3 of that structured export.
The parent must still compute and bind the digest of the actually admitted raw
unit, check the proposed clause or imported-language/selector/site mapping, resolve typed registry
applications, and attach compiled artifact digests for the selected stage.
The original-byte digest is not the admitted Lean unit digest.

Claims are not added to executable MLIR, the native language interface or program
formats. Existing source capture and diagnostic-location identities still track
the full captured source; changing a claim can change those source identities.
Renaming a label does not change `request`. A receipt's actual subject and
semantic dependency identity must be checked before reuse. Until source
correspondence is proved separately, receipts remain IR-relative and retain
`source.correspondence`.

## Diagnostics and limits

| Identifier | Refusal |
|---|---|
| `source.claim.syntax` or existing `source.syntax` | Malformed claim expression or punctuation |
| `source.claim.identifier` | Missing/malformed explicit registry application/version |
| `source.claim.field` | Unknown/missing envelope field, ambiguous quantity or malformed charge/capability shape |
| `source.claim.duplicate-field` | Duplicate named argument |
| `source.claim.duplicate-label` | Duplicate block or claim label |
| `source.claim.subject` | Missing subject or a subject that is not an Entry |
| `source.claim.target` | Missing/different retained target, arbitrary relation application, malformed imported-language wrapper, imported language on a run Entry, or any retained clause in the imported subject's closed unit |
| `source.claim.accept` | Missing, non-Boolean or different acceptance selector |
| `source.claim.domain` | Malformed unversioned `cardinality`, missing/private/non-domain type reference, or a resolved domain that cannot close under the selected Entry's bindings |
| `source.claim.site` | Unexported/ambiguous site |
| `source.claim.stage` | Invalid native stage selection |
| `source.claim.verify` | Missing claim or duplicate method plan |
| `source.claim.export` | Strict export comparison mismatch or malformed JSON |
| `source.limit` | Work, depth, source or output ceiling exceeded |

Registry definition absence and unsupported proof methods are not native name
resolution errors. The Lean resolver must report their definition/attempt states
separately. Existing source/token/expression/work limits bound parsing, retained
claims, site traversal and output. Export returns complete bounded JSON or an
error, never a partial document.
