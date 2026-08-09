//===- SignatureEncoding.h - Canonical declaration bytes --------*- C++ -*-===//
//
// The canonical form of a rule or binding declaration, and the content digest
// taken over it.
//
// A declaration encodes exactly the fields its own semantics reads.  Rule
// well-formedness already forces every field that is inactive for a variant to
// its default (docs/spec/soundness.md §7.1), so omitting those fields loses
// nothing and keeps the digest from depending on unread payload.  Two
// declarations that evaluate identically therefore have the same digest.
//
// A declaration's own revision is excluded from its preimage, because the
// revision is that digest.  A binding's preimage keeps the rule reference
// whole, revision included, since naming an exact rule revision is what a
// binding is for.  Annotations are not part of a declaration at all
// (Signature.h), so no editorial change can move a digest.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SIGNATUREENCODING_H
#define ZKC_SOUNDNESS_SIGNATUREENCODING_H

#include "zkc/Soundness/SoundnessCatalog.h"
#include "zkc/Soundness/SoundnessKernel.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

#include <string>

namespace zkc::soundness {

/// The canonical document for one rule, excluding its own revision.
llvm::json::Value encodeRuleDocument(const SoundnessRule &rule);

/// The canonical document for one binding, excluding its own revision.
llvm::json::Value encodeBindingDocument(const RuleBinding &binding);

/// The canonical document for the closed schema tables a signature declares.
llvm::json::Value encodeSchemaContextDocument(const SchemaContext &schemas);

/// `sha256:` reference over the rule document under the rule domain.  This is
/// the value a well-formed rule carries as its own source revision.
llvm::Expected<std::string> ruleDigest(const SoundnessRule &rule);

/// `sha256:` reference over the binding document under the binding domain.
llvm::Expected<std::string> bindingDigest(const RuleBinding &binding);

/// The canonical document for a whole signature's executable content.
llvm::json::Value encodeSignatureDocument(const SoundnessCatalog &catalog);

/// `sha256:` reference over that document.  This is what "the analysis under
/// signature X" names.
///
/// It covers the schemas, the rules and the bindings, and nothing else.
/// Annotations are excluded for the same reason they are excluded from a
/// declaration digest: correcting a citation must not make an artifact's
/// analysis a different analysis.  The record beside the declarations is
/// versioned by the file that carries it, which is why the two are separable
/// (docs/spec/versioning.md).
llvm::Expected<std::string> signatureDigest(const SoundnessCatalog &catalog);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SIGNATUREENCODING_H
