#include "LayoutReader.h"
#include "zkc/Language/Names.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language::detail {
namespace {
using K = syntax::Kind;
using Id = syntax::NodeId;
using Position = NotationDescriptor::Position;
using Association = NotationDescriptor::Association;

syntax::Budget budget(const Work &work) {
  syntax::Budget result;
  result.bytes = work.limits.fileBytes;
  result.tokens = work.limits.tokens;
  result.tokenBytes = work.limits.tokenBytes;
  result.identifierBytes = work.limits.identifierBytes;
  result.depth = work.limits.parseDepth;
  result.work = work.limits.work - work.used;
  return result;
}
Error acceptSnapshot(const syntax::Snapshot &tree, Work &work) {
  if (auto error = work.charge(tree.workUsed()))
    return error;
  if (tree.status() == syntax::Status::ResourceExhausted)
    return failure("source.limit", "layout parsing resource limit exceeded");
  if (!tree.diagnostics().empty()) {
    const auto &d = tree.diagnostics().front();
    return failure(d.code, d.message, d.primary, d.related);
  }
  if (tree.status() != syntax::Status::Complete)
    return failure("source.limit", "layout parsing did not complete");
  return Error::success();
}

} // namespace

Error expandLayoutSections(std::vector<SyntaxDeclaration> &modules,
                           Work &work) {
  std::function<Error(SyntaxDeclaration &, ArrayRef<SyntaxParameter>,
                      std::vector<SyntaxDeclaration> &)>
      expand;
  expand = [&](SyntaxDeclaration &source, ArrayRef<SyntaxParameter> inherited,
               std::vector<SyntaxDeclaration> &output) -> Error {
    if (auto error = work.charge(
            inherited.size() + source.parameters.size() + 1, source.span))
      return error;
    std::function<Error(const SyntaxType &)> chargeType =
        [&](const SyntaxType &type) -> Error {
      if (auto error =
              work.charge(type.name.size() + type.labels.size() + 1, type.span))
        return error;
      for (const auto &argument : type.arguments)
        if (auto error = chargeType(argument))
          return error;
      return Error::success();
    };
    for (const auto &parameter : inherited)
      if (auto error = chargeType(parameter.constraint))
        return error;
    if (source.section) {
      if (!source.imports.empty() || !source.operators.empty())
        return failure("source.section",
                       "section groups declarations; put imports and notation "
                       "in the enclosing module",
                       source.span);
      std::vector<SyntaxParameter> parameters(inherited.begin(),
                                              inherited.end());
      parameters.insert(parameters.end(), source.parameters.begin(),
                        source.parameters.end());
      for (auto &child : source.members)
        if (auto error = expand(child, parameters, output))
          return error;
    } else {
      source.parameters.insert(source.parameters.begin(), inherited.begin(),
                               inherited.end());
      std::vector<SyntaxDeclaration> members;
      for (auto &child : source.members) {
        if (child.section) {
          std::function<void(SyntaxDeclaration &)> moveFormal =
              [&](SyntaxDeclaration &group) {
                for (auto &formal : group.formalSyntax)
                  source.formalSyntax.push_back(std::move(formal));
                group.formalSyntax.clear();
                for (auto &nested : group.members)
                  if (nested.section)
                    moveFormal(nested);
              };
          moveFormal(child);
        }
        if (auto error = expand(child, {}, members))
          return error;
      }
      source.members = std::move(members);
      output.push_back(std::move(source));
    }
    return Error::success();
  };
  std::vector<SyntaxDeclaration> expanded;
  for (auto &module : modules)
    if (auto error = expand(module, {}, expanded))
      return error;
  modules = std::move(expanded);
  return Error::success();
}

Expected<SyntaxDeclaration> parseLayoutHeaders(const SourceBuffer &source,
                                               SourceId id,
                                               CheckedStorage &storage,
                                               Work &work) {
  auto tree =
      syntax::parseHeaders(source::Revision(source), id, budget(work),
                           work.cancellation.value_or(source::Cancellation{}));
  if (auto error = acceptSnapshot(tree, work))
    return std::move(error);
  auto &tokens = storage.tokens[id.index];
  for (auto token : tree.tokens()) {
    if (token.synthetic() && token.kind != syntax::TokenKind::End)
      continue;
    TokenKind kind;
    switch (token.kind) {
    case syntax::TokenKind::Word:
      kind = TokenKind::Word;
      break;
    case syntax::TokenKind::Number:
      kind = TokenKind::Decimal;
      break;
    case syntax::TokenKind::String:
      kind = TokenKind::String;
      break;
    case syntax::TokenKind::Comment:
      kind = TokenKind::Comment;
      break;
    case syntax::TokenKind::Space:
    case syntax::TokenKind::Newline:
      kind = TokenKind::Whitespace;
      break;
    case syntax::TokenKind::End:
      kind = TokenKind::End;
      break;
    default:
      kind = TokenKind::Punctuation;
      break;
    }
    Span span{id, token.begin, token.end};
    if (auto error =
            work.count(work.tokens, work.limits.tokens, "token count", span))
      return std::move(error);
    tokens.push_back({kind, span});
  }
  storage.layoutHeaders[id.index] = tree;
  return LayoutReader(tree, tokens, work).headers();
}
Error parseLayoutBodies(SourceId id, ArrayRef<BodyParseScope> scopes,
                        CheckedStorage &storage, Work &work,
                        std::vector<Diagnostic> *recovery) {
  syntax::Environments environments;
  syntax::Environment defaults;
  for (const auto &scope : scopes) {
    syntax::Environment environment;
    for (const auto &[_, item] : *scope.environment)
      environment.notation.push_back(*item.descriptor);
    if (scope.module->span.begin == 0 &&
        scope.module->name == (*storage.sources)[id.index].module)
      defaults = std::move(environment);
    else
      environments.emplace(scope.module->span.begin, std::move(environment));
  }
  auto tree =
      syntax::parseBodies(*storage.layoutHeaders[id.index], std::move(defaults),
                          std::move(environments), budget(work),
                          work.cancellation.value_or(source::Cancellation{}));
  storage.layoutBodies[id.index] = tree;
  if (recovery && tree.status() == syntax::Status::Partial) {
    if (auto error = work.charge(tree.workUsed()))
      return error;
    recovery->insert(recovery->end(), tree.diagnostics().begin(),
                     tree.diagnostics().end());
  } else if (auto error = acceptSnapshot(tree, work))
    return error;
  return LayoutReader(tree, storage.tokens[id.index], work)
      .bodies(scopes, recovery);
}
} // namespace zkc::language::detail
