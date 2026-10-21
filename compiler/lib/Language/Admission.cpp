#include "Semantics.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Language/Builtins.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<Semantics::Admission> Semantics::admission(const Type &type,
                                                         Boundary boundary,
                                                         Span span,
                                                         unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "boundary admission depth exceeded", span);
    return {};
  }
  using A = Admission;
  using K = Type::Kind;
  if (isStaticOnly(type) || type.kind == K::Formal)
    return A::Rejected;
  const auto *decl = typeDeclaration(type);
  if (boundary == Boundary::Construction && decl && decl->generated &&
      !decl->generated->constructible)
    return A::Rejected;
  if (decl && decl->resource)
    return A::Rejected;
  // An opaque associated representation remains opaque after specialization.
  if (boundary == Boundary::Construction &&
      (type.kind == K::Associated || (decl && decl->sealed)))
    return A::Rejected;
  if (type.kind == K::Parameter ||
      (type.symbolic && type.arguments.empty() && type.kind != K::Field &&
       type.kind != K::Group))
    return A::Deferred;
  std::vector<Type> children;
  if (type.kind == K::Tuple || type.kind == K::Array)
    children = type.arguments;
  else if (type.kind == K::Record || type.kind == K::Associated) {
    if (decl && decl->abstract)
      return A::Deferred;
    auto product = fields(type, span, depth + 1);
    if (!product)
      return {};
    for (const auto &field : *product) {
      if (boundary == Boundary::Construction && !field.isPublic)
        return A::Rejected;
      children.push_back(field.type);
    }
  } else if (type.kind == K::Variant) {
    auto variants = alternatives(type, span, depth + 1);
    if (!variants)
      return {};
    for (const auto &variant : *variants)
      for (const auto &field : variant.fields)
        children.push_back(field.type);
  } else if (type.kind == K::Unit)
    return A::Accepted;
  else {
    StringRef kind = type.kind == K::Boolean ? "bool"
                     : type.kind == K::Index ? "index"
                     : type.kind == K::Field ? "field"
                     : type.kind == K::Group ? "group"
                                             : StringRef(type.domain);
    auto head = protocol::nativeTypeConstructorPolicy(kind);
    if (!head)
      return A::Rejected;
    bool structural = kind == "sequence";
    bool possible = boundary == Boundary::Participants
                        ? head->shared || structural
                    : boundary == Boundary::Construction ? head->constructible
                                                         : head->message;
    if (!possible)
      return A::Rejected;
    if (boundary == Boundary::Message && !symbolic(type)) {
      auto native = nativeLayout(type);
      if (!native) {
        accept(native.takeError(), span);
        return {};
      }
      return protocol::nativeMessageData(*native) ? A::Accepted : A::Rejected;
    }
    A result = boundary == Boundary::Message ? A::Deferred : A::Accepted;
    for (const auto &argument : type.arguments) {
      if (isStaticOnly(argument))
        continue;
      auto child = admission(argument, boundary, span, depth + 1);
      if (!child || *child == A::Rejected)
        return child;
      if (*child == A::Deferred)
        result = A::Deferred;
    }
    return result;
  }
  A result = A::Accepted;
  for (const auto &child : children) {
    auto admitted = admission(child, boundary, span, depth + 1);
    if (!admitted || *admitted == A::Rejected)
      return admitted;
    if (*admitted == A::Deferred)
      result = A::Deferred;
  }
  return result;
}
bool Semantics::admit(const Type &type, Boundary boundary, Span span,
                      const Declaration *scope, ArrayRef<Span> calls) {
  auto result = admission(type, boundary, span);
  if (!result)
    return false;
  if (*result == Admission::Accepted)
    return true;
  if (*result == Admission::Deferred && scope && recordAdmission)
    return recordAdmission(*scope, {type, boundary, span, calls.vec()});
  StringRef code = boundary == Boundary::Participants   ? "source.participants"
                   : boundary == Boundary::Construction ? "source.ingress"
                                                        : "source.codec";
  StringRef message =
      boundary == Boundary::Participants
          ? "type cannot have multiple participant components"
      : boundary == Boundary::Construction
          ? "type has no external construction authority; receive transparent "
            "data and validate it explicitly"
          : "type has no admitted native message codec";
  if (*result == Admission::Deferred)
    message = "boundary admission requires a concrete type";
  auto related = calls.vec();
  Span at = span;
  if (!related.empty()) {
    at = related.back();
    related.pop_back();
    related.insert(related.begin(), span);
  }
  return fail(code, message, at, related);
}
std::optional<bool> Semantics::setupAuthority(const Type &type, Span span,
                                              unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "Host data traversal depth exceeded", span);
    return {};
  }
  using K = Type::Kind;
  std::vector<Type> children;
  if (type.kind == K::Record || type.kind == K::Associated) {
    const auto *decl = typeDeclaration(type);
    if (decl && decl->abstract)
      return false;
    auto product = fields(type, span, depth + 1);
    if (!product)
      return {};
    for (const auto &field : *product)
      children.push_back(field.type);
  } else if (type.kind == K::Variant) {
    auto variants = alternatives(type, span, depth + 1);
    if (!variants)
      return {};
    for (const auto &variant : *variants)
      for (const auto &field : variant.fields)
        children.push_back(field.type);
  } else {
    if (type.kind == K::Builtin &&
        (type.domain == "prover_key" || type.domain == "verifier_key" ||
         type.domain == "srs"))
      return true;
    if (type.kind == K::Builtin && !symbolic(type)) {
      auto native = nativeLayout(type);
      if (!native) {
        accept(native.takeError(), span);
        return {};
      }
      if (protocol::nativeSetupType(*native))
        return true;
    }
    for (const auto &argument : type.arguments)
      if (!isStaticOnly(argument))
        children.push_back(argument);
  }
  for (const auto &child : children) {
    auto authority = setupAuthority(child, span, depth + 1);
    if (!authority || *authority)
      return authority;
  }
  return false;
}
bool Semantics::hostData(const Type &type, Span span,
                         const Declaration *scope) {
  auto authority = setupAuthority(type, span);
  if (!authority)
    return false;
  if (*authority)
    return fail("source.host-data", "setup authority is not ordinary Host data",
                span);
  for (auto usage : {Usage::Copy, Usage::Drop})
    if (!requireUsage(type, usage, span, scope, "source.host-data",
                      "Host boundaries require ordinary Copy and Drop data"))
      return false;
  return true;
}
bool Semantics::ingress(const Type &type, Span span) {
  return executableType(type, span) &&
         admit(type, Boundary::Construction, span) &&
         admit(type, Boundary::Message, span);
}
} // namespace zkc::language::detail
