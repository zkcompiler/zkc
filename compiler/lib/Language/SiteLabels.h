#ifndef ZKC_LANGUAGE_SITELABELS_H
#define ZKC_LANGUAGE_SITELABELS_H
#include "Internal.h"
namespace zkc::language::detail {
enum class SiteEventFamily {
  None,
  Exchange,
  OracleSend,
  OracleQuery,
  OracleSourceQuery,
  OracleInstantiation,
  OracleSequenceAppend,
  OracleSequenceAt,
  ServiceQuery,
  ProtocolApplication,
  Control,
  ProtocolRepeat
};
inline SiteEventFamily siteEventFamily(const Operation &operation) {
  using F = SiteEventFamily;
  if (std::holds_alternative<Exchange>(operation.action))
    return F::Exchange;
  if (std::holds_alternative<OracleSend>(operation.action))
    return F::OracleSend;
  if (std::holds_alternative<OracleQuery>(operation.action))
    return F::OracleQuery;
  if (std::holds_alternative<OracleSourceQuery>(operation.action))
    return F::OracleSourceQuery;
  if (std::holds_alternative<OracleInstantiation>(operation.action))
    return F::OracleInstantiation;
  if (std::holds_alternative<OracleSequenceAppend>(operation.action))
    return F::OracleSequenceAppend;
  if (std::holds_alternative<OracleSequenceAt>(operation.action))
    return F::OracleSequenceAt;
  if (std::holds_alternative<ServiceQuery>(operation.action))
    return F::ServiceQuery;
  if (std::holds_alternative<ProtocolApplication>(operation.action))
    return F::ProtocolApplication;
  if (std::holds_alternative<Control>(operation.action))
    return F::Control;
  if (std::holds_alternative<ProtocolRepeat>(operation.action))
    return F::ProtocolRepeat;
  return F::None;
}
inline bool siteEvent(const Operation &operation) {
  return siteEventFamily(operation) != SiteEventFamily::None;
}
/// The resolved declaration is source authority, not the candidate action.
inline SiteEventFamily sourceCallSiteFamily(Declaration::Kind kind,
                                            ResolutionCategory category) {
  if (category == ResolutionCategory::ServiceMethod)
    return SiteEventFamily::ServiceQuery;
  if (kind == Declaration::Kind::Protocol)
    return SiteEventFamily::ProtocolApplication;
  if (kind == Declaration::Kind::Oracle)
    return SiteEventFamily::OracleInstantiation;
  return SiteEventFamily::None;
}
/// Absence of call resolution is unknown, never evidence for a Local call.
inline std::optional<SiteEventFamily>
sourceSiteFamily(const Statement &statement, const Expression &expression,
                 Body::Mode mode,
                 std::optional<SiteEventFamily> resolvedCall = {}) {
  using K = Expression::Kind;
  using F = SiteEventFamily;
  if (statement.exchange)
    return F::Exchange;
  switch (expression.kind) {
  case K::OracleSend:
    return F::OracleSend;
  case K::OracleQuery:
    return mode == Body::Mode::Oracle ? F::OracleSourceQuery : F::OracleQuery;
  case K::OracleSequenceAppend:
    return F::OracleSequenceAppend;
  case K::OracleSequenceAt:
    return F::OracleSequenceAt;
  case K::If:
  case K::Match:
    return F::Control;
  case K::For:
    return mode == Body::Mode::Protocol ? F::ProtocolRepeat : F::Control;
  case K::Call:
  case K::MethodCall:
  case K::NotationCall:
  case K::Subscript:
    return resolvedCall;
  default:
    // In particular, eager Protocol Boolean operands execute in an implicit
    // Math helper. They do not introduce selected Protocol events.
    return F::None;
  }
}
inline std::optional<std::string>
sourceSiteLabel(const SyntaxDeclaration &syntax, const Statement &statement,
                Body::Mode mode) {
  if (statement.site)
    return statement.site;
  if ((syntax.layoutSyntax && mode == Body::Mode::Protocol) ||
      mode == Body::Mode::Oracle) {
    if (statement.evaluation == Statement::Evaluation::Ordered &&
        statement.pattern.kind == Pattern::Kind::Name)
      return statement.pattern.name;
    const auto &expression = syntax.expressions[statement.expression];
    if (expression.kind == Expression::Kind::For &&
        expression.index.kind == Pattern::Kind::Name)
      return expression.index.name;
  }
  return {};
}
} // namespace zkc::language::detail
#endif
