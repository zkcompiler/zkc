#ifndef ZKC_LANGUAGE_FINITE_CARDINALITY_H
#define ZKC_LANGUAGE_FINITE_CARDINALITY_H
#include "zkc/Contracts/FiniteCardinality.h"
#include "zkc/Language/Project.h"
namespace zkc::language::detail {
/// Borrow the source constructor's scalar operands and child arity. The
/// caller supplies the actual operand and child environments independently;
/// constructor admission remains separate from count derivation.
inline facts::DomainNode cardinalityNode(const DomainBinding &source) {
  using Kind = DomainBinding::Kind;
  facts::DomainNode view;
  view.children = source.children.size();
  switch (source.kind) {
  case Kind::Elements:
  case Kind::SourceArray:
  case Kind::Indices:
  case Kind::MatrixRow:
  case Kind::MatrixColumn:
    view.kind = facts::DomainKind::Extent;
    view.extent = {source.operands.front().index,
                   source.kind == Kind::Indices     ? source.axis
                   : source.kind == Kind::MatrixRow ? 1u
                                                    : 0u};
    break;
  case Kind::Range:
    view.kind = facts::DomainKind::Range;
    view.lower = source.operands[0].index;
    view.upper = source.operands[1].index;
    break;
  case Kind::Zip:
    view.kind = facts::DomainKind::Zip;
    break;
  case Kind::Product:
    view.kind = facts::DomainKind::Product;
    break;
  case Kind::MatrixCoordinates:
    view.kind = facts::DomainKind::MatrixCoordinates;
    view.extent.value = source.operands.front().index;
    break;
  case Kind::Parameter:
  case Kind::Application:
    break;
  }
  return view;
}
} // namespace zkc::language::detail
#endif
