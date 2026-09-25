#ifndef ZKC_FRONTEND_SEMANTICS_AGGREGATES_H
#define ZKC_FRONTEND_SEMANTICS_AGGREGATES_H
#include "zkc/Frontend/Module.h"
#include <map>
namespace zkc::frontend {
/// One source aggregate: its leaf paths and logical types in declaration
/// order, nested aggregates expanded depth first. An aggregate value is these
/// leaves in the lowering plan. Declaration/type IDs retain its source
/// identity.
struct AggregateShape {
  bool product = false;
  bool array = false;
  TypeId arrayElement;
  size_t arity = 0;
  std::string name;
  DeclId declaration;
  TypeId type;
  source::Names arguments;
  source::Names paths, types;
  /// Aggregate-valued fields by path, so `binding.field` can itself be passed.
  std::vector<std::pair<std::string, AggregateShape>> nested;
};
using Shapes = std::vector<std::optional<AggregateShape>>;
using LocalAggregates = std::map<std::string, AggregateShape>;
/// Compare product shape and every nested nominal identity before flattening.
/// Domain arguments are checked after inference, by the semantic checker.
bool sameAggregateStructure(const AggregateShape &, const AggregateShape &);
} // namespace zkc::frontend
#endif
