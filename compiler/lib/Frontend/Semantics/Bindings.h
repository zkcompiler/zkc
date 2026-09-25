#ifndef ZKC_FRONTEND_SEMANTICS_BINDINGS_H
#define ZKC_FRONTEND_SEMANTICS_BINDINGS_H
#include "../Model/Module.h"
namespace zkc::frontend::semantics {
/// Records lexical resolution in the retained model. It neither parses nor
/// performs inference; the local checker supplies the established source type.
class LocalSymbols {
  model::Module &model;
  DeclId owner;
  ScopeId declarationScope;

public:
  LocalSymbols(model::Module &model, DeclId owner, ScopeId scope)
      : model(model), owner(owner), declarationScope(scope) {}
  ScopeId root() const { return declarationScope; }
  ScopeId scope(ScopeId parent) { return model.addScope(parent, owner); }
  TypeId logical(llvm::StringRef spelling) {
    return model.logical(spelling, declarationScope);
  }
  ValueId bind(ScopeId scope, llvm::StringRef name, TypeId type,
               const source::Names &leaves, bool mutableBinding,
               const source::Node &node) {
    ValueId id{static_cast<uint32_t>(model.bindings.size())};
    model.bindings.push_back(
        {id, scope, type, name.str(), leaves, mutableBinding, node.location});
    return id;
  }
  void use(ValueId binding, ScopeId scope, const source::Node &node) {
    if (binding.valid())
      model.valueUses.push_back({binding, scope, node.location});
  }
};
} // namespace zkc::frontend::semantics
#endif
