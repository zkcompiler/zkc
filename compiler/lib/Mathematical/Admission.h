#ifndef ZKC_MATHEMATICAL_ADMISSION_INTERNAL_H
#define ZKC_MATHEMATICAL_ADMISSION_INTERNAL_H

#include "zkc/Mathematical/Diagnostic.h"
#include "zkc/Mathematical/Subject.h"
#include <deque>
#include <set>

namespace zkc::mathematical {

/// One builder owns one immutable decoded subject and one selected registry.
/// Type interning/substitution caches never cross that ownership boundary.
class AdmissionBuilder {
  raw::Subject source;
  const Registry &registry;
  AdmissionBudget budget;
  TypeTable types;
  std::vector<TypedDefinition> definitions;
  std::vector<Permission> rootPermissions;
  std::deque<ClosedInstance> closedInstances;
  std::map<std::string, uint32_t> instanceIds;
  std::string digest;

  using Parameters = llvm::ArrayRef<NormalStatic>;
  using Roles = std::vector<uint32_t>;
  struct Context {
    // Reversed storage makes prepending an ordered block linear in that block,
    // without copying all earlier bindings for every flat DAG node.
    struct Binding {
      Port port;
      BindingId id;
    };
    std::vector<Binding> reversed;
  };
  struct DefinitionSignature {
    uint32_t roles;
    std::vector<Permission> capabilities;
    std::vector<Port> arguments, results;
  };
  struct ResolvedOperation {
    OperationSignature signature;
    OperationFacts facts;
  };

  llvm::Expected<std::vector<NormalStatic>> parameters(uint64_t arity);
  llvm::Expected<std::vector<NormalStatic>> substitute(llvm::ArrayRef<Static>,
                                                       Parameters);
  llvm::Expected<TypeId> type(const raw::TypeUse &, Parameters);
  llvm::Expected<std::vector<TypeId>> typeList(llvm::ArrayRef<raw::TypeUse>,
                                               Parameters);
  llvm::Expected<Roles> roles(llvm::ArrayRef<raw::Role>, uint32_t arity,
                              bool ordered = true);
  llvm::Expected<Roles> parties(uint64_t arity);
  llvm::Expected<Port> port(const raw::Port &, Parameters, uint32_t roleArity);
  llvm::Expected<std::vector<Port>> ports(llvm::ArrayRef<raw::Port>, Parameters,
                                          uint32_t roleArity);
  llvm::Expected<CapabilitySignature> capability(const raw::CapabilityUse &,
                                                 Parameters);
  llvm::Expected<ResolvedOperation> operation(uint64_t index, Parameters);
  llvm::Expected<TypeId> wire(uint64_t index, Parameters);
  llvm::Expected<DefinitionSignature> signature(uint64_t index, Parameters);
  llvm::Error manifest();
  llvm::Error declarations(const llvm::json::Value &captured);
  llvm::Expected<TypedDefinition> definition(uint32_t index, Parameters);
  llvm::Expected<uint32_t> instance(uint32_t definition,
                                    llvm::ArrayRef<uint64_t> statics,
                                    llvm::ArrayRef<uint32_t> roles,
                                    llvm::ArrayRef<uint32_t> roots,
                                    unsigned depth);
  llvm::Error discover(uint32_t instance, const TypedBody &, unsigned depth);

  llvm::Error push(Context &, llvm::ArrayRef<Port>);
  llvm::Expected<std::vector<BindingId>> latestBindings(const Context &,
                                                        size_t count);
  llvm::Expected<Operand> operand(const Context &, uint64_t index);
  llvm::Expected<std::vector<Operand>> operands(const Context &,
                                                llvm::ArrayRef<raw::ValueRef>);
  llvm::Expected<std::vector<Operand>>
  regionOperands(const Context &, llvm::ArrayRef<raw::RegionRef>);
  llvm::Error covers(const Operand &, const Port &);
  llvm::Error covers(llvm::ArrayRef<Operand>, llvm::ArrayRef<Port>);
  llvm::Expected<Roles> available(llvm::ArrayRef<Operand>,
                                  llvm::ArrayRef<uint32_t>);
  llvm::Expected<std::vector<Port>> operandPorts(llvm::ArrayRef<Operand>);
  llvm::Expected<TypedRegion> region(const raw::Region &, const Context &,
                                     llvm::ArrayRef<Port> prefix, Parameters,
                                     llvm::ArrayRef<uint32_t> parties,
                                     unsigned depth);
  llvm::Expected<TypedNode> node(const raw::PureNode &, const Context &,
                                 Parameters, llvm::ArrayRef<uint32_t> parties,
                                 unsigned depth);
  llvm::Expected<TypedBody>
  body(const raw::Body &, llvm::ArrayRef<Port> arguments,
       llvm::ArrayRef<Port> results, Parameters,
       llvm::ArrayRef<uint32_t> parties, llvm::ArrayRef<Permission>,
       uint32_t definition, uint64_t &site, unsigned depth);
  llvm::Expected<TypedStep> step(const raw::Step &, const Context &, Parameters,
                                 llvm::ArrayRef<uint32_t> parties,
                                 llvm::ArrayRef<Permission>,
                                 uint32_t definition, uint64_t &site,
                                 unsigned depth);
  llvm::Error effectSite(uint64_t actual, uint64_t &expected);
  llvm::Expected<std::vector<Port>> mapPorts(llvm::ArrayRef<Port>,
                                             llvm::ArrayRef<uint32_t>);
  llvm::Error checkCapabilities(llvm::ArrayRef<raw::CapabilityPortRef>,
                                llvm::ArrayRef<Permission> actual,
                                llvm::ArrayRef<Permission> expected,
                                llvm::ArrayRef<uint32_t> roleMap);

public:
  AdmissionBuilder(raw::Subject source, const Registry &registry,
                   AdmissionBudget budget, std::string digest)
      : source(std::move(source)), registry(registry), budget(budget),
        digest(std::move(digest)) {}
  llvm::Expected<Subject> run(const llvm::json::Value &captured);
};

} // namespace zkc::mathematical
#endif
