#ifndef ZKC_MATHEMATICAL_RAW_H
#define ZKC_MATHEMATICAL_RAW_H

#include "zkc/Contracts/Declarations.h"
#include "zkc/Mathematical/Static.h"
#include "llvm/Support/JSON.h"
#include <memory>
#include <variant>

namespace zkc::mathematical::raw {

/// Finite syntax before scope, registry and typing checks. All reference sorts
/// have separate wrappers; admission additionally checks their actual tables.
template <class Tag> struct Reference {
  uint64_t index = 0;
};
using TypeRef = Reference<struct TypeTag>;
using DomainRef = Reference<struct DomainTag>;
using OperationIdentityRef = Reference<struct OperationIdentityTag>;
using WireIdentityRef = Reference<struct WireIdentityTag>;
using ServiceRef = Reference<struct ServiceTag>;
using LawRef = Reference<struct LawTag>;
using OperationRef = Reference<struct OperationTag>;
using WireRef = Reference<struct WireTag>;
using CapabilityTypeRef = Reference<struct CapabilityTypeTag>;
using CapabilityPortRef = Reference<struct CapabilityPortTag>;
using RootRef = Reference<struct RootTag>;
using DefinitionRef = Reference<struct DefinitionTag>;
using RelationRef = Reference<struct RelationTag>;
using ValueRef = Reference<struct ValueTag>;
using RegionRef = Reference<struct RegionTag>;
using LocalDefinitionRef = Reference<struct LocalDefinitionTag>;
using Role = Reference<struct RoleTag>;

struct Identity {
  std::string name, version, digest;
};
struct Manifest {
  std::vector<Identity> domains, operations, wires, services, laws;
};
struct TypeUse {
  TypeRef type;
  std::vector<Static> statics;
};
struct NominalType {
  DomainRef domain;
  std::string name;
  std::vector<Static> arguments;
};
struct ProductType {
  std::vector<TypeUse> elements;
};
struct FinType {
  Static count;
};
struct VectorType {
  TypeUse element;
  Static count;
};
struct PolynomialType {
  enum class Degree { Individual, Total };
  DomainRef domain;
  Static arity, degree;
  Degree convention;
};
struct ResidualType {
  DomainRef domain;
  Static arity, degree;
};
using Type = std::variant<NominalType, ProductType, FinType, VectorType,
                          PolynomialType, ResidualType>;
struct TypeTemplate {
  uint64_t statics = 0;
  Type body;
};
struct CapabilityUse {
  CapabilityTypeRef type;
  std::vector<Static> statics;
};
struct CapabilityType {
  ServiceRef identity;
  uint64_t statics = 0;
  std::vector<TypeUse> arguments;
  TypeUse result;
};
struct CapabilityParameter {
  CapabilityUse signature;
  std::vector<Role> roles;
};
struct Root {
  CapabilityUse signature;
  std::vector<Role> roles;
};
struct Operation {
  using Purity = protocol::OperationPurity;
  OperationIdentityRef identity;
  uint64_t statics = 0;
  std::vector<CapabilityUse> capabilities;
  std::vector<TypeUse> arguments;
  TypeUse result;
  Purity purity = Purity::Ordered;
  std::vector<std::pair<uint64_t, uint64_t>> distinct;
};
struct Wire {
  WireIdentityRef identity;
  uint64_t statics = 0;
  TypeUse type;
};
struct Port {
  std::vector<Role> roles;
  TypeUse type;
};

struct PureOperation {
  OperationRef operation;
  std::vector<Static> statics;
  llvm::json::Value attributes;
  std::vector<RegionRef> arguments;
};
struct Tuple {
  std::vector<RegionRef> elements;
};
struct Project {
  RegionRef value;
  uint64_t component = 0;
};
struct Region;
struct Map {
  Static count;
  std::shared_ptr<const Region> body;
};
struct Fold {
  Static count;
  std::vector<RegionRef> initial;
  std::shared_ptr<const Region> body;
};
using PureNode = std::variant<PureOperation, Tuple, Project, Map, Fold>;
struct Region {
  std::vector<ValueRef> captures;
  std::vector<PureNode> nodes;
  std::vector<RegionRef> outputs;
};
struct Relation {
  uint64_t statics = 0;
  std::vector<TypeUse> publicInputs, witnessInputs;
  std::vector<LawRef> assumptions;
  Region body;
};
struct RelationBinding {
  RelationRef relation;
  std::vector<Static> statics;
  std::vector<ValueRef> publicInputs, witnessInputs;
};
struct Pure {
  Region region;
};
struct Local {
  uint64_t site = 0;
  Role owner;
  OperationRef operation;
  std::vector<Static> statics;
  llvm::json::Value attributes;
  std::vector<CapabilityPortRef> capabilities;
  std::vector<ValueRef> arguments;
};
struct Query {
  uint64_t site = 0;
  Role owner;
  CapabilityPortRef capability;
  std::vector<ValueRef> arguments;
};
struct Guard {
  uint64_t site = 0;
  Role owner;
  ValueRef condition;
};
struct Message {
  uint64_t site = 0;
  WireRef wire;
  std::vector<Static> statics;
  Role sender, receiver;
  ValueRef value;
};
struct Invoke {
  uint64_t site = 0;
  DefinitionRef definition;
  std::vector<Static> statics;
  std::vector<Role> roles;
  std::vector<CapabilityPortRef> capabilities;
  std::vector<ValueRef> arguments;
};
struct Body;
struct Repeat {
  uint64_t site = 0;
  Static count;
  std::vector<Port> carried;
  std::vector<ValueRef> initial, captures;
  std::shared_ptr<const Body> body;
};
using Step = std::variant<Pure, Local, Query, Guard, Message, Invoke, Repeat>;
struct Return {
  std::vector<ValueRef> values;
};
enum class StopReason { Reject, Abort, Exhausted, Incomplete, Refused };
struct Stop {
  uint64_t site = 0;
  Role owner;
  StopReason reason;
};
struct Body {
  std::vector<Step> steps;
  std::variant<Return, Stop> terminal;
};
struct Definition {
  uint64_t statics = 0, roles = 0;
  std::vector<CapabilityParameter> capabilities;
  std::vector<Port> arguments, results;
  std::vector<RelationBinding> relations;
  Body body;
};
struct Entry {
  DefinitionRef definition;
  std::vector<uint64_t> statics;
  std::vector<Role> roles;
  std::vector<RootRef> capabilities;
};
struct Module {
  std::vector<std::string> roles;
  std::vector<TypeTemplate> types;
  std::vector<Operation> operations;
  std::vector<Wire> wires;
  std::vector<CapabilityType> capabilityTypes;
  std::vector<Root> roots;
  std::vector<Relation> relations;
  std::vector<Definition> definitions;
  Entry entry;
};
struct Subject {
  Manifest manifest;
  Module module;
};

/// Exact v1 mathematical schema. The value codec must still validate canonical
/// resource limits, even for programmatically constructed JSON. No semantic
/// admission is conferred by structural decoding.
llvm::Expected<Subject> decode(const llvm::json::Value &);
llvm::Expected<llvm::json::Value> encode(const Subject &);

} // namespace zkc::mathematical::raw
#endif
