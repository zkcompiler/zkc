#ifndef ZKC_COMPILER_LANGUAGEINTERFACE_H
#define ZKC_COMPILER_LANGUAGEINTERFACE_H
#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Language/CommonControl.h"
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"
#include <variant>
namespace zkc::language {
struct InterfaceOracle {
  std::string kind;
  std::vector<protocol::TypeArgument> arguments;
  bool operator==(const InterfaceOracle &other) const {
    return kind == other.kind && arguments == other.arguments;
  }
  bool operator!=(const InterfaceOracle &other) const {
    return !(*this == other);
  }
};
struct InterfaceOraclePort {
  unsigned holder;
  /// Forbidden at a logical record root; each direct field owns its bound.
  std::optional<uint64_t> maximumRows;
};
struct InterfaceSchema;
struct InterfaceField {
  std::string name;
  /// Body offset: handles count once, including within logical records.
  unsigned offset = 0;
  std::shared_ptr<const InterfaceSchema> schema;
  /// Fields retain public visibility and nullable placement. An unsized direct
  /// handle field of a logical record additionally requires maximum_rows,
  /// encoded as a canonical unsigned 64-bit decimal string (including "0").
  /// Every other field omits that member, including statically sized handles.
  std::optional<uint64_t> maximumRows = {};
  bool isPublic = true;
  /// External formula: Product.instance is the child schema identity digest.
  std::optional<ValuePlacement> placement = {};
};
struct InterfaceAlternative {
  std::string name;
  std::vector<InterfaceField> fields;
};
/// Recursive logical metadata, independently admitted against the native ABI.
struct InterfaceSchema {
  Type::Kind kind = Type::Kind::Unit;
  std::string identity, type;
  /// Generated-family identity, bound to capture/installation/home when
  /// present.
  std::string generated;
  Permissions permissions;
  unsigned custody = 0;
  bool sealed = false;
  std::vector<std::string> roles;
  std::shared_ptr<const InterfaceSchema> element;
  bool constructible = false;
  /// Ordinary native data only. Logical records and handles have no aggregate
  /// carrier; their complete representation is given by fields / oracleData.
  std::vector<std::string> leaves;
  std::vector<InterfaceField> fields;
  std::vector<InterfaceAlternative> alternatives;
  /// Present only for a logical handle or bounded handle sequence. Such a
  /// schema has no native data leaves.
  std::optional<InterfaceOracle> oracle;
  /// Present only for a bounded handle sequence, including zero capacity.
  std::optional<uint64_t> maximum;
  /// Holder projection: K::Data for a singleton, sequence<K::Data> otherwise.
  std::shared_ptr<const InterfaceSchema> oracleData;
};
enum class InterfaceComponentFacet { Data, OracleData, OracleAnchor, Custody };
struct InterfaceComponent {
  std::vector<unsigned> path;
  unsigned leaf = 0, role = 0;
  InterfaceComponentFacet facet = InterfaceComponentFacet::Data;
  unsigned native = 0;
  bool operator==(const InterfaceComponent &other) const {
    return path == other.path && leaf == other.leaf && role == other.role &&
           facet == other.facet && native == other.native;
  }
};
struct InterfacePort {
  std::string name;
  /// Derived participation summary for diagnostics, never field authority.
  std::vector<unsigned> roles;
  std::vector<unsigned> native;
  std::shared_ptr<const InterfaceSchema> schema;
  std::optional<InterfaceOraclePort> oracle = {};
  /// External instances equal schema.identity, never internal typeIdentity.
  std::optional<ValuePlacement> placement = {};
  std::vector<InterfaceComponent> components = {};
};
struct InterfaceService {
  std::string name, contract;
  unsigned owner = 0, native = 0;
};
struct InterfaceSelector {
  bool output = false;
  unsigned port = 0, role = 0;
  std::vector<unsigned> path, native;
  bool anchor = false;
};
struct InterfaceApplication {
  unsigned relation = 0;
  std::vector<InterfaceSelector> operands;
};
struct InterfaceClause {
  SpecificationClause::Kind kind = SpecificationClause::Kind::Input;
  std::string name;
  InterfaceApplication subject;
  std::optional<InterfaceApplication> residual;
  std::optional<InterfaceSelector> decision;
};
struct InterfaceRelationInput {
  std::string name;
  RelationPurpose purpose = RelationPurpose::Statement;
  std::vector<unsigned> native;
  std::shared_ptr<const InterfaceSchema> schema;
};
struct InterfaceRelation {
  std::string symbol, externalKind, key, revision;
  llvm::json::Value staticArguments = llvm::json::Array{};
  RelationDefinition::Kind kind = RelationDefinition::Kind::Opaque;
  std::vector<InterfaceRelationInput> inputs;
  std::optional<std::string> formula;
  std::optional<Asset> asset;
};
struct InterfaceCommonValue {};
struct InterfaceCommonTag {};
struct InterfaceCommonExtent {
  unsigned axis;
};
using InterfaceCommonObservation =
    std::variant<InterfaceCommonValue, InterfaceCommonTag,
                 InterfaceCommonExtent>;
struct InterfaceCommonRequirement {
  std::vector<CommonControlComponent> components;
  InterfaceCommonObservation observation;
};
struct InterfaceProtocol {
  std::string symbol;
  std::vector<std::string> roles;
  std::vector<InterfacePort> inputs, outputs;
  std::vector<InterfaceService> services;
  std::vector<InterfaceClause> clauses;
  /// Canonical complete equivalence classes; no span or redundant native map.
  std::vector<InterfaceCommonRequirement> commonInputRequirements;
};
struct InterfaceEntryInput {
  unsigned port = 0;
  std::vector<unsigned> path, native;
};
struct InterfaceSetup {
  std::string name;
  std::vector<InterfaceEntryInput> inputs;
};
struct InterfaceProofEntry {
  ProofEntry::Construction construction = ProofEntry::Construction::Authored;
  unsigned prover = 0, verifier = 0;
  std::vector<EntryInputSelection> publicInputs;
  InterfaceSelector acceptance;
  std::optional<InterfaceSelector> completion;
  std::optional<unsigned> target;
  std::vector<unsigned> services;
  std::string suite, selectedConstruction;
  std::vector<ProofGate> gates;
  protocol::ProofFormat format = protocol::ProofFormat::Native;
};
struct InterfaceFunctionParameter {
  std::string name;
  std::shared_ptr<const InterfaceSchema> schema;
};
struct InterfaceFunction {
  std::string symbol;
  std::vector<InterfaceFunctionParameter> parameters;
  std::shared_ptr<const InterfaceSchema> result;
};
struct InterfaceHostEntry {
  std::string function;
  std::vector<InterfaceFunction> functions;
};
struct LanguageInterface {
  std::string capture, original, toolchain, entry;
  std::vector<InterfaceProtocol> protocols;
  std::vector<InterfaceRelation> relations;
  unsigned selected = 0;
  std::optional<InterfaceHostEntry> host;
  std::optional<InterfaceProofEntry> proof;
  std::vector<InterfaceSetup> setups;
  const InterfaceProtocol &selectedProtocol() const {
    return protocols.at(selected);
  }
};
/// Compare a decoded view with the checked source, including template clause
/// inventory, every concrete common-input inventory and captured specification
/// tokens. Does not admit or compare MLIR;
/// use admitOriginal for the complete checked-source boundary.
llvm::Error compareInterface(const ClosedEntry &, const LanguageInterface &,
                             const Limits & = {});
/// Independently admit the original MLIR and check interface structure, native
/// leaf types, logical offsets, role mappings, services and exact byte
/// identity and the complete independently derived native common-input
/// inventory of every Protocol. Does not authenticate source names, permissions
/// or nominal schemas; source correspondence and compareInterface bind those to
/// the retained source project through admitOriginal. This is a read-only view,
/// not authority to compile, decode private inputs or introduce an
/// implementation. No source checker or emitter is called.
llvm::Expected<LanguageInterface>
readInterface(llvm::StringRef original, llvm::StringRef interface,
              const Limits & = {}, llvm::ArrayRef<Asset> assets = {});
} // namespace zkc::language
#endif
