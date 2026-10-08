#ifndef ZKC_COMPILER_LANGUAGEINTERFACE_H
#define ZKC_COMPILER_LANGUAGEINTERFACE_H
#include "zkc/Language/Project.h"
namespace zkc::language {
struct InterfaceSchema;
struct InterfaceField {
  std::string name;
  unsigned offset = 0;
  std::shared_ptr<const InterfaceSchema> schema;
};
struct InterfaceAlternative {
  std::string name;
  std::vector<InterfaceField> fields;
};
/// Logical metadata read without consulting the source layout builder.
struct InterfaceSchema {
  Type::Kind kind = Type::Kind::Unit;
  std::string identity, type;
  Permissions permissions;
  bool custody = false;
  std::vector<std::string> leaves;
  std::vector<InterfaceField> fields;
  std::vector<InterfaceAlternative> alternatives;
};
struct InterfacePort {
  std::string name;
  std::vector<unsigned> roles, native;
  std::shared_ptr<const InterfaceSchema> schema;
};
struct InterfaceService {
  std::string name, contract;
  unsigned owner = 0, native = 0;
};
struct InterfaceSelector {
  bool output = false;
  unsigned port = 0, role = 0;
  std::vector<unsigned> path, native;
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
  RelationDefinition::Kind kind = RelationDefinition::Kind::Opaque;
  std::vector<InterfaceRelationInput> inputs;
  std::optional<std::string> formula;
  std::optional<RelationAsset> asset;
};
struct InterfaceProtocol {
  std::string symbol;
  std::vector<std::string> roles;
  std::vector<InterfacePort> inputs, outputs;
  std::vector<InterfaceService> services;
  std::vector<InterfaceClause> clauses;
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
  std::vector<unsigned> publicInputs;
  InterfaceSelector acceptance;
  std::optional<unsigned> target, service;
  std::string suite;
};
struct LanguageInterface {
  std::string capture, original, toolchain, entry;
  std::vector<InterfaceProtocol> protocols;
  std::vector<InterfaceRelation> relations;
  unsigned selected = 0;
  std::optional<InterfaceProofEntry> proof;
  std::vector<InterfaceSetup> setups;
  const InterfaceProtocol &selectedProtocol() const {
    return protocols.at(selected);
  }
};
/// Compare a decoded view with the checked source, including template clause
/// inventory and captured specification tokens. Does not admit or compare MLIR;
/// use admitOriginal for the complete checked-source boundary.
llvm::Error compareInterface(const ClosedEntry &, const LanguageInterface &,
                             const Limits & = {});
/// Independently admit the original MLIR and check interface structure, native
/// leaf types, logical offsets, role mappings, services and exact byte
/// identity. Does not authenticate source names, permissions or nominal
/// schemas; source correspondence and checkInterface bind those to the retained
/// source project through admitOriginal. This is a read-only view, not
/// authority to compile, decode private inputs or introduce an implementation.
/// No source checker or emitter is called.
llvm::Expected<LanguageInterface>
readInterface(llvm::StringRef original, llvm::StringRef interface,
              const Limits & = {}, llvm::ArrayRef<RelationAsset> assets = {});
} // namespace zkc::language
#endif
