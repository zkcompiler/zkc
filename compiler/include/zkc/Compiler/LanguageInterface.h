#ifndef ZKC_COMPILER_LANGUAGEINTERFACE_H
#define ZKC_COMPILER_LANGUAGEINTERFACE_H
#include "zkc/Language/Project.h"
namespace zkc::language {
struct InterfaceSchema;
struct InterfaceField {
  std::string name;
  unsigned offset;
  std::shared_ptr<const InterfaceSchema> schema;
};
struct InterfaceAlternative {
  std::string name;
  std::vector<InterfaceField> fields;
};
/// Logical metadata read without consulting the source layout builder.
struct InterfaceSchema {
  std::string type;
  Permissions permissions;
  bool custody;
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
  unsigned owner, native;
};
struct LanguageInterface {
  std::string capture, original, toolchain, entry, protocol;
  std::vector<std::string> roles;
  std::vector<InterfacePort> inputs, outputs;
  std::vector<InterfaceService> services;
};
/// Independently admit the original MLIR and check interface structure, native
/// leaf types, logical offsets, role mappings, services and exact byte
/// identity. Does not authenticate source names, permissions or nominal
/// schemas; source correspondence and checkInterface bind those to the retained
/// source project. This is a read-only view, not authority to compile, decode
/// private inputs or introduce an implementation. No source checker or emitter
/// is called.
llvm::Expected<LanguageInterface> readInterface(llvm::StringRef original,
                                                llvm::StringRef interface,
                                                const Limits & = {});
} // namespace zkc::language
#endif
