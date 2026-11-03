#ifndef ZKC_TABLEGEN_ROLES_H
#define ZKC_TABLEGEN_ROLES_H
namespace llvm {
class Record;
class RecordKeeper;
class raw_ostream;
} // namespace llvm
bool emitRoleAttributes(llvm::raw_ostream &, const llvm::RecordKeeper &);
/// The role shape constraint an argument constraint declares, looking through
/// wrappers such as OptionalAttr; null for an attribute that holds no roles.
const llvm::Record *roleConstraint(const llvm::Record *constraint);
#endif
