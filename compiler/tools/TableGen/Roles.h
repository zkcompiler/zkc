#ifndef ZKC_TABLEGEN_ROLES_H
#define ZKC_TABLEGEN_ROLES_H
namespace llvm {
class RecordKeeper;
class raw_ostream;
} // namespace llvm
bool emitRoleAttributes(llvm::raw_ostream &, const llvm::RecordKeeper &);
#endif
