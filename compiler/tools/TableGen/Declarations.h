#ifndef ZKC_TABLEGEN_DECLARATIONS_H
#define ZKC_TABLEGEN_DECLARATIONS_H
namespace llvm {
class raw_ostream;
class RecordKeeper;
} // namespace llvm
void validateContractDeclarations(const llvm::RecordKeeper &);
bool emitContractDeclarations(llvm::raw_ostream &, const llvm::RecordKeeper &);
bool emitContractInventory(llvm::raw_ostream &, const llvm::RecordKeeper &);
#endif
