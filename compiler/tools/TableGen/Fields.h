#ifndef ZKC_TABLEGEN_FIELDS_H
#define ZKC_TABLEGEN_FIELDS_H
namespace llvm {
class RecordKeeper;
class raw_ostream;
} // namespace llvm
bool emitFieldInventory(llvm::raw_ostream &, const llvm::RecordKeeper &);
#endif
