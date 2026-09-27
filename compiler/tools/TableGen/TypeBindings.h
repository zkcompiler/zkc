#ifndef ZKC_TABLEGEN_TYPE_BINDINGS_H
#define ZKC_TABLEGEN_TYPE_BINDINGS_H
namespace llvm {
class raw_ostream;
class RecordKeeper;
} // namespace llvm
bool emitTypeBindings(llvm::raw_ostream &, const llvm::RecordKeeper &);
#endif
