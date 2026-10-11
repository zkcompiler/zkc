#ifndef ZKC_TABLEGEN_MATHEMATICAL_H
#define ZKC_TABLEGEN_MATHEMATICAL_H
namespace llvm {
class Record;
class RecordKeeper;
class raw_ostream;
} // namespace llvm
void validateMathematicalFacet(const llvm::Record *, const llvm::Record *);
void validateLinearFacet(const llvm::Record *, const llvm::Record *);
void emitMathematicalFacet(llvm::raw_ostream &, const llvm::Record *,
                           const llvm::Record *);
bool emitMathematicalDeclarations(llvm::raw_ostream &,
                                  const llvm::RecordKeeper &);
#endif
