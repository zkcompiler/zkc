#ifndef ZKC_TABLEGEN_RECIPES_H
#define ZKC_TABLEGEN_RECIPES_H
namespace llvm {
class RecordKeeper;
class raw_ostream;
} // namespace llvm
bool emitMathematicalRecipes(llvm::raw_ostream &, const llvm::RecordKeeper &);
#endif
