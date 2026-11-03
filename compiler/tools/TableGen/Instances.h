#ifndef ZKC_TABLEGEN_INSTANCES_H
#define ZKC_TABLEGEN_INSTANCES_H
namespace llvm {
class raw_ostream;
class RecordKeeper;
namespace json {
class Object;
} // namespace json
} // namespace llvm
/// Check the installed-instance tables of the declaration records.
void validateInstalledInstances(const llvm::RecordKeeper &);
/// Add the installed-instance tables to a declaration inventory. Physical
/// installation tables never join it.
void addInstalledInstanceInventory(llvm::json::Object &,
                                   const llvm::RecordKeeper &);
/// Check the declarations and their native installation together, then emit
/// the generated C++ tables.
bool emitInstalledInstances(llvm::raw_ostream &, const llvm::RecordKeeper &);
/// Check both documents and print only the native installation tables.
bool emitNativeInstallationInventory(llvm::raw_ostream &,
                                     const llvm::RecordKeeper &);
#endif
