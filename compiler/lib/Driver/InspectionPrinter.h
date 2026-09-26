#ifndef ZKC_DRIVER_INSPECTION_PRINTER_H
#define ZKC_DRIVER_INSPECTION_PRINTER_H
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
namespace zkc {
// Input must be the unchanged report produced by inspectSource.
void printSourceInspection(const llvm::json::Value &, llvm::raw_ostream &);
} // namespace zkc
#endif
