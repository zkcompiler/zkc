#ifndef ZKC_TRANSFORMS_PIPELINE_OPTIONS_H
#define ZKC_TRANSFORMS_PIPELINE_OPTIONS_H

#include "zkc/Target/CpuTarget.h"
#include "llvm/Support/CommandLine.h"

namespace llvm::cl {
/// MLIR strips an outer pair of option delimiters. A typed printer adds that
/// pair explicitly, retaining the JSON object's own braces in reproductions.
template <>
struct parser<zkc::target::CpuTarget> : basic_parser<zkc::target::CpuTarget> {
  using basic_parser<zkc::target::CpuTarget>::basic_parser;
  bool parse(llvm::cl::Option &option, llvm::StringRef, llvm::StringRef text,
             zkc::target::CpuTarget &value) {
    auto parsed = zkc::target::CpuTarget::parse(text);
    if (!parsed)
      return option.error(llvm::toString(parsed.takeError()));
    value = *parsed;
    return false;
  }
  static void print(llvm::raw_ostream &out,
                    const zkc::target::CpuTarget &value) {
    out << '{' << value.descriptor() << '}';
  }
  void printOptionDiff(const Option &option,
                       const zkc::target::CpuTarget &value,
                       const OptionValue<zkc::target::CpuTarget> &initial,
                       size_t width) const {
    printOptionName(option, width);
    llvm::outs() << "= " << value.descriptor();
    if (initial.hasValue())
      llvm::outs() << " (default: " << initial.getValue().descriptor() << ")";
    llvm::outs() << '\n';
  }
};
} // namespace llvm::cl
#endif
