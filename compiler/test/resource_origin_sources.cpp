#include "support/ResourceSources.h"
using namespace mlir;
using namespace zkc::test;
using namespace zkc::test::resource_sources;
int main(int argc, char **argv) {
  try {
    require(argc == 2 || (argc == 3 && StringRef(argv[2]) == "--outside"),
            "expected resource source name and optional --outside");
    Source source;
    StringRef name(argv[1]);
    require(argc == 2 || !(name.starts_with("role-") || name == "execution" ||
                           name == "stop" || name == "nested_stop" ||
                           name == "private-history"),
            "this source has no outside-repeat variant");
    if (name == "conditional-completion")
      conditionalCompletion(source);
    else if (name == "execution" || name == "stop" || name == "nested_stop" ||
             name == "private-history")
      execution(source, name);
    else if (name.starts_with("role-"))
      roles(source, name);
    else if (name == "dag" || name == "protocol-calls80")
      calls(source, name, argc == 3);
    else if (name.starts_with("swap") || name.starts_with("formal") ||
             name.starts_with("callee-repeat"))
      pair(source, name, argc == 3);
    else
      simple(source, name, argc == 3);
    source.module->print(llvm::outs());
    llvm::outs() << "\n";
    return 0;
  } catch (const std::exception &error) {
    llvm::errs() << error.what() << "\n";
    return 1;
  }
}
