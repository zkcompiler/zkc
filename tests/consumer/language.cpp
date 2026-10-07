#include "zkc/Language/Project.h"
#include "llvm/Support/raw_ostream.h"
int main() {
  auto capture = zkc::language::capture({{"m", R"(module m;
    protocol Run roles(P)(x:bool@P)->(r:bool@P){return(r=x);}
    entry Demo=Run;)",
                                          "consumer.zkc"}});
  if (!capture) {
    llvm::errs() << llvm::toString(capture.takeError());
    return 1;
  }
  auto checked = zkc::language::analyze(*capture).checkedProject();
  if (!checked) {
    llvm::errs() << llvm::toString(checked.takeError());
    return 2;
  }
  auto entry = zkc::language::closeEntry(*checked, "m::Demo");
  if (!entry) {
    llvm::errs() << llvm::toString(entry.takeError());
    return 3;
  }
  return entry->protocol().symbol == "s1_m3_Run" ? 0 : 4;
}
