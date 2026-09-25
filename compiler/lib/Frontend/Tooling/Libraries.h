#ifndef ZKC_FRONTEND_TOOLING_LIBRARIES_H
#define ZKC_FRONTEND_TOOLING_LIBRARIES_H
#include "llvm/Support/JSON.h"
namespace zkc::frontend::model {
struct LibraryReport;
}
namespace zkc::frontend::resolution {
struct Context;
}
namespace zkc::frontend::tooling {
llvm::json::Value inspectLibraries(const model::LibraryReport &,
                                   const resolution::Context * = nullptr);
}
#endif
