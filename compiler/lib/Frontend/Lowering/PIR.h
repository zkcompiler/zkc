#ifndef ZKC_FRONTEND_LOWERING_PIR_H
#define ZKC_FRONTEND_LOWERING_PIR_H

#include "../Model/Module.h"

namespace zkc::frontend::lowering {
llvm::Expected<source::Content> lower(const model::Module &);
} // namespace zkc::frontend::lowering
#endif
