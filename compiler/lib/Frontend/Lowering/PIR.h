#ifndef ZKC_FRONTEND_LOWERING_PIR_H
#define ZKC_FRONTEND_LOWERING_PIR_H

#include "../Model/Checked.h"

namespace zkc::frontend::lowering {
llvm::Expected<model::EmittedSource> lower(model::CheckedSource &&,
                                           WorkBudget &);
} // namespace zkc::frontend::lowering
#endif
