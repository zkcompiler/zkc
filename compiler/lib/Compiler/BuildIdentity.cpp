#include "BuildIdentity.h"

namespace zkc::language::detail {
const char *compilerBuildIdentity() { return ZKC_BUILD_ID; }
} // namespace zkc::language::detail
