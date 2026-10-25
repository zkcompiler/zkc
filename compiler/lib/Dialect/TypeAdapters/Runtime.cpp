#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
namespace zkc::protocol::type_adapters {
namespace {
using QuotientMatrixAdapter = NullaryAdapter<zkc::runtime::QuotientMatrixType>;
}
} // namespace zkc::protocol::type_adapters
#include "zkc/Dialect/TypeAdapters/Runtime.inc"
