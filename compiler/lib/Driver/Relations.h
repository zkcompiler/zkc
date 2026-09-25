#ifndef ZKC_RELATION_DRIVER_H
#define ZKC_RELATION_DRIVER_H

namespace mlir {
class DialectRegistry;
}
namespace zkc::relation {
int runCommand(int argc, char **argv, const mlir::DialectRegistry &);
} // namespace zkc::relation
#endif
