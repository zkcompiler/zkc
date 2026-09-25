#ifndef ZKC_RELATION_AIR_COMMANDS_H
#define ZKC_RELATION_AIR_COMMANDS_H
namespace mlir {
class DialectRegistry;
}
namespace zkc::relation {
int runAIRCommand(int argc, char **argv, const mlir::DialectRegistry &);
}
#endif
