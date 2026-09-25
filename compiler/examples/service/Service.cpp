#include "Service.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Compiler/Library.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "ServiceDialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "ServiceTypes.cpp.inc"
#define GET_OP_CLASSES
#include "ServiceOps.cpp.inc"
namespace zkc::service {
namespace {
class ServiceLibrary final : public SourceLibraryInterface {
public:
  using SourceLibraryInterface::SourceLibraryInterface;
  llvm::json::Value dependencies() const final {
    return llvm::json::Array{llvm::json::Array{"vector-service", "1"}};
  }
  Type conditionType(Builder &b) const final {
    return PredicateType::get(b.getContext());
  }
  llvm::Expected<Type> decodeType(const llvm::json::Value &v,
                                  Builder &b) const final {
    auto *a = v.getAsArray();
    if (!a || a->size() != 1)
      return error("unknown-type");
    if ((*a)[0] == "count")
      return Type(CountType::get(b.getContext()));
    if ((*a)[0] == "vector")
      return Type(VectorType::get(b.getContext()));
    if ((*a)[0] == "predicate")
      return Type(PredicateType::get(b.getContext()));
    return error("unknown-type");
  }
  llvm::Expected<llvm::json::Value> encodeType(Type t) const final {
    if (isa<CountType>(t))
      return llvm::json::Value(llvm::json::Array{"count"});
    if (isa<VectorType>(t))
      return llvm::json::Value(llvm::json::Array{"vector"});
    if (isa<PredicateType>(t))
      return llvm::json::Value(llvm::json::Array{"predicate"});
    return error("unknown-type");
  }
  llvm::Expected<ResolvedOperation> resolveOperation(const llvm::json::Value &v,
                                                     Builder &b) const final {
    auto *a = v.getAsArray();
    if (!a || a->size() != 1)
      return error("unknown-operation");
    Type count = CountType::get(b.getContext()),
         vector = VectorType::get(b.getContext());
    if ((*a)[0] == "request")
      return ResolvedOperation{"service.request", {count}, vector, {}, true};
    if ((*a)[0] == "send")
      return ResolvedOperation{
          "service.send", {count}, conditionType(b), {}, true};
    if ((*a)[0] == "request_and_send")
      return ResolvedOperation{
          "service.request_and_send", {count}, conditionType(b), {}, true};
    if ((*a)[0] == "sum")
      return ResolvedOperation{"service.sum", {vector}, count, {}, false};
    return error("unknown-operation");
  }
};
// Deliberately conflicting installation used only by the example's admission
// test.
class ShadowDialect final : public Dialect {
public:
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(ShadowDialect)
  explicit ShadowDialect(MLIRContext *context)
      : Dialect(getDialectNamespace(), context, TypeID::get<ShadowDialect>()) {
    addInterfaces<ServiceLibrary>();
  }
  static llvm::StringRef getDialectNamespace() { return "shadow_service"; }
};
} // namespace
void ServiceDialect::initialize() {
  addTypes<CountType, VectorType, PredicateType>();
  addOperations<RequestOp, SendOp, RequestAndSendOp, SumOp, ForeignSendOp>();
  addInterfaces<ServiceLibrary>();
}
llvm::json::Value RequestOp::getSourceDescriptor() {
  return llvm::json::Array{"request"};
}
llvm::json::Value SendOp::getSourceDescriptor() {
  return llvm::json::Array{"send"};
}
llvm::json::Value RequestAndSendOp::getSourceDescriptor() {
  return llvm::json::Array{"request_and_send"};
}
LogicalResult RequestAndSendOp::verify() {
  return verifySourceOperationContext(getOperation());
}
llvm::json::Value SumOp::getSourceDescriptor() {
  return llvm::json::Array{"sum"};
}
llvm::json::Value ForeignSendOp::getSourceDescriptor() {
  return llvm::json::Array{"send"};
}
LogicalResult RequestOp::verify() {
  return verifySourceOperationContext(getOperation());
}
LogicalResult SendOp::verify() {
  return verifySourceOperationContext(getOperation());
}
LogicalResult SumOp::verify() {
  return verifySourceOperationContext(getOperation());
}
LogicalResult ForeignSendOp::verify() {
  return verifySourceOperationContext(getOperation());
}
void registerService(DialectRegistry &registry, bool ambiguous) {
  registerDialects(registry);
  registry.insert<ServiceDialect>();
  if (ambiguous)
    registry.insert<ShadowDialect>();
}
} // namespace zkc::service
