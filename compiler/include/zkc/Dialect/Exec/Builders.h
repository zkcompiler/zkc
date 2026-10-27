#ifndef ZKC_DIALECT_EXEC_BUILDERS_H
#define ZKC_DIALECT_EXEC_BUILDERS_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "llvm/ADT/STLFunctionalExtras.h"

namespace zkc::exec {
// Mechanical construction of scoped CFG and transient SCF loops. Callers own
// source and result-type selection and construct the actual outlined bodies. No
// native record, source checker, admission cache or physical plan is stored
// here. Callbacks return a formed scoped function; construction restores this
// builder's insertion point even if the callback shares the builder. A null
// callback result aborts that control construction. The caller owns the
// failure state and discards its partial candidate before publication.
class ScopedExecutionBuilder {
public:
  using Values = llvm::SmallVector<mlir::Value>;
  using RegionBuilder = llvm::function_ref<mlir::func::FuncOp(unsigned)>;

  enum class LoopForm { CFG, Structured };
  ScopedExecutionBuilder(mlir::OpBuilder &builder, mlir::func::FuncOp function,
                         LoopForm loops = LoopForm::CFG);
  LoopForm getLoopForm() const { return loops; }
  mlir::func::FuncOp getFunction() const { return function; }
  mlir::Value getScope() const { return scope; }
  mlir::Location getLocation() const { return location; }
  void setLocation(mlir::Location value) { location = value; }
  Values scoped(mlir::ValueRange inputs);
  Values invoke(llvm::StringRef name, mlir::TypeRange outputs,
                mlir::ValueRange inputs,
                llvm::ArrayRef<mlir::NamedAttribute> attributes = {},
                mlir::Block *stop = nullptr);
  Values conditional(mlir::Value condition, mlir::ValueRange captures,
                     mlir::TypeRange outputs, llvm::StringRef site,
                     RegionBuilder body);
  Values match(mlir::Value input, mlir::ValueRange captures,
               mlir::TypeRange outputs,
               llvm::ArrayRef<std::string> alternatives, llvm::StringRef site,
               RegionBuilder body);
  Values loop(mlir::Value lower, mlir::Value upper, mlir::ValueRange seeds,
              mlir::ValueRange captures, mlir::TypeRange outputs,
              bool conditional, llvm::StringRef site, RegionBuilder body);
  // Transient numerical schedule. SCF carries continuation and outcome state;
  // reached scope/transfer actions remain explicit. Native admission requires
  // the corresponding flat CFG and does not accept this scheduling form.
  Values scheduledLoop(mlir::Value lower, mlir::Value upper,
                       mlir::ValueRange seeds, mlir::ValueRange captures,
                       mlir::TypeRange outputs, bool conditional,
                       llvm::StringRef site, RegionBuilder body);
  void release(mlir::ValueRange values);
  void reject(llvm::StringRef reason, llvm::StringRef site);
  // Charged native completion. Source helper return packaging has a different
  // meaning and must not call this as an implementation shortcut.
  void complete(mlir::ValueRange values);
  // Ordinary source helper packaging does not perform a native completion.
  void returned(mlir::ValueRange values);

private:
  mlir::OpBuilder &builder;
  mlir::Location location;
  mlir::func::FuncOp function;
  mlir::Value scope;
  exec::OutcomeType result;
  mlir::Block *failure = nullptr;
  mlir::Region *insertionRegion;
  LoopForm loops;
  mlir::Operation *make(llvm::StringRef name, mlir::TypeRange types,
                        mlir::ValueRange operands,
                        llvm::ArrayRef<mlir::NamedAttribute> attributes = {},
                        llvm::ArrayRef<mlir::Block *> successors = {});
  mlir::NamedAttribute text(llvm::StringRef name, llvm::StringRef value);
  mlir::Block *block(mlir::TypeRange types = {});
  mlir::Block *failed();
  void branch(mlir::Block *target, mlir::ValueRange values = {});
  exec::OutcomeType outcome(mlir::TypeRange payload);
  runtime::TransferType transfer(mlir::TypeRange payload);
  Values dispatch(mlir::Value result, mlir::Block *stop);
  Values accept(mlir::Value held, mlir::TypeRange types);
  mlir::func::FuncOp outline(RegionBuilder body, unsigned index);
  mlir::Value region(mlir::func::FuncOp helper, mlir::ValueRange inputs,
                     mlir::TypeRange outputs, llvm::StringRef kind,
                     llvm::StringRef site, llvm::StringRef selection = {},
                     mlir::Value coordinate = {}, mlir::Block *stop = nullptr);
};
} // namespace zkc::exec
#endif
