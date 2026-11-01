#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/UB/IR/UBOps.h"
#include "mlir/Dialect/Vector/IR/VectorOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ResidueTile.h"
#include "zkc/Dialect/Data/IR/DataDialect.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"
#include "zkc/Transforms/Residue.h"
#include "llvm/ADT/ScopeExit.h"
#include <future>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr StringLiteral sourceText = R"mlir(
!R = !residue.value<12289 : ui16>
module {
 func.func @tile(%x: !R, %y: !R) -> !R {
  %square = residue.multiply %x, %x : !R
  %result = residue.add %square, %y : !R
  return %result : !R
 }
}
)mlir";
}
int main() {
  DialectRegistry registry;
  registry.insert<residue::ResidueDialect, arith::ArithDialect,
                  func::FuncDialect>();
  MLIRContext context(registry);
  auto source = parseSourceString<ModuleOp>(sourceText, &context);
  require(bool(source), "tile source failed to parse");
  Cases cases;
  cases.run(
      "tile initialization leaves unrelated registered dialects lazy", [&] {
        DialectRegistry lazyRegistry;
        lazyRegistry.insert<residue::ResidueDialect, func::FuncDialect,
                            data::DataDialect>();
        MLIRContext lazy(lazyRegistry);
        auto original = parseSourceString<ModuleOp>(sourceText, &lazy);
        require(bool(original) && !lazy.getLoadedDialect<data::DataDialect>(),
                "lazy fixture eagerly loaded Data");
        auto tile = residue::proposeTile(*original, {true, false}, 8);
        require(bool(tile) && !lazy.getLoadedDialect<data::DataDialect>(),
                "tile initialization loaded unrelated Data");
        require(bool(residue::readTile(*original, {true, false}, *tile)),
                "lazy tile failed independent admission");
      });
  cases.run(
      "prepared tile dependencies are read-only during parallel calls", [&] {
        residue::initializeTileDialects(context);
        context.enterMultiThreadedExecution();
        auto leave =
            llvm::scope_exit([&] { context.exitMultiThreadedExecution(); });
        auto work = [&] {
          auto tile = residue::proposeTile(*source, {true, false}, 8);
          return bool(tile) &&
                 bool(residue::readTile(*source, {true, false}, *tile));
        };
        auto first = std::async(std::launch::async, work);
        auto second = std::async(std::launch::async, work);
        require(first.get() && second.get(),
                "parallel tile construction failed");
      });
  for (unsigned lanes : {1, 8, 256})
    for (unsigned mask : {0, 1, 3})
      cases.run(
          "standard private tile " + Twine(lanes) + "/" + Twine(mask), [&] {
            SmallVector<bool> rowwise{bool(mask & 1), bool(mask & 2)};
            auto candidate = residue::proposeTile(*source, rowwise, lanes);
            require(bool(candidate),
                    "standard vectorization/bufferization failed");
            require(succeeded(verify(*candidate)),
                    "private tile failed MLIR verification");
            unsigned allocations = 0, stores = 0;
            candidate->walk([&](memref::AllocOp) { ++allocations; });
            candidate->walk([&](vector::TransferWriteOp) { ++stores; });
            require(allocations == 1 && stores == 1,
                    "tile did not retain one fresh complete output");
            auto read = residue::readTile(*source, rowwise, *candidate);
            require(bool(read),
                    "independent tile reader refused standard output");
            require(read->lanes == lanes && read->peakPrivateBytes == 2 * lanes,
                    "actual tile extent or requested storage was not read");
          });
  SmallVector<bool> rowwise{true, false};
  auto base = residue::proposeTile(*source, rowwise, 8);
  require(bool(base), "mutation control failed to produce a tile");
  auto mutation = [&](StringRef name,
                      llvm::function_ref<void(func::FuncOp)> change) {
    cases.run(name, [&] {
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(base->clone()));
      require(bool(residue::readTile(*source, rowwise, *candidate)),
              "pre-mutation tile was not admitted");
      change(*candidate->getOps<func::FuncOp>().begin());
      require(succeeded(verify(*candidate)), "mutation is malformed MLIR");
      std::vector<diagnostics::RefusalInfo> failures;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        auto codes = diagnostics::refusals(diagnostic);
        failures.insert(failures.end(), codes.begin(), codes.end());
        return success();
      });
      require(!residue::readTile(*source, rowwise, *candidate),
              "mutated tile retained stale admission");
      require(llvm::any_of(
                  failures,
                  [](const auto &r) { return r.code == "represented-tile"; }),
              "refusal lost represented-tile");
    });
  };
  mutation("write to borrowed input", [](func::FuncOp function) {
    auto store = *function.getOps<vector::TransferWriteOp>().begin();
    store->setOperand(1, function.getArgument(0));
  });
  mutation("publish borrowed input", [](func::FuncOp function) {
    function.front().getTerminator()->setOperand(0, function.getArgument(0));
  });
  mutation("read uninitialized allocation", [](func::FuncOp function) {
    auto load = *function.getOps<vector::TransferReadOp>().begin();
    auto allocate = *function.getOps<memref::AllocOp>().begin();
    load->setOperand(0, allocate);
  });
  mutation("unreleased private allocation", [](func::FuncOp function) {
    OpBuilder builder(function.front().getTerminator());
    memref::AllocOp::create(builder, function.getLoc(),
                            cast<MemRefType>(function.getResultTypes()[0]));
  });
  mutation("released output owner", [](func::FuncOp function) {
    auto *returned = function.front().getTerminator();
    OpBuilder builder(returned);
    memref::DeallocOp::create(builder, function.getLoc(),
                              returned->getOperand(0));
  });
  mutation("store after release through alias", [](func::FuncOp function) {
    auto store = *function.getOps<vector::TransferWriteOp>().begin();
    OpBuilder builder(store);
    auto allocation = store.getBase();
    auto alias = memref::CastOp::create(builder, store.getLoc(),
                                        allocation.getType(), allocation);
    memref::DeallocOp::create(builder, store.getLoc(), alias);
  });
  mutation("release borrowed owner", [](func::FuncOp function) {
    OpBuilder builder(function.front().getTerminator());
    memref::DeallocOp::create(builder, function.getLoc(),
                              function.getArgument(0));
  });
  mutation("double release", [](func::FuncOp function) {
    OpBuilder builder(function.front().getTerminator());
    auto temporary =
        memref::AllocOp::create(builder, function.getLoc(),
                                cast<MemRefType>(function.getResultTypes()[0]));
    memref::DeallocOp::create(builder, function.getLoc(), temporary);
    memref::DeallocOp::create(builder, function.getLoc(), temporary);
  });
  mutation("claimed bounds with changed offset", [](func::FuncOp function) {
    auto load = *function.getOps<vector::TransferReadOp>().begin();
    OpBuilder builder(load);
    auto one = arith::ConstantIndexOp::create(builder, load.getLoc(), 1);
    load.getIndicesMutable().assign(ValueRange{one});
    load.setInBoundsAttr(builder.getBoolArrayAttr({true}));
  });
  mutation("poison escapes transfer padding", [](func::FuncOp function) {
    auto extend = *function.getOps<arith::ExtUIOp>().begin();
    auto poison = *function.getOps<ub::PoisonOp>().begin();
    OpBuilder builder(extend);
    auto vector = vector::BroadcastOp::create(builder, extend.getLoc(),
                                              extend.getIn().getType(), poison);
    extend->setOperand(0, vector);
  });
  mutation("masked read", [](func::FuncOp function) {
    auto load = *function.getOps<vector::TransferReadOp>().begin();
    OpBuilder builder(load);
    auto type = VectorType::get({8}, builder.getI1Type());
    auto mask = arith::ConstantOp::create(
        builder, load.getLoc(), type,
        DenseElementsAttr::get(type, builder.getBoolAttr(true)));
    load.getMaskMutable().assign(ValueRange{mask});
  });
  mutation("changed word modulus", [](func::FuncOp function) {
    auto remainder = *function.getOps<arith::RemUIOp>().begin();
    OpBuilder builder(remainder);
    auto type = cast<VectorType>(remainder.getType());
    auto wrong = arith::ConstantOp::create(
        builder, remainder.getLoc(), type,
        DenseElementsAttr::get(
            type, builder.getIntegerAttr(type.getElementType(), 12287)));
    remainder->setOperand(1, wrong);
  });
  mutation("unsupported alignment", [](func::FuncOp function) {
    auto allocate = *function.getOps<memref::AllocOp>().begin();
    allocate.setAlignment(128);
  });
  mutation("unknown memory operation attribute", [](func::FuncOp function) {
    auto load = *function.getOps<vector::TransferReadOp>().begin();
    load->setAttr("approval", UnitAttr::get(function.getContext()));
  });
  mutation("wrong extent with asserted bounds", [](func::FuncOp function) {
    auto load = *function.getOps<vector::TransferReadOp>().begin();
    OpBuilder builder(load);
    auto type = MemRefType::get({4}, builder.getI16Type());
    auto smaller = memref::AllocOp::create(builder, load.getLoc(), type);
    load->setOperand(0, smaller);
    load.setInBoundsAttr(builder.getBoolArrayAttr({true}));
  });
  cases.run("actual bounds admit either transfer assertion", [&] {
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(base->clone()));
    auto function = *candidate->getOps<func::FuncOp>().begin();
    OpBuilder builder(&context);
    auto load = *function.getOps<vector::TransferReadOp>().begin();
    load.setInBoundsAttr(builder.getBoolArrayAttr({true}));
    auto store = *function.getOps<vector::TransferWriteOp>().begin();
    store.setInBoundsAttr(builder.getBoolArrayAttr({true}));
    require(bool(residue::readTile(*source, rowwise, *candidate)),
            "reader depended on transfer flag spelling");
  });
  cases.run("safe alias and released staging owner", [&] {
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(base->clone()));
    auto function = *candidate->getOps<func::FuncOp>().begin();
    auto *returned = function.front().getTerminator();
    auto original = returned->getOperand(0);
    OpBuilder builder(returned);
    auto type = cast<MemRefType>(original.getType());
    auto temporary = memref::AllocOp::create(builder, function.getLoc(), type);
    auto alias =
        memref::CastOp::create(builder, function.getLoc(), type, temporary);
    memref::CopyOp::create(builder, function.getLoc(), original, alias);
    memref::DeallocOp::create(builder, function.getLoc(), original);
    returned->setOperand(0, temporary);
    auto read = residue::readTile(*source, rowwise, *candidate);
    require(bool(read) && read->peakPrivateBytes == 32,
            "safe memory alternative did not retain exact ownership and peak "
            "bytes");
  });
  for (StringRef type : {"2130706433 : ui32", "18446744069414584321 : ui64",
                         "18446744073709551615 : ui64"})
    cases.run("full-width represented tile " + type, [&] {
      std::string text = sourceText.str();
      const std::string old = "12289 : ui16";
      text.replace(text.find(old), old.size(), type.str());
      auto wideSource = parseSourceString<ModuleOp>(text, &context);
      require(bool(wideSource), "wide tile source failed to parse");
      auto candidate = residue::proposeTile(*wideSource, rowwise, 8);
      require(bool(candidate), "wide tile proposal failed");
      auto read = residue::readTile(*wideSource, rowwise, *candidate);
      require(bool(read), "wide tile readback failed");
      require(read->peakPrivateBytes == (type.contains("ui32") ? 32u : 64u),
              "wide tile storage used the wrong word width");
    });
  return cases.result();
}
