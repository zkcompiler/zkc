#include "../lib/Transforms/Computation/Schedule.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "support/NumericalLoops.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::loops;
namespace {
protocol_ir::ProtocolModuleOp owner(mlir::ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
// Independently spell the expected traversal, ports, primitive occurrences and
// completion rules. No schedule reader or consumer supplies this body.
OwningOpRef<mlir::ModuleOp> expected(MLIRContext &context, bool omit = false,
                                     bool extra = false,
                                     bool structured = false) {
  auto location = UnknownLoc::get(&context);
  OwningOpRef<mlir::ModuleOp> module(mlir::ModuleOp::create(location));
  OpBuilder builder(module->getBody(), module->getBody()->end());
  auto root = protocol_ir::ProtocolModuleOp::create(
      builder, location, protocol_ir::Profile::Exec, mlir::ArrayAttr{});
  root.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&root.getBody().front());
  for (auto [name, contract] :
       {std::pair{"add", "field.add"}, std::pair{"subtract", "field.sub"}})
    runtime::BindingOp::create(builder, location, name, contract,
                               builder.getStrArrayAttr({"bls12-381.fr"}), "");
  auto field = algebra::FieldType::get(&context, "bls12-381.fr");
  auto index = builder.getIntegerType(64, false);
  auto scope = runtime::ScopeType::get(&context);
  auto result = exec::OutcomeType::get(&context, {field, field});
  auto entry = func::FuncOp::create(
      builder, location, "evaluate",
      builder.getFunctionType({scope, index, index, field, field, field, field},
                              {result}));
  entry.setPrivate();
  entry.setNoInline(true);
  entry->setAttr("runtime.origin",
                 builder.getArrayAttr({builder.getStringAttr("evaluate"),
                                       builder.getArrayAttr({})}));
  entry.addEntryBlock();
  builder.setInsertionPointToEnd(&entry.front());
  exec::ScopedExecutionBuilder control(builder, entry);
  auto buildLoop = structured ? &exec::ScopedExecutionBuilder::scheduledLoop
                              : &exec::ScopedExecutionBuilder::loop;
  auto outputs = (control.*buildLoop)(
      entry.getArgument(1), entry.getArgument(2),
      entry.getArguments().slice(3, 2), entry.getArguments().slice(5, 2),
      TypeRange{field, field}, false, "traverse", [&](unsigned) {
        OpBuilder::InsertionGuard restore(builder);
        builder.setInsertionPointToEnd(&root.getBody().front());
        auto body = func::FuncOp::create(
            builder, location, "body",
            builder.getFunctionType({scope, index, field, field, field, field},
                                    {result}));
        body.setPrivate();
        body.setNoInline(true);
        body->setAttr("runtime.region", builder.getUnitAttr());
        body.addEntryBlock();
        builder.setInsertionPointToEnd(&body.front());
        exec::ScopedExecutionBuilder inner(builder, body);
        auto apply = [&](StringRef name, StringRef site, ValueRange inputs) {
          return inner.invoke(
              "exec.apply", TypeRange{field}, inner.scoped(inputs),
              {builder.getNamedAttr("binding",
                                    FlatSymbolRefAttr::get(&context, name)),
               builder.getNamedAttr("parameters", builder.getArrayAttr({})),
               builder.getNamedAttr("site", builder.getStringAttr(site))})[0];
        };
        Value sum = body.getArgument(2);
        if (!omit)
          sum = apply("add", "sum", {sum, body.getArgument(4)});
        if (extra)
          (void)apply("add", "extra", {sum, body.getArgument(4)});
        auto next = apply("subtract", "next", {sum, body.getArgument(5)});
        inner.complete({body.getArgument(3), next});
        return body;
      });
  control.returned(outputs);
  return module;
}
OwningOpRef<mlir::ModuleOp> scheduled(MLIRContext &context) {
  return expected(context, false, false, true);
}
void acceptSchedule(mlir::ModuleOp schedule, mlir::ModuleOp actual) {
  require(succeeded(computation::verifyRecipeOutput(actual)),
          "scoped recipe admission refused");
  require(succeeded(computation::verifyScheduleLowering(schedule, actual)),
          "actual scoped schedule differs");
}
void rejectLowering(mlir::ModuleOp schedule, mlir::ModuleOp actual) {
  require(succeeded(computation::verifyScheduledRecipeOutput(schedule)) &&
              succeeded(computation::verifyRecipeOutput(actual)),
          "semantic mutation must remain natively admitted");
  finite::VerificationResult outcome{finite::VerificationStatus::Verified, {}};
  require(failed(computation::verifyScheduleLowering(schedule, actual, nullptr,
                                                     &outcome)) &&
              outcome.status == finite::VerificationStatus::Mismatch,
          "native difference accepted or classified as capacity");
}
void annotate(mlir::ModuleOp module, bool changedArgument = false,
              bool changedResult = false) {
  OpBuilder builder(module.getContext());
  auto note = [&](StringRef value) {
    return builder.getDictionaryAttr(
        {builder.getNamedAttr("test.note", builder.getStringAttr(value))});
  };
  auto binding = SymbolTable(owner(module)).lookup<runtime::BindingOp>("add");
  binding.setArgAttrsAttr(builder.getArrayAttr(
      {note("scope"), note(changedArgument ? "changed" : "left"),
       note("right")}));
  binding.setResAttrsAttr(
      builder.getArrayAttr({note(changedResult ? "changed" : "outcome")}));
}
// A second ordinary root and its outlined body are dormant relative to
// evaluate, but remain part of the checked closure. Preserve their inventory
// even when testing changes to only the dormant body or selected child symbol.
void addDormantRoot(mlir::ModuleOp module) {
  auto root = owner(module);
  SymbolTable symbols(root);
  auto body = cast<func::FuncOp>(symbols.lookup("body")->clone());
  body.setSymName("unused_body");
  root.getBody().front().push_back(body);
  auto entry = cast<func::FuncOp>(symbols.lookup("evaluate")->clone());
  entry.setSymName("unused");
  OpBuilder builder(module.getContext());
  entry->setAttr("runtime.origin",
                 builder.getArrayAttr({builder.getStringAttr("unused"),
                                       builder.getArrayAttr({})}));
  entry.walk([&](func::CallOp call) {
    if (call.getCallee() == "body")
      call.setCallee("unused_body");
  });
  root.getBody().front().push_back(entry);
}
void addConstant(mlir::ModuleOp module) {
  auto root = owner(module);
  OpBuilder builder(&root.getBody().front(), root.getBody().front().end());
  auto location = module.getLoc();
  auto field = algebra::FieldType::get(module.getContext(), "bls12-381.fr");
  runtime::BindingOp::create(builder, location, "constant", "field.constant",
                             builder.getStrArrayAttr({"bls12-381.fr"}), "");
  auto entry = func::FuncOp::create(
      builder, location, "literal",
      builder.getFunctionType(
          {runtime::ScopeType::get(module.getContext())},
          {exec::OutcomeType::get(module.getContext(), {field})}));
  entry.setPrivate();
  entry.setNoInline(true);
  entry->setAttr("runtime.origin",
                 builder.getArrayAttr({builder.getStringAttr("literal"),
                                       builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(entry.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, entry);
  auto values = control.invoke(
      "exec.apply", TypeRange{field}, control.scoped(ValueRange{}),
      {builder.getNamedAttr(
           "binding", FlatSymbolRefAttr::get(module.getContext(), "constant")),
       builder.getNamedAttr(
           "parameters", builder.getArrayAttr(
                             {take(algebra::decodeFieldLiteral(field, "7"))})),
       builder.getNamedAttr("site", builder.getStringAttr("literal"))});
  control.returned(values);
}
// The actual loop carries nested native sequences and invokes a typed binding.
// Its depth is within native admission but outside the byte type grammar.
OwningOpRef<mlir::ModuleOp>
nestedSequence(MLIRContext &context, bool structured, unsigned depth = 12) {
  auto location = UnknownLoc::get(&context);
  OwningOpRef<mlir::ModuleOp> module(mlir::ModuleOp::create(location));
  OpBuilder builder(module->getBody(), module->getBody()->end());
  auto root = protocol_ir::ProtocolModuleOp::create(
      builder, location, protocol_ir::Profile::Exec, mlir::ArrayAttr{});
  root.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&root.getBody().front());
  Type element = algebra::FieldType::get(&context, "bls12-381.fr");
  for (unsigned i = 0; i < depth; ++i)
    element = data::SequenceType::get(&context, element);
  auto sequence = data::SequenceType::get(&context, element);
  runtime::BindingOp::create(builder, location, "append", "sequence.append",
                             builder.getArrayAttr({TypeAttr::get(element)}),
                             "");
  auto scope = runtime::ScopeType::get(&context);
  auto index = builder.getIntegerType(64, false);
  auto outcome = exec::OutcomeType::get(&context, {sequence});
  auto function = [&](StringRef name, TypeRange inputs, bool region) {
    auto result = func::FuncOp::create(
        builder, location, name, builder.getFunctionType(inputs, {outcome}));
    result.setPrivate();
    result.setNoInline(true);
    if (region)
      result->setAttr("runtime.region", builder.getUnitAttr());
    else
      result->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr(name),
                                            builder.getArrayAttr({})}));
    result.addEntryBlock();
    return result;
  };
  auto entry =
      function("evaluate", {scope, index, index, sequence, element}, false);
  builder.setInsertionPointToEnd(&entry.front());
  exec::ScopedExecutionBuilder control(builder, entry);
  auto buildLoop = structured ? &exec::ScopedExecutionBuilder::scheduledLoop
                              : &exec::ScopedExecutionBuilder::loop;
  auto outputs = (control.*buildLoop)(
      entry.getArgument(1), entry.getArgument(2), entry.getArgument(3),
      entry.getArgument(4), TypeRange{sequence}, false, "append_all",
      [&](unsigned) {
        OpBuilder::InsertionGuard restore(builder);
        builder.setInsertionPointToEnd(&root.getBody().front());
        auto body = function("body", {scope, index, sequence, element}, true);
        builder.setInsertionPointToEnd(&body.front());
        exec::ScopedExecutionBuilder inner(builder, body);
        auto next = inner.invoke(
            "exec.apply", TypeRange{sequence},
            inner.scoped(body.getArguments().drop_front(2)),
            {builder.getNamedAttr("binding",
                                  FlatSymbolRefAttr::get(&context, "append")),
             builder.getNamedAttr("parameters", builder.getArrayAttr({})),
             builder.getNamedAttr("site", builder.getStringAttr("append"))});
        inner.complete(next);
        return body;
      });
  control.returned(outputs);
  return module;
}
OwningOpRef<mlir::ModuleOp> authored(MLIRContext &context, StringRef filename,
                                     StringRef entryName) {
  auto input = parseSourceFile<mlir::ModuleOp>(
      std::string(ZKC_LOOP_FIXTURES) + "/../runtime/" + filename.str(),
      &context);
  require(bool(input), "missing independently authored execution fixture");
  auto entry = input->lookupSymbol<func::FuncOp>(entryName);
  auto completion =
      cast<exec::CompleteOp>(operations(entry, "exec.complete").front());
  OpBuilder builder(completion);
  auto returned = exec::ReturnOp::create(builder, completion.getLoc(),
                                         completion.getOutcome().getType(),
                                         completion.getValues());
  completion.getOutcome().replaceAllUsesWith(returned.getOutcome());
  completion.erase();
  OwningOpRef<mlir::ModuleOp> result(mlir::ModuleOp::create(input->getLoc()));
  builder.setInsertionPointToEnd(result->getBody());
  auto root = protocol_ir::ProtocolModuleOp::create(
      builder, input->getLoc(), protocol_ir::Profile::Exec, mlir::ArrayAttr{});
  root.getBody().takeBody(input->getBodyRegion());
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<scf::SCFDialect, arith::ArithDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run(
      "numerical candidate ports read the actual scoped SCF schedule", [&] {
        auto schedule = expected(context, false, false, true);
        auto flat = expected(context);
        auto root = owner(*schedule);
        auto entry = SymbolTable(root).lookup<func::FuncOp>("evaluate");
        auto actual = protocol::readScheduledExecutionClosure(root);
        require(bool(actual), actual ? "" : llvm::toString(actual.takeError()));
        acceptSchedule(*schedule, *flat);
        auto view = mathematical::ScopedCandidate::readSchedule(root);
        require(bool(view), view ? "" : llvm::toString(view.takeError()));
        mathematical::CandidatePorts ports(view->get());
        auto *loop = ports.first(&entry.front());
        require(isa_and_nonnull<exec::RangeOp>(loop) &&
                    ports.bodies(loop) == 1 &&
                    ports.inputs(loop) == entry.getArguments().drop_front() &&
                    ports.outputs(loop).size() == 2,
                "loop data coordinates differ from actual schedule");
        auto *body = ports.body(loop, 0);
        auto *sum = ports.first(body);
        require(ports.arguments(body).size() == 5 &&
                    isa_and_nonnull<exec::ApplyOp>(sum) &&
                    ports.inputs(sum) == ValueRange{body->getArgument(2),
                                                    body->getArgument(4)} &&
                    ports.producer(ports.outputs(sum).front()) == sum,
                "outlined scalar association did not retain actual SSA");
        auto *returned = ports.next(loop);
        require(isa_and_nonnull<exec::ReturnOp>(returned) &&
                    !ports.next(returned) &&
                    ports.inputs(returned) == ports.outputs(loop),
                "scheduled output boundary differs");
      });
  cases.run("independent SCF and scoped execution agree", [&] {
    auto schedule = scheduled(context), native = expected(context);
    auto before = clone(*schedule), nativeBefore = clone(*native);
    acceptSchedule(*schedule, *native);
    uint64_t remaining = 1000000;
    auto result = computation::consumeSchedule(*schedule, remaining);
    require(bool(result), "scoped schedule consumption failed");
    acceptSchedule(*schedule, *result);
    require(same(*schedule, *before) && same(*native, *nativeBefore),
            "reader changed its input");
  });
  cases.run("native ABI annotations survive comparison and consumption", [&] {
    auto schedule = scheduled(context), native = expected(context);
    annotate(*schedule);
    annotate(*native);
    auto before = clone(*schedule), nativeBefore = clone(*native);
    require(succeeded(computation::verifyScheduledRecipeOutput(*schedule)),
            "annotated native schedule refused");
    acceptSchedule(*schedule, *native);
    uint64_t remaining = 1000000;
    auto consumed = computation::consumeSchedule(*schedule, remaining);
    require(bool(consumed), "annotated schedule was not consumed");
    acceptSchedule(*schedule, *consumed);
    auto binding =
        SymbolTable(owner(*consumed)).lookup<runtime::BindingOp>("add");
    refuses(protocol::readBinding(binding), "binding-attributes");
    require(same(*schedule, *before) && same(*native, *nativeBefore),
            "annotation comparison mutated its input");
  });
  for (bool argument : {false, true})
    for (bool changeSchedule : {false, true})
      cases.run(
          std::string(changeSchedule ? "schedule" : "execution") +
              " annotation mismatch: " + (argument ? "argument" : "result"),
          [&] {
            auto schedule = scheduled(context), native = expected(context);
            annotate(*schedule, changeSchedule && argument,
                     changeSchedule && !argument);
            annotate(*native, !changeSchedule && argument,
                     !changeSchedule && !argument);
            rejectLowering(*schedule, *native);
          });
  cases.run("native loop types need not fit the byte profile", [&] {
    auto schedule = nestedSequence(context, true);
    auto native = nestedSequence(context, false);
    auto before = clone(*schedule), nativeBefore = clone(*native);
    acceptSchedule(*schedule, *native);
    uint64_t remaining = 1000000;
    auto consumed = computation::consumeSchedule(*schedule, remaining);
    require(bool(consumed), "deep native schedule was not consumed");
    acceptSchedule(*schedule, *consumed);
    auto binding =
        SymbolTable(owner(*consumed)).lookup<runtime::BindingOp>("append");
    refuses(protocol::readBinding(binding), "binding-type-limit");
    require(same(*schedule, *before) && same(*native, *nativeBefore),
            "native type comparison mutated its input");
  });
  cases.run("native types outside byte profile must still match exactly", [&] {
    auto schedule = nestedSequence(context, true);
    auto native = nestedSequence(context, false, 11);
    rejectLowering(*schedule, *native);
  });
  cases.run("typed invocation parameters in a dormant root must agree", [&] {
    auto schedule = scheduled(context), native = expected(context);
    addConstant(*schedule);
    addConstant(*native);
    acceptSchedule(*schedule, *native);
    auto literal = SymbolTable(owner(*native)).lookup<func::FuncOp>("literal");
    auto *apply = operations(literal, "exec.apply").front();
    auto field = algebra::FieldType::get(&context, "bls12-381.fr");
    apply->setAttr("parameters",
                   OpBuilder(&context).getArrayAttr(
                       {take(algebra::decodeFieldLiteral(field, "8"))}));
    rejectLowering(*schedule, *native);
  });
  for (StringRef mutation :
       {"dormant instruction", "dormant result", "child symbols",
        "binding symbol", "unused binding", "missing dormant root"})
    cases.run("complete native closure comparison refuses " + mutation, [&] {
      auto schedule = scheduled(context), native = expected(context);
      for (auto module : {*schedule, *native}) {
        addDormantRoot(module);
        auto root = owner(module);
        auto *binding = SymbolTable(root).lookup("add")->clone();
        SymbolTable::setSymbolName(binding, "other_add");
        root.getBody().front().push_back(binding);
      }
      acceptSchedule(*schedule, *native);
      auto root = owner(*native);
      SymbolTable symbols(root);
      auto unused = symbols.lookup<func::FuncOp>("unused");
      auto body = symbols.lookup<func::FuncOp>("unused_body");
      if (mutation == "dormant instruction") {
        auto *apply = operations(body, "exec.apply").front();
        apply->setOperand(2, apply->getOperand(1));
      } else if (mutation == "dormant result") {
        auto *complete = operations(body, "exec.complete").front();
        auto left = complete->getOperand(1), right = complete->getOperand(2);
        complete->setOperand(1, right);
        complete->setOperand(2, left);
      } else if (mutation == "child symbols") {
        // Both children remain reachable and have identical types and bodies.
        // The changed control association must still be detected.
        root.walk([&](func::CallOp call) {
          if (call.getCallee() == "body")
            call.setCallee("unused_body");
          else if (call.getCallee() == "unused_body")
            call.setCallee("body");
        });
      } else if (mutation == "binding symbol")
        operations(body, "exec.apply")
            .front()
            ->setAttr("binding", FlatSymbolRefAttr::get(&context, "other_add"));
      else if (mutation == "unused binding") {
        OpBuilder builder(&context);
        symbols.lookup("other_add")
            ->setAttr("res_attrs",
                      builder.getArrayAttr(
                          {builder.getDictionaryAttr({builder.getNamedAttr(
                              "test.note", builder.getUnitAttr())})}));
      } else {
        unused.erase();
        body.erase();
      }
      rejectLowering(*schedule, *native);
    });
  cases.run("native comparison permits declaration order and SSA renaming",
            [&] {
              auto schedule = scheduled(context), native = expected(context);
              auto root = owner(*native);
              auto body = SymbolTable(root).lookup<func::FuncOp>("body");
              body->moveBefore(&root.getBody().front(),
                               root.getBody().front().begin());
              body->setLoc(FileLineColLoc::get(&context, "renamed", 3, 4));
              acceptSchedule(*schedule, *native);
            });
  cases.run("authored conditional SCF and CFG fixtures agree natively", [&] {
    auto schedule = authored(context, "execution-scheduled-loop.mlir", "loop");
    auto native = authored(context, "execution-loop.mlir", "loop");
    acceptSchedule(*schedule, *native);
    uint64_t remaining = 1000000;
    auto consumed = computation::consumeSchedule(*schedule, remaining);
    require(bool(consumed), "conditional schedule consumption failed");
    acceptSchedule(*schedule, *consumed);
  });
  cases.run("native stop reasons remain part of schedule correspondence", [&] {
    auto schedule = authored(context, "execution-conditional.mlir", "work");
    auto native = authored(context, "execution-conditional.mlir", "work");
    acceptSchedule(*schedule, *native);
    operations(*native, "exec.reject")
        .front()
        ->setAttr("reason", StringAttr::get(&context, "abort"));
    rejectLowering(*schedule, *native);
  });
  cases.run("conditional loop flags and children must match exact roots", [&] {
    auto schedule = authored(context, "execution-scheduled-loop.mlir", "loop");
    auto native = authored(context, "execution-loop.mlir", "loop");
    auto build = [&](mlir::ModuleOp module, bool structured, bool swapped) {
      auto root = owner(module);
      SymbolTable symbols(root);
      auto loop = symbols.lookup<func::FuncOp>("loop");
      auto step = symbols.lookup<func::FuncOp>("step");
      auto always = symbols.lookup<func::FuncOp>("always");
      auto alwaysStep = symbols.lookup<func::FuncOp>("always_step");
      OpBuilder builder(&context);
      if (!always) {
        always = cast<func::FuncOp>(loop->clone());
        always.setSymName("always");
        always->setAttr("runtime.origin",
                        builder.getArrayAttr({builder.getStringAttr("always"),
                                              builder.getArrayAttr({})}));
        root.getBody().front().push_back(always);
        alwaysStep = cast<func::FuncOp>(step->clone());
        alwaysStep.setSymName("always_step");
        alwaysStep.setType(builder.getFunctionType(step.getArgumentTypes(),
                                                   loop.getResultTypes()));
        alwaysStep.getBody().dropAllReferences();
        alwaysStep.getBody().getBlocks().clear();
        builder.setInsertionPointToEnd(alwaysStep.addEntryBlock());
        exec::ScopedExecutionBuilder completion(builder, alwaysStep);
        completion.complete(alwaysStep.getArgument(2));
        root.getBody().front().push_back(alwaysStep);
      }
      for (auto [entry, conditional] :
           {std::pair{loop, !swapped}, std::pair{always, swapped}}) {
        entry.getBody().dropAllReferences();
        entry.getBody().getBlocks().clear();
        builder.setInsertionPointToEnd(entry.addEntryBlock());
        exec::ScopedExecutionBuilder control(builder, entry);
        auto buildLoop = structured
                             ? &exec::ScopedExecutionBuilder::scheduledLoop
                             : &exec::ScopedExecutionBuilder::loop;
        auto values = (control.*buildLoop)(
            entry.getArgument(1), entry.getArgument(2), entry.getArgument(3),
            entry.getArgument(4), entry.getArgument(3).getType(), conditional,
            "iterate", [&, selected = conditional](unsigned) {
              return selected ? step : alwaysStep;
            });
        control.returned(values);
      }
    };
    build(*schedule, true, false);
    build(*native, false, false);
    acceptSchedule(*schedule, *native);
    build(*native, false, true);
    auto expected =
        take(protocol::readScheduledExecutionClosure(owner(*schedule)));
    auto actual = take(protocol::readSourceExecutionClosure(owner(*native)));
    require(expected.bodies.at("loop").front().conditional &&
                !actual.bodies.at("loop").front().conditional,
            "mutation did not change the actual loop flag");
    rejectLowering(*schedule, *native);
  });
  for (StringRef mutation :
       {"bound", "seed order", "capture order", "state order", "formula",
        "site", "missing instruction", "extra instruction", "dormant body",
        "nominal domain"})
    cases.run("independent reader refuses " + mutation, [&] {
      auto schedule = scheduled(context);
      auto candidate = expected(context, mutation == "missing instruction",
                                mutation == "extra instruction");
      auto root = owner(*candidate);
      auto entry = SymbolTable(root).lookup<func::FuncOp>("evaluate");
      auto body = SymbolTable(root).lookup<func::FuncOp>("body");
      if (mutation == "bound") {
        auto range =
            cast<exec::RangeOp>(operations(entry, "exec.range").front());
        range->setOperand(2, range->getOperand(1));
      } else if (mutation == "seed order" || mutation == "capture order") {
        unsigned start = mutation == "seed order" ? 3 : 5;
        auto a = entry.getArgument(start), b = entry.getArgument(start + 1);
        entry.walk([&](Operation *op) {
          for (auto &operand : op->getOpOperands()) {
            if (operand.get() == a)
              operand.set(b);
            else if (operand.get() == b)
              operand.set(a);
          }
        });
      } else if (mutation == "state order")
        operations(body, "exec.complete")
            .front()
            ->setOperand(1, body.getArgument(2));
      else if (mutation == "formula") {
        auto *apply = operations(body, "exec.apply").front();
        apply->setOperand(2, apply->getOperand(1));
      } else if (mutation == "site")
        operations(body, "exec.apply")
            .front()
            ->setAttr("site", StringAttr::get(&context, "changed"));
      else if (mutation == "dormant body") {
        auto duplicate = cast<func::FuncOp>(body->clone());
        duplicate.setSymName("unused");
        root.getBody().front().push_back(duplicate);
      }
      if (mutation == "nominal domain")
        SymbolTable(root).lookup<runtime::BindingOp>("add")->setAttr(
            "arguments", OpBuilder(&context).getStrArrayAttr({"bn254.fr"}));
      if (mutation == "dormant body" || mutation == "nominal domain")
        require(failed(computation::verifyRecipeOutput(*candidate)),
                "invalid declaration must fail admission");
      else
        require(succeeded(computation::verifyRecipeOutput(*candidate)),
                "semantic mutation should remain admitted");
      require(
          failed(computation::verifyScheduleLowering(*schedule, *candidate)),
          "changed semantics accepted");
    });
  cases.run("consumer capacity preserves immutable source", [&] {
    auto schedule = scheduled(context), before = clone(*schedule);
    uint64_t remaining = 0;
    require(!computation::consumeSchedule(*schedule, remaining) && !remaining &&
                same(*schedule, *before),
            "capacity published or changed input");
  });
  cases.run("reader exact capacity boundary", [&] {
    auto schedule = scheduled(context), native = expected(context);
    uint64_t remaining = 100000;
    require(succeeded(computation::verifyScheduleLowering(*schedule, *native,
                                                          &remaining)),
            "positive reader control failed");
    uint64_t exact = 100000 - remaining, shortWork = exact - 1;
    require(succeeded(computation::verifyScheduleLowering(*schedule, *native,
                                                          &exact)) &&
                !exact,
            "exact allowance failed");
    finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                       {}};
    require(failed(computation::verifyScheduleLowering(*schedule, *native,
                                                       &shortWork, &outcome)) &&
                outcome.status == finite::VerificationStatus::RequiredCapacity,
            "short allowance misclassified");
  });
  cases.run("native association comparison debits the shared allowance", [&] {
    auto schedule = scheduled(context), native = expected(context);
    uint64_t structural = 0;
    for (auto module : {*schedule, *native})
      module.walk([&](Operation *op) {
        structural += 1 + op->getNumOperands() + op->getNumResults();
        for (auto &region : op->getRegions()) {
          ++structural;
          for (auto &block : region)
            structural += 1 + block.getNumArguments();
        }
      });
    finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                       {}};
    require(
        failed(computation::verifyScheduleLowering(*schedule, *native,
                                                   &structural, &outcome)) &&
            outcome.status == finite::VerificationStatus::RequiredCapacity &&
            outcome.capacity &&
            outcome.capacity->owner == WorkOwner::AlgorithmChecking &&
            !structural,
        "structural allowance hid uncharged association comparison");
    acceptSchedule(*schedule, *native);
  });
  cases.run("comparison bounds nesting before recursive formation", [&] {
    auto schedule = scheduled(context), native = expected(context);
    auto entry = SymbolTable(owner(*schedule)).lookup<func::FuncOp>("evaluate");
    OpBuilder builder(&context);
    builder.setInsertionPointToStart(&entry.front());
    for (unsigned i = 0; i < 70; ++i) {
      auto nested =
          scf::ExecuteRegionOp::create(builder, entry.getLoc(), TypeRange{});
      auto *block = builder.createBlock(&nested.getRegion());
      scf::YieldOp::create(builder, entry.getLoc());
      builder.setInsertionPointToStart(block);
    }
    finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                       {}};
    uint64_t remaining = 1000000;
    require(failed(computation::verifyScheduleLowering(*schedule, *native,
                                                       &remaining, &outcome)) &&
                outcome.status == finite::VerificationStatus::Mismatch &&
                remaining < 1000000,
            "excessive nesting reached recursive formation or became capacity");
  });
  cases.run("empty malformed blocks cannot evade inspection capacity", [&] {
    OwningOpRef<mlir::ModuleOp> schedule(
        mlir::ModuleOp::create(UnknownLoc::get(&context)));
    OwningOpRef<mlir::ModuleOp> native(
        mlir::ModuleOp::create(UnknownLoc::get(&context)));
    for (unsigned i = 0; i < 128; ++i)
      schedule->getBodyRegion().emplaceBlock();
    uint64_t remaining = 64;
    finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                       {}};
    require(failed(computation::verifyScheduleLowering(*schedule, *native,
                                                       &remaining, &outcome)) &&
                outcome.status == finite::VerificationStatus::RequiredCapacity,
            "empty blocks bypassed the structural work bound");
    remaining = 64;
    std::optional<CapacityCause> capacity;
    require(!computation::consumeSchedule(*schedule, remaining, &capacity) &&
                capacity && capacity->owner == WorkOwner::AlgorithmExpansion,
            "consumer preflight skipped empty structural allocations");
  });
  for (StringRef name : {"elements", "indices"})
    for (auto policy : {ordered, fused})
      cases.run(name + (policy.collectFoldFusion ? " fused scoped recipe"
                                                 : " ordered scoped recipe"),
                [&] {
                  auto unit = source(context, name);
                  mathematical::RealizationWork work;
                  uint64_t remaining = 1000000, bytes = 16 * 1024 * 1024;
                  OwningOpRef<mlir::ModuleOp> schedule;
                  auto actual = computation::realizeEntry(
                      *unit, "collect_fold", policy, work, remaining, bytes, {},
                      nullptr, nullptr, nullptr, false, &schedule);
                  require(
                      bool(actual) && bool(schedule),
                      "numerical source did not realize into scoped execution");
                  acceptSchedule(*schedule, *actual);
                  zkc::test::loops::accepts(*unit, *actual, policy);
                });
  return cases.result();
}
