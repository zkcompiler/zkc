#include "Bindings.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringSet.h"

using namespace llvm;
using namespace mlir;

namespace zkc::protocol {
Error realizeRoots(ModuleOp module) {
  auto root = cast<ProtocolModuleOp>(&module.getBody()->front());
  SmallVector<ServiceRootOp> roots(
      root.getBody().front().getOps<ServiceRootOp>());
  if (roots.empty())
    return Error::success();
  // The initial realization has one closed instance and one state owner/root.
  // Calls and loops need explicit state interfaces at their own boundaries.
  StringRef instance;
  for (auto participant : root.getBody().front().getOps<ParticipantOp>()) {
    if (!instance.empty() && instance != participant.getInstance())
      return error("interactive-root-realization-instances");
    instance = participant.getInstance();
    bool unsupported = false;
    participant.walk([&](Operation *op) {
      unsupported |= isa<ProtocolCallOp, ProtocolLoopOp>(op);
      if (auto query = dyn_cast<ServiceQueryOp>(op))
        unsupported |= query->getParentOp() != participant.getOperation();
    });
    if (unsupported)
      return error("interactive-root-realization-control");
  }
  SymbolTable symbols(root);
  OpBuilder builder(module.getContext());
  unsigned fresh = 0;
  for (auto indexed : enumerate(roots)) {
    auto index = indexed.index();
    auto declaration = indexed.value();
    if (declaration.getOwners().size() != 1)
      return error("interactive-root-realization-owners");
    SmallVector<ServiceQueryOp> queries;
    root.walk([&](ServiceQueryOp query) {
      if (query.getRoot() == declaration.getSymName())
        queries.push_back(query);
    });
    if (queries.empty())
      continue;
    auto participant = queries.front()->getParentOfType<ParticipantOp>();
    for (auto query : queries)
      if (query->getParentOfType<ParticipantOp>() != participant)
        return error("interactive-root-realization-owner");
    auto binding = readBinding(symbols.lookup(declaration.getService()));
    if (!binding)
      return binding.takeError();
    auto service = resolveEntropyService(binding->application);
    if (!service)
      return service.takeError();
    Type state = decodeBoundType(module.getContext(), service->state);
    Type reply = decodeBoundType(module.getContext(), service->reply);
    if (!state || !reply)
      return error("binding-type");

    std::string name;
    do {
      name = "root_sampler_" + std::to_string(fresh++);
    } while (symbols.lookup(name));
    builder.setInsertionPointToEnd(&root.getBody().front());
    auto helper = func::FuncOp::create(
        builder, declaration.getLoc(), name,
        builder.getFunctionType(TypeRange{state}, TypeRange{reply, state}));
    symbols.insert(helper);
    helper->setAttr("logical_origin",
                    builder.getArrayAttr({builder.getStringAttr(
                                              "query_" + std::to_string(index)),
                                          builder.getArrayAttr({})}));
    auto *body = helper.addEntryBlock();
    builder.setInsertionPointToEnd(body);
    auto draw = operation(
        builder, boundOperationName(binding->application.contract),
        body->getArguments(), TypeRange{reply, state},
        {named(builder, "site", "draw"),
         named(builder, "parameters", builder.getArrayAttr({})),
         named(builder, "binding",
               FlatSymbolRefAttr::get(module.getContext(), binding->name))},
        0, declaration.getLoc());
    func::ReturnOp::create(builder, declaration.getLoc(), draw->getResults());

    auto &block = participant.getBody().front();
    Value current = block.addArgument(state, declaration.getLoc());
    // Preserve existing input labels for diagnostic export while reserving a
    // distinct generated argument.
    if (auto named = participant->getAttrOfType<ArrayAttr>("argument_names")) {
      SmallVector<Attribute> names(named.begin(), named.end());
      llvm::StringSet<> used;
      for (auto value : names)
        used.insert(cast<StringAttr>(value).getValue());
      std::string input;
      do {
        input = "root_state_" + std::to_string(fresh++);
      } while (used.contains(input));
      names.push_back(builder.getStringAttr(input));
      participant->setAttr("argument_names", builder.getArrayAttr(names));
    }
    auto signature = participant.getFunctionType();
    SmallVector<Type> inputs(signature.getInputs()),
        outputs(signature.getResults());
    inputs.push_back(state);
    outputs.push_back(state);
    participant.setFunctionType(builder.getFunctionType(inputs, outputs));
    for (auto query : queries) {
      builder.setInsertionPoint(query);
      auto call = LocalCallOp::create(
          builder, query.getLoc(), TypeRange{reply, state}, ValueRange{current},
          helper.getSymName(), query.getSite(), StringAttr());
      query.getResult(0).replaceAllUsesWith(call.getResult(0));
      current = call.getResult(1);
      query.erase();
    }
    if (auto finish = dyn_cast<FinishOp>(block.back()))
      finish->insertOperands(finish->getNumOperands(), ValueRange{current});
    // A terminal stop has no normal successor. Issuer custody still retains
    // the actual completed state prefix for host observation and cleanup.
  }
  for (auto declaration : roots)
    declaration.erase();
  return Error::success();
}
} // namespace zkc::protocol
