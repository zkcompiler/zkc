#include "Check.h"
#include "zkc/Frontend/Diagnostic.h"

using namespace llvm;
namespace zkc::frontend::semantics {
Expected<model::Body> resolveBody(const model::Module &module,
                                  DeclId definition, ScopeId operationScope,
                                  const source::Body &body) {
  const auto &owner = module.declarations.at(definition.index);
  model::Body result;
  for (const auto &instruction : body) {
    auto failure = [&](StringRef code, const Twine &message) {
      return diagnostic(module.text, module.filename,
                        instruction.location ? instruction.location->offset : 0,
                        code, message);
    };
    auto target = [&](StringRef name, Declaration::Kind kind,
                      ScopeId scope) -> Expected<DeclId> {
      auto id = module.lookup(scope, name);
      if (!id.valid() || (module.declarations.at(id.index).kind != kind &&
                          !(kind == Declaration::Kind::Function &&
                            module.declarations.at(id.index).kind ==
                                Declaration::Kind::Configuration)))
        return failure("source-call-target",
                       "no resolved callable '" + name + "'");
      return id;
    };
    model::Instruction out;
    out.location = instruction.location;
    out.site = instruction.site;
    if (const auto *op = instruction.get<source::Operation>()) {
      auto id = target(op->callee,
                       owner.generic ? Declaration::Kind::Operation
                                     : Declaration::Kind::Binding,
                       owner.generic ? operationScope : ScopeId{0});
      if (!id)
        return id.takeError();
      out.value = model::Call{model::Call::Kind::Operation,
                              *id,
                              op->inputs,
                              op->outputs,
                              op->staticArguments,
                              op->attributes,
                              {}};
    } else if (const auto *call = instruction.get<source::AlgorithmCall>()) {
      auto id = target(call->callee, Declaration::Kind::Function, {0});
      if (!id)
        return id.takeError();
      out.value = model::Call{model::Call::Kind::Algorithm,
                              *id,
                              call->inputs,
                              call->outputs,
                              call->staticArguments,
                              {},
                              {}};
    } else if (const auto *call = instruction.get<source::LocalCall>()) {
      auto id = target(call->callee, Declaration::Kind::Function, {0});
      if (!id)
        return id.takeError();
      out.value = model::Call{model::Call::Kind::Local,
                              *id,
                              call->inputs,
                              call->outputs,
                              {},
                              {},
                              call->role};
    } else if (const auto *call = instruction.get<source::ProtocolCall>()) {
      auto id =
          target(call->callee, Declaration::Kind::Dependency, owner.members);
      if (!id)
        return id.takeError();
      out.value = model::Call{model::Call::Kind::Protocol,
                              *id,
                              call->inputs,
                              call->outputs,
                              {},
                              {},
                              {}};
    } else if (const auto *loop = instruction.get<source::Loop>()) {
      auto body = resolveBody(module, definition, operationScope, loop->body);
      if (!body)
        return body.takeError();
      out.value = model::Loop{loop->count, loop->carried, loop->captures,
                              std::move(*body), loop->outputs};
    } else if (const auto *loop = instruction.get<source::For>()) {
      auto body = resolveBody(module, definition, operationScope, loop->body);
      if (!body)
        return body.takeError();
      out.value = model::For{loop->induction, loop->lower,    loop->upper,
                             loop->carried,   loop->captures, std::move(*body),
                             loop->outputs};
    } else if (const auto *branch = instruction.get<source::Conditional>()) {
      auto left =
          resolveBody(module, definition, operationScope, branch->thenBody);
      if (!left)
        return left.takeError();
      auto right =
          resolveBody(module, definition, operationScope, branch->elseBody);
      if (!right)
        return right.takeError();
      out.value = model::Conditional{branch->condition, branch->captures,
                                     std::move(*left), std::move(*right),
                                     branch->outputs};
    } else if (const auto *match = instruction.get<source::Match>()) {
      model::Match result{match->input, match->captures, {}, match->outputs};
      for (const auto &arm : match->arms) {
        auto body = resolveBody(module, definition, operationScope, arm.body);
        if (!body)
          return body.takeError();
        result.arms.push_back({arm.alternative, arm.payload, std::move(*body)});
      }
      out.value = std::move(result);
    } else if (const auto *v = instruction.get<source::VariantConstruct>())
      out.value = *v;
    else if (const auto *v = instruction.get<source::Message>())
      out.value = *v;
    else if (const auto *v = instruction.get<source::Return>())
      out.value = *v;
    else if (const auto *v = instruction.get<source::Yield>())
      out.value = *v;
    else if (const auto *v = instruction.get<source::Stop>())
      out.value = *v;
    else if (const auto *v = instruction.get<source::Release>())
      out.value = *v;
    else
      report_fatal_error("checked source holds an instruction the model does "
                         "not represent");
    result.push_back(std::move(out));
  }
  return result;
}
} // namespace zkc::frontend::semantics
