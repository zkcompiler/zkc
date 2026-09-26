#include "zkc/Contracts/Generic.h"
#include "RequirementChecks.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include <functional>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::generic {
namespace {
Error invalid(StringRef code) { return zkc::error(code); }

Error scope(const Scope &scope) {
  if (scope.terms.size() != scope.sorts.size())
    return invalid("generic-sort-count");
  // Pure applications belong to checked frontend selections. This older
  // portable domain-signature profile has no application sort declaration.
  if (any_of(scope.terms,
             [](const auto &term) { return term.arguments.has_value(); }))
    return invalid("generic-application");
  for (const auto &[index, identity] : scope.constants)
    if (index >= scope.terms.size() || scope.terms[index].parent ||
        identity.empty() || identity.size() > 255)
      return invalid("generic-constant-scope");
  if (any_of(scope.sorts, [](const auto &sort) {
        return sort.empty() || sort.size() > 256;
      }))
    return invalid("generic-sort");
  return requirements::checkFormation(scope.terms, {}, {}, {});
}

Error signature(const Signature &sig, ArrayRef<TypeConstructor> constructors) {
  if (auto e = scope(sig.scope))
    return e;
  if (sig.inputs.size() > 1024 || sig.outputs.size() > 1024)
    return invalid("generic-port-limit");
  auto valid = [&](const Type &type) {
    const TypeConstructor *selected = nullptr;
    for (const auto &constructor : constructors)
      if (constructor.name == type.constructor) {
        if (selected)
          return false;
        selected = &constructor;
      }
    if (!selected || selected->parameters.size() != type.arguments.size())
      return false;
    for (auto [parameter, sort] : zip(type.arguments, selected->parameters))
      if (parameter >= sig.scope.sorts.size() ||
          sig.scope.sorts[parameter] != sort)
        return false;
    return true;
  };
  if (!all_of(sig.inputs, valid) || !all_of(sig.outputs, valid))
    return invalid("generic-type");
  for (const auto &p : sig.requirements)
    if (p.kind == requirements::Predicate::Kind::Equal &&
        p.arguments.size() == 2 && p.arguments[0] < sig.scope.sorts.size() &&
        p.arguments[1] < sig.scope.sorts.size() &&
        sig.scope.sorts[p.arguments[0]] != sig.scope.sorts[p.arguments[1]])
      return invalid("generic-equality-sort");
  return requirements::checkFormation(sig.scope.terms, sig.requirements, {},
                                      {});
}

Type relocate(const Type &type, ArrayRef<unsigned> mapping) {
  Type result{type.constructor, {}};
  for (unsigned term : type.arguments)
    result.arguments.push_back(mapping[term]);
  return result;
}

Error same(const Type &actual, const Type &expected,
           std::vector<requirements::Predicate> &obligations) {
  if (actual.constructor != expected.constructor ||
      actual.arguments.size() != expected.arguments.size())
    return invalid("generic-signature");
  for (auto [a, b] : zip(actual.arguments, expected.arguments))
    if (a != b)
      obligations.push_back(requirements::Predicate::equal(a, b));
  return Error::success();
}
} // namespace

Expected<Signature> instantiate(const Signature &sig,
                                ArrayRef<unsigned> arguments,
                                const Scope &caller) {
  if (auto e = scope(sig.scope))
    return e;
  if (auto e = scope(caller))
    return e;
  if (arguments.size() + sig.scope.constants.size() !=
      size_t(
          count_if(sig.scope.terms, [](const auto &t) { return !t.parent; })))
    return invalid("generic-static-arity");
  Signature result;
  result.scope = caller;
  std::vector<unsigned> mapping;
  unsigned root = 0;
  for (auto [index, term] : enumerate(sig.scope.terms)) {
    const auto &sort = sig.scope.sorts[index];
    if (auto constant = sig.scope.constants.find(index);
        constant != sig.scope.constants.end()) {
      unsigned found = result.scope.terms.size();
      for (const auto &[i, identity] : result.scope.constants)
        if (identity == constant->second && result.scope.sorts[i] == sort)
          found = i;
      if (found == result.scope.terms.size()) {
        if (found >= 128)
          return invalid("requirements-limit");
        result.scope.terms.push_back({"$" + constant->second, {}});
        result.scope.sorts.push_back(sort);
        result.scope.constants.emplace(found, constant->second);
      }
      mapping.push_back(found);
      continue;
    }
    if (!term.parent) {
      unsigned bound = arguments[root++];
      if (bound >= caller.terms.size() || caller.sorts[bound] != sort)
        return invalid("generic-static-sort");
      mapping.push_back(bound);
      continue;
    }
    unsigned parent = mapping[*term.parent];
    unsigned found = result.scope.terms.size();
    for (auto [i, candidate] : enumerate(result.scope.terms))
      if (candidate.parent == parent && candidate.name == term.name) {
        found = i;
        break;
      }
    if (found == result.scope.terms.size()) {
      if (found >= 128)
        return invalid("requirements-limit");
      result.scope.terms.push_back({term.name, parent});
      result.scope.sorts.push_back(sort);
    } else if (result.scope.sorts[found] != sort)
      return invalid("generic-associated-sort");
    mapping.push_back(found);
  }
  auto validRefs = [&](const auto &items) {
    return all_of(items, [&](const auto &item) {
      return all_of(item.arguments,
                    [&](unsigned a) { return a < mapping.size(); });
    });
  };
  if (!validRefs(sig.inputs) || !validRefs(sig.outputs) ||
      !validRefs(sig.requirements))
    return invalid("generic-term-reference");
  for (const auto &input : sig.inputs)
    result.inputs.push_back(relocate(input, mapping));
  for (const auto &output : sig.outputs)
    result.outputs.push_back(relocate(output, mapping));
  for (const auto &predicate : sig.requirements) {
    auto relocated = predicate;
    for (auto &argument : relocated.arguments)
      argument = mapping[argument];
    result.requirements.push_back(std::move(relocated));
  }
  if (auto e = scope(result.scope))
    return e;
  return result;
}

Expected<Inference> infer(const Function &function,
                          ArrayRef<TypeConstructor> constructors,
                          ArrayRef<Operation> operations) {
  if (function.body.size() > 32768 || constructors.size() > 1024 ||
      operations.size() > 4096)
    return invalid("generic-declaration-limit");
  std::map<std::string, const Operation *> installed;
  for (const auto &op : operations) {
    if (op.name.empty() || !installed.emplace(op.name, &op).second)
      return invalid("generic-operation-declaration");
    if (auto e = signature(op.signature, constructors))
      return e;
  }
  if (auto e = signature(function.signature, constructors))
    return e;
  Inference result{function.signature.scope, {}, {}};
  std::set<std::string> sites;
  size_t work = 0, valueCount = 0;
  auto affine = [&](const Type &type) {
    return any_of(constructors, [&](const auto &c) {
      return c.name == type.constructor && c.affine;
    });
  };
  std::function<Expected<std::vector<Type>>(ArrayRef<Call>, ArrayRef<unsigned>,
                                            std::vector<Type>, unsigned)>
      region;
  region = [&](ArrayRef<Call> body, ArrayRef<unsigned> returns,
               std::vector<Type> values,
               unsigned depth) -> Expected<std::vector<Type>> {
    if (depth > 64)
      return invalid("generic-body-limit");
    valueCount += values.size();
    if (valueCount > 32768)
      return invalid("generic-body-limit");
    std::set<unsigned> consumed;
    auto use = [&](unsigned index) -> Error {
      if (index >= values.size())
        return invalid("generic-value-reference");
      if (consumed.count(index))
        return invalid("generic-resource-reuse");
      if (affine(values[index]))
        consumed.insert(index);
      return Error::success();
    };
    for (const auto &call : body) {
      if (++work > 32768)
        return invalid("generic-body-limit");
      if (call.site.empty() || !sites.insert(call.site).second)
        return invalid("generic-site");
      std::vector<Type> inputs, outputs;
      for (unsigned i : call.inputs) {
        if (auto e = use(i))
          return std::move(e);
        inputs.push_back(values[i]);
      }
      if (call.kind == Call::Kind::Operation) {
        auto operation = installed.find(call.operation);
        if (operation == installed.end())
          return invalid("generic-operation");
        auto selected = instantiate(operation->second->signature,
                                    call.staticArguments, result.scope);
        if (!selected)
          return selected.takeError();
        result.scope = std::move(selected->scope);
        if (inputs.size() != selected->inputs.size())
          return invalid("generic-signature");
        for (auto [actual, expected] : zip(inputs, selected->inputs))
          if (auto e = same(actual, expected, result.obligations))
            return std::move(e);
        llvm::append_range(result.obligations, selected->requirements);
        outputs = std::move(selected->outputs);
      } else if (call.kind == Call::Kind::Conditional) {
        if (inputs.empty() || inputs[0].constructor != "bool")
          return invalid("local-if-condition");
        std::vector<Type> captures(inputs.begin() + 1, inputs.end());
        auto left = region(call.body, call.yields, captures, depth + 1);
        if (!left)
          return left.takeError();
        auto right = region(call.elseBody, call.elseYields, std::move(captures),
                            depth + 1);
        if (!right)
          return right.takeError();
        if (left->size() != right->size())
          return invalid("local-if-yield");
        for (auto [a, b] : zip(*left, *right))
          if (auto e = same(a, b, result.obligations))
            return std::move(e);
        outputs = std::move(*left);
      } else if (call.kind == Call::Kind::For) {
        if (call.carried > inputs.size() || inputs.size() - call.carried < 2 ||
            inputs[0].constructor != "index" ||
            inputs[1].constructor != "index")
          return invalid("local-for-bounds");
        for (unsigned i = 2 + call.carried; i < inputs.size(); ++i)
          if (affine(inputs[i]))
            return invalid("local-control-capture");
        std::vector<Type> inner{{"index", {}}};
        inner.insert(inner.end(), inputs.begin() + 2, inputs.end());
        auto yielded =
            region(call.body, call.yields, std::move(inner), depth + 1);
        if (!yielded)
          return yielded.takeError();
        if (yielded->size() != call.carried)
          return invalid("local-for-yield");
        outputs.assign(inputs.begin() + 2, inputs.begin() + 2 + call.carried);
        for (auto [actual, expected] : zip(*yielded, outputs))
          if (auto e = same(actual, expected, result.obligations))
            return std::move(e);
      } else
        return invalid("generic-instruction");
      valueCount += outputs.size();
      if (result.obligations.size() > 1024 || valueCount > 32768)
        return invalid("generic-body-limit");
      llvm::append_range(values, outputs);
    }
    std::vector<Type> yielded;
    for (unsigned i : returns) {
      if (auto e = use(i))
        return std::move(e);
      yielded.push_back(values[i]);
    }
    if (!depth)
      result.values = std::move(values);
    return yielded;
  };
  auto returned =
      region(function.body, function.returns, function.signature.inputs, 0);
  if (!returned)
    return returned.takeError();
  if (returned->size() != function.signature.outputs.size())
    return invalid("generic-return-signature");
  for (auto [actual, expected] : zip(*returned, function.signature.outputs))
    if (auto e = same(actual, expected, result.obligations))
      return std::move(e);
  return result;
}

Expected<CheckedFunction>
check(const Function &function, ArrayRef<TypeConstructor> constructors,
      ArrayRef<Operation> operations,
      ArrayRef<requirements::Implication> implications) {
  auto inferred = infer(function, constructors, operations);
  if (!inferred)
    return inferred.takeError();
  auto proof = requirements::derive(inferred->scope.terms,
                                    function.signature.requirements,
                                    implications, inferred->obligations);
  if (!proof)
    return proof.takeError();
  if (any_of(proof->goals, [](const auto &goal) { return !goal; }))
    return invalid("generic-public-requirement");
  return CheckedFunction{std::move(*inferred), std::move(*proof)};
}
} // namespace zkc::generic
