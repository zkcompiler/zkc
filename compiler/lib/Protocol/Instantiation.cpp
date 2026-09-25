#include "zkc/Protocol/Instantiation.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <functional>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::generic {
namespace {
using Value = json::Value;
using Array = json::Array;
struct Definition {
  std::string name;
  Function function;
  const source::GenericFunction *record = nullptr;
  std::string identity;
  std::map<std::string, unsigned> terms;
  Inference inferred;
  std::map<std::string, Call> calls;
  std::map<std::string, const source::Instruction *> callRecords;
  unsigned height = 1;
};
struct Configuration {
  const Definition *definition = nullptr;
  unsigned depth = 1;
  std::map<std::string, std::string> arguments, implementations;
};

std::string digest(StringRef input) {
  SHA256 hash;
  hash.update(input);
  return toHex(hash.final(), true);
}

class Elaborator {
  bool preserveSourceNames = false;
  std::string problem;
  const source::Node *current = nullptr, *problemRecord = nullptr;
  std::map<const source::Node *, const source::Node *> origins;
  std::map<std::string, Definition> definitions;
  std::map<std::string, const source::GenericFunction *> definitionRecords;
  std::set<std::string> checking;
  std::map<std::string, std::map<std::string, Configuration>> callTargets;
  std::map<std::string, const source::Configuration *> declarations;
  std::map<std::string, Configuration> configurations;
  std::set<std::string> symbols, active;
  std::map<std::string, std::string> generated;
  std::map<std::string, std::string> demanded;
  std::vector<source::Function> functions;
  std::vector<source::OperationBinding> bindings;
  std::vector<const source::Node *> functionOrigins, bindingOrigins;
  size_t specializationWork = 0, specializedInstructions = 0;

  bool fail(StringRef code) {
    if (problem.empty()) {
      problem = code.str();
      problemRecord = current;
    }
    return false;
  }
  bool name(StringRef value) {
    return (!value.empty() && value.size() <= 128 &&
            (isAlpha(value.front()) || value.front() == '_') &&
            all_of(value,
                   [](char c) {
                     return isAlnum(c) || c == '_' || c == '.' || c == '-';
                   })) ||
           fail("generic-source-name");
  }
  bool symbol(StringRef value) {
    return (name(value) && symbols.insert(value.str()).second) ||
           fail("generic-duplicate-symbol");
  }
  std::string fresh(StringRef prefix, StringRef key) {
    std::string result = prefix.str() + digest(key);
    while (symbols.count(result)) {
      if (result.size() == 128) {
        fail("generic-generated-name-limit");
        return {};
      }
      result = "_" + result;
    }
    symbols.insert(result);
    return result;
  }
  std::optional<unsigned> term(Definition &def, StringRef path,
                               unsigned depth = 0) {
    if (depth > 64) {
      fail("generic-term-depth");
      return {};
    }
    if (auto found = def.terms.find(path.str()); found != def.terms.end())
      return found->second;
    auto [parent, member] = path.rsplit('.');
    if (parent.empty() || member.empty() || parent == path) {
      fail("generic-term-reference");
      return {};
    }
    auto p = term(def, parent, depth + 1);
    if (!p)
      return {};
    auto &scope = def.function.signature.scope;
    auto sort = protocol::associatedMemberSort(scope.sorts[*p], member);
    if (sort.empty() || scope.terms.size() >= 128) {
      fail("generic-associated-member");
      return {};
    }
    unsigned index = scope.terms.size();
    scope.terms.push_back({member.str(), *p});
    scope.sorts.push_back(sort.str());
    def.terms.emplace(path.str(), index);
    return index;
  }
  std::optional<Type> type(Definition &def, StringRef spelling) {
    auto [kind, parameter] = spelling.split(':');
    Type type{kind.str(), {}};
    if (!parameter.empty()) {
      auto index = term(def, parameter);
      if (!index)
        return {};
      type.arguments.push_back(*index);
    } else if (spelling.contains(':')) {
      fail("generic-type");
      return {};
    }
    return type;
  }
  bool arguments(const source::Assignments &pairs,
                 std::map<std::string, std::string> &out) {
    if (pairs.size() > 128)
      return fail("generic-configuration-limit");
    for (const auto &[key, value] : pairs)
      if (!name(key) || value.empty() || !out.emplace(key, value).second)
        return fail("generic-configuration-binding");
    return true;
  }
  bool definition(const source::GenericFunction &record) {
    if (auto found = definitions.find(record.name); found != definitions.end())
      return checking.size() + found->second.height <= 65 ||
             fail("algorithm-call-depth");
    current = &record;
    if (checking.size() > 64)
      return fail("algorithm-call-depth");
    if (!checking.insert(record.name).second)
      return fail("algorithm-call-cycle");
    auto finish = scope_exit([&] { checking.erase(record.name); });
    Definition def;
    def.name = record.name;
    def.record = &record;
    // The canonical portable record is used only at the generated-symbol
    // identity boundary. Source analysis below uses the owning typed record.
    def.identity = printJson(source::encode(record));
    if (record.parameters.size() > 128 || record.body.empty())
      return fail("generic-function-shape");
    auto &signature = def.function.signature;
    for (const auto &parameter : record.parameters) {
      if (!name(parameter.name) || StringRef(parameter.name).contains('.') ||
          !name(parameter.sort))
        return fail("generic-parameter");
      unsigned i = signature.scope.terms.size();
      if (!def.terms.emplace(parameter.name, i).second)
        return fail("generic-duplicate-parameter");
      signature.scope.terms.push_back({parameter.name, {}});
      signature.scope.sorts.push_back(parameter.sort);
    }
    for (const auto &promise : record.requirements) {
      current = &promise;
      std::vector<unsigned> terms;
      for (const auto &argument : promise.arguments) {
        auto index = term(def, argument);
        if (!index)
          return false;
        terms.push_back(*index);
      }
      signature.requirements.push_back(
          {promise.predicate == "=" ? requirements::Predicate::Kind::Equal
                                    : requirements::Predicate::Kind::Relation,
           promise.predicate == "=" ? "" : promise.predicate,
           std::move(terms)});
    }
    current = &record;
    std::map<std::string, unsigned> values;
    for (const auto &input : record.arguments) {
      if (!name(input.name) ||
          !values.emplace(input.name, values.size()).second)
        return fail("generic-value-name");
      auto t = type(def, input.type);
      if (!t)
        return false;
      signature.inputs.push_back(std::move(*t));
    }
    for (const auto &output : record.results) {
      auto t = type(def, output);
      if (!t)
        return false;
      signature.outputs.push_back(std::move(*t));
    }
    std::vector<Operation> operations(
        protocol::boundOperationContracts().begin(),
        protocol::boundOperationContracts().end());
    std::set<std::string> sites;
    size_t instructionCount = 0;
    using Values = std::map<std::string, unsigned>;
    std::function<bool(const source::Body &, Values, std::vector<Call> &,
                       std::vector<unsigned> &, unsigned)>
        readBody;
    readBody = [&](const source::Body &body, Values values,
                   std::vector<Call> &calls, std::vector<unsigned> &returns,
                   unsigned depth) {
      if (body.empty() || depth > 64)
        return fail("generic-terminator");
      auto readValues = [&](const source::Names &names,
                            std::vector<unsigned> &out) {
        for (const auto &n : names) {
          auto it = values.find(n);
          if (it == values.end())
            return fail("generic-value-reference");
          out.push_back(it->second);
        }
        return true;
      };
      for (auto [index, instruction] : enumerate(body)) {
        current = &instruction;
        if (++instructionCount > 32768)
          return fail("generic-body-limit");
        if (index + 1 == body.size()) {
          auto *ret = instruction.get<source::Return>();
          auto *yield = instruction.get<source::Yield>();
          if (depth ? !yield : !ret)
            return fail("generic-terminator");
          return readValues(depth ? yield->values : ret->values, returns);
        }
        if (!name(instruction.site) || !sites.insert(instruction.site).second)
          return fail("generic-site");
        auto *branch = instruction.get<source::Conditional>();
        auto *loop = instruction.get<source::For>();
        if (branch || loop) {
          Call call;
          call.site = instruction.site;
          call.kind = branch ? Call::Kind::Conditional : Call::Kind::For;
          Values inner;
          auto bind = [&](const std::string &n) {
            return (name(n) && inner.emplace(n, inner.size()).second) ||
                   fail("generic-value-name");
          };
          if (branch) {
            if (!readValues({branch->condition}, call.inputs) ||
                !readValues(branch->captures, call.inputs))
              return false;
            for (const auto &capture : branch->captures)
              if (!bind(capture))
                return false;
            if (!readBody(branch->thenBody, inner, call.body, call.yields,
                          depth + 1) ||
                !readBody(branch->elseBody, inner, call.elseBody,
                          call.elseYields, depth + 1))
              return false;
            if (call.yields.size() != branch->outputs.size() ||
                call.elseYields.size() != branch->outputs.size())
              return fail("local-if-yield");
          } else {
            if (!readValues({loop->lower, loop->upper}, call.inputs) ||
                !bind(loop->induction))
              return false;
            call.carried = loop->carried.size();
            for (const auto &[n, initial] : loop->carried)
              if (!bind(n) || !readValues({initial}, call.inputs))
                return false;
            for (const auto &capture : loop->captures)
              if (!bind(capture) || !readValues({capture}, call.inputs))
                return false;
            if (!readBody(loop->body, inner, call.body, call.yields, depth + 1))
              return false;
            if (loop->outputs.size() != call.carried)
              return fail("local-for-yield");
          }
          for (const auto &output : branch ? branch->outputs : loop->outputs)
            if (!name(output) || !values.emplace(output, values.size()).second)
              return fail("generic-value-name");
          calls.push_back(std::move(call));
          continue;
        }
        auto *op = instruction.get<source::Operation>();
        auto *apply = instruction.get<source::AlgorithmCall>();
        if ((!op && !apply) || !name(instruction.site))
          return fail("generic-instruction");
        Call call{instruction.site,
                  op ? op->callee : "apply:" + apply->callee,
                  {},
                  {}};
        for (const auto &argument :
             op ? op->staticArguments : apply->staticArguments) {
          auto t = term(def, argument);
          if (!t)
            return false;
          call.staticArguments.push_back(*t);
        }
        if (!readValues(op ? op->inputs : apply->inputs, call.inputs))
          return false;
        if (apply) {
          auto selected = target(apply->callee);
          if (!selected)
            return false;
          def.height = std::max(def.height, 1 + selected->definition->height);
          if (def.height > 65)
            return fail("algorithm-call-depth");
          auto calleeSignature = selected->definition->function.signature;
          for (const auto &[parameter, identity] : selected->arguments)
            calleeSignature.scope.constants.emplace(
                selected->definition->terms.at(parameter), identity);
          if (!any_of(operations, [&](const auto &operation) {
                return operation.name == call.operation;
              }))
            operations.push_back({call.operation, std::move(calleeSignature)});
          callTargets[record.name].emplace(instruction.site, *selected);
        }
        current = &instruction;
        const Operation *installed = nullptr;
        for (const auto &o : operations)
          if (o.name == call.operation)
            installed = &o;
        const auto &outputs = op ? op->outputs : apply->outputs;
        if (!installed || outputs.size() != installed->signature.outputs.size())
          return fail("generic-operation");
        if (op) {
          // Constants are natural casts; reduce only after nominal selection.
          if (call.operation == "field.constant" ||
              call.operation == "vector.constant") {
            if (call.operation == "field.constant" &&
                op->attributes.size() != 1)
              return fail("generic-field-literal");
            for (const auto &literal : op->attributes)
              if (literal.empty() || literal.size() > 1024 ||
                  (literal.size() > 1 && literal.front() == '0') ||
                  !all_of(literal, [](char c) { return isDigit(c); }))
                return fail("generic-field-literal");
          } else if (auto e = protocol::checkParameters(call.operation,
                                                        op->attributes))
            return fail(toString(std::move(e)));
        }
        for (const auto &output : outputs)
          if (!name(output) || !values.emplace(output, values.size()).second)
            return fail("generic-value-name");
        def.callRecords.emplace(call.site, &instruction);
        def.calls.emplace(call.site, call);
        calls.push_back(std::move(call));
      }
      return false;
    };
    if (!readBody(record.body, std::move(values), def.function.body,
                  def.function.returns, 0))
      return false;
    current = &record;
    if (auto e = protocol::checkStaticVocabulary(signature))
      return fail(toString(std::move(e)));
    auto inferred = generic::infer(
        def.function, protocol::boundTypeConstructors(), operations);
    if (!inferred)
      return fail(toString(inferred.takeError()));
    // Ground obligations from a configuration are checked against installed
    // nominal facts. All residual obligations must follow from the caller's
    // public promises, including equalities needed by argument/result types.
    std::vector<std::string> known;
    for (auto [i, t] : enumerate(inferred->scope.terms)) {
      auto fixed = inferred->scope.constants.find(i);
      known.push_back(
          t.parent
              ? (known[*t.parent].empty()
                     ? ""
                     : protocol::associatedIdentity(known[*t.parent], t.name)
                           .str())
          : fixed == inferred->scope.constants.end() ? ""
                                                     : fixed->second);
    }
    std::vector<requirements::Predicate> residual;
    for (const auto &need : inferred->obligations) {
      if (all_of(need.arguments,
                 [&](unsigned i) { return !known[i].empty(); })) {
        if (auto e = protocol::checkClosedRequirements({need}, known))
          return fail(toString(std::move(e)));
      } else
        residual.push_back(need);
    }
    auto proof =
        requirements::derive(inferred->scope.terms, signature.requirements,
                             protocol::boundCapabilityRules(), residual);
    if (!proof)
      return fail(toString(proof.takeError()));
    if (any_of(proof->goals, [](const auto &goal) { return !goal; }))
      return fail("generic-public-requirement");
    def.function.signature.scope = inferred->scope;
    def.inferred = std::move(*inferred);
    definitions.emplace(def.name, std::move(def));
    return problem.empty();
  }

  std::optional<Configuration> target(const std::string &name) {
    if (auto found = definitionRecords.find(name);
        found != definitionRecords.end()) {
      if (!definition(*found->second))
        return {};
      Configuration result;
      result.definition = &definitions.at(name);
      return result;
    }
    if (const auto *selected = configuration(name))
      return *selected;
    return {};
  }

  const Configuration *configuration(const std::string &name) {
    auto existing = configurations.find(name);
    if (existing != configurations.end()) {
      if (active.size() + existing->second.depth > 64) {
        fail("generic-configuration-reference");
        return nullptr;
      }
      return &existing->second;
    }
    auto found = declarations.find(name);
    if (found == declarations.end() || active.size() >= 64 ||
        !active.insert(name).second) {
      fail("generic-configuration-reference");
      return nullptr;
    }
    const auto &r = *found->second;
    const auto *caller = current;
    auto restore = scope_exit([&] { current = caller; });
    current = &r;
    const auto &base = r.base;
    Configuration result{};
    if (auto def = definitionRecords.find(base);
        def != definitionRecords.end()) {
      if (!definition(*def->second))
        return nullptr;
      result.definition = &definitions.at(base);
    } else {
      auto *inherited = configuration(base);
      if (!inherited)
        return nullptr;
      result = *inherited;
      ++result.depth;
    }
    std::map<std::string, std::string> arguments, implementations;
    if (!this->arguments(r.arguments, arguments) ||
        !this->arguments(r.implementations, implementations))
      return nullptr;
    const auto &scope = result.definition->function.signature.scope;
    for (const auto &[parameter, value] : arguments) {
      auto declared = result.definition->terms.find(parameter);
      if (declared == result.definition->terms.end() ||
          scope.terms[declared->second].parent ||
          protocol::installedIdentitySort(value) !=
              scope.sorts[declared->second]) {
        fail("generic-configuration-sort");
        return nullptr;
      }
      if (!result.arguments.emplace(parameter, value).second) {
        fail("generic-configuration-rebinding");
        return nullptr;
      }
    }
    for (const auto &selection : implementations) {
      const auto &site = selection.first;
      const auto &implementation = selection.second;
      auto selected = result.definition->calls.find(site);
      if (selected == result.definition->calls.end() ||
          StringRef(selected->second.operation).starts_with("apply:") ||
          !result.implementations.emplace(site, implementation).second) {
        fail("generic-implementation-site");
        return nullptr;
      }
      if (auto e = protocol::checkImplementation(selected->second.operation,
                                                 implementation)) {
        fail(toString(std::move(e)));
        return nullptr;
      }
    }
    // Formation is independent of demand. Resolve the part already fixed,
    // retaining unknown terms in partial configurations without inventing
    // facts.
    std::vector<std::string> known;
    for (auto [i, term] : enumerate(scope.terms)) {
      if (auto fixed = scope.constants.find(i); fixed != scope.constants.end())
        known.push_back(fixed->second);
      else if (term.parent)
        known.push_back(
            known[*term.parent].empty()
                ? ""
                : protocol::associatedIdentity(known[*term.parent], term.name)
                      .str());
      else {
        auto value = result.arguments.find(term.name);
        known.push_back(value == result.arguments.end() ? "" : value->second);
      }
    }
    for (const auto &predicate :
         result.definition->function.signature.requirements)
      if (all_of(predicate.arguments,
                 [&](unsigned i) { return !known[i].empty(); }))
        if (auto e = protocol::checkClosedRequirements({predicate}, known)) {
          fail(toString(std::move(e)));
          return nullptr;
        }
    auto closure = requirements::derive(
        scope.terms, result.definition->function.signature.requirements,
        protocol::boundCapabilityRules(), {});
    if (!closure) {
      fail(toString(closure.takeError()));
      return nullptr;
    }
    // An unresolved parameter may already have a determined identity through
    // a public equality. Propagate that knowledge for consistency checking,
    // without assigning the parameter or closing the configuration implicitly.
    bool changed;
    do {
      changed = false;
      for (const auto &step : closure->steps) {
        const auto &p = step.conclusion;
        if (p.kind != requirements::Predicate::Kind::Equal)
          continue;
        auto &left = known[p.arguments[0]];
        auto &right = known[p.arguments[1]];
        if (!left.empty() && !right.empty() && left != right) {
          fail("binding-requirement");
          return nullptr;
        }
        if (left.empty() != right.empty()) {
          if (left.empty())
            left = right;
          else
            right = left;
          changed = true;
        }
      }
      for (auto [index, term] : enumerate(scope.terms))
        if (term.parent && !known[*term.parent].empty()) {
          auto identity =
              protocol::associatedIdentity(known[*term.parent], term.name);
          if (identity.empty() ||
              (!known[index].empty() && known[index] != identity)) {
            fail("binding-requirement");
            return nullptr;
          }
          if (known[index].empty()) {
            known[index] = identity.str();
            changed = true;
          }
        }
    } while (changed);
    for (const auto &step : closure->steps)
      if (all_of(step.conclusion.arguments,
                 [&](unsigned i) { return !known[i].empty(); }))
        if (auto e =
                protocol::checkClosedRequirements({step.conclusion}, known)) {
          fail(toString(std::move(e)));
          return nullptr;
        }
    active.erase(name);
    return &configurations.emplace(name, std::move(result)).first->second;
  }

  std::optional<std::string> instantiate(const Configuration &configuration,
                                         StringRef sourceName) {
    if (++specializationWork > 32768) {
      fail("generic-specialization-limit");
      return {};
    }
    const auto &def = *configuration.definition;
    const auto &signature = def.function.signature;
    std::vector<std::string> arguments;
    Array originArguments, choices;
    for (auto [i, term] : enumerate(signature.scope.terms)) {
      if (term.parent || signature.scope.constants.count(i))
        continue;
      auto found = configuration.arguments.find(term.name);
      if (found == configuration.arguments.end()) {
        fail("generic-open-instance");
        return {};
      }
      arguments.push_back(found->second);
      originArguments.push_back(Array{term.name, found->second});
    }
    for (const auto &[site, implementation] : configuration.implementations)
      choices.push_back(Array{site, implementation});
    // Keep the existing canonical key bytes without decoding a source tree.
    std::string key = "[" + def.identity + "," +
                      printJson(std::move(originArguments)) + "," +
                      printJson(std::move(choices)) + "]";
    if (preserveSourceNames && !sourceName.empty())
      key = printJson(Array{sourceName, key});
    if (auto existing = generated.find(key); existing != generated.end())
      return existing->second;
    source::walk(def.record->body, [&](const source::Instruction &) {
      ++specializedInstructions;
    });
    if (specializedInstructions > 32768) {
      fail("generic-specialization-limit");
      return {};
    }
    auto identities =
        protocol::resolveStaticArguments(signature.scope, arguments);
    if (!identities) {
      fail(toString(identities.takeError()));
      return {};
    }
    if (auto e = protocol::checkClosedRequirements(signature.requirements,
                                                   *identities)) {
      fail(toString(std::move(e)));
      return {};
    }
    auto concrete = [&](const Type &t) {
      return protocol::BoundType{
          t.constructor,
          t.arguments.empty() ? "" : (*identities)[t.arguments[0]], ""}
          .spelling();
    };
    source::Function function;
    function.location = def.record->location;
    for (auto [input, type] : zip(def.record->arguments, signature.inputs))
      function.arguments.push_back({input.name, concrete(type)});
    for (const auto &output : signature.outputs)
      function.results.push_back(concrete(output));
    // Configuration symbols are already reserved; shared code mints names.
    std::string name = preserveSourceNames && !sourceName.empty()
                           ? sourceName.str()
                           : fresh("g_", key);
    function.name = name;
    function.origin = source::LogicalOrigin{def.name, {}};
    for (auto [i, term] : enumerate(signature.scope.terms))
      if (!term.parent && !signature.scope.constants.count(i))
        function.origin->arguments.emplace_back(
            term.name, configuration.arguments.at(term.name));
    function.body = def.record->body;
    source::walk(*function.body, [&](source::Instruction &instruction) {
      if (!problem.empty() || (!instruction.get<source::Operation>() &&
                               !instruction.get<source::AlgorithmCall>()))
        return;
      current = def.callRecords.at(instruction.site);
      const auto &call = def.calls.at(instruction.site);
      if (const auto *apply = instruction.get<source::AlgorithmCall>()) {
        auto selected = callTargets.at(def.name).at(call.site);
        size_t next = 0;
        for (const auto &parameter : selected.definition->record->parameters)
          if (!selected.arguments.count(parameter.name))
            selected.arguments.emplace(
                parameter.name, (*identities)[call.staticArguments[next++]]);
        auto callee = instantiate(selected, "");
        if (!callee)
          return;
        source::Instruction item = instruction;
        item.value =
            source::AlgorithmCall{*callee, apply->inputs, apply->outputs, {}};
        instruction = std::move(item);
        return;
      }
      const auto &op = *instruction.get<source::Operation>();
      std::string bindingName = fresh("b_", printJson(Array{name, call.site}));
      source::OperationBinding binding{
          {}, bindingName, {call.operation, {}, ""}};
      for (unsigned t : call.staticArguments)
        binding.application.arguments.push_back((*identities)[t]);
      auto choice = configuration.implementations.find(call.site);
      if (choice != configuration.implementations.end())
        binding.application.implementation = choice->second;
      auto installed = protocol::resolveBinding(binding.application, false);
      if (!installed) {
        fail(toString(installed.takeError()));
        return;
      }
      auto attrs = op.attributes;
      if (call.operation == "field.constant" ||
          call.operation == "vector.constant") {
        // Literal elaboration in the installed scalar field, not execution.
        StringRef modulus =
            protocol::fieldModulus(installed->outputs[0].identity);
        if (modulus.empty()) {
          fail("interactive-constant");
          return;
        }
        for (auto &literal : attrs) {
          StringRef digits = literal;
          unsigned width = std::max<unsigned>(256, 4 * digits.size());
          APInt n(width, digits, 10), p(width, modulus, 10);
          SmallString<128> encoded;
          n.urem(p).toString(encoded, 10, false);
          literal = encoded.str().str();
        }
      }
      if (bindings.size() >= 4096) {
        fail("generic-specialization-limit");
        return;
      }
      binding.location = instruction.location;
      bindings.push_back(std::move(binding));
      bindingOrigins.push_back(current);
      source::Instruction generated = instruction;
      generated.value = source::Operation{
          bindingName, {}, std::move(attrs), op.inputs, op.outputs};
      instruction = std::move(generated);
    });
    if (!problem.empty())
      return {};
    remember(*function.body, def.record->body);
    functions.push_back(std::move(function));
    functionOrigins.push_back(def.record);
    if (functions.size() > 4096 || bindings.size() > 4096) {
      fail("generic-specialization-limit");
      return {};
    }
    generated.emplace(std::move(key), name);
    return name;
  }

  bool rewrite(source::Body &body, const source::Body &original,
               unsigned depth = 0) {
    if (depth > 64)
      return fail("generic-common-body");
    for (auto [item, input] : zip(body, original)) {
      current = &input;
      if (auto *call = item.get<source::LocalCall>()) {
        auto found = configurations.find(call->callee);
        if (found == configurations.end())
          continue;
        auto symbol = instantiate(found->second, found->first);
        if (!symbol)
          return false;
        demanded.emplace(found->first, *symbol);
        call->callee = *symbol;
      } else if (auto *call = item.get<source::AlgorithmCall>()) {
        if (!definitionRecords.count(call->callee) &&
            !configurations.count(call->callee)) {
          if (!call->staticArguments.empty())
            return fail("generic-static-arity");
          continue;
        }
        auto selected = target(call->callee);
        if (!selected)
          return false;
        size_t next = 0;
        for (const auto &parameter : selected->definition->record->parameters)
          if (!selected->arguments.count(parameter.name)) {
            if (next >= call->staticArguments.size())
              return fail("generic-static-arity");
            const auto &identity = call->staticArguments[next++];
            if (protocol::installedIdentitySort(identity) != parameter.sort)
              return fail("generic-static-sort");
            selected->arguments.emplace(parameter.name, identity);
          }
        if (next != call->staticArguments.size())
          return fail("generic-static-arity");
        auto callee = instantiate(
            *selected, call->staticArguments.empty() ? call->callee : "");
        if (!callee)
          return false;
        call->callee = *callee;
        call->staticArguments.clear();
      } else if (auto *match = item.get<source::Match>()) {
        const auto *before = input.get<source::Match>();
        for (size_t i = 0; i < match->arms.size(); ++i)
          if (!rewrite(match->arms[i].body, before->arms[i].body, depth + 1))
            return false;
      } else if (auto *branch = item.get<source::Conditional>()) {
        const auto *before = input.get<source::Conditional>();
        if (!rewrite(branch->thenBody, before->thenBody, depth + 1) ||
            !rewrite(branch->elseBody, before->elseBody, depth + 1))
          return false;
      } else if (auto *loop = item.get<source::For>()) {
        if (!rewrite(loop->body, input.get<source::For>()->body, depth + 1))
          return false;
      } else if (auto *loop = item.get<source::Loop>()) {
        if (!rewrite(loop->body, input.get<source::Loop>()->body, depth + 1))
          return fail("generic-common-loop");
      }
    }
    return problem.empty();
  }

  // Record provenance while copying typed declarations. Generated records are
  // registered at their creation above; neither spans nor JSON positions are
  // used to guess correspondence after the transformation.
  void remember(const source::Body &copy, const source::Body &input) {
    for (auto [a, b] : zip(copy, input)) {
      origins.emplace(&a, &b);
      if (auto *match = a.get<source::Match>())
        for (size_t i = 0; i < match->arms.size(); ++i)
          remember(match->arms[i].body, b.get<source::Match>()->arms[i].body);
      if (auto *branch = a.get<source::Conditional>()) {
        remember(branch->thenBody, b.get<source::Conditional>()->thenBody);
        remember(branch->elseBody, b.get<source::Conditional>()->elseBody);
      }
      if (auto *loop = a.get<source::For>())
        remember(loop->body, b.get<source::For>()->body);
      if (auto *loop = a.get<source::Loop>())
        remember(loop->body, b.get<source::Loop>()->body);
    }
  }
  template <typename T>
  void remember(const std::vector<T> &copy, const std::vector<T> &input) {
    for (auto [a, b] : zip(copy, input))
      origins.emplace(&a, &b);
  }

  Expected<source::Module> runImpl(const source::Module &value,
                                   bool sourceNames) {
    current = &value;
    preserveSourceNames = sourceNames;
    if (auto e = source::checkStructure(value))
      return e;
    if (!value.isLibrary())
      return error("generic-library-format");
    if (value.definitions.size() + value.configurations.size() > 4096)
      return error("generic-library-shape");
    for (const auto &def : value.definitions) {
      current = &def;
      if (!symbol(def.name))
        return error(problem);
      definitionRecords.emplace(def.name, &def);
    }
    for (const auto &config : value.configurations) {
      current = &config;
      if (!symbol(config.name))
        return error(problem.empty() ? "generic-configuration" : problem);
      declarations.emplace(config.name, &config);
    }
    for (const auto &def : value.definitions)
      if (!definition(def))
        return error(problem);
    for (const auto &[name, record] : declarations) {
      current = record;
      if (!configuration(name))
        return error(problem);
    }
    // Reserve all original symbols before minting executable names.
    auto reserve = [&](const auto &records) {
      for (const auto &record : records) {
        current = &record;
        if (!symbol(record.name))
          return false;
      }
      return true;
    };
    if (!reserve(value.bindings) || !reserve(value.functions) ||
        !reserve(value.protocols) || !reserve(value.instances) ||
        !reserve(value.entries))
      return error(problem);
    source::Module result;
    result.location = value.location;
    result.relations = value.relations;
    result.relationViews = value.relationViews;
    result.protocols = value.protocols;
    result.instances = value.instances;
    result.entries = value.entries;
    origins.emplace(&result, &value);
    functions = value.functions;
    bindings = value.bindings;
    for (const auto &function : value.functions)
      functionOrigins.push_back(&function);
    for (const auto &binding : value.bindings)
      bindingOrigins.push_back(&binding);
    remember(result.protocols, value.protocols);
    remember(result.instances, value.instances);
    remember(result.entries, value.entries);
    for (size_t i = 0; i < value.functions.size(); ++i) {
      auto copy = functions[i];
      const auto &input = value.functions[i];
      if (copy.body && !rewrite(*copy.body, *input.body))
        return error(problem);
      functions[i] = std::move(copy);
      if (functions[i].body)
        remember(*functions[i].body, *input.body);
    }
    for (auto [copy, input] : zip(result.protocols, value.protocols)) {
      remember(copy.dependencies, input.dependencies);
      current = &input;
      if (copy.body) {
        remember(*copy.body, *input.body);
        if (!rewrite(*copy.body, *input.body))
          return error(problem);
      }
    }
    result.bindings = std::move(bindings);
    result.functions = std::move(functions);
    // Headers are registered after vector growth finishes. Nested body storage
    // moves with each owning function, preserving its registered addresses.
    for (auto [copy, input] : zip(result.functions, functionOrigins))
      origins.emplace(&copy, input);
    for (auto [copy, input] : zip(result.bindings, bindingOrigins))
      origins.emplace(&copy, input);
    if (!problem.empty())
      return error(problem);
    const source::Node *failure = nullptr;
    if (auto e = protocol::admit(result, false, &failure)) {
      auto found = origins.find(failure);
      current = found == origins.end() ? &value : found->second;
      return e;
    }
    current = &value;
    // Typed admission also checks the portable structural/byte budget.
    return result;
  }

public:
  Expected<source::Module> run(const source::Module &value, bool sourceNames,
                               const source::Node **failureLocation) {
    if (failureLocation)
      *failureLocation = nullptr;
    auto result = runImpl(value, sourceNames);
    if (!result && failureLocation)
      *failureLocation = problemRecord ? problemRecord : current;
    return result;
  }

  Expected<Value> inspect(const source::Module &value,
                          const source::Node **failureLocation) {
    auto closed = run(value, false, failureLocation);
    if (!closed)
      return closed.takeError();
    Array declared, resolved, instances;
    for (const auto &[name, def] : definitions) {
      const auto &scope = def.function.signature.scope;
      std::vector<std::string> terms;
      Array parameters;
      for (size_t i = 0; i < scope.terms.size(); ++i) {
        const auto &t = scope.terms[i];
        terms.push_back(t.parent ? terms[*t.parent] + "." + t.name : t.name);
        if (!t.parent && !scope.constants.count(i))
          parameters.push_back(Array{t.name, scope.sorts[i]});
      }
      auto predicates = [&](ArrayRef<requirements::Predicate> values) {
        Array result;
        for (const auto &p : values) {
          Array arguments;
          for (unsigned i : p.arguments)
            arguments.push_back(terms[i]);
          result.push_back(Array{
              p.kind == requirements::Predicate::Kind::Equal ? "=" : p.relation,
              std::move(arguments)});
        }
        return result;
      };
      declared.push_back(json::Object{
          {"name", name},
          {"parameters", std::move(parameters)},
          {"declared", predicates(def.function.signature.requirements)},
          {"inferred", predicates(def.inferred.obligations)},
          {"operations", int64_t(def.calls.size())}});
    }
    for (const auto &[name, configuration] : configurations) {
      Array arguments, implementations, remaining;
      for (const auto &[key, value] : configuration.arguments)
        arguments.push_back(Array{key, value});
      for (const auto &[site, implementation] : configuration.implementations)
        implementations.push_back(Array{site, implementation});
      const auto &scope = configuration.definition->function.signature.scope;
      for (size_t i = 0; i < scope.terms.size(); ++i)
        if (!scope.terms[i].parent && !scope.constants.count(i) &&
            !configuration.arguments.count(scope.terms[i].name))
          remaining.push_back(Array{scope.terms[i].name, scope.sorts[i]});
      resolved.push_back(
          json::Object{{"name", name},
                       {"definition", configuration.definition->name},
                       {"arguments", std::move(arguments)},
                       {"implementations", std::move(implementations)},
                       {"remaining", std::move(remaining)},
                       {"demanded", demanded.count(name) != 0}});
    }
    for (const auto &[configuration, symbol] : demanded)
      instances.push_back(Array{configuration, symbol});
    return json::Object{{"format", "zkc.source-inspection/1"},
                        {"definitions", std::move(declared)},
                        {"configurations", std::move(resolved)},
                        {"specializations", std::move(instances)},
                        {"source", source::encode(*closed)}};
  }
};
} // namespace

Expected<source::Module>
elaborateLibrary(const source::Module &source,
                 const source::Node **failureLocation) {
  return Elaborator().run(source, false, failureLocation);
}
Expected<source::Module> prepareLibrary(const source::Module &source,
                                        const source::Node **failureLocation) {
  return Elaborator().run(source, true, failureLocation);
}
Expected<json::Value> inspectLibrary(const source::Module &source,
                                     const source::Node **failureLocation) {
  return Elaborator().inspect(source, failureLocation);
}

} // namespace zkc::generic
