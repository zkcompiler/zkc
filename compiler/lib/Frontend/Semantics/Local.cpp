#include "Local.h"
#include "llvm/ADT/STLExtras.h"
#include <set>

using namespace llvm;
namespace zkc::frontend {
namespace {
struct Variable {
  std::string value;
  bool mutableBinding = false;
  ValueId binding;
};
struct Environment {
  ScopeId scope;
  LocalTypes types;
  std::map<std::string, Variable> names;
  // A struct binding is its leaves, each an ordinary entry of `names` under
  // `binding.path`. This map only records which bindings are structs.
  LocalAggregates structs;
};
/// The values of one authored operand or result: one value, or a struct's
/// leaves in declaration order.
struct Operand {
  source::Names values;
  std::optional<AggregateShape> shape;
};
class LocalElaborator {
  const LocalCallbacks &cb;
  semantics::LocalSymbols &symbols;
  std::set<std::string> reservedNames, reservedSites;
  size_t nextName = 0, nextSite = 0, work = 0;

  void reserve(const syntax::Body &body) {
    for (const auto &ins : body) {
      reservedSites.insert(ins.site);
      if (auto *call = std::get_if<syntax::Call>(&ins.value))
        reservedNames.insert(call->outputs.begin(), call->outputs.end());
      else if (auto *binding = std::get_if<syntax::Binding>(&ins.value))
        reservedNames.insert(binding->outputs.begin(), binding->outputs.end());
      else if (auto *branch = std::get_if<syntax::Conditional>(&ins.value)) {
        reservedNames.insert(branch->outputs.begin(), branch->outputs.end());
        reserve(branch->thenBody);
        reserve(branch->elseBody);
      } else if (auto *loop = std::get_if<syntax::For>(&ins.value)) {
        reservedNames.insert(loop->induction);
        reservedNames.insert(loop->outputs.begin(), loop->outputs.end());
        for (const auto &[name, value] : loop->carried)
          reservedNames.insert(name);
        reserve(loop->body);
      }
    }
  }
  std::string fresh(bool site = false) {
    auto &reserved = site ? reservedSites : reservedNames;
    auto &next = site ? nextSite : nextName;
    std::string name;
    do {
      name = (site ? "__expr_" : "__value_") + std::to_string(next++);
    } while (!reserved.insert(name).second);
    return name;
  }
  bool budget(const source::Node &node) {
    if (++work > 32768) {
      cb.fail(node, "source-expression-limit",
              "local elaboration exceeds 32768 steps");
      return false;
    }
    return cb.good();
  }
  std::string lookup(StringRef name, const source::Node &node,
                     const Environment &env) {
    auto it = env.names.find(name.str());
    if (it == env.names.end()) {
      // Names may contain '-', so `a-b` is one name and not a subtraction.
      auto [left, right] = name.split('-');
      bool subtraction = !right.empty() && env.names.count(left.str()) &&
                         env.names.count(right.str());
      cb.fail(node, "source-value-reference",
              "unknown input value '" + name + "'" +
                  (subtraction ? "; write a subtraction with spaces, as '" +
                                     left + " - " + right + "'"
                               : Twine()));
      return {};
    }
    symbols.use(it->second.binding, env.scope, node);
    return it->second.value;
  }
  source::Names lookup(const source::Names &names, const source::Node &node,
                       const Environment &env) {
    source::Names result;
    for (const auto &name : names)
      result.push_back(lookup(name, node, env));
    return result;
  }
  std::string type(const Environment &env, StringRef name) {
    auto it = env.types.find(name.str());
    return it == env.types.end() ? std::string{} : it->second;
  }
  void append(source::Body &out, const source::Node &node, StringRef site,
              source::Instruction::Value value) {
    source::Instruction ins;
    ins.location = node.location;
    ins.site = site.str();
    ins.value = std::move(value);
    out.push_back(std::move(ins));
  }
  std::vector<Operand>
  emit(syntax::Call call, ArrayRef<Operand> operands,
       const source::Names &outputs,
       const std::optional<std::vector<syntax::Type>> &annotation,
       Environment &env, source::Body &out, StringRef site) {
    CallShapes shapes;
    call.inputs.resize(operands.size());
    auto order = cb.argumentOrder(call);
    if (!order)
      return {};
    call.inputs.clear();
    auto appendOperand = [&](const Operand &operand) {
      call.inputs.insert(call.inputs.end(), operand.values.begin(),
                         operand.values.end());
      shapes.operands.push_back(operand.shape);
    };
    if (call.argumentNames.empty())
      for (const auto &operand : operands)
        appendOperand(operand);
    else
      for (auto index : *order)
        appendOperand(operands[index]);
    call.outputs = outputs;
    call.annotation = annotation;
    auto value = cb.call(call, env.types, site, shapes);
    if (!value)
      return {};
    append(out, call, site, std::move(*value));
    std::vector<Operand> results;
    size_t next = 0;
    for (const auto &shape : shapes.results) {
      size_t width = shape ? shape->paths.size() : 1;
      Operand result;
      result.shape = shape;
      result.values.assign(shapes.outputs.begin() + next,
                           shapes.outputs.begin() + next + width);
      next += width;
      results.push_back(std::move(result));
    }
    return results;
  }
  std::vector<Operand> unpack(const Operand &value, const source::Node &node) {
    if (!value.shape || !value.shape->product) {
      cb.fail(node, "source-product-pattern",
              "a tuple pattern requires a product value");
      return {};
    }
    std::vector<Operand> result;
    for (size_t i = 0; i < value.shape->arity; ++i) {
      auto key = std::to_string(i);
      Operand item;
      auto nested = llvm::find_if(
          value.shape->nested, [&](const auto &p) { return p.first == key; });
      if (nested != value.shape->nested.end())
        item.shape = nested->second;
      for (auto [path, leaf] : zip(value.shape->paths, value.values))
        if (path == key || StringRef(path).starts_with(key + "."))
          item.values.push_back(leaf);
      result.push_back(std::move(item));
    }
    return result;
  }
  /// The values of an authored name: a struct binding's leaves, or one value.
  Operand named(StringRef name, const source::Node &node,
                const Environment &env) {
    Operand result;
    auto it = env.structs.find(name.str());
    if (it == env.structs.end()) {
      result.values.push_back(lookup(name, node, env));
      return result;
    }
    auto binding = env.names.find(name.str());
    if (binding != env.names.end())
      symbols.use(binding->second.binding, env.scope, node);
    result.shape = it->second;
    for (const auto &path : it->second.paths)
      result.values.push_back(lookup(name.str() + "." + path, node, env));
    return result;
  }
  void registerStruct(StringRef name, const AggregateShape &shape,
                      Environment &env) {
    env.structs[name.str()] = shape;
    for (const auto &[path, inner] : shape.nested)
      env.structs[name.str() + "." + path] = inner;
  }
  /// Bind an authored result name to its values. A struct binding defines one
  /// name per leaf and emits nothing.
  void bind(StringRef name, const Operand &value, bool mut,
            const source::Node &node, Environment &env) {
    if (!value.shape) {
      if (!value.values.empty())
        define(name, value.values.front(), mut, node, env);
      return;
    }
    if (mut) {
      cb.fail(node, "source-struct-mutable",
              "a struct binding is immutable; bind its fields instead");
      return;
    }
    if (env.names.count(name.str()) || env.structs.count(name.str())) {
      cb.fail(node, "source-value-duplicate",
              "duplicate lexical binding '" + name + "'");
      return;
    }
    for (auto [path, leaf] : zip(value.shape->paths, value.values))
      define(name.str() + "." + path, leaf, false, node, env);
    auto id = symbols.bind(env.scope, name, value.shape->type, value.values,
                           false, node);
    env.names.emplace(name.str(), Variable{{}, false, id});
    registerStruct(name, *value.shape, env);
  }
  std::string primitive(StringRef name, source::Names inputs,
                        const source::Node &node, Environment &env,
                        source::Body &out, source::Names attributes = {},
                        std::optional<source::Names> statics = std::nullopt,
                        StringRef output = {}, StringRef site = {}) {
    syntax::Call call;
    call.location = node.location;
    call.callee = name.str();
    call.qualified = true;
    call.inputs = std::move(inputs);
    call.attributes = std::move(attributes);
    call.staticArguments = std::move(statics);
    std::string result = output.empty() ? fresh() : output.str();
    std::vector<Operand> operands;
    for (auto &input : call.inputs)
      operands.push_back({{input}, std::nullopt});
    emit(std::move(call), operands, {result}, std::nullopt, env, out,
         site.empty() ? fresh(true) : site.str());
    return result;
  }
  Operand operand(const syntax::Expression &expression, Environment &env,
                  source::Body &out,
                  const std::optional<syntax::Type> &expected = std::nullopt) {
    auto annotation =
        expected ? std::optional<std::vector<syntax::Type>>({*expected})
                 : std::nullopt;
    auto result = expressionValues(expression, {fresh()}, annotation, env, out,
                                   fresh(true));
    return result.empty() ? Operand{} : std::move(result.front());
  }
  std::string scalar(const syntax::Expression &expression, Environment &env,
                     source::Body &out) {
    auto result = operand(expression, env, out);
    if (result.shape) {
      cb.fail(expression, "source-struct-value",
              "a single value is required here, not a struct");
      return {};
    }
    return result.values.empty() ? std::string{} : result.values.front();
  }
  bool annotated(const Operand &value,
                 const std::optional<std::vector<syntax::Type>> &annotation,
                 const source::Node &node) {
    if (!annotation)
      return true;
    auto expected = cb.aggregate(annotation->front());
    if (!expected || !value.shape ||
        !cb.sameAggregate(*value.shape, *expected, node)) {
      if (cb.good())
        cb.fail(node, "source-annotation-type",
                "aggregate differs from its result annotation");
      return false;
    }
    return cb.good();
  }
  std::vector<Operand>
  expressionValues(const syntax::Expression &expr, const source::Names &outputs,
                   const std::optional<std::vector<syntax::Type>> &annotation,
                   Environment &env, source::Body &out, StringRef site) {
    using Kind = syntax::Expression::Kind;
    if (!budget(expr))
      return {};
    if (expr.kind == Kind::Call) {
      syntax::Call call;
      call.location = expr.location;
      call.callee = expr.name;
      call.qualified = expr.qualified;
      call.staticArguments = expr.staticArguments;
      call.staticTerms = expr.staticTerms;
      call.attributes = expr.attributes;
      call.argumentNames = expr.argumentNames;
      call.inputs.resize(expr.operands.size());
      Shapes actualShapes(expr.operands.size());
      for (auto [i, argument] : enumerate(expr.operands))
        if (argument.kind == Kind::Name && env.names.count(argument.name)) {
          call.inputs[i] = env.names.at(argument.name).value;
          if (auto found = env.structs.find(argument.name);
              found != env.structs.end())
            actualShapes[i] = found->second;
        }
      call.annotation = annotation;
      auto order = cb.argumentOrder(call);
      if (!order)
        return {};
      auto expected = cb.argumentTypes(call, env.types, actualShapes);
      std::vector<unsigned> formal(expr.operands.size());
      for (unsigned i = 0; i < formal.size(); ++i)
        formal[order->empty() ? i : (*order)[i]] = i;
      std::vector<Operand> operands;
      for (auto [i, argument] : enumerate(expr.operands))
        operands.push_back(operand(
            argument, env, out,
            formal[i] < expected.size() ? expected[formal[i]] : std::nullopt));
      if (!cb.good())
        return {};
      return emit(std::move(call), operands, outputs, annotation, env, out,
                  site);
    }
    if (expr.kind == Kind::Operator) {
      // Operands run once, left to right as written, whatever order the
      // declared target takes them in. The use then is that call.
      std::vector<Operand> operands;
      std::vector<std::string> types;
      for (const auto &argument : expr.operands) {
        operands.push_back({{scalar(argument, env, out)}, std::nullopt});
        types.push_back(type(env, operands.back().values.front()));
      }
      if (!cb.good())
        return {};
      auto target = cb.resolveOperator(expr, types);
      if (!target)
        return {};
      syntax::Call call;
      call.location = expr.location;
      call.callee = target->callee;
      call.qualified = target->qualified;
      std::vector<Operand> ordered;
      for (unsigned index : target->order)
        ordered.push_back(operands[index]);
      return emit(std::move(call), ordered, outputs, annotation, env, out,
                  site);
    }
    if (outputs.size() != 1 || (annotation && annotation->size() != 1)) {
      cb.fail(expr, "source-expression-arity",
              "this expression produces exactly one value");
      return {};
    }
    if (expr.kind == Kind::Get) {
      auto spelling = [&](auto &&self,
                          const syntax::Expression &e) -> std::string {
        if (e.kind == Kind::Name && !e.quoted)
          return e.name;
        if (e.kind != Kind::Get || e.operands.size() != 2 ||
            e.operands[1].kind != Kind::Index)
          return {};
        auto base = self(self, e.operands.front());
        return base.empty() ? std::string{} : base + "." + e.operands[1].name;
      };
      auto place = spelling(spelling, expr);
      if (!place.empty() &&
          (env.names.count(place) || env.structs.count(place))) {
        auto value = named(place, expr, env);
        if (value.shape) {
          if (!annotated(value, annotation, expr))
            return {};
        } else if (annotation && !cb.same(type(env, value.values.front()),
                                          cb.type(annotation->front()), expr)) {
          cb.fail(expr, "source-type-mismatch",
                  "projected value differs from expected type");
          return {};
        }
        return {std::move(value)};
      }
    }
    if (expr.kind == Kind::Name && env.structs.count(expr.name)) {
      auto value = named(expr.name, expr, env);
      if (!annotated(value, annotation, expr))
        return {};
      return {std::move(value)};
    }
    if (expr.kind == Kind::Product) {
      std::vector<ConstructedField> fields;
      Operand result;
      for (auto [i, item] : enumerate(expr.operands)) {
        std::optional<syntax::Type> expected;
        if (annotation && annotation->size() == 1 &&
            annotation->front().product &&
            i < annotation->front().arguments.size())
          expected = annotation->front().arguments[i];
        auto value = operand(item, env, out, expected);
        if (value.values.size() > 4096 - result.values.size()) {
          cb.fail(expr, "source-product-limit",
                  "a product has at most 4096 leaf values");
          return {};
        }
        result.values.insert(result.values.end(), value.values.begin(),
                             value.values.end());
        fields.push_back(
            {std::to_string(i), std::move(value.values), value.shape});
      }
      if (!cb.good())
        return {};
      result.shape = cb.product(fields, env.types);
      if (!annotated(result, annotation, expr))
        return {};
      return {std::move(result)};
    }
    if (expr.kind == Kind::Struct) {
      // Initializers run once, in written order; the leaves are then arranged
      // in declaration order. A construction emits no operation.
      std::vector<ConstructedField> fields;
      auto expected = cb.fieldTypes(expr, annotation);
      for (auto [i, initializer] : enumerate(expr.operands)) {
        const auto &field = expr.fields[i];
        auto value = operand(initializer, env, out,
                             i < expected.size() ? expected[i] : std::nullopt);
        fields.push_back({field, std::move(value.values), value.shape});
      }
      if (!cb.good())
        return {};
      Operand result;
      result.shape = cb.construct(expr, fields, env.types);
      if (!result.shape || !annotated(result, annotation, expr))
        return {};
      std::map<std::string, std::pair<const ConstructedField *, size_t>> byName;
      for (const auto &field : fields)
        byName[field.name] = {&field, 0};
      for (const auto &path : result.shape->paths) {
        auto &[field, next] = byName.at(StringRef(path).split('.').first.str());
        result.values.push_back(field->values[next++]);
      }
      return {std::move(result)};
    }
    std::string result;
    if (expr.kind == Kind::Name)
      result = lookup(expr.name, expr, env);
    else if (expr.kind == Kind::Index)
      result = primitive("index.constant", {}, expr, env, out, {expr.name},
                         std::nullopt, outputs[0], site);
    else if (expr.kind == Kind::Boolean) {
      auto zero = primitive("index.constant", {}, expr, env, out, {"0"});
      auto other = expr.name == "true"
                       ? zero
                       : primitive("index.constant", {}, expr, env, out, {"1"});
      result = primitive("index.equal", {zero, other}, expr, env, out, {},
                         std::nullopt, outputs[0], site);
    } else if (expr.kind == Kind::Get || expr.kind == Kind::Length) {
      auto collection = scalar(expr.operands[0], env, out);
      auto spelling = type(env, collection);
      auto kind = StringRef(spelling).split(':').first;
      std::string prefix = kind == "vector"    ? "vector"
                           : kind == "groups"  ? "curve"
                           : kind == "indices" ? "indices"
                                               : "";
      if (prefix.empty()) {
        cb.fail(expr, "source-collection-type",
                "indexing/length requires a supported collection");
        return {};
      }
      source::Names inputs{collection};
      if (expr.kind == Kind::Get)
        inputs.push_back(scalar(expr.operands[1], env, out));
      std::string suffix = expr.kind == Kind::Length ? ".length"
                           : kind == "indices"       ? ".at"
                                                     : ".get";
      result = primitive(prefix + suffix, std::move(inputs), expr, env, out, {},
                         std::nullopt, outputs[0], site);
    } else if (expr.kind == Kind::Vector) {
      if (annotation && annotation->size() == 1 &&
          annotation->front().name == "Array") {
        auto expected = cb.aggregate(annotation->front());
        if (!expected || !expected->array)
          return {};
        if (expr.operands.size() != expected->arity) {
          cb.fail(expr, "source-array-arity",
                  "array literal length differs from its expected type");
          return {};
        }
        Operand result;
        result.shape = *expected;
        for (const auto &element : expr.operands) {
          auto value =
              operand(element, env, out, annotation->front().arguments.front());
          result.values.insert(result.values.end(), value.values.begin(),
                               value.values.end());
        }
        return cb.good() ? std::vector<Operand>{std::move(result)}
                         : std::vector<Operand>{};
      }
      source::Names elements;
      for (const auto &operand : expr.operands)
        elements.push_back(scalar(operand, env, out));
      if (!cb.good())
        return {};
      std::string vectorType;
      if (annotation)
        vectorType = cb.type(annotation->front());
      else if (!elements.empty()) {
        auto element = type(env, elements.front());
        auto [kind, domain] = StringRef(element).split(':');
        if (kind == "field")
          vectorType = "vector:" + domain.str();
        if (kind == "group")
          vectorType = "groups:" + domain.str();
        if (kind == "index")
          vectorType = "indices";
      }
      auto [kind, domain] = StringRef(vectorType).split(':');
      std::string prefix = kind == "vector"    ? "vector"
                           : kind == "groups"  ? "curve"
                           : kind == "indices" ? "indices"
                                               : "";
      if (prefix.empty()) {
        cb.fail(expr, "source-vector-type",
                "vector literals require field/group elements or indices; "
                "annotate empty literals");
        return {};
      }
      std::optional<source::Names> statics;
      if (!domain.empty())
        statics = source::Names{domain.str()};
      result = primitive(prefix + ".empty", {}, expr, env, out, {}, statics,
                         elements.empty() ? outputs[0] : fresh(),
                         elements.empty() ? site.str() : fresh(true));
      for (size_t i = 0; i < elements.size() && cb.good(); ++i)
        result = primitive(prefix + ".append", {result, elements[i]}, expr, env,
                           out, {}, std::nullopt,
                           i + 1 == elements.size() ? outputs[0] : fresh(),
                           i + 1 == elements.size() ? site.str() : fresh(true));
    }
    if (cb.good() && annotation) {
      if (cb.aggregate(annotation->front()))
        cb.fail(expr, "source-struct-value",
                "a scalar expression cannot produce an aggregate");
      else if (cb.good() &&
               !cb.same(type(env, result), cb.type(annotation->front()), expr))
        cb.fail(expr, "source-type-mismatch",
                "expression differs from its result annotation");
    }
    if (result.empty())
      return {};
    return {Operand{{result}, std::nullopt}};
  }
  void define(StringRef name, StringRef value, bool mut,
              const source::Node &node, Environment &env) {
    if (env.structs.count(name.str()) || env.names.count(name.str())) {
      cb.fail(node, "source-value-duplicate",
              "duplicate lexical binding '" + name + "'");
      return;
    }
    auto id = symbols.bind(env.scope, name, symbols.logical(type(env, value)),
                           {value.str()}, mut, node);
    env.names.emplace(name.str(), Variable{value.str(), mut, id});
  }
  std::set<std::string> assignments(const syntax::Body &body) {
    std::set<std::string> result;
    auto visit = [&](auto &&self, const syntax::Body &body) -> void {
      for (const auto &ins : body)
        if (auto *b = std::get_if<syntax::Binding>(&ins.value)) {
          if (b->assignment)
            result.insert(b->outputs.begin(), b->outputs.end());
        } else if (auto *b = std::get_if<syntax::Conditional>(&ins.value)) {
          self(self, b->thenBody);
          self(self, b->elseBody);
        } else if (auto *f = std::get_if<syntax::For>(&ins.value))
          self(self, f->body);
    };
    visit(visit, body);
    return result;
  }
  source::Names captures(const source::Body &body,
                         const std::set<std::string> &arguments = {}) {
    std::set<std::string> defined = arguments, seen;
    source::Names free;
    auto use = [&](const source::Names &values) {
      for (const auto &value : values)
        if (!defined.count(value) && seen.insert(value).second)
          free.push_back(value);
    };
    for (const auto &ins : body) {
      if (auto *op = ins.get<source::Operation>()) {
        use(op->inputs);
        defined.insert(op->outputs.begin(), op->outputs.end());
      } else if (auto *call = ins.get<source::AlgorithmCall>()) {
        use(call->inputs);
        defined.insert(call->outputs.begin(), call->outputs.end());
      } else if (auto *branch = ins.get<source::Conditional>()) {
        use({branch->condition});
        use(branch->captures);
        defined.insert(branch->outputs.begin(), branch->outputs.end());
      } else if (auto *loop = ins.get<source::For>()) {
        use({loop->lower, loop->upper});
        for (const auto &[name, initial] : loop->carried)
          use({initial});
        use(loop->captures);
        defined.insert(loop->outputs.begin(), loop->outputs.end());
      } else if (auto *ret = ins.get<source::Return>())
        use(ret->values);
      else if (auto *yield = ins.get<source::Yield>())
        use(yield->values);
      else if (ins.get<source::Stop>())
        continue;
      else
        cb.fail(ins, "source-local-control",
                "unsupported instruction in local capture analysis");
    }
    return free;
  }
  source::Names yielded(const source::Body &body, const source::Node &node) {
    if (body.empty() || !body.back().get<source::Yield>()) {
      cb.fail(node, "source-control-yield",
              "an explicit local region must end in yield");
      return {};
    }
    return body.back().get<source::Yield>()->values;
  }
  bool terminal(const source::Body &body) {
    if (body.empty())
      return false;
    if (body.back().get<source::Stop>())
      return true;
    if (auto *branch = body.back().get<source::Conditional>())
      return terminal(branch->thenBody) && terminal(branch->elseBody);
    return false;
  }
  Environment capturedEnvironment(const source::Names &names,
                                  const source::Node &node,
                                  const Environment &outer) {
    Environment inner;
    inner.scope = symbols.scope(outer.scope);
    for (const auto &name : names) {
      auto value = named(name, node, outer);
      for (const auto &leaf : value.values)
        inner.types.emplace(leaf, type(outer, leaf));
      bind(name, value, false, node, inner);
    }
    return inner;
  }
  Environment nestedEnvironment(const Environment &outer) {
    auto inner = outer;
    inner.scope = symbols.scope(outer.scope);
    return inner;
  }
  /// Flat values of authored names, expanding struct bindings.
  source::Names flatten(const source::Names &names, const source::Node &node,
                        const Environment &env) {
    source::Names result;
    for (const auto &name : names) {
      auto value = named(name, node, env);
      result.insert(result.end(), value.values.begin(), value.values.end());
    }
    return result;
  }
  source::Names captureValues(const source::Names &names, bool explicitCaptures,
                              const source::Node &node,
                              const Environment &env) {
    auto result = flatten(names, node, env);
    if (explicitCaptures)
      return result;
    std::set<std::string> seen;
    source::Names unique;
    for (const auto &value : result)
      if (seen.insert(value).second)
        unique.push_back(value);
    return unique;
  }
  source::Names captureNames(const source::Names &names, bool explicitCaptures,
                             const Environment &env) {
    if (explicitCaptures)
      return names;
    source::Names result;
    for (const auto &name : names) {
      auto selected = name;
      // A runtime vector is one logical value. Only statically shaped
      // products/records expose independent captured field places.
      if (!env.names.count(name) && !env.structs.count(name)) {
        StringRef prefix(name);
        while (prefix.contains('.')) {
          prefix = prefix.rsplit('.').first;
          auto found = env.names.find(prefix.str());
          if (found == env.names.end() || found->second.value.empty())
            continue;
          auto spelling = type(env, found->second.value);
          auto kind = StringRef(spelling).split(':').first;
          if (kind == "vector" || kind == "groups" || kind == "indices") {
            selected = prefix.str();
            break;
          }
        }
      }
      if (!llvm::is_contained(result, selected))
        result.push_back(std::move(selected));
    }
    return result;
  }
  /// Region results and carried values are single values.
  source::Names singles(const source::Names &names, const source::Node &node,
                        const Environment &env) {
    for (const auto &name : names)
      if (env.structs.count(name))
        cb.fail(node, "source-struct-value",
                "a region carries and yields single values; use the fields "
                "of '" +
                    name + "'");
    return lookup(names, node, env);
  }
  void bindResults(const source::Names &outputs, const source::Names &returned,
                   const Environment &region, const source::Node &node,
                   Environment &env) {
    if (outputs.size() != returned.size()) {
      cb.fail(node, "source-control-results",
              "region result arity differs from its binding");
      return;
    }
    for (auto [name, value] : zip(outputs, returned)) {
      if (!env.types.emplace(name, type(region, value)).second)
        cb.fail(node, "source-value-duplicate", "duplicate region result");
      define(name, name, false, node, env);
    }
  }
  source::Body body(const syntax::Body &input, Environment &env,
                    bool region = false, bool explicitYield = false) {
    // Region parameters already belong to the scope created by their caller.
    if (!region)
      env.scope = symbols.scope(env.scope);
    source::Body out;
    for (const auto &ins : input) {
      if (!budget(ins))
        break;
      if (terminal(out)) {
        cb.fail(ins, "source-control-stop",
                "instruction follows a terminal stop");
        break;
      }
      if (auto *call = std::get_if<syntax::Call>(&ins.value)) {
        std::vector<Operand> operands;
        for (const auto &name : call->inputs)
          operands.push_back(named(name, ins, env));
        syntax::Call resolved = *call;
        if (call->isOperator && cb.good()) {
          syntax::Expression use;
          use.location = call->location;
          use.name = call->callee;
          std::vector<std::string> types;
          for (const auto &operand : operands) {
            if (operand.shape) {
              cb.fail(ins, "source-struct-value",
                      "a single value is required here, not a struct");
              break;
            }
            types.push_back(type(env, operand.values.front()));
          }
          auto target =
              cb.good() ? cb.resolveOperator(use, types) : std::nullopt;
          if (!target)
            break;
          resolved.callee = target->callee;
          resolved.qualified = target->qualified;
          std::vector<Operand> ordered;
          for (unsigned index : target->order)
            ordered.push_back(operands[index]);
          operands = std::move(ordered);
        }
        auto results = emit(resolved, operands, call->outputs, call->annotation,
                            env, out, ins.site);
        if (cb.good())
          out.back().location = ins.location;
        for (auto [name, value] : zip(call->outputs, results))
          bind(name, value, false, ins, env);
      } else if (auto *binding = std::get_if<syntax::Binding>(&ins.value)) {
        source::Names outputs = binding->outputs;
        if (binding->assignment) {
          auto it = env.names.find(outputs.front());
          if (it == env.names.end() || !it->second.mutableBinding) {
            cb.fail(ins, "source-assignment",
                    "assignment requires an existing mutable binding");
            break;
          }
          outputs = {fresh()};
        }
        if (binding->destructure)
          outputs = {fresh()};
        auto values = expressionValues(binding->expression, outputs,
                                       binding->annotation, env, out, ins.site);
        if (!cb.good())
          break;
        if (binding->destructure) {
          if (values.size() != 1) {
            cb.fail(ins, "source-product-pattern",
                    "a tuple pattern binds one product value");
            break;
          }
          values = unpack(values.front(), ins);
          if (values.size() != binding->outputs.size()) {
            cb.fail(ins, "source-product-pattern",
                    "tuple pattern has the wrong number of elements");
            break;
          }
        }
        if (binding->assignment) {
          if (values.empty() || values.front().shape) {
            cb.fail(ins, "source-struct-mutable",
                    "a struct cannot be assigned; assign its fields' values");
            break;
          }
          auto &variable = env.names.at(binding->outputs.front());
          const auto &assigned = values.front().values.front();
          if (!cb.same(type(env, variable.value), type(env, assigned), ins)) {
            cb.fail(ins, "source-assignment-type",
                    "assignment cannot change a binding's type");
            break;
          }
          variable.value = assigned;
        } else
          for (auto [name, value] : zip(binding->outputs, values))
            bind(name, value, binding->mutableBinding, ins, env);
      } else if (auto *ret = std::get_if<syntax::Exit>(&ins.value)) {
        if (region) {
          cb.fail(ins, "source-control-return",
                  "early return from a local region is not supported");
          break;
        }
        if (&ins != &input.back()) {
          cb.fail(ins, "source-control-return",
                  "a local return must terminate its body");
          break;
        }
        auto value = operand(ret->expression, env, out, cb.resultAnnotation);
        if (!cb.good())
          break;
        if (cb.inferResult) {
          cb.returned(value.values, value.shape, env.types);
          append(out, ins, {}, source::Return{std::move(value.values)});
          continue;
        }
        if (cb.results.size() != 1 ||
            bool(value.shape) != bool(cb.results.front())) {
          cb.fail(ins, "source-struct-value",
                  "return differs from the declared source result");
          break;
        }
        if (value.shape &&
            !cb.sameAggregate(*cb.results.front(), *value.shape, ins)) {
          cb.fail(ins, "source-struct-mismatch",
                  "return aggregate differs from the declared type");
          break;
        }
        append(out, ins, {}, source::Return{std::move(value.values)});
      } else if (auto *ret = std::get_if<source::Return>(&ins.value)) {
        if (region)
          cb.fail(ins, "source-control-return",
                  "early return from a local region is not supported");
        source::Names returned;
        for (auto [index, name] : enumerate(ret->values)) {
          auto value = named(name, ins, env);
          const std::optional<AggregateShape> *declared =
              index < cb.results.size() ? &cb.results[index] : nullptr;
          if (bool(value.shape) != bool(declared && *declared))
            cb.fail(ins, "source-struct-value",
                    "'" + name + "' and the declared result " +
                        Twine(index + 1) +
                        " must both be structs or both single values");
          else if (value.shape &&
                   !cb.sameAggregate(**declared, *value.shape, ins))
            cb.fail(ins, "source-struct-mismatch",
                    "'" + name + "' is a " + value.shape->name +
                        ", but result " + Twine(index + 1) + " declares " +
                        (*declared)->name);
          returned.insert(returned.end(), value.values.begin(),
                          value.values.end());
        }
        append(out, ins, {}, source::Return{std::move(returned)});
      } else if (auto *stop = std::get_if<source::Stop>(&ins.value)) {
        if (!stop->role.empty())
          cb.fail(ins, "source-local-control",
                  "local stop names no participant");
        append(out, ins, ins.site, *stop);
      } else if (auto *yield = std::get_if<source::Yield>(&ins.value)) {
        if (!region || !explicitYield)
          cb.fail(ins, "source-control-yield",
                  "yield requires an explicit capture/carry region");
        append(out, ins, {}, source::Yield{singles(yield->values, ins, env)});
      } else if (auto *branch = std::get_if<syntax::Conditional>(&ins.value)) {
        source::Conditional result;
        result.condition = scalar(branch->condition, env, out);
        if (type(env, result.condition) != "bool")
          cb.fail(ins, "source-condition-type", "if requires bool");
        auto captured =
            captureNames(branch->captures, branch->explicitCaptures, env);
        Environment yes = branch->explicitRegion
                              ? capturedEnvironment(captured, ins, env)
                              : nestedEnvironment(env);
        Environment no = branch->explicitRegion
                             ? capturedEnvironment(captured, ins, env)
                             : nestedEnvironment(env);
        result.thenBody =
            body(branch->thenBody, yes, true, branch->explicitRegion);
        result.elseBody =
            body(branch->elseBody, no, true, branch->explicitRegion);
        if (branch->explicitRegion) {
          result.captures =
              captureValues(captured, branch->explicitCaptures, ins, env);
          result.outputs = branch->outputs;
          bool yesStops = terminal(result.thenBody),
               noStops = terminal(result.elseBody);
          auto y = yesStops ? source::Names{} : yielded(result.thenBody, ins),
               n = noStops ? source::Names{} : yielded(result.elseBody, ins);
          if (yesStops && noStops && !result.outputs.empty())
            cb.fail(ins, "source-control-results",
                    "terminal branches cannot produce outputs");
          else if (!yesStops && !noStops && y.size() != n.size())
            cb.fail(ins, "source-control-results",
                    "branch result arities differ");
          else if (!yesStops && !noStops)
            for (auto [a, b] : zip(y, n))
              if (!cb.same(type(yes, a), type(no, b), ins))
                cb.fail(ins, "source-control-results",
                        "branch result types differ");
          if (!yesStops || !noStops)
            bindResults(result.outputs, yesStops ? n : y, yesStops ? no : yes,
                        ins, env);
        } else {
          source::Names yesValues, noValues;
          for (auto &[name, variable] : env.names) {
            if (yes.names.at(name).value == variable.value &&
                no.names.at(name).value == variable.value)
              continue;
            if (!variable.mutableBinding) {
              cb.fail(ins, "source-assignment",
                      "only mutable bindings can merge");
              break;
            }
            auto output = fresh();
            env.types.emplace(output, type(env, variable.value));
            result.outputs.push_back(output);
            yesValues.push_back(yes.names.at(name).value);
            noValues.push_back(no.names.at(name).value);
            variable.value = output;
          }
          if (!terminal(result.thenBody))
            append(result.thenBody, ins, {}, source::Yield{yesValues});
          if (!terminal(result.elseBody))
            append(result.elseBody, ins, {}, source::Yield{noValues});
          auto a = captures(result.thenBody), b = captures(result.elseBody);
          result.captures = std::move(a);
          for (const auto &name : b)
            if (!llvm::is_contained(result.captures, name))
              result.captures.push_back(name);
          if (terminal(result.thenBody) && terminal(result.elseBody))
            result.outputs.clear();
        }
        append(out, ins, ins.site, std::move(result));
      } else if (auto *loop = std::get_if<syntax::For>(&ins.value)) {
        source::For result;
        result.lower = scalar(loop->lower, env, out);
        result.upper = scalar(loop->upper, env, out);
        result.induction = loop->induction;
        if (type(env, result.lower) != "index" ||
            type(env, result.upper) != "index")
          cb.fail(ins, "source-loop-bound-type",
                  "for bounds require index values");
        auto captured =
            captureNames(loop->captures, loop->explicitCaptures, env);
        Environment inner = loop->explicitRegion
                                ? capturedEnvironment(captured, ins, env)
                                : nestedEnvironment(env);
        inner.types.emplace(result.induction, "index");
        define(loop->induction, result.induction, false, ins, inner);
        std::set<std::string> arguments{result.induction};
        std::vector<std::string> changed;
        if (loop->explicitRegion) {
          for (const auto &[name, initial] : loop->carried) {
            auto value = singles({initial}, ins, env).front();
            result.carried.emplace_back(name, value);
            inner.types.emplace(name, type(env, value));
            define(name, name, false, ins, inner);
            arguments.insert(name);
          }
        } else {
          for (const auto &name : assignments(loop->body)) {
            auto it = env.names.find(name);
            if (it == env.names.end())
              continue; // Inner lexical binding.
            if (!it->second.mutableBinding) {
              cb.fail(ins, "source-assignment",
                      "loop assignment requires mutable binding");
              break;
            }
            auto carried = fresh();
            result.carried.emplace_back(carried, it->second.value);
            inner.types.emplace(carried, type(env, it->second.value));
            inner.names[name] = {carried, true, it->second.binding};
            arguments.insert(carried);
            changed.push_back(name);
          }
        }
        result.body = body(loop->body, inner, true, loop->explicitRegion);
        if (loop->explicitRegion) {
          result.captures =
              captureValues(captured, loop->explicitCaptures, ins, env);
          result.outputs = loop->outputs;
          bindResults(result.outputs, yielded(result.body, ins), inner, ins,
                      env);
        } else {
          source::Names yieldedValues;
          for (const auto &name : changed) {
            yieldedValues.push_back(inner.names.at(name).value);
            auto output = fresh();
            env.types.emplace(output, type(env, env.names.at(name).value));
            env.names.at(name).value = output;
            result.outputs.push_back(output);
          }
          append(result.body, ins, {}, source::Yield{yieldedValues});
          result.captures = captures(result.body, arguments);
        }
        append(out, ins, ins.site, std::move(result));
      } else
        cb.fail(ins, "source-local-control",
                "instruction is not local algorithm syntax");
    }
    return out;
  }

public:
  LocalElaborator(const LocalCallbacks &callbacks,
                  semantics::LocalSymbols &symbols)
      : cb(callbacks), symbols(symbols) {}
  source::Body run(const syntax::Body &input, LocalTypes types,
                   const LocalAggregates &structs) {
    Environment env;
    env.scope = symbols.root();
    env.types = std::move(types);
    for (const auto &[name, type] : env.types) {
      reservedNames.insert(name);
      define(name, name, false, {}, env);
    }
    // A struct parameter arrives as its leaves, already among the types.
    for (const auto &[name, shape] : structs) {
      registerStruct(name, shape, env);
      source::Names leaves;
      for (const auto &path : shape.paths)
        leaves.push_back(name + "." + path);
      auto id = symbols.bind(env.scope, name, shape.type, leaves, false, {});
      env.names.emplace(name, Variable{{}, false, id});
    }
    reserve(input);
    return body(input, env);
  }
};
} // namespace
source::Body elaborateLocal(const syntax::Body &body, LocalTypes types,
                            LocalAggregates structs,
                            const LocalCallbacks &callbacks,
                            semantics::LocalSymbols &symbols) {
  return LocalElaborator(callbacks, symbols)
      .run(body, std::move(types), structs);
}
} // namespace zkc::frontend
