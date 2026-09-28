#include "Local.h"
#include "Collections.h"
#include "Places.h"
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
// A captured place bound in a region under its checked flat key.
struct Alias {
  syntax::Place place;
  std::string key;
};
struct Environment {
  ScopeId scope;
  LocalTypes types;
  std::map<std::string, Variable> names;
  // A struct binding is its leaves, each an ordinary entry of `names` under
  // `binding.path`. This map only records which bindings are structs.
  LocalAggregates structs;
  std::vector<Alias> captured;
};
/// The values of one authored operand or result: one value, or a struct's
/// leaves in declaration order.
struct Operand {
  source::Names values;
  std::optional<AggregateShape> shape;
};
/// A place checked against the typed environment: its normalized steps and
/// flat key. `complete` is false when an inferred capture stopped at an index
/// into one bulk collection value, which is captured whole.
struct Selected {
  syntax::Place place;
  std::string key;
  bool complete = true;
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
      cb.fail(node, "source-value-reference",
              "unknown input value '" + name + "'");
      return {};
    }
    symbols.use(it->second.binding, env.scope, node);
    return it->second.value;
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
  emit(CallRequest call, ArrayRef<Operand> operands,
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
  /// The values bound under a checked flat key: a struct binding's leaves, or
  /// one value.
  Operand named(StringRef key, const source::Node &node,
                const Environment &env) {
    Operand result;
    auto it = env.structs.find(key.str());
    if (it == env.structs.end()) {
      result.values.push_back(lookup(key, node, env));
      return result;
    }
    auto binding = env.names.find(key.str());
    if (binding != env.names.end())
      symbols.use(binding->second.binding, env.scope, node);
    result.shape = it->second;
    for (const auto &path : it->second.paths)
      result.values.push_back(lookup(key.str() + "." + path, node, env));
    return result;
  }
  static places::AggregateKind aggregateKind(const AggregateShape &shape) {
    return shape.array     ? places::AggregateKind::Array
           : shape.product ? places::AggregateKind::Product
                           : places::AggregateKind::Record;
  }
  static source::Names fieldNames(const AggregateShape &shape) {
    source::Names fields;
    auto add = [&](StringRef path) {
      auto field = path.split('.').first.str();
      if (!llvm::is_contained(fields, field))
        fields.push_back(std::move(field));
    };
    for (const auto &path : shape.paths)
      add(path);
    for (const auto &nested : shape.nested)
      add(nested.first);
    return fields;
  }
  /// Check a place's steps against the aggregate shapes of its binding. A
  /// region reads a captured place through the longest captured ancestor.
  std::optional<Selected> select(const syntax::Place &place,
                                 const source::Node &node,
                                 const Environment &env,
                                 bool captureCollection = false) {
    Selected result;
    const auto *root = syntax::localRoot(place);
    const auto *alias = places::capturedAncestor(ArrayRef(env.captured), place);
    size_t begin = 0;
    if (alias) {
      result.place = alias->place;
      result.key = alias->key;
      begin = alias->place.steps.size();
    } else if (root && (env.names.count(*root) || env.structs.count(*root))) {
      result.place.root = place.root;
      result.place.location = place.location;
      result.key = *root;
    } else {
      cb.fail(place.location ? place : node, "source-value-reference",
              "unknown input value '" + syntax::spelling(place) + "'");
      return std::nullopt;
    }
    for (size_t i = begin; i < place.steps.size(); ++i) {
      const auto &step = place.steps[i];
      auto parent = env.structs.find(result.key);
      if (parent == env.structs.end()) {
        auto scalar = env.names.find(result.key);
        if (captureCollection && step.kind == syntax::Projection::Kind::Index &&
            scalar != env.names.end() &&
            collectionOperations(
                StringRef(type(env, scalar->second.value)).split(':').first)) {
          result.complete = false;
          return result;
        }
        cb.fail(step.location ? step : node, "source-projection",
                "projection requires the corresponding aggregate kind");
        return std::nullopt;
      }
      const auto &shape = parent->second;
      auto selection = places::select(step, aggregateKind(shape), shape.arity,
                                      fieldNames(shape));
      if (!selection) {
        cb.fail(step.location ? step : node, "source-projection",
                "invalid projection kind, field, or static index");
        return std::nullopt;
      }
      auto checked = step;
      checked.key = selection->key;
      result.place.steps.push_back(std::move(checked));
      result.key += "." + selection->key;
    }
    if (!env.names.count(result.key) && !env.structs.count(result.key)) {
      cb.fail(place.location ? place : node, "source-value-reference",
              "unknown input value '" + syntax::spelling(place) + "'");
      return std::nullopt;
    }
    return result;
  }
  Operand named(const syntax::Place &place, const source::Node &node,
                const Environment &env) {
    auto selected = select(place, node, env);
    return selected ? named(selected->key, node, env) : Operand{};
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
    CallRequest call;
    call.location = node.location;
    call.target = syntax::Target::operation(name);
    call.inputs = std::move(inputs);
    call.attributes = std::move(attributes);
    call.suppliedStatics = std::move(statics);
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
  static source::Names atomValues(ArrayRef<syntax::Atom> atoms) {
    source::Names result;
    for (const auto &atom : atoms)
      result.push_back(atom.value);
    return result;
  }
  /// The flat key of a selection receiver. A place performs no computation;
  /// any other receiver is evaluated once and bound, as
  /// `let fresh = receiver; fresh.step`, under this route's ordinary rules.
  std::optional<std::string> receiver(const syntax::Expression &base,
                                      Environment &env, source::Body &out) {
    if (auto candidate = syntax::placeCandidate(base)) {
      auto selected = select(*candidate, base, env, true);
      if (!selected)
        return std::nullopt;
      // A literal index into a collection value is itself a runtime query.
      if (selected->complete)
        return selected->key;
    }
    auto value = operand(base, env, out);
    if (!cb.good())
      return std::nullopt;
    auto name = fresh();
    bind(name, value, false, base, env);
    return cb.good() ? std::optional<std::string>(name) : std::nullopt;
  }
  std::vector<Operand>
  expressionValues(const syntax::Expression &expr, const source::Names &outputs,
                   const std::optional<std::vector<syntax::Type>> &annotation,
                   Environment &env, source::Body &out, StringRef site) {
    using Kind = syntax::Expression::Kind;
    if (!budget(expr))
      return {};
    if (expr.kind == Kind::Call) {
      CallRequest call;
      call.location = expr.location;
      call.target = expr.reference.target;
      call.staticArguments = expr.staticArguments;
      call.attributes = atomValues(expr.attributes);
      call.argumentNames = expr.argumentNames;
      call.inputs.resize(expr.operands.size());
      Shapes actualShapes(expr.operands.size());
      // Known argument types guide expectations before operands run.
      for (auto [i, argument] : enumerate(expr.operands)) {
        const auto &target = argument.reference.target;
        if (argument.kind != Kind::Name ||
            target.kind != syntax::Target::Kind::Local ||
            !env.names.count(target.symbol))
          continue;
        call.inputs[i] = env.names.at(target.symbol).value;
        if (auto found = env.structs.find(target.symbol);
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
      // Operands run once, left to right as written, whatever order the
      // callee's ports take them in.
      std::vector<Operand> operands;
      for (auto [i, argument] : enumerate(expr.operands)) {
        operands.push_back(operand(
            argument, env, out,
            formal[i] < expected.size() ? expected[formal[i]] : std::nullopt));
        if (!cb.good())
          return {};
      }
      return emit(std::move(call), operands, outputs, annotation, env, out,
                  site);
    }
    if (expr.kind == Kind::Operator) {
      // Operands run once, left to right as written, whatever order the
      // declared target takes them in. The use then is that call.
      std::vector<Operand> operands;
      std::vector<std::string> types;
      for (const auto &argument : expr.operands) {
        operands.push_back(operand(argument, env, out));
        if (!cb.good())
          return {};
        const auto &value = operands.back();
        if (value.shape && (value.shape->product || value.shape->array)) {
          cb.fail(argument, "source-struct-value",
                  "operator requires a logical value or nominal record");
          return {};
        }
        types.push_back(value.shape ? "record:" + value.shape->name
                                    : type(env, value.values.front()));
      }
      auto target = cb.resolveOperator(expr, expr.name, types);
      if (!target)
        return {};
      CallRequest call;
      call.location = expr.location;
      call.target = target->target;
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
    auto checkedValue = [&](Operand value) -> std::vector<Operand> {
      if (!cb.good())
        return {};
      if (value.shape) {
        if (!annotated(value, annotation, expr))
          return {};
      } else if (annotation && !cb.same(type(env, value.values.front()),
                                        cb.type(annotation->front()), expr)) {
        if (cb.good())
          cb.fail(expr, "source-type-mismatch",
                  "projected value differs from expected type");
        return {};
      }
      return {std::move(value)};
    };
    std::string nameKey;
    if (expr.kind == Kind::Name) {
      auto selected = select(*syntax::placeCandidate(expr), expr, env);
      if (!selected)
        return {};
      if (env.structs.count(selected->key))
        return checkedValue(named(selected->key, expr, env));
      nameKey = selected->key;
    }
    if (expr.kind == Kind::Field || expr.kind == Kind::TupleField ||
        expr.kind == Kind::Get || expr.kind == Kind::Length) {
      // A place read through a captured ancestor is selected as a whole.
      if (auto candidate = syntax::placeCandidate(expr))
        if (places::capturedAncestor(ArrayRef(env.captured), *candidate)) {
          auto selected = select(*candidate, expr, env, true);
          if (!selected)
            return {};
          if (selected->complete)
            return checkedValue(named(selected->key, expr, env));
        }
      auto root = receiver(expr.operands.front(), env, out);
      if (!root)
        return {};
      if (auto parent = env.structs.find(*root); parent != env.structs.end()) {
        if (expr.kind == Kind::Length) {
          cb.fail(expr, "source-collection-type",
                  "length requires a supported collection value");
          return {};
        }
        // Select the named component without reading its siblings.
        const auto &shape = parent->second;
        auto step = syntax::projection(expr);
        std::optional<places::Selection> selection;
        if (step)
          selection = places::select(*step, aggregateKind(shape), shape.arity,
                                     fieldNames(shape));
        if (!selection) {
          cb.fail(expr, "source-projection",
                  expr.kind == Kind::Get && !step
                      ? "an aggregate index must be a static literal"
                      : "invalid projection kind, field, or static index");
          return {};
        }
        return checkedValue(named(*root + "." + selection->key, expr, env));
      }
      if (expr.kind == Kind::Field || expr.kind == Kind::TupleField) {
        cb.fail(expr, "source-projection",
                "projection requires the corresponding aggregate kind");
        return {};
      }
      // A runtime query on one collection value.
      auto collection = lookup(*root, expr, env);
      auto spelling = type(env, collection);
      auto operations =
          collectionOperations(StringRef(spelling).split(':').first);
      if (!operations) {
        cb.fail(expr, "source-collection-type",
                "indexing/length requires a supported collection");
        return {};
      }
      source::Names inputs{collection};
      if (expr.kind == Kind::Get)
        inputs.push_back(scalar(expr.operands[1], env, out));
      if (!cb.good())
        return {};
      auto result = primitive(expr.kind == Kind::Length ? operations->length
                                                        : operations->index,
                              std::move(inputs), expr, env, out, {},
                              std::nullopt, outputs[0], site);
      return checkedValue(Operand{{result}, std::nullopt});
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
        if (!cb.good())
          return {};
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
      result = lookup(nameKey, expr, env);
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
      auto operations = collectionOperations(kind);
      if (!operations) {
        cb.fail(expr, "source-vector-type",
                "vector literals require field/group elements or indices; "
                "annotate empty literals");
        return {};
      }
      std::optional<source::Names> statics;
      if (!domain.empty())
        statics = source::Names{domain.str()};
      result = primitive(operations->empty, {}, expr, env, out, {}, statics,
                         elements.empty() ? outputs[0] : fresh(),
                         elements.empty() ? site.str() : fresh(true));
      for (size_t i = 0; i < elements.size() && cb.good(); ++i)
        result = primitive(operations->append, {result, elements[i]}, expr, env,
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
          // Only a whole mutable scalar binding can be assigned.
          if (b->assignment && b->assignment->steps.empty())
            if (const auto *root = syntax::localRoot(*b->assignment))
              result.insert(*root);
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
  // A region binds each captured place under its checked key and reads
  // selections below it through that capture.
  Environment capturedEnvironment(ArrayRef<Selected> captured,
                                  const source::Node &node,
                                  const Environment &outer) {
    Environment inner;
    inner.scope = symbols.scope(outer.scope);
    for (const auto &place : captured) {
      auto value = named(place.key, node, outer);
      for (const auto &leaf : value.values)
        inner.types.emplace(leaf, type(outer, leaf));
      bind(place.key, value, false, node, inner);
      inner.captured.push_back({place.place, place.key});
    }
    return inner;
  }
  Environment nestedEnvironment(const Environment &outer) {
    auto inner = outer;
    inner.scope = symbols.scope(outer.scope);
    return inner;
  }
  /// Region capture values: each captured place's flat values, without
  /// repeating a value an inferred capture list already contains.
  source::Names captureValues(ArrayRef<Selected> captured,
                              bool explicitCaptures, const source::Node &node,
                              const Environment &env) {
    source::Names result;
    std::set<std::string> seen;
    for (const auto &place : captured)
      for (auto &value : named(place.key, node, env).values)
        if (explicitCaptures || seen.insert(value).second)
          result.push_back(std::move(value));
    return result;
  }
  /// Check captured places against their types before any flattening. An
  /// inferred index into one bulk collection value captures that whole value;
  /// its index expression's inputs are candidates of their own. Inferred
  /// captures keep first use, and a whole value subsumes its selections.
  /// Explicit capture lists keep their written order and refusals.
  std::optional<std::vector<Selected>>
  normalizeCaptures(const syntax::Places &places, bool explicitCaptures,
                    const source::Node &node, const Environment &env) {
    std::vector<Selected> result;
    for (const auto &place : places) {
      auto selected = select(place, node, env, !explicitCaptures);
      if (!selected)
        return std::nullopt;
      if (explicitCaptures)
        result.push_back(std::move(*selected));
      else
        syntax::unite(
            result, std::move(*selected),
            [](const Selected &a, const Selected &b) {
              return syntax::ancestor(a.place, b.place);
            },
            [](Selected &, Selected &&) {});
    }
    return result;
  }
  /// Region results and carried values are single values.
  source::Names singles(const syntax::Places &places, const source::Node &node,
                        const Environment &env) {
    source::Names result;
    for (const auto &place : places) {
      auto value = named(place, node, env);
      if (!cb.good())
        return {};
      if (value.shape || value.values.size() != 1) {
        cb.fail(place.location ? place : node, "source-struct-value",
                "a region carries and yields single values; select a field");
        return {};
      }
      result.push_back(value.values.front());
    }
    return result;
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
        for (const auto &place : call->inputs)
          operands.push_back(named(place, ins, env));
        CallRequest resolved;
        resolved.location = call->location;
        resolved.target = call->callee.target;
        resolved.staticArguments = call->staticArguments;
        resolved.attributes = atomValues(call->attributes);
        resolved.argumentNames = call->argumentNames;
        resolved.destructure = call->destructure;
        if (call->operatorSymbol && cb.good()) {
          std::vector<std::string> types;
          for (const auto &operand : operands) {
            if (operand.shape &&
                (operand.shape->product || operand.shape->array)) {
              cb.fail(ins, "source-struct-value",
                      "operator requires a logical value or nominal record");
              break;
            }
            types.push_back(operand.shape ? "record:" + operand.shape->name
                                          : type(env, operand.values.front()));
          }
          auto target =
              cb.good()
                  ? cb.resolveOperator(*call, *call->operatorSymbol, types)
                  : std::nullopt;
          if (!target)
            break;
          resolved.target = target->target;
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
        std::string assignedKey;
        if (binding->assignment) {
          auto assigned = select(*binding->assignment, ins, env);
          if (!assigned)
            break;
          assignedKey = assigned->key;
          auto it = env.names.find(assignedKey);
          if (it == env.names.end() || !it->second.mutableBinding ||
              env.structs.count(assignedKey)) {
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
          auto &variable = env.names.at(assignedKey);
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
      } else if (auto *ret = std::get_if<syntax::Return>(&ins.value)) {
        if (region)
          cb.fail(ins, "source-control-return",
                  "early return from a local region is not supported");
        source::Names returned;
        for (auto [index, place] : enumerate(ret->values)) {
          auto value = named(place, ins, env);
          auto name = syntax::spelling(place);
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
      } else if (auto *yield = std::get_if<syntax::Yield>(&ins.value)) {
        if (!region || !explicitYield)
          cb.fail(ins, "source-control-yield",
                  "yield requires an explicit capture/carry region");
        append(out, ins, {}, source::Yield{singles(yield->values, ins, env)});
      } else if (auto *branch = std::get_if<syntax::Conditional>(&ins.value)) {
        source::Conditional result;
        result.condition = scalar(branch->condition, env, out);
        if (type(env, result.condition) != "bool")
          cb.fail(ins, "source-condition-type", "if requires bool");
        auto captured = normalizeCaptures(branch->captures,
                                          branch->explicitCaptures, ins, env);
        if (!captured)
          break;
        Environment yes = branch->explicitRegion
                              ? capturedEnvironment(*captured, ins, env)
                              : nestedEnvironment(env);
        Environment no = branch->explicitRegion
                             ? capturedEnvironment(*captured, ins, env)
                             : nestedEnvironment(env);
        result.thenBody =
            body(branch->thenBody, yes, true, branch->explicitRegion);
        result.elseBody =
            body(branch->elseBody, no, true, branch->explicitRegion);
        if (branch->explicitRegion) {
          result.captures =
              captureValues(*captured, branch->explicitCaptures, ins, env);
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
            normalizeCaptures(loop->captures, loop->explicitCaptures, ins, env);
        if (!captured)
          break;
        Environment inner = loop->explicitRegion
                                ? capturedEnvironment(*captured, ins, env)
                                : nestedEnvironment(env);
        inner.types.emplace(result.induction, "index");
        define(loop->induction, result.induction, false, ins, inner);
        std::set<std::string> arguments{result.induction};
        std::vector<std::string> changed;
        if (loop->explicitRegion) {
          for (const auto &[name, initial] : loop->carried) {
            auto values = singles({initial}, ins, env);
            if (values.empty())
              break;
            const auto &value = values.front();
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
              captureValues(*captured, loop->explicitCaptures, ins, env);
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
