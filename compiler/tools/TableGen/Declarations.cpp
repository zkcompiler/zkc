#include "Declarations.h"
#include "Contributions.h"
#include "Mathematical.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

using namespace llvm;
namespace {
using Records = std::vector<const Record *>;
StringRef name(const Record *r) { return r->getValueAsString("name"); }
std::string quote(StringRef s) {
  std::string result;
  raw_string_ostream os(result);
  os << '"';
  os.write_escaped(s);
  os << '"';
  return result;
}
std::string boolean(bool v) { return v ? "true" : "false"; }
std::string number(const Record *r, StringRef field) {
  return std::to_string(r->getValueAsInt(field));
}
const Record *optionalDef(const Record *r, StringRef field) {
  auto *init = r->getValueInit(field);
  auto *def = dyn_cast<DefInit>(init);
  return def ? def->getDef() : nullptr;
}
void require(bool valid, const Record *r, const Twine &message) {
  if (!valid)
    PrintFatalError(r, message);
}
bool identifier(StringRef value) {
  return !value.empty() && (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) { return isAlnum(c) || c == '_'; });
}
bool path(StringRef value, StringRef separator) {
  if (value.empty())
    return false;
  while (true) {
    auto [head, tail] = value.split(separator);
    if (!identifier(head))
      return false;
    if (tail.empty())
      return !value.ends_with(separator);
    value = tail;
  }
}
std::pair<StringRef, StringRef> parameter(const Record *r) {
  return {name(r->getValueAsDef("kind")), r->getValueAsString("sort")};
}
bool sameParameter(const Record *a, const Record *b) {
  return parameter(a) == parameter(b);
}
std::string strings(ArrayRef<StringRef> values) {
  std::string result = "{";
  for (auto [i, v] : enumerate(values)) {
    if (i)
      result += ", ";
    result += quote(v);
  }
  return result + "}";
}
std::string names(ArrayRef<const Record *> values) {
  std::vector<StringRef> ns;
  for (const auto *r : values)
    ns.push_back(name(r));
  return strings(ns);
}
std::string indices(ArrayRef<int64_t> values) {
  std::string result = "{";
  for (auto [i, v] : enumerate(values)) {
    if (i)
      result += ", ";
    result += std::to_string(v);
  }
  return result + "}";
}
struct Model {
  DeclarationOrder order;
  Records sorts, types, operations, members, capabilities, rules, typeExports,
      families, familyCases, associatedTypes, capabilityExports;
  explicit Model(const RecordKeeper &records)
      : order(records), sorts(order.sort("ZKC_Sort")),
        types(order.sort("ZKC_Type")), operations(order.sort("ZKC_Operation")),
        members(order.sort("ZKC_Member")),
        capabilities(order.sort("ZKC_Capability")),
        rules(order.sort("ZKC_Implication")),
        typeExports(order.sort("ZKC_TypeExport")),
        families(order.sort("ZKC_TypeFamily")),
        familyCases(order.sort("ZKC_TypeFamilyCase")),
        associatedTypes(order.sort("ZKC_AssociatedType")),
        capabilityExports(order.sort("ZKC_CapabilityExport")) {
    if (records.getAllDerivedDefinitions("ZKC_Declaration").size() > 100000)
      PrintFatalError("declaration record limit");
    validateMathematicalDeclarations(records);
    validate();
  }
  void validate();
  void validateOperation(const Record *op);
  void validateFacets(const Record *op);
};
void uniqueNames(ArrayRef<const Record *> records, StringRef category) {
  std::set<std::string> names;
  for (const auto *r : records)
    require(names.insert(name(r).str()).second, r,
            "duplicate " + category + " ownership: " + name(r));
}
void validateParameters(const Record *owner, ArrayRef<const Record *> ps,
                        ArrayRef<const Record *> args) {
  require(ps.size() == args.size(), owner, "parameter arity mismatch");
  for (auto [p, a] : zip(ps, args))
    require(sameParameter(p, a->getValueAsDef("parameter")), owner,
            "parameter kind or sort mismatch");
}
void Model::validate() {
  uniqueNames(types, "type");
  uniqueNames(operations, "operation");
  uniqueNames(capabilities, "capability");
  uniqueNames(order.sort("ZKC_TypeHead"), "source type head");
  uniqueNames(sorts, "sort");
  for (const auto *sort : sorts)
    require(name(sort) != "Type" && name(sort) != "Nat", sort,
            "reserved static kind used as a domain sort");
  for (const auto *p : order.sort("ZKC_Parameter")) {
    auto [kind, sort] = parameter(p);
    require(kind == "Domain" || kind == "Type" || kind == "Nat", p,
            "unknown parameter kind");
    require(kind == "Domain"
                ? any_of(sorts, [sort = sort](
                                    const auto *s) { return name(s) == sort; })
                : sort.empty(),
            p, "invalid parameter sort");
  }
  for (const auto *t : types) {
    require(identifier(name(t)), t, "invalid constructor name");
    const auto ps = t->getValueAsListOfDefs("parameters");
    require(ps.size() <= 16, t, "type parameter limit");
    auto custody = name(t->getValueAsDef("custody"));
    require(custody == "PublicValue" || custody == "PrivateImmutable" ||
                custody == "Affine",
            t, "unknown custody");
    require(custody == "Affine"
                ? !t->getValueAsBit("copy")
                : t->getValueAsBit("copy") && t->getValueAsBit("drop"),
            t, "incoherent type permissions");
    require(!t->getValueAsBit("participants") || t->getValueAsBit("copy"), t,
            "participant families require Copy data");
    require(!t->getValueAsBit("message") || t->getValueAsBit("constructible"),
            t, "message frames require native decoder authority");
    require(!t->getValueAsBit("mathematical") ||
                (t->getValueAsBit("nativeLocal") && t->getValueAsBit("copy")),
            t, "mathematical native data requires reusable local data");
    const bool atomic = ps.empty() || (ps.size() == 1 &&
                                       parameter(ps.front()).first == "Domain");
    require(atomic || custody != "PublicValue", t,
            "applied types require an explicit complete-type codec model");
  }
  std::set<std::tuple<std::string, std::string, std::string>> memberKeys;
  for (const auto *m : members) {
    auto [kind, sort] = parameter(m->getValueAsDef("owner"));
    require(identifier(name(m)), m, "invalid associated member name");
    require(memberKeys.emplace(kind.str(), sort.str(), name(m).str()).second, m,
            "duplicate associated member ownership");
  }
  std::set<std::pair<std::string, std::string>> ruleKeys;
  for (const auto *r : rules) {
    auto *p = r->getValueAsDef("premise");
    auto *c = r->getValueAsDef("conclusion");
    auto ps = p->getValueAsListOfDefs("parameters");
    auto cs = c->getValueAsListOfDefs("parameters");
    require(ps.size() == 1 && cs.size() == 1 && sameParameter(ps[0], cs[0]), r,
            "capability implication parameter mismatch");
    require(ruleKeys.emplace(name(p).str(), name(c).str()).second, r,
            "duplicate capability implication");
  }
  for (const auto *op : operations)
    validateOperation(op);
  std::set<std::pair<const Record *, const Record *>> familyKeys;
  for (const auto *r : familyCases) {
    auto *family = r->getValueAsDef("family");
    auto *element = r->getValueAsDef("elementConstructor");
    auto *result = r->getValueAsDef("resultConstructor");
    require(familyKeys.emplace(family, element).second, r,
            "duplicate source family case");
    auto ep = element->getValueAsListOfDefs("parameters");
    auto rp = result->getValueAsListOfDefs("parameters");
    require(ep.size() == 1 && rp.size() == 1 && sameParameter(ep[0], rp[0]), r,
            "source family parameter mismatch");
  }
  for (const auto *f : families)
    require(!name(f).empty() && any_of(familyCases,
                                       [&](const auto *r) {
                                         return r->getValueAsDef("family") == f;
                                       }),
            f, "source family requires a case");
  std::set<std::pair<std::string, std::string>> associatedKeys;
  for (const auto *r : associatedTypes) {
    auto *owner = r->getValueAsDef("owner");
    auto [kind, sort] = parameter(owner);
    auto member = r->getValueAsString("member");
    auto *t = r->getValueAsDef("constructor");
    auto ps = t->getValueAsListOfDefs("parameters");
    require(kind == "Domain" && identifier(member) && ps.size() == 1 &&
                sameParameter(ps[0], owner),
            r, "associated source type parameter mismatch");
    require(associatedKeys.emplace(sort.str(), member.str()).second, r,
            "duplicate associated source type");
  }
  // All export kinds share a module namespace. Other modules may reuse names.
  std::set<std::pair<std::string, std::string>> exports;
  auto checkExport = [&](const Record *r) {
    auto module = r->getValueAsString("module");
    require(module.starts_with("zkc::") && path(module, "::") &&
                identifier(name(r)),
            r, "invalid source export name");
    require(exports.emplace(module.str(), name(r).str()).second, r,
            "duplicate source export ownership");
  };
  for (const auto *r : typeExports) {
    checkExport(r);
    auto *t = r->getValueAsDef("type");
    require(t->isSubClassOf("ZKC_TypeFamily") || t->isSubClassOf("ZKC_Type"), r,
            "source export requires an admitted type");
  }
  for (const auto *r : capabilityExports) {
    checkExport(r);
    auto ps =
        r->getValueAsDef("capability")->getValueAsListOfDefs("parameters");
    require(ps.size() == 1 && parameter(ps[0]).first == "Domain", r,
            "source capability requires a unary domain predicate");
  }
}
void Model::validateOperation(const Record *op) {
  require(path(name(op), "."), op, "invalid operation key");
  const auto stage = name(op->getValueAsDef("stage"));
  require(stage == "Source" || stage == "Construction" ||
              stage == "CompilerGenerated" || stage == "Physical",
          op, "unknown authoring stage");
  auto scope = op->getValueAsListOfDefs("scope");
  require(scope.size() <= 1024, op, "static scope limit");
  std::set<const Record *> available;
  std::set<std::string> roots;
  std::set<std::string> derived;
  for (const auto *term : scope) {
    auto *p = term->getValueAsDef("parameter");
    if (term->isSubClassOf("ZKC_Apply")) {
      require(!optionalDef(term, "parent") && !optionalDef(term, "member"), op,
              "ambiguous type application");
      auto args = term->getValueAsListOfDefs("arguments");
      for (const auto *arg : args)
        require(available.count(arg), op,
                "type application must follow its scoped arguments");
      auto *head = term->getValueAsDef("constructor");
      require(parameter(p).first == "Type" && name(term) == name(head), op,
              "invalid type application kind or head");
      validateParameters(op, head->getValueAsListOfDefs("parameters"), args);
      std::string key = "apply:" + name(head).str();
      for (const auto *arg : args)
        key += ":" + std::to_string(llvm::find(scope, arg) - scope.begin());
      require(derived.insert(key).second, op, "duplicate scoped application");
    } else if (term->isSubClassOf("ZKC_Natural")) {
      require(parameter(p).first == "Nat" && !optionalDef(term, "parent") &&
                  !optionalDef(term, "member"),
              op, "invalid natural static kind");
      require(term->getValueAsInt("number") >= 0 &&
                  term->getValueAsInt("number") <= 1048576,
              op, "natural static argument limit");
      require(derived.insert("natural:" + number(term, "number")).second, op,
              "duplicate scoped constant");
    } else if (const auto *parent = optionalDef(term, "parent")) {
      require(available.count(parent), op,
              "associated projection must follow its scoped parent");
      auto *member = optionalDef(term, "member");
      require(member &&
                  sameParameter(parent->getValueAsDef("parameter"),
                                member->getValueAsDef("owner")) &&
                  sameParameter(p, member->getValueAsDef("result")) &&
                  name(term) == name(member),
              op, "associated member parameter mismatch");
      require(derived
                  .insert("project:" +
                          std::to_string(llvm::find(scope, parent) -
                                         scope.begin()) +
                          ":" + name(term).str())
                  .second,
              op, "duplicate scoped projection");
    } else {
      require(term->isSubClassOf("ZKC_Root") && !optionalDef(term, "member") &&
                  identifier(name(term)) &&
                  roots.insert(name(term).str()).second,
              op, "invalid or duplicate formal root");
    }
    require(available.insert(term).second, op, "duplicate scoped term");
  }
  auto scoped = [&](ArrayRef<const Record *> args) {
    for (const auto *arg : args)
      require(available.count(arg), op, "unscoped typed reference");
  };
  for (auto field : {"inputs", "outputs", "requirements", "facets"})
    require(op->getValueAsListOfDefs(field).size() <= 1024, op,
            "operation declaration limit");
  if (auto *family = optionalDef(op, "numerical")) {
    auto *field = family->getValueAsDef("fieldTerm");
    const auto result = family->getValueAsString("result");
    auto [kind, sort] = parameter(field->getValueAsDef("parameter"));
    require(scope.size() == 1 && scope[0] == field &&
                field->isSubClassOf("ZKC_Root") && kind == "Domain" &&
                sort == "Field" && stage == "CompilerGenerated" &&
                name(op->getValueAsDef("parameters")) ==
                    "NumericalExpression" &&
                (result == "map" || result == "sum" || result == "product") &&
                op->getValueAsListOfDefs("inputs").empty() &&
                op->getValueAsListOfDefs("outputs").empty() &&
                op->getValueAsListOfDefs("facets").empty(),
            op, "invalid numerical signature family");
    auto needs = op->getValueAsListOfDefs("requirements");
    require(needs.size() == 1 &&
                name(needs[0]->getValueAsDef("capability")) == "Field" &&
                needs[0]->getValueAsListOfDefs("arguments") == Records{field},
            op, "numerical family requires its exact Field capability");
  } else {
    require(name(op->getValueAsDef("parameters")) != "NumericalExpression", op,
            "numerical expression requires an explicit signature family");
  }
  for (auto port : {"inputs", "outputs"}) {
    for (const auto *app : op->getValueAsListOfDefs(port)) {
      if (!app->isSubClassOf("ZKC_Apply")) {
        require(stage == "Construction" &&
                    (StringRef(port) == "inputs" ||
                     op->isSubClassOf("SequenceOperation")) &&
                    available.count(app) && app->isSubClassOf("ZKC_Root") &&
                    parameter(app->getValueAsDef("parameter")).first == "Type",
                op, "direct Type ports require a scoped construction type");
        continue;
      }
      auto args = app->getValueAsListOfDefs("arguments");
      scoped(args);
      auto *constructor = app->getValueAsDef("constructor");
      validateParameters(op, constructor->getValueAsListOfDefs("parameters"),
                         args);
    }
  }
  auto inputs = op->getValueAsListOfDefs("inputs");
  for (auto [i, input] : enumerate(inputs))
    if (!input->isSubClassOf("ZKC_Apply"))
      // Sequence kernels expose their declared element type directly. Other
      // complete-type input ports retain the observation-only restriction.
      require(op->isSubClassOf("SequenceOperation") ||
                  any_of(op->getValueAsListOfDefs("facets"),
                         [i = i](const Record *f) {
                           return f->isSubClassOf("ZKC_Observation") &&
                                  f->getValueAsInt("payloadInput") ==
                                      int64_t(i);
                         }),
              op, "complete-type port must be an observation payload");
  for (const auto *p : op->getValueAsListOfDefs("requirements")) {
    auto args = p->getValueAsListOfDefs("arguments");
    scoped(args);
    validateParameters(
        op, p->getValueAsDef("capability")->getValueAsListOfDefs("parameters"),
        args);
  }
  const auto *parameters = op->getValueAsDef("parameters");
  static const std::map<std::string, std::pair<int64_t, int64_t>> schemas = {
      {"None", {0, 0}},
      {"Natural", {1, 1}},
      {"Extent", {1, 1}},
      {"FieldLiteral", {1, 1}},
      {"FieldLiterals", {0, -1}},
      {"MatrixShape", {2, 2}},
      {"MatrixIdentity", {1, 1}},
      {"AssetIdentity", {1, 1}},
      {"MatrixVector", {3, 3}},
      {"GatherIndices", {0, -1}},
      {"ScatterIndices", {1, -1}},
      {"NumericalExpression", {1, 1}},
      {"NativeOrigin", {1, 1}}};
  auto found = schemas.find(name(parameters).str());
  require(found != schemas.end() &&
              found->second ==
                  std::make_pair(parameters->getValueAsInt("minimum"),
                                 parameters->getValueAsInt("maximum")),
          op, "unsupported parameter validator or bounds");
  const auto assetFormat = parameters->getValueAsString("assetFormat");
  require(name(parameters) == "AssetIdentity"
              ? (assetFormat == "zkc.ring/0" ||
                 assetFormat == "zkc.relation-bundle/0")
              : assetFormat.empty(),
          op, "asset parameter requires its mathematical carrier format");
  auto *field = optionalDef(op, "parameterField");
  const bool literals =
      name(parameters) == "FieldLiteral" || name(parameters) == "FieldLiterals";
  require(literals == bool(field), op,
          "field literal validator requires exactly one field term");
  if (field) {
    require(available.count(field), op, "unscoped parameter field");
    auto [kind, sort] = parameter(field->getValueAsDef("parameter"));
    require(kind == "Domain" && sort == "Field", op,
            "parameter field must have Field sort");
  }
  validateFacets(op);
}
std::string facetKind(const Record *r) {
  for (auto kind : {"History", "Observation", "Sampling", "Diagonal",
                    "Contraction", "Coset", "DomainValue", "Mathematical"})
    if (r->isSubClassOf((Twine("ZKC_") + kind).str()))
      return kind;
  return r->getName().str();
}
void Model::validateFacets(const Record *op) {
  auto inputs = op->getValueAsListOfDefs("inputs");
  auto outputs = op->getValueAsListOfDefs("outputs");
  auto port = [&](const Record *r, StringRef field, bool output,
                  StringRef constructor = "") -> const Record * {
    auto index = r->getValueAsInt(field);
    auto &ports = output ? outputs : inputs;
    require(index >= 0 && size_t(index) < ports.size(), op,
            "facet port outside signature");
    auto *app = ports[index];
    require(constructor.empty() ||
                (app->isSubClassOf("ZKC_Apply") &&
                 name(app->getValueAsDef("constructor")) == constructor),
            op, "facet port constructor mismatch");
    return app;
  };
  auto sameType = [](const Record *a, const Record *b) {
    if (!a->isSubClassOf("ZKC_Apply") || !b->isSubClassOf("ZKC_Apply"))
      return a == b;
    return a->getValueAsDef("constructor") == b->getValueAsDef("constructor") &&
           a->getValueAsListOfDefs("arguments") ==
               b->getValueAsListOfDefs("arguments");
  };
  std::set<std::string> kinds;
  const Record *sampling = nullptr, *history = nullptr, *observation = nullptr;
  for (const auto *r : op->getValueAsListOfDefs("facets")) {
    auto kind = facetKind(r);
    require(kinds.insert(kind).second, op, "duplicate semantic facet");
    if (kind == "Mathematical") {
      validateMathematicalFacet(op, r);
    } else if (kind == "History") {
      history = r;
      require(
          sameType(port(r, "stateInput", false), port(r, "stateOutput", true)),
          op, "history successor type mismatch");
    } else if (kind == "Observation") {
      observation = r;
      require(sameType(port(r, "stateInput", false, "transcript"),
                       port(r, "stateOutput", true, "transcript")),
              op, "observation successor type mismatch");
      port(r, "payloadInput", false);
      require(r->getValueAsInt("stateInput") !=
                  r->getValueAsInt("payloadInput"),
              op, "observation ports overlap");
    } else if (kind == "Sampling") {
      sampling = r;
      auto provider = name(r->getValueAsDef("provider"));
      auto domain = name(r->getValueAsDef("domain"));
      require(provider == "Entropy" || provider == "Transcript", op,
              "unknown sampling provider");
      require(domain == "Field" || domain == "FieldVector" ||
                  domain == "BoundedIndex",
              op, "unknown sample domain");
      auto state = provider == "Entropy" ? "rng" : "transcript";
      require(sameType(port(r, "stateInput", false, state),
                       port(r, "stateOutput", true, state)),
              op, "sampling successor type mismatch");
      port(r, "valueOutput", true,
           domain == "Field"         ? "field"
           : domain == "FieldVector" ? "vector"
                                     : "index");
      require(r->getValueAsInt("valueOutput") !=
                  r->getValueAsInt("stateOutput"),
              op, "sampling result ports overlap");
      auto bound = r->getValueAsInt("boundInput");
      require(domain == "BoundedIndex" ? bound >= 0 : bound == -1, op,
              "sampling bound domain mismatch");
      if (bound >= 0)
        port(r, "boundInput", false, "index");
    } else if (kind == "Diagonal" || kind == "Contraction") {
      StringRef factors =
          kind == "Diagonal" ? "factorsInput" : "coefficientsInput";
      port(r, factors, false, "vector");
      port(r, "valuesInput", false);
      require(r->getValueAsInt(factors) != r->getValueAsInt("valuesInput"), op,
              "linear facet input ports overlap");
      if (kind == "Diagonal")
        require(sameType(port(r, "valuesInput", false),
                         port(r, "resultOutput", true)),
                op, "diagonal result type mismatch");
      validateLinearFacet(op, r);
    } else if (kind == "Coset") {
      port(r, "shiftInput", false, "field");
      port(r, "sizeInput", false,
           r->getValueAsBit("sizeIsLength") ? "vector" : "index");
      require(r->getValueAsInt("vectorOutput") >= -1, op,
              "invalid optional facet port");
      if (r->getValueAsInt("vectorOutput") >= 0)
        port(r, "vectorOutput", true, "vector");
    } else if (kind == "DomainValue") {
      port(r, "output", true);
      auto rule = name(r->getValueAsDef("rule"));
      require(rule == "Constant" || rule == "Length" || rule == "Multiply" ||
                  rule == "Divide",
              op, "unknown domain value rule");
      if (rule == "Constant") {
        auto index = r->getValueAsInt("input");
        require(
            index >= 0 &&
                index <
                    op->getValueAsDef("parameters")->getValueAsInt("minimum"),
            op, "constant facet outside parameter signature");
      } else
        port(r, "input", false);
      if (rule == "Multiply" || rule == "Divide")
        port(r, "otherInput", false);
    } else {
      require(kind == "PublicReplay" || kind == "AcceptanceGuard" ||
                  kind == "Conjunction" || kind == "SourceHistory" ||
                  kind == "ManagedHistory",
              op, "unsupported semantic facet");
      if (kind == "AcceptanceGuard")
        require(inputs.size() == 1 && outputs.empty() &&
                    inputs[0]->isSubClassOf("ZKC_Apply") &&
                    name(inputs[0]->getValueAsDef("constructor")) == "bool",
                op, "acceptance guard signature mismatch");
      if (kind == "Conjunction")
        require(inputs.size() == 2 && outputs.size() == 1 &&
                    inputs[0]->isSubClassOf("ZKC_Apply") &&
                    name(inputs[0]->getValueAsDef("constructor")) == "bool" &&
                    sameType(inputs[0], inputs[1]) &&
                    sameType(inputs[0], outputs[0]),
                op, "conjunction signature mismatch");
    }
  }
  if (kinds.count("ManagedHistory")) {
    require(history && name(op->getValueAsDef("stage")) == "Source", op,
            "managed authoring requires an explicit source history transition");
    port(history, "stateInput", false, "transcript");
    port(history, "stateOutput", true, "transcript");
  }
  if (kinds.count("SourceHistory")) {
    require(history && !sampling && !observation &&
                name(op->getValueAsDef("stage")) == "Source",
            op, "source history requires an explicit data-state transition");
    auto *state = port(history, "stateInput", false);
    require(state->isSubClassOf("ZKC_Apply"), op,
            "source history requires a concrete state constructor");
    auto *type = state->getValueAsDef("constructor");
    require(type->getValueAsBit("copy") && type->getValueAsBit("drop") &&
                state->getValueAsListOfDefs("arguments").empty(),
            op, "source history state must be copyable and discardable data");
  }
  if (observation ||
      (sampling && name(sampling->getValueAsDef("provider")) == "Transcript")) {
    auto *facet = observation ? observation : sampling;
    require(history &&
                history->getValueAsInt("stateInput") ==
                    facet->getValueAsInt("stateInput") &&
                history->getValueAsInt("stateOutput") ==
                    facet->getValueAsInt("stateOutput"),
            op, "transcript facet requires matching history ports");
  }
  if (const auto *target = optionalDef(op, "derivedCounterpart")) {
    require(sampling && name(sampling->getValueAsDef("provider")) == "Entropy",
            op, "construction counterpart requires entropy sampling");
    const Record *derived = nullptr;
    for (const auto *r : target->getValueAsListOfDefs("facets"))
      if (r->isSubClassOf("ZKC_Sampling"))
        derived = r;
    require(derived &&
                name(derived->getValueAsDef("provider")) == "Transcript" &&
                name(target->getValueAsDef("stage")) == "Construction" &&
                name(derived->getValueAsDef("domain")) ==
                    name(sampling->getValueAsDef("domain")),
            op, "incompatible construction counterpart");
    for (auto field :
         {"stateInput", "stateOutput", "valueOutput", "boundInput"})
      require(derived->getValueAsInt(field) == sampling->getValueAsInt(field),
              op, "construction counterpart port mismatch");
    for (auto field : {"inputs", "outputs"}) {
      auto left = op->getValueAsListOfDefs(field);
      auto right = target->getValueAsListOfDefs(field);
      require(left.size() == right.size(), op,
              "construction counterpart arity mismatch");
      auto state = sampling->getValueAsInt(
          StringRef(field) == "inputs" ? "stateInput" : "stateOutput");
      for (auto [i, app] : enumerate(left))
        if (int64_t(i) != state)
          require(app->isSubClassOf("ZKC_Apply") &&
                      right[i]->isSubClassOf("ZKC_Apply") &&
                      app->getValueAsDef("constructor") ==
                          right[i]->getValueAsDef("constructor"),
                  op, "construction counterpart payload mismatch");
    }
  }
}
unsigned termIndex(ArrayRef<const Record *> scope, const Record *term) {
  return unsigned(llvm::find(scope, term) - scope.begin());
}
std::string arguments(ArrayRef<const Record *> scope, const Record *r) {
  std::vector<int64_t> values;
  for (const auto *arg : r->getValueAsListOfDefs("arguments"))
    values.push_back(termIndex(scope, arg));
  return indices(values);
}
std::string optionalPort(const Record *r, StringRef field) {
  return r->getValueAsInt(field) < 0 ? "std::nullopt" : number(r, field);
}
void emitFacets(raw_ostream &os, const Record *op) {
  os << "[] { OperationContracts c;\n";
  for (const auto *r : op->getValueAsListOfDefs("facets")) {
    auto kind = facetKind(r);
    if (kind == "Mathematical")
      emitMathematicalFacet(os, op, r);
    else if (kind == "PublicReplay")
      os << "c.publicReplay = true;\n";
    else if (kind == "AcceptanceGuard")
      os << "c.acceptanceGuard = true;\n";
    else if (kind == "Conjunction")
      os << "c.conjunction = true;\n";
    else if (kind == "SourceHistory")
      os << "c.sourceHistory = true;\n";
    else if (kind == "ManagedHistory")
      os << "c.managedHistory = true;\n";
    else if (kind == "History")
      os << "c.history = HistoryContract{" << number(r, "stateInput") << ", "
         << number(r, "stateOutput") << "};\n";
    else if (kind == "Observation")
      os << "c.observation = ObservationContract{" << number(r, "stateInput")
         << ", " << number(r, "payloadInput") << ", "
         << number(r, "stateOutput") << "};\n";
    else if (kind == "Sampling") {
      os << "c.sampling = SamplingContract{RandomnessProvider::"
         << name(r->getValueAsDef("provider"))
         << ", SampleDomain::" << name(r->getValueAsDef("domain")) << ", "
         << number(r, "stateInput") << ", " << number(r, "valueOutput") << ", "
         << number(r, "stateOutput") << ", " << optionalPort(r, "boundInput")
         << ", ";
      auto *target = optionalDef(op, "derivedCounterpart");
      os << quote(target ? name(target) : "") << "};\n";
    } else if (kind == "Diagonal")
      os << "c.diagonalMap = DiagonalMapContract{" << number(r, "factorsInput")
         << ", " << number(r, "valuesInput") << ", "
         << number(r, "resultOutput") << "};\n";
    else if (kind == "Contraction")
      os << "c.linearContraction = LinearContractionContract{"
         << number(r, "coefficientsInput") << ", " << number(r, "valuesInput")
         << "};\n";
    else if (kind == "Coset")
      os << "c.coset = CosetContract{" << number(r, "shiftInput") << ", "
         << number(r, "sizeInput") << ", "
         << boolean(r->getValueAsBit("sizeIsLength")) << ", "
         << optionalPort(r, "vectorOutput") << ", "
         << boolean(r->getValueAsBit("foldedOutput")) << "};\n";
    else if (kind == "DomainValue")
      os << "c.domainValue = DomainValueContract{DomainValueRule::"
         << name(r->getValueAsDef("rule")) << ", " << number(r, "output")
         << ", " << number(r, "input") << ", " << number(r, "otherInput")
         << "};\n";
  }
  os << "return c; }()";
}
void emitDescriptors(raw_ostream &os, const Model &m) {
  os << "// Generated from neutral contract declarations. Do not edit.\n";
  os << "llvm::ArrayRef<std::string> domainSorts() {\n"
        "static const std::vector<std::string> values = "
     << names(m.sorts) << "; return values; }\n";
  auto emitParameter = [&](const Record *p) {
    auto [kind, sort] = parameter(p);
    os << "{StaticKind::" << kind << ", " << quote(sort) << "}";
  };
  os << "llvm::ArrayRef<CapabilityDeclaration> capabilityDeclarations() {\n"
        "static const std::vector<CapabilityDeclaration> values = {\n";
  for (const auto *capability : m.capabilities) {
    os << "{" << quote(name(capability)) << ", {";
    for (const auto *p : capability->getValueAsListOfDefs("parameters")) {
      emitParameter(p);
      os << ",";
    }
    os << "}},\n";
  }
  os << "}; return values; }\n";
  os << "llvm::ArrayRef<TypeDeclaration> typeDeclarations() {\n"
        "static const std::vector<TypeDeclaration> values = {\n";
  for (const auto *type : m.types) {
    os << "{" << quote(name(type)) << ", {";
    for (const auto *p : type->getValueAsListOfDefs("parameters")) {
      emitParameter(p);
      os << ",";
    }
    os << "}";
    for (auto fact : {"nativeLocal", "mathematical", "participants",
                      "constructible", "message"})
      os << ", " << boolean(type->getValueAsBit(fact));
    os << "},\n";
  }
  os << "}; return values; }\n"
        "const TypeDeclaration *typeDeclaration(llvm::StringRef name) {\n"
        "for (const auto &t : typeDeclarations()) if (t.name == name) return "
        "&t;\n"
        "return nullptr; }\n";
  os << "llvm::ArrayRef<AssociatedMemberDeclaration> "
        "associatedMemberDeclarations() {\n"
        "static const std::vector<AssociatedMemberDeclaration> values = {\n";
  for (const auto *member : m.members) {
    os << "{" << quote(name(member)) << ", ";
    emitParameter(member->getValueAsDef("owner"));
    os << ", ";
    emitParameter(member->getValueAsDef("result"));
    os << "},\n";
  }
  os << "}; return values; }\n";
  os << "llvm::ArrayRef<generic::TypeConstructor> boundTypeConstructors() {\n"
        "static const std::vector<generic::TypeConstructor> values = {\n";
  for (const auto *t : m.types) {
    std::vector<StringRef> sorts;
    for (const auto *p : t->getValueAsListOfDefs("parameters")) {
      auto [kind, sort] = parameter(p);
      sorts.push_back(kind == "Domain" ? sort : kind);
    }
    os << "{" << quote(name(t)) << ", " << strings(sorts) << ", "
       << boolean(!t->getValueAsBit("copy")) << "},\n";
  }
  os << "}; return values; }\n";
  os << "const TypePermissions *typePermissions(llvm::StringRef constructor) "
        "{\n"
        "static const std::pair<llvm::StringRef, TypePermissions> values[] = "
        "{\n";
  for (const auto *t : m.types)
    os << "{" << quote(name(t)) << ", {" << boolean(t->getValueAsBit("copy"))
       << ", " << boolean(t->getValueAsBit("drop"))
       << ", Custody::" << name(t->getValueAsDef("custody")) << "}},\n";
  os << "}; for (const auto &v : values) if (v.first == constructor) return "
        "&v.second; return nullptr; }\n";
  os << "llvm::ArrayRef<requirements::Implication> boundCapabilityRules() {\n"
        "static const std::vector<requirements::Implication> values = {\n";
  for (const auto *r : m.rules)
    os << "{" << quote(name(r->getValueAsDef("premise"))) << ", "
       << quote(name(r->getValueAsDef("conclusion"))) << "},\n";
  os << "}; return values; }\n";
  os << "llvm::StringRef associatedMemberSort(llvm::StringRef sort, "
        "llvm::StringRef member) {\n";
  for (const auto *r : m.members) {
    auto owner = parameter(r->getValueAsDef("owner"));
    auto result = parameter(r->getValueAsDef("result"));
    if (owner.first == "Domain" && result.first == "Domain")
      os << "if (sort == " << quote(owner.second)
         << " && member == " << quote(name(r)) << ") return "
         << quote(result.second) << ";\n";
  }
  os << "return {}; }\n";
  os << "llvm::ArrayRef<generic::Operation> executableOperationContracts() {\n"
        "static const std::vector<generic::Operation> values = {\n";
  for (const auto *op : m.operations) {
    auto scope = op->getValueAsListOfDefs("scope");
    os << "{" << quote(name(op)) << ", {{{";
    for (const auto *t : scope) {
      os << "{" << quote(name(t)) << ", ";
      auto *parent = optionalDef(t, "parent");
      os << (parent ? std::to_string(termIndex(scope, parent)) : "std::nullopt")
         << ", ";
      if (t->isSubClassOf("ZKC_Apply"))
        os << "std::vector<unsigned>" << arguments(scope, t);
      else
        os << "std::nullopt";
      os << "},";
    }
    std::vector<StringRef> sorts;
    for (const auto *t : scope) {
      auto [kind, sort] = parameter(t->getValueAsDef("parameter"));
      sorts.push_back(kind == "Domain" ? sort : kind);
    }
    os << "}, " << strings(sorts) << ", {";
    for (auto [i, t] : enumerate(scope))
      if (t->isSubClassOf("ZKC_Natural"))
        os << "{" << i << ", " << quote(number(t, "number")) << "},";
    os << "}}, ";
    for (auto field : {"inputs", "outputs"}) {
      os << "{";
      for (const auto *app : op->getValueAsListOfDefs(field)) {
        if (app->isSubClassOf("ZKC_Apply"))
          os << "{" << quote(name(app->getValueAsDef("constructor"))) << ", "
             << arguments(scope, app) << "},";
        else
          os << "{\"\", {}, " << termIndex(scope, app) << "},";
      }
      os << "}, ";
    }
    os << "{";
    for (const auto *r : op->getValueAsListOfDefs("requirements"))
      os << "requirements::Predicate::holds("
         << quote(name(r->getValueAsDef("capability"))) << ", "
         << arguments(scope, r) << "),";
    os << "}}, ";
    if (auto *family = optionalDef(op, "numerical")) {
      auto result = family->getValueAsString("result");
      os << "generic::NumericalSignature{"
         << termIndex(scope, family->getValueAsDef("fieldTerm"))
         << ", generic::NumericalSignature::Result::"
         << (result == "map"   ? "Map"
             : result == "sum" ? "Sum"
                               : "Product")
         << "}";
    } else
      os << "std::nullopt";
    os << "},\n";
  }
  os << "}; return values; }\n";
  os << "llvm::ArrayRef<OperationShape> operationShapes() {\nstatic const "
        "std::vector<OperationShape> "
        "values = {\n";
  for (const auto *op : m.operations) {
    os << "{" << quote(name(op)) << ", ";
    for (auto field : {"inputs", "outputs"}) {
      std::vector<StringRef> heads;
      for (const auto *a : op->getValueAsListOfDefs(field))
        heads.push_back(a->isSubClassOf("ZKC_Apply")
                            ? name(a->getValueAsDef("constructor"))
                            : "data");
      os << strings(heads) << ", ";
    }
    emitFacets(os, op);
    os << "},\n";
  }
  os << "}; return values; }\n";
  os << "namespace {\nstruct OperationDeclaration { llvm::StringRef name; "
        "AuthoringStage stage; ParameterContract parameters; };\n"
        "const OperationDeclaration *declaration(llvm::StringRef name) {\n"
        "static const OperationDeclaration values[] = {\n";
  for (const auto *op : m.operations) {
    const auto *p = op->getValueAsDef("parameters");
    os << "{" << quote(name(op))
       << ", AuthoringStage::" << name(op->getValueAsDef("stage"))
       << ", {ParameterValidator::" << name(p) << ", " << number(p, "minimum")
       << ", " << optionalPort(p, "maximum") << ", ";
    const auto *field = optionalDef(op, "parameterField");
    os << (field ? std::to_string(
                       termIndex(op->getValueAsListOfDefs("scope"), field))
                 : "std::nullopt")
       << ", " << quote(p->getValueAsString("assetFormat")) << "}},\n";
  }
  os << "}; for (const auto &v : values) if (v.name == name) return &v; return "
        "nullptr; }\n}\n"
        "AuthoringStage authoringStage(llvm::StringRef key) { auto *d = "
        "declaration(key); return d ? d->stage : "
        "AuthoringStage::CompilerGenerated; }\n"
        "const ParameterContract *parameterContract(llvm::StringRef key) { "
        "auto *d = declaration(key); return d ? &d->parameters : nullptr; }\n";
  os << "llvm::ArrayRef<SourceTypeExport> sourceTypeExports() {\nstatic const "
        "std::vector<SourceTypeExport> values = {\n";
  for (const auto *r : m.typeExports)
    os << "{" << quote(r->getValueAsString("module")) << ", " << quote(name(r))
       << ", " << quote(name(r->getValueAsDef("type"))) << "},\n";
  os << "}; return values; }\n";
  os << "llvm::ArrayRef<SourceTypeFamilyCase> sourceTypeFamilies() {\n"
        "static const std::vector<SourceTypeFamilyCase> values = {\n";
  for (const auto *r : m.familyCases)
    os << "{" << quote(name(r->getValueAsDef("family"))) << ", "
       << quote(name(r->getValueAsDef("elementConstructor"))) << ", "
       << quote(name(r->getValueAsDef("resultConstructor"))) << "},\n";
  os << "}; return values; }\n";
  os << "llvm::ArrayRef<SourceAssociatedType> sourceAssociatedTypes() {\n"
        "static const std::vector<SourceAssociatedType> values = {\n";
  for (const auto *r : m.associatedTypes)
    os << "{" << quote(parameter(r->getValueAsDef("owner")).second) << ", "
       << quote(r->getValueAsString("member")) << ", "
       << quote(name(r->getValueAsDef("constructor"))) << "},\n";
  os << "}; return values; }\n";
  os << "llvm::ArrayRef<SourceCapabilityExport> sourceCapabilityExports() {\n"
        "static const std::vector<SourceCapabilityExport> values = {\n";
  for (const auto *r : m.capabilityExports)
    os << "{" << quote(r->getValueAsString("module")) << ", " << quote(name(r))
       << ", " << quote(name(r->getValueAsDef("capability"))) << "},\n";
  os << "}; return values; }\n";
}
// An inert inspection view. It exposes declaration structure, never executable
// callbacks or an admission claim. Native/formal interpretation stays separate.
json::Object parameterJSON(const Record *p) {
  auto [kind, sort] = parameter(p);
  return json::Object{{"kind", kind}, {"sort", sort}};
}
json::Array parametersJSON(const Record *r) {
  json::Array result;
  for (const auto *p : r->getValueAsListOfDefs("parameters"))
    result.push_back(parameterJSON(p));
  return result;
}
json::Object scopeTermJSON(const Record *term, ArrayRef<const Record *> scope) {
  if (term->isSubClassOf("ZKC_Apply")) {
    json::Array args;
    for (const auto *argument : term->getValueAsListOfDefs("arguments"))
      args.push_back(termIndex(scope, argument));
    return json::Object{
        {"kind", "apply"},
        {"constructor", name(term->getValueAsDef("constructor"))},
        {"arguments", std::move(args)}};
  }
  if (term->isSubClassOf("ZKC_Natural"))
    return json::Object{{"kind", "natural"}, {"value", number(term, "number")}};
  if (auto *parent = optionalDef(term, "parent"))
    return json::Object{{"kind", "project"},
                        {"member", name(term->getValueAsDef("member"))},
                        {"parent", termIndex(scope, parent)}};
  return json::Object{
      {"kind", "root"},
      {"name", name(term)},
      {"parameter", parameterJSON(term->getValueAsDef("parameter"))}};
}
json::Array applicationsJSON(const Record *op, StringRef field) {
  auto scope = op->getValueAsListOfDefs("scope");
  json::Array result;
  for (const auto *app : op->getValueAsListOfDefs(field)) {
    if (field != "requirements" && !app->isSubClassOf("ZKC_Apply")) {
      result.push_back(json::Object{{"term", termIndex(scope, app)}});
      continue;
    }
    json::Array args;
    for (const auto *term : app->getValueAsListOfDefs("arguments"))
      args.push_back(termIndex(scope, term));
    auto key = field == "requirements" ? "capability" : "constructor";
    result.push_back(json::Object{{key, name(app->getValueAsDef(key))},
                                  {"arguments", std::move(args)}});
  }
  return result;
}
json::Object facetJSON(const Record *facet) {
  const auto kind = facetKind(facet);
  json::Object result{{"kind", kind}};
  auto integer = [&](StringRef field) {
    result[field] = facet->getValueAsInt(field);
  };
  auto optionalPort = [&](StringRef field) {
    auto value = facet->getValueAsInt(field);
    result[field] = value < 0 ? json::Value(nullptr) : json::Value(value);
  };
  if (kind == "Mathematical")
    result["identity"] = name(facet->getValueAsDef("identity"));
  else if (kind == "History" || kind == "Observation" || kind == "Sampling") {
    integer("stateInput");
    integer("stateOutput");
    if (kind == "Observation")
      integer("payloadInput");
    if (kind == "Sampling") {
      result["provider"] = name(facet->getValueAsDef("provider"));
      result["domain"] = name(facet->getValueAsDef("domain"));
      integer("valueOutput");
      optionalPort("boundInput");
    }
  } else if (kind == "Diagonal" || kind == "Contraction") {
    integer(kind == "Diagonal" ? "factorsInput" : "coefficientsInput");
    integer("valuesInput");
    if (kind == "Diagonal")
      integer("resultOutput");
  } else if (kind == "Coset") {
    integer("shiftInput");
    integer("sizeInput");
    result["sizeIsLength"] = facet->getValueAsBit("sizeIsLength");
    result["foldedOutput"] = facet->getValueAsBit("foldedOutput");
    optionalPort("vectorOutput");
  } else if (kind == "DomainValue") {
    const auto rule = name(facet->getValueAsDef("rule"));
    result["rule"] = rule;
    integer("output");
    if (rule == "Constant")
      result["parameter"] = facet->getValueAsInt("input");
    else
      integer("input");
    if (rule == "Multiply" || rule == "Divide")
      integer("otherInput");
  }
  return result;
}
json::Object inventory(const Model &m) {
  json::Object result{{"format", "zkc.contract-declarations/0"}};
  json::Array sorts;
  for (const auto *sort : m.sorts)
    sorts.push_back(name(sort));
  result["sorts"] = std::move(sorts);
  json::Array types, ops, members, rules, capabilities, exports, families,
      associatedTypes, meanings, intrinsics;
  for (const auto *t : m.types)
    types.push_back(
        json::Object{{"name", name(t)},
                     {"parameters", parametersJSON(t)},
                     {"copy", t->getValueAsBit("copy")},
                     {"drop", t->getValueAsBit("drop")},
                     {"custody", name(t->getValueAsDef("custody"))},
                     {"nativeLocal", t->getValueAsBit("nativeLocal")},
                     {"mathematical", t->getValueAsBit("mathematical")},
                     {"participants", t->getValueAsBit("participants")},
                     {"constructible", t->getValueAsBit("constructible")},
                     {"message", t->getValueAsBit("message")}});
  for (const auto *c : m.capabilities)
    capabilities.push_back(
        json::Object{{"name", name(c)}, {"parameters", parametersJSON(c)}});
  for (const auto *member : m.members)
    members.push_back(json::Object{
        {"name", name(member)},
        {"owner", parameterJSON(member->getValueAsDef("owner"))},
        {"result", parameterJSON(member->getValueAsDef("result"))}});
  for (const auto *r : m.rules)
    rules.push_back(json::Array{name(r->getValueAsDef("premise")),
                                name(r->getValueAsDef("conclusion"))});
  for (const auto *op : m.operations) {
    auto scope = op->getValueAsListOfDefs("scope");
    json::Array terms, facets;
    for (const auto *term : scope)
      terms.push_back(scopeTermJSON(term, scope));
    const auto *p = op->getValueAsDef("parameters");
    const auto maximum = p->getValueAsInt("maximum");
    json::Object object{
        {"name", name(op)},
        {"scope", std::move(terms)},
        {"stage", name(op->getValueAsDef("stage"))},
        {"parameters",
         json::Object{{"validator", name(p)},
                      {"minimum", p->getValueAsInt("minimum")},
                      {"maximum", maximum < 0 ? json::Value(nullptr)
                                              : json::Value(maximum)}}},
        {"requirements", applicationsJSON(op, "requirements")}};
    if (auto *field = optionalDef(op, "parameterField"))
      object["parameters"].getAsObject()->try_emplace("fieldTerm",
                                                      termIndex(scope, field));
    if (!p->getValueAsString("assetFormat").empty())
      object["parameters"].getAsObject()->try_emplace(
          "assetFormat", p->getValueAsString("assetFormat"));
    if (auto *family = optionalDef(op, "numerical"))
      object["signature"] = json::Object{
          {"kind", "numerical"},
          {"fieldTerm", termIndex(scope, family->getValueAsDef("fieldTerm"))},
          {"result", family->getValueAsString("result")}};
    else
      object["signature"] =
          json::Object{{"kind", "fixed"},
                       {"inputs", applicationsJSON(op, "inputs")},
                       {"outputs", applicationsJSON(op, "outputs")}};
    for (const auto *facet : op->getValueAsListOfDefs("facets"))
      facets.push_back(facetJSON(facet));
    object["facets"] = std::move(facets);
    if (auto *counterpart = optionalDef(op, "derivedCounterpart"))
      object["derivedCounterpart"] = name(counterpart);
    ops.push_back(std::move(object));
  }
  for (const auto *r : m.typeExports)
    exports.push_back(
        json::Object{{"module", r->getValueAsString("module")},
                     {"name", name(r)},
                     {"constructor", name(r->getValueAsDef("type"))}});
  for (const auto *r : m.familyCases)
    families.push_back(json::Object{
        {"family", name(r->getValueAsDef("family"))},
        {"elementConstructor", name(r->getValueAsDef("elementConstructor"))},
        {"resultConstructor", name(r->getValueAsDef("resultConstructor"))}});
  for (const auto *r : m.associatedTypes)
    associatedTypes.push_back(
        json::Object{{"sort", parameter(r->getValueAsDef("owner")).second},
                     {"member", r->getValueAsString("member")},
                     {"constructor", name(r->getValueAsDef("constructor"))}});
  for (const auto *r : m.capabilityExports)
    exports.push_back(
        json::Object{{"module", r->getValueAsString("module")},
                     {"name", name(r)},
                     {"predicate", name(r->getValueAsDef("capability"))}});
  for (const auto *identity : m.order.sort("ZKC_MathematicalIdentity")) {
    json::Value laws = nullptr;
    if (const auto *l = optionalDef(identity, "laws")) {
      json::Object fields;
      for (auto key : {"algebra", "signature", "leftIdentity", "rightIdentity",
                       "annihilator", "access"})
        fields[key] = l->getValueAsString(key);
      for (auto key : {"associative", "commutative", "total", "scalarAction"})
        fields[key] = l->getValueAsBit(key);
      laws = std::move(fields);
    }
    meanings.push_back(
        json::Object{{"name", name(identity)}, {"laws", std::move(laws)}});
  }
  for (const auto *intrinsic : m.order.sort("ZKC_MathematicalIntrinsic"))
    intrinsics.push_back(
        json::Object{{"name", name(intrinsic)},
                     {"identity", name(intrinsic->getValueAsDef("identity"))},
                     {"domainKind", intrinsic->getValueAsString("domainKind")},
                     {"naturals", intrinsic->getValueAsInt("naturals")},
                     {"domainPoints", intrinsic->getValueAsBit("domainPoints")},
                     {"scalar", intrinsic->getValueAsBit("scalar")}});
  result["types"] = std::move(types);
  result["operations"] = std::move(ops);
  result["members"] = std::move(members);
  result["rules"] = std::move(rules);
  result["capabilities"] = std::move(capabilities);
  result["exports"] = std::move(exports);
  result["families"] = std::move(families);
  result["associatedTypes"] = std::move(associatedTypes);
  result["mathematicalIdentities"] = std::move(meanings);
  result["mathematicalIntrinsics"] = std::move(intrinsics);
  return result;
}
} // namespace
void validateContractDeclarations(const RecordKeeper &records) {
  Model validated(records);
}
bool emitContractDeclarations(raw_ostream &os, const RecordKeeper &records) {
  emitDescriptors(os, Model(records));
  return false;
}
bool emitContractInventory(raw_ostream &os, const RecordKeeper &records) {
  os << formatv("{0:2}\n", json::Value(inventory(Model(records))));
  return false;
}
