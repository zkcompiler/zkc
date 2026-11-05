#include "Declarations.h"
#include "Contributions.h"
#include "Instances.h"
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
void exactFields(const Record *r, ArrayRef<StringRef> fields,
                 bool ordered = true) {
  for (const auto &value : r->getValues())
    require((ordered && value.getName() == "ordinal") ||
                is_contained(fields, value.getName()),
            r, "unknown field " + value.getName());
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
// Installation-only bounded pattern graphs. These checks precede projection.
Records boundedDefs(const Record *r, StringRef field, unsigned limit) {
  require(r->getValueAsListInit(field)->size() <= limit, r,
          "scheme pattern limit");
  return r->getValueAsListOfDefs(field);
}
std::string checkedPattern(const Record *r, ArrayRef<StringRef> variables,
                           ArrayRef<const Record *> statics,
                           std::set<const Record *> &active, unsigned &nodes,
                           unsigned depth = 0) {
  require(depth <= 32 && ++nodes <= 1024, r, "scheme pattern limit");
  require(active.insert(r).second, r, "cyclic scheme pattern");
  exactFields(r, {"kind", "variable", "elements", "extent", "extentVariable"},
              false);
  auto tag = r->getValueAsString("kind");
  auto variable = r->getValueAsInt("variable");
  auto children = boundedDefs(r, "elements", 1024 - nodes);
  auto extent = r->getValueAsString("extent");
  auto position = r->getValueAsInt("extentVariable");
  auto scoped = [&](int64_t index, StringRef sort) {
    return index >= 0 && uint64_t(index) < variables.size() &&
           variables[index] == sort;
  };
  std::string result;
  if (tag == "contract") {
    require(scoped(variable, "Contract") && children.empty() &&
                extent.empty() && position == -1,
            r, "invalid contract variable pattern");
    result = "c" + std::to_string(variable);
  } else {
    require(variable == -1 && children.size() <= 1024 - nodes, r,
            "invalid structural pattern");
    if (tag == "product") {
      require(extent.empty() && position == -1, r, "invalid product pattern");
      result = "p(";
      for (const auto *child : children)
        result += checkedPattern(child, variables, statics, active, nodes,
                                 depth + 1) +
                  ",";
      result += ")";
    } else {
      require(tag == "sequence" && children.size() == 1, r,
              "invalid sequence pattern");
      std::string e;
      if (extent == "unsized") {
        require(position == -1, r, "invalid unsized extent pattern");
        e = "u";
      } else if (extent == "extent") {
        require(scoped(position, "OptionalExtent"), r,
                "invalid extent variable pattern");
        e = "e" + std::to_string(position);
      } else {
        require(extent == "static" && position >= 0 &&
                    uint64_t(position) < statics.size() &&
                    parameter(statics[position]) ==
                        std::make_pair(StringRef("Nat"), StringRef("")),
                r, "invalid static extent pattern");
        e = "n" + std::to_string(position);
      }
      result = "s(" +
               checkedPattern(children.front(), variables, statics, active,
                              nodes, depth + 1) +
               "," + e + ")";
    }
  }
  active.erase(r);
  return result;
}
std::string checkedPattern(const Record *r, ArrayRef<StringRef> variables,
                           ArrayRef<const Record *> statics) {
  std::set<const Record *> active;
  unsigned nodes = 0;
  return checkedPattern(r, variables, statics, active, nodes);
}
std::string checkedSchemePort(const Record *r, ArrayRef<StringRef> variables,
                              ArrayRef<const Record *> statics, bool named) {
  exactFields(r, {"kind", "patterns", "name"}, false);
  require(named ? identifier(name(r)) : name(r).empty(), r,
          "invalid scheme port name");
  auto tag = r->getValueAsString("kind");
  auto patterns = boundedDefs(r, "patterns", 2);
  require((tag == "descriptor" && patterns.size() == 1) ||
              (tag == "selectedView" && patterns.size() == 2),
          r, "invalid scheme port");
  std::string result = tag == "descriptor" ? "d(" : "v(";
  for (auto [i, p] : enumerate(patterns)) {
    if (i)
      result += ",";
    result += checkedPattern(p, variables, statics);
  }
  return result + ")";
}
struct SchemeShape {
  std::vector<StringRef> variables;
  unsigned statics;
  std::vector<std::string> inputs;
  std::string output;
};
SchemeShape schemeShape(StringRef form, const Record *r) {
  if (form == "Append")
    return {{"Contract"}, 0, {"d(s(c0,u))", "d(c0)"}, "s(c0,u)"};
  if (form == "Concat")
    return {{"Contract"}, 0, {"d(s(c0,u))", "d(s(c0,u))"}, "s(c0,u)"};
  if (form == "Replace")
    return {{"Contract", "OptionalExtent"},
            1,
            {"d(s(c0,e1))", "d(c0)"},
            "s(c0,e1)"};
  if (form == "ForgetExtent")
    return {{"Contract", "OptionalExtent"}, 0, {"d(s(c0,e1))"}, "s(c0,u)"};
  if (form == "CheckExtent")
    return {{"Contract"}, 1, {"d(s(c0,u))"}, "s(c0,n0)"};
  require(form == "Fold", r, "unknown descriptor scheme form");
  return {{"Contract", "Contract"}, 1, {"v(c0,c1)", "d(c0)", "d(c1)"}, "c1"};
}
json::Object patternJSON(const Record *r) {
  auto tag = r->getValueAsString("kind");
  json::Object result{{"kind", tag}};
  if (tag == "contract")
    result["variable"] = r->getValueAsInt("variable");
  else if (tag == "product") {
    json::Array elements;
    for (const auto *c : r->getValueAsListOfDefs("elements"))
      elements.push_back(patternJSON(c));
    result["elements"] = std::move(elements);
  } else {
    result["element"] =
        patternJSON(r->getValueAsListOfDefs("elements").front());
    auto tag = r->getValueAsString("extent");
    json::Object extent{{"kind", tag}};
    if (tag != "unsized")
      extent[tag == "extent" ? "variable" : "index"] =
          r->getValueAsInt("extentVariable");
    result["extent"] = std::move(extent);
  }
  return result;
}
json::Object schemePortJSON(const Record *r, bool named = false) {
  auto tag = r->getValueAsString("kind");
  json::Object result{{"kind", tag}};
  if (named)
    result["name"] = name(r);
  auto patterns = r->getValueAsListOfDefs("patterns");
  if (tag == "descriptor")
    result["contract"] = patternJSON(patterns.front());
  else {
    result["context"] = patternJSON(patterns[0]);
    result["state"] = patternJSON(patterns[1]);
  }
  return result;
}
std::string patternCpp(const Record *r) {
  auto tag = r->getValueAsString("kind");
  std::string value;
  if (tag == "contract")
    value = "ContractVariable{" + number(r, "variable") + "u}";
  else if (tag == "product") {
    value = "ProductPattern{{";
    for (const auto *c : r->getValueAsListOfDefs("elements"))
      value += patternCpp(c) + ",";
    value += "}}";
  } else {
    auto e = r->getValueAsString("extent");
    auto extent = e == "unsized"
                      ? "UnsizedExtent{}"
                      : (e == "extent" ? "ExtentVariable{" : "NatStatic{") +
                            number(r, "extentVariable") + "u}";
    value = "SequencePattern{" +
            patternCpp(r->getValueAsListOfDefs("elements").front()) + "," +
            extent + "}";
  }
  return "std::make_shared<const ContractPattern>(ContractPattern{" + value +
         "})";
}
std::string schemePortCpp(const Record *r) {
  auto patterns = r->getValueAsListOfDefs("patterns");
  if (r->getValueAsString("kind") == "descriptor")
    return "DescriptorPort{" + patternCpp(patterns.front()) + "}";
  return "SelectedViewPort{" + patternCpp(patterns[0]) + "," +
         patternCpp(patterns[1]) + "}";
}

struct Model {
  DeclarationOrder order;
  Records sorts, types, operations, members, capabilities, rules, typeExports,
      families, familyCases, associatedTypes, capabilityExports,
      consumerProfiles, frontendRules, frontendSchemes, frontendDeclarations,
      frontendNotations, frontendConstructors, frontendHomes, serviceSignatures,
      serviceMethods;
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
        capabilityExports(order.sort("ZKC_CapabilityExport")),
        consumerProfiles(order.sort("ZKC_ConsumerProfile")),
        frontendRules(order.sort("ZKC_FrontendRule")),
        frontendSchemes(order.sort("ZKC_FrontendScheme")),
        frontendDeclarations(order.sort("ZKC_FrontendDeclaration")),
        frontendNotations(order.sort("ZKC_FrontendNotation")),
        frontendConstructors(order.sort("ZKC_FrontendConstructor")),
        frontendHomes(order.sort("ZKC_FrontendHome")),
        serviceSignatures(order.sort("ZKC_ServiceSignature")),
        serviceMethods(order.sort("ZKC_ServiceMethod")) {
    if (records.getAllDerivedDefinitions("ZKC_Declaration").size() > 100000)
      PrintFatalError("declaration record limit");
    validateMathematicalDeclarations(records);
    validate();
    validateConsumerProfiles();
    validateInstalledInstances(records);
  }
  void validate();
  void validateOperation(const Record *op, bool consumer = false);
  void validateFacets(const Record *op);
  void validateConsumerProfiles();
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
    if (const auto *collection = optionalDef(t, "collection")) {
      const auto rank = collection->getValueAsInt("rank");
      const auto element = collection->getValueAsString("element");
      require(rank == 1 || rank == 2, t, "collection rank is 1 or 2");
      require(element == "parameter" || element == "index" || element == "byte",
              t, "unknown collection element");
      // The element is the first parameter's value type: a Field or Group
      // domain's element, or the Type argument itself.
      if (element == "parameter")
        require(!ps.empty() &&
                    (parameter(ps[0]) == std::make_pair(StringRef("Domain"),
                                                        StringRef("Field")) ||
                     parameter(ps[0]) == std::make_pair(StringRef("Domain"),
                                                        StringRef("Group")) ||
                     parameter(ps[0]).first == "Type"),
                t,
                "parameter collection element requires a Field, Group or Type "
                "first parameter");
    }
    if (!t->isValueUnset("setup"))
      require(t->getValueAsString("setup") == "prover" ||
                  t->getValueAsString("setup") == "verifier",
              t, "unknown setup key");
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
  // Installed source declarations. Rule shapes, service capabilities and
  // declaration references are data: no rule or method name is fixed here.
  using Term = std::tuple<int, std::string, std::string>;
  using Shape =
      std::tuple<std::string, std::vector<std::pair<std::string, std::string>>,
                 std::vector<Term>, std::optional<Term>>;
  auto sourceShape = [&](const Record *r, StringRef kind,
                         ArrayRef<const Record *> statics,
                         ArrayRef<const Record *> inputs,
                         ArrayRef<const Record *> output) {
    require(kind == "Math" || kind == "Local" || kind == "Interface" ||
                kind == "Requirement",
            r, "unknown source declaration kind");
    auto term = [&](const Record *t) -> Term {
      auto index = t->getValueAsInt("index");
      auto member = t->getValueAsString("member");
      auto head = t->getValueAsString("constructor");
      if (index < 0) {
        require(
            index == -1 && member.empty() &&
                any_of(
                    types,
                    [&](const auto *type) {
                      return name(type) == head &&
                             type->getValueAsListOfDefs("parameters").empty();
                    }),
            r, "unknown source constructor");
        return {-1, "", head.str()};
      }
      require(head.empty() && size_t(index) < statics.size(), r,
              "source static index out of range");
      require(member.empty() ||
                  any_of(members,
                         [&](const auto *m) {
                           return name(m) == member &&
                                  sameParameter(m->getValueAsDef("owner"),
                                                statics[index]);
                         }),
              r, "unknown source static member");
      return {int(index), member.str(), ""};
    };
    Shape shape{kind.str(), {}, {}, {}};
    for (const auto *p : statics) {
      exactFields(p, {"kind", "sort"}, false);
      std::get<1>(shape).emplace_back(parameter(p).first.str(),
                                      parameter(p).second.str());
    }
    for (const auto *t : inputs)
      std::get<2>(shape).push_back(term(t));
    require(
        output.size() <= 1 &&
            (kind == "Interface" || kind == "Requirement") == output.empty() &&
            ((kind != "Interface" && kind != "Requirement") || inputs.empty()),
        r, "source declaration kind and signature disagree");
    if (!output.empty())
      std::get<3>(shape) = term(output.front());
    return shape;
  };
  std::map<StringRef, Shape> ruleShapes;
  for (const auto *r : frontendRules) {
    require(identifier(name(r)) && !ruleShapes.count(name(r)), r,
            "invalid or duplicate frontend rule");
    ruleShapes.emplace(name(r), sourceShape(r, r->getValueAsString("kind"),
                                            r->getValueAsListOfDefs("statics"),
                                            r->getValueAsListOfDefs("inputs"),
                                            r->getValueAsListOfDefs("output")));
  }
  std::map<StringRef, const Record *> schemes, contractHeads;
  std::set<StringRef> schemeForms, usedSchemes, usedHeads;
  for (const auto *r : frontendConstructors) {
    exactFields(r, {"name", "form"});
    contractHeads.emplace(name(r), r);
  }
  for (const auto *r : frontendSchemes) {
    exactFields(r,
                {"name", "form", "variables", "statics", "inputs", "output"});
    require(identifier(name(r)) && schemes.emplace(name(r), r).second &&
                schemeForms.insert(r->getValueAsString("form")).second,
            r, "duplicate descriptor scheme");
    auto expected = schemeShape(r->getValueAsString("form"), r);
    require(r->getValueAsListInit("variables")->size() <= 1024, r,
            "scheme signature limit");
    auto variables = r->getValueAsListOfStrings("variables");
    auto statics = boundedDefs(r, "statics", 1024);
    for (const auto *p : statics)
      exactFields(p, {"kind", "sort"}, false);
    require(variables.size() <= 1024 && statics.size() <= 1024, r,
            "scheme signature limit");
    require(variables == expected.variables &&
                statics.size() == expected.statics &&
                all_of(statics,
                       [](auto *p) {
                         return parameter(p) ==
                                std::make_pair(StringRef("Nat"), StringRef(""));
                       }),
            r, "descriptor scheme form mismatch");
    auto inputs = boundedDefs(r, "inputs", 1024);
    require(inputs.size() <= 1024, r, "scheme port limit");
    std::vector<std::string> ports;
    for (const auto *p : inputs)
      ports.push_back(checkedSchemePort(p, variables, statics, false));
    auto output =
        checkedPattern(r->getValueAsDef("output"), variables, statics);
    require(ports == expected.inputs && output == expected.output, r,
            "descriptor scheme form mismatch");
  }
  if (schemeForms.size() != 6)
    PrintFatalError("missing descriptor scheme form");
  std::set<StringRef> intrinsicNames, operationNames;
  for (const auto *r : order.sort("ZKC_MathematicalIntrinsic"))
    intrinsicNames.insert(name(r));
  for (const auto *r : operations)
    operationNames.insert(name(r));
  std::set<StringRef> frontendIds, preludeNames, homes, serviceConstructors;
  std::set<std::pair<StringRef, StringRef>> methods;
  std::set<std::pair<StringRef, StringRef>> declared;
  for (const auto *r : frontendDeclarations) {
    bool scheme = r->getValueAsString("kind") == "View";
    if (scheme)
      exactFields(r, {"identity", "module", "name", "kind", "statics", "inputs",
                      "output", "association", "target", "prelude",
                      "schemeInputs", "schemeOutput"});
    else
      exactFields(r, {"identity", "module", "name", "kind", "statics", "inputs",
                      "output", "association", "target", "prelude"});
    auto identity = r->getValueAsString("identity");
    require(!identity.empty() && frontendIds.insert(identity).second, r,
            "duplicate frontend identity");
    checkExport(r);
    declared.emplace(r->getValueAsString("module"), name(r));
    auto kind = r->getValueAsString("kind");
    auto association = r->getValueAsString("association");
    auto target = r->getValueAsString("target");
    if (kind == "ContractConstructor") {
      auto head = contractHeads.find(target);
      require(
          r->isSubClassOf("ZKC_ContractHeadDeclaration") &&
              association == "constructor" && !r->getValueAsBit("prelude") &&
              head != contractHeads.end() &&
              (head->second->getValueAsString("form") == "DescriptorProduct" ||
               head->second->getValueAsString("form") ==
                   "DescriptorSequence") &&
              usedHeads.insert(target).second &&
              r->getValueAsListInit("statics")->size() == 0 &&
              r->getValueAsListInit("inputs")->size() == 0 &&
              r->getValueAsListInit("output")->size() == 0,
          r, "invalid contract constructor association");
      continue;
    }
    std::vector<const Record *> statics;
    std::set<StringRef> names;
    if (scheme)
      require(r->getValueAsListInit("statics")->size() <= 1024, r,
              "scheme signature limit");
    for (const auto *slot : r->getValueAsListOfDefs("statics")) {
      exactFields(slot, {"name", "parameter"}, false);
      if (scheme)
        exactFields(slot->getValueAsDef("parameter"), {"kind", "sort"}, false);
      require(identifier(name(slot)) && names.insert(name(slot)).second, r,
              "invalid or duplicate source parameter name");
      statics.push_back(slot->getValueAsDef("parameter"));
    }
    if (scheme) {
      auto found = schemes.find(target);
      require(r->isSubClassOf("ZKC_ViewSchemeDeclaration") &&
                  association == "scheme" && !r->getValueAsBit("prelude") &&
                  found != schemes.end() && usedSchemes.insert(target).second &&
                  r->getValueAsListInit("inputs")->size() == 0 &&
                  r->getValueAsListInit("output")->size() == 0,
              r, "invalid View scheme association");
      auto *definition = found->second;
      auto variables = definition->getValueAsListOfStrings("variables");
      auto expectedStatics = definition->getValueAsListOfDefs("statics");
      require(statics.size() == expectedStatics.size(), r,
              "View scheme declaration mismatch");
      for (unsigned i = 0; i < statics.size(); ++i)
        require(sameParameter(statics[i], expectedStatics[i]), r,
                "View scheme declaration mismatch");
      auto expected = definition->getValueAsListOfDefs("inputs");
      auto inputs = boundedDefs(r, "schemeInputs", expected.size());
      require(inputs.size() == expected.size(), r,
              "View scheme declaration mismatch");
      for (unsigned i = 0; i < inputs.size(); ++i) {
        require(names.insert(name(inputs[i])).second, r,
                "invalid or duplicate source parameter name");
        require(checkedSchemePort(inputs[i], variables, statics, true) ==
                    checkedSchemePort(expected[i], variables, statics, false),
                r, "View scheme declaration mismatch");
      }
      require(checkedPattern(r->getValueAsDef("schemeOutput"), variables,
                             statics) ==
                  checkedPattern(definition->getValueAsDef("output"), variables,
                                 statics),
              r, "View scheme declaration mismatch");
      continue;
    }
    std::vector<const Record *> inputs;
    for (const auto *slot : r->getValueAsListOfDefs("inputs")) {
      require(identifier(name(slot)) && names.insert(name(slot)).second, r,
              "invalid or duplicate source parameter name");
      inputs.push_back(slot->getValueAsDef("type"));
    }
    auto shape = sourceShape(r, kind, statics, inputs,
                             r->getValueAsListOfDefs("output"));
    if (association == "rule" && target == "RandomConstructor")
      serviceConstructors.insert(identity);
    if (association == "rule") {
      auto rule = ruleShapes.find(target);
      require(rule != ruleShapes.end() && rule->second == shape, r,
              "frontend rule signature mismatch");
    } else
      require(
          association == "primitive" && kind != "Interface" &&
              kind != "Requirement" &&
              (kind == "Math" ? intrinsicNames : operationNames).count(target),
          r, "frontend primitive kind mismatch");
    if (r->getValueAsBit("prelude"))
      require(preludeNames.insert(name(r)).second, r,
              "duplicate prelude frontend name");
  }
  if (usedSchemes.size() != schemes.size())
    PrintFatalError("unreferenced descriptor scheme");
  if (usedHeads.size() != 2)
    PrintFatalError("unreferenced contract constructor");
  std::set<std::tuple<StringRef, StringRef, StringRef>> notations;
  for (const auto *r : frontendNotations) {
    auto module = r->getValueAsString("module");
    auto symbol = r->getValueAsString("symbol");
    auto target = r->getValueAsString("target");
    require(any_of(declared, [&](const auto &d) { return d.first == module; }),
            r, "frontend notation owner is not installed");
    require(declared.count({module, target}), r,
            "frontend notation target is not declared");
    require(!symbol.empty() && none_of(symbol, isSpace), r,
            "invalid frontend notation symbol");
    auto fixity = r->getValueAsString("fixity");
    auto precedence = r->getValueAsInt("precedence");
    require(fixity.empty()
                ? precedence == 0
                : (fixity == "left" || fixity == "right" || fixity == "none") &&
                      precedence >= 1 && precedence <= 99,
            r, "invalid frontend notation fixity");
    require(notations.emplace(module, symbol, target).second, r,
            "duplicate frontend notation");
  }
  // A home names a catalog type constructor or a declared frontend
  // constructor, a structural head the source language owns. Exactly one
  // row spells each form, the structural meaning the frontend gives a head.
  static constexpr StringRef frontendConstructorForms[] = {
      "OracleHandle", "OracleHandleSequence", "FiniteDescriptor",
      "DescriptorProduct", "DescriptorSequence"};
  std::set<StringRef> heads, forms;
  for (const auto *t : types)
    heads.insert(name(t));
  for (const auto *r : frontendConstructors) {
    require(identifier(name(r)) && heads.insert(name(r)).second, r,
            "invalid or duplicate frontend constructor");
    auto form = r->getValueAsString("form");
    require(is_contained(frontendConstructorForms, form), r,
            "unknown frontend constructor form");
    require(forms.insert(form).second, r,
            "duplicate frontend constructor form");
  }
  if (forms.size() != std::size(frontendConstructorForms))
    PrintFatalError("missing frontend constructor form");
  for (const auto *r : frontendHomes) {
    auto head = name(r), module = r->getValueAsString("module");
    require(heads.count(head) && module.starts_with("zkc::") &&
                path(module, "::"),
            r, "invalid frontend home");
    require(homes.insert(head).second, r, "duplicate frontend home");
    std::set<StringRef> exports;
    for (auto member : r->getValueAsListOfStrings("members"))
      require(member.starts_with("zkc::") && path(member, "::") &&
                  exports.insert(member).second,
              r, "invalid frontend home members");
  }
  std::map<StringRef, StringRef> serviceRules;
  for (const auto *r : serviceSignatures) {
    auto cap = r->getValueAsString("capability");
    require(identifier(name(r)) && serviceRules.emplace(name(r), cap).second, r,
            "invalid or duplicate service signature");
    require(cap.empty() || any_of(capabilities,
                                  [&](const auto *c) {
                                    auto ps =
                                        c->getValueAsListOfDefs("parameters");
                                    return name(c) == cap && ps.size() == 1 &&
                                           parameter(ps.front()) ==
                                               std::pair<StringRef, StringRef>(
                                                   "Domain", "Field");
                                  }),
            r, "unknown service capability");
  }
  for (const auto *r : serviceMethods) {
    exactFields(r,
                {"identity", "constructor", "name", "signature", "capability"});
    auto rule = r->getValueAsString("signature"),
         cap = r->getValueAsString("capability");
    auto identity = r->getValueAsString("identity"),
         constructor = r->getValueAsString("constructor");
    require(!identity.empty() && frontendIds.insert(identity).second, r,
            "duplicate service method identity");
    require(serviceConstructors.count(constructor), r,
            "invalid service method constructor");
    require(identifier(name(r)) && methods.emplace(constructor, name(r)).second,
            r, "invalid or duplicate service method");
    require(serviceRules.count(rule) && serviceRules.at(rule) == cap, r,
            "service method capability mismatch");
    require(cap.empty() ||
                any_of(capabilities,
                       [&](const auto *c) {
                         auto ps = c->getValueAsListOfDefs("parameters");
                         return name(c) == cap && ps.size() == 1 &&
                                parameter(ps.front()) ==
                                    std::make_pair(StringRef("Domain"),
                                                   StringRef("Field"));
                       }),
            r, "unknown service capability");
  }
}
void Model::validateOperation(const Record *op, bool consumer) {
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
  for (auto field : {"inputs", "outputs", "requirements"})
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
        // The catalog describes complete signatures. Consumer profiles decide
        // which instantiated Type ports they can admit; a TableGen subclass
        // cannot grant an exception absent from the neutral declaration data.
        require(available.count(app) &&
                    parameter(app->getValueAsDef("parameter")).first == "Type",
                op, "direct ports require a scoped Type term");
        continue;
      }
      auto args = app->getValueAsListOfDefs("arguments");
      scoped(args);
      auto *constructor = app->getValueAsDef("constructor");
      validateParameters(op, constructor->getValueAsListOfDefs("parameters"),
                         args);
    }
  }
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
      {"NativeOrigin", {1, 1}},
      {"NativeIndexBlock", {3, 4}}};
  auto found = schemas.find(name(parameters).str());
  require(found != schemas.end() &&
              (name(parameters) == "NativeIndexBlock"
                   ? parameters->getValueAsInt("minimum") ==
                             (name(op) == "transcript.native.indexed.indices"
                                  ? 3
                                  : 4) &&
                         parameters->getValueAsInt("maximum") ==
                             parameters->getValueAsInt("minimum")
                   : found->second ==
                         std::make_pair(parameters->getValueAsInt("minimum"),
                                        parameters->getValueAsInt("maximum"))),
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
  if (!consumer) {
    require(op->getValueAsListOfDefs("facets").size() <= 1024, op,
            "operation declaration limit");
    validateFacets(op);
  }
}
std::string facetKind(const Record *r) {
  for (auto kind :
       {"History", "Succession", "Observation", "Sampling", "Diagonal",
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
    } else if (kind == "Succession") {
      // The exact resource received at stateInput is returned at stateOutput:
      // both are resource_unit applications of one Slot root, and no other
      // port carries a resource unit, so custody is neither duplicated nor
      // dropped.
      auto received = port(r, "stateInput", false, "resource_unit")
                          ->getValueAsListOfDefs("arguments");
      auto returned = port(r, "stateOutput", true, "resource_unit")
                          ->getValueAsListOfDefs("arguments");
      require(received.size() == 1 && received == returned, op,
              "succession resource types differ");
      const auto *slot = received.front();
      require(slot->isSubClassOf("ZKC_Root") &&
                  is_contained(op->getValueAsListOfDefs("scope"), slot) &&
                  parameter(slot->getValueAsDef("parameter")) ==
                      std::make_pair(StringRef("Domain"), StringRef("Slot")),
              op, "succession requires a Slot root");
      auto resource = [](const Record *app) {
        return app->isSubClassOf("ZKC_Apply") &&
               name(app->getValueAsDef("constructor")) == "resource_unit";
      };
      for (auto [i, app] : enumerate(inputs))
        require(int64_t(i) == r->getValueAsInt("stateInput") || !resource(app),
                op, "succession operation has another resource unit port");
      for (auto [i, app] : enumerate(outputs))
        require(int64_t(i) == r->getValueAsInt("stateOutput") || !resource(app),
                op, "succession operation has another resource unit port");
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
                  domain == "BoundedIndex" || domain == "IndexBlock",
              op, "unknown sample domain");
      auto state = provider == "Entropy" ? "rng" : "transcript";
      require(sameType(port(r, "stateInput", false, state),
                       port(r, "stateOutput", true, state)),
              op, "sampling successor type mismatch");
      port(r, "valueOutput", true,
           domain == "Field"         ? "field"
           : domain == "FieldVector" ? "vector"
           : domain == "IndexBlock"  ? "indices"
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
      require(kind == "PublicReplay" || kind == "DeterministicData" ||
                  kind == "AcceptanceGuard" || kind == "Conjunction" ||
                  kind == "SourceHistory" || kind == "ManagedHistory",
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
    else if (kind == "DeterministicData")
      os << "c.deterministicData = true;\n";
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
    else if (kind == "Succession")
      os << "c.succession = SuccessionContract{" << number(r, "stateInput")
         << ", " << number(r, "stateOutput") << "};\n";
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
                      "constructible", "message", "sourceData"})
      os << ", " << boolean(type->getValueAsBit(fact));
    if (const auto *collection = optionalDef(type, "collection")) {
      const auto element = collection->getValueAsString("element");
      os << ", TypeCollection{" << number(collection, "rank")
         << ", CollectionElement::"
         << (element == "parameter" ? "Parameter"
             : element == "index"   ? "Index"
                                    : "Byte")
         << "}";
    } else
      os << ", std::nullopt";
    if (type->isValueUnset("setup"))
      os << ", std::nullopt";
    else
      os << ", SetupKey::"
         << (type->getValueAsString("setup") == "prover" ? "Prover"
                                                         : "Verifier");
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
  auto sourceTerm = [](const Record *t) {
    auto index = t->getValueAsInt("index");
    return index < 0 ? "{std::nullopt, \"\", " +
                           quote(t->getValueAsString("constructor")) + "}"
                     : "{" + std::to_string(index) + "u, " +
                           quote(t->getValueAsString("member")) + ", \"\"}";
  };
  os << "llvm::ArrayRef<FrontendScheme> frontendSchemes() {\n"
        "static const std::vector<FrontendScheme> rows = {\n";
  std::map<StringRef, unsigned> schemeIndices;
  for (auto [i, r] : enumerate(m.frontendSchemes)) {
    schemeIndices.emplace(name(r), i);
    os << "{" << quote(name(r))
       << ", DescriptorForm::" << r->getValueAsString("form") << ", {";
    for (auto v : r->getValueAsListOfStrings("variables"))
      os << "PatternSort::" << v << ",";
    os << "}, {";
    for (auto *p : r->getValueAsListOfDefs("statics")) {
      auto [kind, sort] = parameter(p);
      os << "{StaticKind::" << kind << "," << quote(sort) << "},";
    }
    os << "}, {";
    for (auto *p : r->getValueAsListOfDefs("inputs"))
      os << schemePortCpp(p) << ",";
    os << "}," << patternCpp(r->getValueAsDef("output")) << "},\n";
  }
  os << "}; return rows; }\n"
        "const FrontendScheme *frontendScheme(SchemeId id) { auto rows = "
        "frontendSchemes(); "
        "return id.index < rows.size() ? &rows[id.index] : nullptr; }\n";
  os << "llvm::ArrayRef<FrontendDeclaration> frontendDeclarations() {\n"
        "static const std::vector<FrontendDeclaration> rows = {\n";
  for (const auto *r : m.frontendDeclarations) {
    os << "{" << quote(r->getValueAsString("identity")) << ", "
       << quote(r->getValueAsString("module")) << ", " << quote(name(r))
       << ", SourceDeclarationKind::" << r->getValueAsString("kind") << ", ";
    auto kind = r->getValueAsString("kind");
    if (kind == "ContractConstructor") {
      os << "InstalledContractHead{" << quote(r->getValueAsString("target"))
         << "}";
    } else {
      bool scheme = kind == "View";
      os << (scheme ? "InstalledViewSignature" : "ConcreteSourceSignature")
         << "{{";
      for (const auto *slot : r->getValueAsListOfDefs("statics")) {
        auto [kind, sort] = parameter(slot->getValueAsDef("parameter"));
        os << "{" << quote(name(slot)) << ", " << quote(kind) << ", "
           << quote(sort) << "}, ";
      }
      os << "}, {";
      if (scheme) {
        for (auto *slot : r->getValueAsListOfDefs("schemeInputs"))
          os << "{" << quote(name(slot)) << "," << schemePortCpp(slot) << "},";
        os << "}," << patternCpp(r->getValueAsDef("schemeOutput"))
           << ", SchemeId{" << schemeIndices.at(r->getValueAsString("target"))
           << "u}}";
      } else {
        for (const auto *slot : r->getValueAsListOfDefs("inputs"))
          os << "{" << quote(name(slot)) << ", "
             << sourceTerm(slot->getValueAsDef("type")) << "}, ";
        os << "}, ";
        auto output = r->getValueAsListOfDefs("output");
        os << (output.empty() ? std::string("std::nullopt")
                              : "SourceTerm" + sourceTerm(output.front()))
           << ", ";
        bool rule = r->getValueAsString("association") == "rule";
        os << (rule
                   ? "FrontendSignature::" + r->getValueAsString("target").str()
                   : std::string("std::nullopt"))
           << ", " << quote(rule ? "" : r->getValueAsString("target")) << "}";
      }
    }
    os << "," << boolean(r->getValueAsBit("prelude")) << "},\n";
  }
  os << "}; return rows; }\n"
        "const FrontendDeclaration *frontendDeclaration(llvm::StringRef "
        "qualified) {\n"
        "for (const auto &r : frontendDeclarations())\n"
        "if (qualified == r.module + \"::\" + r.name) return &r;\n"
        "return nullptr; }\n";
  os << "llvm::ArrayRef<FrontendNotation> frontendNotations() {\n"
        "static const std::vector<FrontendNotation> rows = {\n";
  for (const auto *r : m.frontendNotations)
    os << "{" << quote(r->getValueAsString("module")) << ", "
       << quote(r->getValueAsString("symbol")) << ", "
       << quote(r->getValueAsString("fixity")) << ", "
       << r->getValueAsInt("precedence") << ", "
       << quote(r->getValueAsString("target")) << ", "
       << boolean(r->getValueAsBit("public")) << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<FrontendConstructor> frontendConstructors() {\n"
        "static const std::vector<FrontendConstructor> rows = {\n";
  for (const auto *r : m.frontendConstructors)
    os << "{" << quote(name(r))
       << ", FrontendConstructorForm::" << r->getValueAsString("form")
       << "},\n";
  os << "}; return rows; }\n"
        "const FrontendConstructor *frontendConstructor(llvm::StringRef "
        "spelling) {\n"
        "for (const auto &r : frontendConstructors())\n"
        "if (spelling == r.name) return &r;\n"
        "return nullptr; }\n";
  os << "llvm::ArrayRef<FrontendHome> frontendHomes() {\n"
        "static const std::vector<FrontendHome> rows = {\n";
  for (const auto *r : m.frontendHomes)
    os << "{" << quote(name(r)) << ", " << quote(r->getValueAsString("module"))
       << ", " << strings(r->getValueAsListOfStrings("members")) << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<ServiceMethodDeclaration> serviceMethodDeclarations() "
        "{\n"
        "static const std::vector<ServiceMethodDeclaration> rows = {\n";
  for (const auto *r : m.serviceMethods)
    os << "{" << quote(r->getValueAsString("identity")) << ", "
       << quote(r->getValueAsString("constructor")) << ", " << quote(name(r))
       << ", ServiceSignature::" << r->getValueAsString("signature") << ", "
       << quote(r->getValueAsString("capability")) << "},\n";
  os << "}; return rows; }\n";
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
  os << "llvm::ArrayRef<ConsumerProfile> consumerProfiles() {\n"
        "static const std::vector<ConsumerProfile> values = {\n";
  for (const auto *profile : m.consumerProfiles) {
    os << "{" << quote(name(profile))
       << ", ConsumerImplementation::Unselected, "
       << names(profile->getValueAsListOfDefs("typeConstructors")) << ", {";
    for (auto validator :
         profile->getValueAsListOfStrings("parameterValidators"))
      os << "ParameterValidator::" << validator << ",";
    os << "}, {\n";
    for (const auto *entry : profile->getValueAsListOfDefs("operations")) {
      os << "{" << quote(name(entry->getValueAsDef("operation"))) << ", {";
      for (const auto *term : entry->getValueAsListOfDefs("scope"))
        if (term->isSubClassOf("ZKC_Root")) {
          emitParameter(term->getValueAsDef("parameter"));
          os << ",";
        }
      os << "}},\n";
    }
    os << "}},\n";
  }
  os << "}; return values; }\n"
        "const ConsumerProfile *consumerProfile(llvm::StringRef name) {\n"
        "for (const auto &p : consumerProfiles()) if (p.name == name) return "
        "&p;\n"
        "return nullptr; }\n"
        "const ConsumerProfileOperation *consumerProfileOperation(\n"
        "llvm::StringRef profile, llvm::StringRef operation) {\n"
        "auto *p = consumerProfile(profile); if (!p) return nullptr;\n"
        "for (const auto &op : p->operations) if (op.operation == operation) "
        "return &op;\n"
        "return nullptr; }\n";
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
  else if (kind == "History" || kind == "Succession" || kind == "Observation" ||
           kind == "Sampling") {
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
json::Object operationInterfaceJSON(const Record *op) {
  auto scope = op->getValueAsListOfDefs("scope");
  json::Array terms;
  for (const auto *term : scope)
    terms.push_back(scopeTermJSON(term, scope));
  const auto *p = op->getValueAsDef("parameters");
  const auto maximum = p->getValueAsInt("maximum");
  json::Object object{
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
  return object;
}
void Model::validateConsumerProfiles() {
  uniqueNames(consumerProfiles, "consumer profile");
  const std::set<StringRef> supportedValidators{"None",
                                                "Natural",
                                                "Extent",
                                                "FieldLiteral",
                                                "FieldLiterals",
                                                "MatrixShape",
                                                "MatrixIdentity",
                                                "AssetIdentity",
                                                "MatrixVector",
                                                "GatherIndices",
                                                "ScatterIndices",
                                                "NativeOrigin",
                                                "NativeIndexBlock"};
  std::set<const Record *> selectedEntries;
  for (const auto *profile : consumerProfiles) {
    require(!name(profile).empty(), profile, "empty consumer profile identity");
    require(profile->getValueAsString("implementation") == "unselected",
            profile, "unsupported profile implementation policy");
    std::set<const Record *> constructors;
    for (const auto *type : profile->getValueAsListOfDefs("typeConstructors")) {
      require(is_contained(types, type), profile,
              "unknown profile constructor");
      require(constructors.insert(type).second, profile,
              "duplicate profile constructor");
    }
    std::set<StringRef> validators;
    for (auto validator :
         profile->getValueAsListOfStrings("parameterValidators")) {
      require(supportedValidators.count(validator), profile,
              "unsupported profile parameter family");
      require(validators.insert(validator).second, profile,
              "duplicate profile validator");
    }
    std::set<const Record *> selected;
    for (const auto *entry : profile->getValueAsListOfDefs("operations")) {
      selectedEntries.insert(entry);
      const auto *op = entry->getValueAsDef("operation");
      require(is_contained(operations, op), entry, "unknown profile operation");
      require(selected.insert(op).second, entry,
              "duplicate profile membership");
      require(!optionalDef(op, "numerical") && !optionalDef(entry, "numerical"),
              entry, "unsupported profile signature family");
      // Validate the expectation independently, before comparing its neutral
      // form. Record identity and TableGen inheritance confer no exception.
      validateOperation(entry, true);
      auto actual = operationInterfaceJSON(op);
      auto expected = operationInterfaceJSON(entry);
      for (auto field :
           {"scope", "stage", "signature", "requirements", "parameters"})
        require(*actual.get(field) == *expected.get(field), entry,
                Twine("consumer operation ") + field + " mismatch");
      require(validators.count(name(op->getValueAsDef("parameters"))), entry,
              "unsupported profile validator");
      auto checkType = [&](const Record *term) {
        auto kind = parameter(term->getValueAsDef("parameter")).first;
        require(kind != "Type" || term->isSubClassOf("ZKC_Apply"), entry,
                "unsupported profile Type term");
        if (term->isSubClassOf("ZKC_Apply"))
          require(constructors.count(term->getValueAsDef("constructor")), entry,
                  "unsupported profile type constructor");
      };
      for (auto field : {"scope", "inputs", "outputs"})
        for (const auto *term : op->getValueAsListOfDefs(field))
          checkType(term);
    }
  }
  for (const auto *entry : order.sort("ZKC_ConsumerOperation"))
    require(selectedEntries.count(entry), entry, "unowned consumer operation");
}
json::Object inventory(const Model &m, const RecordKeeper &records) {
  json::Object result{{"format", "zkc.contract-declarations/0"}};
  json::Array sorts;
  for (const auto *sort : m.sorts)
    sorts.push_back(name(sort));
  result["sorts"] = std::move(sorts);
  json::Array types, ops, members, rules, capabilities, exports, families,
      associatedTypes, meanings, intrinsics;
  for (const auto *t : m.types) {
    json::Value collection = nullptr;
    if (const auto *c = optionalDef(t, "collection"))
      collection = json::Object{{"rank", c->getValueAsInt("rank")},
                                {"element", c->getValueAsString("element")}};
    json::Value setup = nullptr;
    if (!t->isValueUnset("setup"))
      setup = t->getValueAsString("setup");
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
                     {"message", t->getValueAsBit("message")},
                     {"sourceData", t->getValueAsBit("sourceData")},
                     {"collection", std::move(collection)},
                     {"setup", std::move(setup)}});
  }
  for (const auto *c : m.capabilities) {
    auto names = [&](StringRef field) {
      json::Array values;
      for (auto member : c->getValueAsListOfStrings(field))
        values.push_back(member);
      return values;
    };
    capabilities.push_back(json::Object{{"name", name(c)},
                                        {"parameters", parametersJSON(c)},
                                        {"requires", names("requires")},
                                        {"permits", names("permits")}});
  }
  for (const auto *member : m.members)
    members.push_back(json::Object{
        {"name", name(member)},
        {"owner", parameterJSON(member->getValueAsDef("owner"))},
        {"result", parameterJSON(member->getValueAsDef("result"))}});
  for (const auto *r : m.rules)
    rules.push_back(json::Array{name(r->getValueAsDef("premise")),
                                name(r->getValueAsDef("conclusion"))});
  for (const auto *op : m.operations) {
    auto object = operationInterfaceJSON(op);
    object["name"] = name(op);
    json::Array facets;
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
  json::Array frontendRules, schemes, declarations, notations, constructors,
      homes, signatures, services;
  auto sourceTerm = [](const Record *t) {
    auto index = t->getValueAsInt("index");
    if (index < 0)
      return json::Object{{"constructor", t->getValueAsString("constructor")}};
    json::Object term{{"static", index}};
    if (!t->getValueAsString("member").empty())
      term["member"] = t->getValueAsString("member");
    return term;
  };
  auto sourceOutput = [&](const Record *r) -> json::Value {
    auto output = r->getValueAsListOfDefs("output");
    return output.empty() ? json::Value(nullptr)
                          : json::Value(sourceTerm(output.front()));
  };
  for (const auto *r : m.frontendRules) {
    json::Array statics, inputs;
    for (const auto *p : r->getValueAsListOfDefs("statics"))
      statics.push_back(parameterJSON(p));
    for (const auto *t : r->getValueAsListOfDefs("inputs"))
      inputs.push_back(sourceTerm(t));
    frontendRules.push_back(json::Object{{"name", name(r)},
                                         {"kind", r->getValueAsString("kind")},
                                         {"statics", std::move(statics)},
                                         {"inputs", std::move(inputs)},
                                         {"output", sourceOutput(r)}});
  }
  for (const auto *r : m.frontendSchemes) {
    json::Array variables, statics, inputs;
    for (auto v : r->getValueAsListOfStrings("variables"))
      variables.push_back(v);
    for (auto *p : r->getValueAsListOfDefs("statics"))
      statics.push_back(parameterJSON(p));
    for (auto *p : r->getValueAsListOfDefs("inputs"))
      inputs.push_back(schemePortJSON(p));
    schemes.push_back(
        json::Object{{"name", name(r)},
                     {"form", r->getValueAsString("form")},
                     {"variables", std::move(variables)},
                     {"statics", std::move(statics)},
                     {"inputs", std::move(inputs)},
                     {"output", patternJSON(r->getValueAsDef("output"))}});
  }
  for (const auto *r : m.frontendDeclarations) {
    json::Object declaration{
        {"identity", r->getValueAsString("identity")},
        {"owner", r->getValueAsString("module")},
        {"name", name(r)},
        {"kind", r->getValueAsString("kind")},
        {"association",
         json::Object{{"kind", r->getValueAsString("association")},
                      {"target", r->getValueAsString("target")}}},
        {"prelude", r->getValueAsBit("prelude")}};
    if (r->getValueAsString("kind") != "ContractConstructor") {
      bool scheme = r->getValueAsString("kind") == "View";
      json::Array statics, inputs;
      for (auto *slot : r->getValueAsListOfDefs("statics"))
        statics.push_back(json::Object{
            {"name", name(slot)},
            {"parameter", parameterJSON(slot->getValueAsDef("parameter"))}});
      for (auto *slot :
           r->getValueAsListOfDefs(scheme ? "schemeInputs" : "inputs")) {
        if (scheme)
          inputs.push_back(schemePortJSON(slot, true));
        else
          inputs.push_back(
              json::Object{{"name", name(slot)},
                           {"type", sourceTerm(slot->getValueAsDef("type"))}});
      }
      declaration["statics"] = std::move(statics);
      declaration["inputs"] = std::move(inputs);
      declaration["output"] =
          scheme ? json::Value(patternJSON(r->getValueAsDef("schemeOutput")))
                 : sourceOutput(r);
    }
    declarations.push_back(std::move(declaration));
  }
  for (const auto *r : m.frontendNotations) {
    json::Value fixity = nullptr;
    if (!r->getValueAsString("fixity").empty())
      fixity = json::Object{{"associativity", r->getValueAsString("fixity")},
                            {"precedence", r->getValueAsInt("precedence")}};
    notations.push_back(json::Object{{"owner", r->getValueAsString("module")},
                                     {"symbol", r->getValueAsString("symbol")},
                                     {"fixity", std::move(fixity)},
                                     {"target", r->getValueAsString("target")},
                                     {"public", r->getValueAsBit("public")}});
  }
  for (const auto *r : m.serviceSignatures)
    signatures.push_back(json::Object{
        {"name", name(r)}, {"capability", r->getValueAsString("capability")}});
  for (const auto *r : m.frontendConstructors)
    constructors.push_back(
        json::Object{{"name", name(r)}, {"form", r->getValueAsString("form")}});
  for (const auto *r : m.frontendHomes)
    homes.push_back(json::Object{{"constructor", name(r)},
                                 {"module", r->getValueAsString("module")},
                                 {"members", [&] {
                                    json::Array members;
                                    for (auto member :
                                         r->getValueAsListOfStrings("members"))
                                      members.push_back(member);
                                    return members;
                                  }()}});
  for (const auto *r : m.serviceMethods)
    services.push_back(
        json::Object{{"identity", r->getValueAsString("identity")},
                     {"constructor", r->getValueAsString("constructor")},
                     {"name", name(r)},
                     {"signature", r->getValueAsString("signature")},
                     {"capability", r->getValueAsString("capability")}});
  result["frontendRules"] = std::move(frontendRules);
  result["frontendSchemes"] = std::move(schemes);
  result["frontendDeclarations"] = std::move(declarations);
  result["frontendNotations"] = std::move(notations);
  result["frontendConstructors"] = std::move(constructors);
  result["frontendHomes"] = std::move(homes);
  result["serviceSignatures"] = std::move(signatures);
  result["serviceMethods"] = std::move(services);
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
  json::Array profiles;
  for (const auto *profile : m.consumerProfiles) {
    json::Array entries, constructors, validators;
    for (const auto *entry : profile->getValueAsListOfDefs("operations")) {
      auto object = operationInterfaceJSON(entry);
      object["operation"] = name(entry->getValueAsDef("operation"));
      entries.push_back(std::move(object));
    }
    for (const auto *type : profile->getValueAsListOfDefs("typeConstructors"))
      constructors.push_back(name(type));
    for (auto validator :
         profile->getValueAsListOfStrings("parameterValidators"))
      validators.push_back(validator);
    profiles.push_back(json::Object{
        {"name", name(profile)},
        {"implementation", profile->getValueAsString("implementation")},
        {"typeConstructors", std::move(constructors)},
        {"parameterValidators", std::move(validators)},
        {"operations", std::move(entries)}});
  }
  result["consumerProfiles"] = std::move(profiles);
  // Logical installed-instance tables only; the native installation has its
  // own inventory action.
  addInstalledInstanceInventory(result, records);
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
  os << formatv("{0:2}\n", json::Value(inventory(Model(records), records)));
  return false;
}
