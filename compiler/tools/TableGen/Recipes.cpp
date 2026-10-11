#include "Recipes.h"
#include "Declarations.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include <map>
#include <set>

using namespace llvm;
namespace {
StringRef name(const Record *r) { return r->getValueAsString("name"); }
void require(bool valid, const Record *r, StringRef message) {
  if (!valid)
    PrintFatalError(r, message);
}
const Record *optional(const Record *r, StringRef field) {
  auto *value = dyn_cast<DefInit>(r->getValueInit(field));
  return value ? value->getDef() : nullptr;
}
const Record *meaning(const Record *op) {
  for (const auto *facet : op->getValueAsListOfDefs("facets"))
    if (facet->isSubClassOf("ZKC_Mathematical"))
      return facet->getValueAsDef("identity");
  return nullptr;
}
// Endpoint comparison is under an explicit root substitution. Anonymous
// application records and independently scoped roots are never compared by
// record identity across declarations.
class Endpoint {
  std::map<const Record *, std::string> terms;

public:
  Endpoint(const Record *recipe, const Record *source, const Record *target,
           ArrayRef<int64_t> mapping) {
    auto sourceScope = source->getValueAsListOfDefs("scope");
    unsigned next = 0;
    for (const auto *term : target->getValueAsListOfDefs("scope")) {
      if (const auto *parent = optional(term, "parent")) {
        require(terms.count(parent), recipe,
                "recipe projection parent mapping");
        terms[term] = terms.at(parent) + "." + name(term).str();
      } else {
        require(term->isSubClassOf("ZKC_Root") && next < mapping.size(), recipe,
                "recipe static argument mapping arity");
        auto position = mapping[next++];
        require(position >= 0 && size_t(position) < sourceScope.size(), recipe,
                "recipe static argument outside source scope");
        auto *selected = sourceScope[position];
        auto *sp = selected->getValueAsDef("parameter");
        auto *tp = term->getValueAsDef("parameter");
        require(name(sp->getValueAsDef("kind")) ==
                        name(tp->getValueAsDef("kind")) &&
                    sp->getValueAsString("sort") ==
                        tp->getValueAsString("sort"),
                recipe, "recipe static argument kind mismatch");
        terms[term] = symbol(selected, sourceScope);
      }
    }
    require(next == mapping.size(), recipe,
            "recipe static argument mapping arity");
  }
  static std::string symbol(const Record *term,
                            ArrayRef<const Record *> scope) {
    if (const auto *parent = optional(term, "parent"))
      return symbol(parent, scope) + "." + name(term).str();
    return "$" + std::to_string(llvm::find(scope, term) - scope.begin());
  }
  std::string argument(const Record *port) const {
    auto args = port->getValueAsListOfDefs("arguments");
    return args.size() == 1 && terms.count(args[0]) ? terms.at(args[0]) : "";
  }
  bool requirement(const Record *op, StringRef capability,
                   StringRef term) const {
    return any_of(op->getValueAsListOfDefs("requirements"),
                  [&](const Record *r) {
                    return name(r->getValueAsDef("capability")) == capability &&
                           argument(r) == term;
                  });
  }
};
StringRef head(const Record *port) {
  return port->isSubClassOf("ZKC_Apply")
             ? name(port->getValueAsDef("constructor"))
             : StringRef{};
}
StringRef lifted(StringRef scalar) {
  return scalar == "field" ? "vector" : scalar == "group" ? "groups" : "";
}
void validateEndpoint(const Record *recipe, const Record *source,
                      const Record *target, ArrayRef<int64_t> order,
                      StringRef form, int mixedScalar = -1) {
  auto sourceInputs = source->getValueAsListOfDefs("inputs");
  auto sourceOutputs = source->getValueAsListOfDefs("outputs");
  auto inputs = target->getValueAsListOfDefs("inputs");
  auto outputs = target->getValueAsListOfDefs("outputs");
  auto map = recipe->getValueAsListOfInts("staticArguments");
  // These closed recipes have exactly one root. Derived scope terms (notably
  // G.Scalar) remain explicit and are compared recursively below.
  require(ArrayRef<int64_t>(map) == ArrayRef<int64_t>{0}, recipe,
          "recipe requires the source domain root mapping");
  Endpoint sourceTerms(recipe, source, source, map);
  Endpoint targetTerms(recipe, source, target, map);
  bool lanes = form == "Lanes";
  bool direct = form == "Direct";
  bool matrix = form == "MatrixRow" || form == "MatrixColumn";
  unsigned arity = direct ? 1 : 2;
  require(order.size() == arity && inputs.size() == arity + unsigned(matrix) &&
              outputs.size() == 1 && sourceOutputs.size() == 1 &&
              sourceInputs.size() == 2,
          recipe, "recipe endpoint arity mismatch");
  require(!direct || order == ArrayRef<int64_t>{0}, recipe,
          "direct reduction has exactly one semantic input role");
  require(!matrix || order == ArrayRef<int64_t>{0, 1}, recipe,
          "matrix recipe requires matrix then vector roles");
  require(name(target->getValueAsDef("parameters")) == "None", recipe,
          "recipe endpoint parameters unsupported");
  std::set<int64_t> used;
  for (auto [i, position] : enumerate(order)) {
    require(position >= 0 && size_t(position) < sourceInputs.size() &&
                used.insert(position).second,
            recipe, "recipe operand mapping must be a permutation");
    auto *scalar = sourceInputs[position];
    StringRef expected =
        int(i) == mixedScalar ? head(scalar) : lifted(head(scalar));
    if (matrix && i == 0)
      expected = "matrix";
    require(!expected.empty() && head(inputs[i]) == expected &&
                targetTerms.argument(inputs[i]) == sourceTerms.argument(scalar),
            recipe, "recipe endpoint input nominal type mismatch");
  }
  if (matrix)
    require(head(inputs.back()) == "index" &&
                inputs.back()->getValueAsListOfDefs("arguments").empty(),
            recipe, "recipe matrix index must follow collection operands");
  require(head(outputs[0]) == (lanes ? lifted(head(sourceOutputs[0]))
                                     : head(sourceOutputs[0])) &&
              targetTerms.argument(outputs[0]) ==
                  sourceTerms.argument(sourceOutputs[0]),
          recipe, "recipe endpoint result nominal type mismatch");
  for (const auto *requirement : source->getValueAsListOfDefs("requirements"))
    require(targetTerms.requirement(
                target, name(requirement->getValueAsDef("capability")),
                sourceTerms.argument(requirement)),
            recipe, "recipe endpoint missing source capability");
}
} // namespace
bool emitMathematicalRecipes(raw_ostream &os, const RecordKeeper &records) {
  validateContractDeclarations(records);
  auto lanes = records.getAllDerivedDefinitions("ZKC_LaneRecipe");
  auto reductions = records.getAllDerivedDefinitions("ZKC_ReductionRecipe");
  std::set<std::string> laneKeys, reductionKeys;
  for (const auto *r : lanes) {
    auto *source = r->getValueAsDef("source");
    auto *identity = meaning(source);
    require(identity && optional(identity, "laws"), r,
            "recipe source requires mathematical laws");
    auto *laws = identity->getValueAsDef("laws");
    require(laws->getValueAsBit("total"), r,
            "lane recipe requires total scalar meaning");
    auto order = r->getValueAsListOfInts("operands");
    validateEndpoint(r, source, r->getValueAsDef("target"), order, "Lanes");
    if (auto *mixed = optional(r, "mixed")) {
      require(laws->getValueAsBit("commutative") &&
                  r->getValueAsInt("scalarOperand") >= 0 &&
                  r->getValueAsInt("scalarOperand") < 2,
              r, "mixed lane recipe requires commutative scalar roles");
      validateEndpoint(r, source, mixed, order, "Lanes",
                       r->getValueAsInt("scalarOperand"));
    }
    require(laneKeys.insert(name(identity).str()).second, r,
            "duplicate lane recipe meaning");
  }
  for (const auto *r : reductions) {
    auto *source = r->getValueAsDef("source");
    auto *identity = meaning(source);
    require(identity && optional(identity, "laws"), r,
            "recipe source requires mathematical laws");
    auto *laws = identity->getValueAsDef("laws");
    require(laws->getValueAsBit("associative") &&
                laws->getValueAsBit("total") &&
                laws->getValueAsString("leftIdentity") != "None",
            r,
            "reduction recipe requires associative total combiner and empty "
            "identity");
    auto form = r->getValueAsString("kind");
    require(is_contained(ArrayRef<StringRef>{"Direct", "Contraction",
                                             "MatrixRow", "MatrixColumn"},
                         form),
            r, "unknown reduction recipe form");
    auto *term = optional(r, "term");
    require((form == "Direct") == !term, r, "reduction term and form mismatch");
    if (term) {
      auto *termIdentity = meaning(term);
      require(termIdentity && optional(termIdentity, "laws") &&
                  termIdentity->getValueAsDef("laws")->getValueAsBit("total"),
              r, "contraction term requires total scalar meaning");
      Endpoint sourceTerms(r, source, source, {0});
      Endpoint termTerms(r, source, term, {0});
      auto result = source->getValueAsListOfDefs("outputs")[0];
      auto termResult = term->getValueAsListOfDefs("outputs")[0];
      require(head(result) == head(termResult) &&
                  sourceTerms.argument(result) ==
                      termTerms.argument(termResult),
              r, "contraction term result differs from combiner domain");
    }
    auto *scalar = term ? term : source;
    validateEndpoint(r, scalar, r->getValueAsDef("endpoint"),
                     r->getValueAsListOfInts("operands"), form);
    auto staticInput = r->getValueAsInt("staticSourceOperand");
    auto inputs = scalar->getValueAsListOfDefs("inputs");
    require(form != "Direct" || staticInput == 0, r,
            "direct reduction static source must use its single input");
    require(staticInput >= 0 && size_t(staticInput) < inputs.size(), r,
            "recipe static source operand outside signature");
    Endpoint terms(r, scalar, scalar, {0});
    require(terms.argument(inputs[staticInput]) == "$0", r,
            "recipe static source must supply the nominal root, not an "
            "associated scalar");
    std::string key = (name(identity) + ":" + form).str();
    if (term)
      key += ":" + name(meaning(term)).str();
    require(reductionKeys.insert(key).second, r,
            "duplicate reduction recipe meaning");
  }
  os << "// Generated private realization associations. Do not edit.\n"
        "static const LaneRecipe laneRecipes[] = {\n";
  for (const auto *r : lanes) {
    auto *source = r->getValueAsDef("source");
    auto *mixed = optional(r, "mixed");
    auto order = r->getValueAsListOfInts("operands");
    os << "{MathematicalIdentity::" << name(meaning(source)) << ", \""
       << name(source) << "\", \"" << name(r->getValueAsDef("target"))
       << "\", \"" << (mixed ? name(mixed) : "") << "\", "
       << r->getValueAsInt("scalarOperand") << ", " << order[0] << ", "
       << order[1] << "},\n";
  }
  os << "};\nstatic const ReductionRecipe reductionRecipes[] = {\n";
  for (const auto *r : reductions) {
    auto *source = r->getValueAsDef("source");
    auto *term = optional(r, "term");
    auto order = r->getValueAsListOfInts("operands");
    os << "{MathematicalIdentity::" << name(meaning(source)) << ", ";
    if (term)
      os << "MathematicalIdentity::" << name(meaning(term));
    else
      os << "std::nullopt";
    os << ", ReductionForm::" << r->getValueAsString("kind") << ", \""
       << name(r->getValueAsDef("endpoint")) << "\", \"" << name(source)
       << "\", " << order[0] << ", " << (order.size() > 1 ? order[1] : 0)
       << ", " << r->getValueAsInt("staticSourceOperand")
       << ", protocol::ScalarIdentity::"
       << meaning(source)->getValueAsDef("laws")->getValueAsString(
              "leftIdentity")
       << "},\n";
  }
  os << "};\n";
  return false;
}
