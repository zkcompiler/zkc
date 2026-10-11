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
void validateFieldEndpoint(const Record *recipe, const Record *source,
                           const Record *target, ArrayRef<StringRef> inputHeads,
                           StringRef outputHead) {
  auto mapping = recipe->getValueAsListOfInts("staticArguments");
  require(ArrayRef<int64_t>(mapping) == ArrayRef<int64_t>{0}, recipe,
          "recipe requires the source domain root mapping");
  Endpoint terms(recipe, source, target, mapping);
  auto inputs = target->getValueAsListOfDefs("inputs");
  auto outputs = target->getValueAsListOfDefs("outputs");
  require(inputs.size() == inputHeads.size() && outputs.size() == 1, recipe,
          "matrix contraction endpoint arity mismatch");
  require(name(target->getValueAsDef("parameters")) == "None", recipe,
          "recipe endpoint parameters unsupported");
  for (auto [input, expected] : zip(inputs, inputHeads))
    require(head(input) == expected && terms.argument(input) == "$0", recipe,
            "matrix contraction endpoint input nominal type mismatch");
  require(head(outputs[0]) == outputHead && terms.argument(outputs[0]) == "$0",
          recipe, "matrix contraction endpoint result nominal type mismatch");
  require(terms.requirement(target, "Field", "$0"), recipe,
          "matrix contraction endpoint requires the source field capability");
}
void validateMatrixContraction(const Record *recipe) {
  auto *source = recipe->getValueAsDef("source");
  auto *term = recipe->getValueAsDef("term");
  auto *combine = meaning(source);
  auto *product = meaning(term);
  require(combine && product && name(combine) == "FieldAdd" &&
              name(product) == "FieldMultiply" && optional(combine, "laws") &&
              optional(product, "laws"),
          recipe, "matrix contraction requires field sum and product meanings");
  auto *combineLaws = combine->getValueAsDef("laws");
  auto *productLaws = product->getValueAsDef("laws");
  for (const auto *laws : {combineLaws, productLaws})
    require(laws->getValueAsString("algebra") == "FieldRing" &&
                laws->getValueAsBit("associative") &&
                laws->getValueAsBit("commutative") &&
                laws->getValueAsBit("total"),
            recipe, "matrix contraction requires total commutative field laws");
  require(combineLaws->getValueAsString("leftIdentity") == "Zero" &&
              combineLaws->getValueAsString("rightIdentity") == "Zero" &&
              productLaws->getValueAsString("annihilator") == "Zero",
          recipe, "matrix contraction requires additive zero and annihilator");
  validateFieldEndpoint(recipe, source, source, {"field", "field"}, "field");
  validateFieldEndpoint(recipe, source, term, {"field", "field"}, "field");

  StringRef form = recipe->getValueAsString("kind");
  require(
      is_contained(ArrayRef<StringRef>{"Bilinear", "Rows", "Columns"}, form),
      recipe, "unknown matrix contraction form");
  bool bilinear = form == "Bilinear";
  auto order = recipe->getValueAsListOfInts("operands");
  unsigned arity = bilinear ? 3 : 2;
  std::set<int64_t> used;
  require(order.size() == arity, recipe,
          "matrix contraction operand mapping arity");
  for (auto position : order)
    require(position >= 0 && size_t(position) < arity &&
                used.insert(position).second,
            recipe, "recipe operand mapping must be a permutation");
  // Nominal types alone cannot distinguish left/right vector roles or the
  // two matvec orientations. The closed form ties these roles to the declared
  // endpoint interpretation, without redefining scalar law facets.
  require(ArrayRef<int64_t>(order) ==
              (bilinear ? ArrayRef<int64_t>{0, 1, 2} : ArrayRef<int64_t>{0, 1}),
          recipe,
          "matrix contraction requires matrix then ordered vector roles");
  auto free = recipe->getValueAsListOfInts("freeAxes");
  auto reduced = recipe->getValueAsListOfInts("reducedAxes");
  require(bilinear ? free.empty() &&
                         ArrayRef<int64_t>(reduced) == ArrayRef<int64_t>{0, 1}
                   : ArrayRef<int64_t>(free) ==
                             ArrayRef<int64_t>{form == "Rows" ? 0 : 1} &&
                         ArrayRef<int64_t>(reduced) ==
                             ArrayRef<int64_t>{form == "Rows" ? 1 : 0},
          recipe, "matrix contraction free and reduced axis roles mismatch");
  auto *target = recipe->getValueAsDef("endpoint");
  validateFieldEndpoint(recipe, source, target,
                        bilinear
                            ? ArrayRef<StringRef>{"matrix", "vector", "vector"}
                            : ArrayRef<StringRef>{"matrix", "vector"},
                        bilinear ? "field" : "vector");
  require(name(target) == (bilinear         ? "matrix.bilinear"
                           : form == "Rows" ? "matrix.mul_vector"
                                            : "matrix.transpose_mul_vector"),
          recipe, "matrix contraction endpoint does not implement axis roles");
  auto *seed = recipe->getValueAsDef("seedCombiner");
  validateFieldEndpoint(recipe, source, seed,
                        bilinear ? ArrayRef<StringRef>{"field", "field"}
                                 : ArrayRef<StringRef>{"vector", "vector"},
                        bilinear ? "field" : "vector");
  require(bilinear ? meaning(seed) == combine : name(seed) == "vector.add",
          recipe, "matrix contraction seed combiner meaning mismatch");
}
} // namespace
bool emitMathematicalRecipes(raw_ostream &os, const RecordKeeper &records) {
  validateContractDeclarations(records);
  auto lanes = records.getAllDerivedDefinitions("ZKC_LaneRecipe");
  auto reductions = records.getAllDerivedDefinitions("ZKC_ReductionRecipe");
  auto matrices =
      records.getAllDerivedDefinitions("ZKC_MatrixContractionRecipe");
  std::set<std::string> laneKeys, reductionKeys, matrixKeys;
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
  for (const auto *r : matrices) {
    validateMatrixContraction(r);
    auto key = (name(meaning(r->getValueAsDef("source"))) + ":" +
                name(meaning(r->getValueAsDef("term"))) + ":" +
                r->getValueAsString("kind"))
                   .str();
    require(matrixKeys.insert(key).second, r,
            "duplicate matrix contraction recipe meaning");
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
  os << "};\nstatic const MatrixContractionRecipe matrixContractionRecipes[] = "
        "{\n";
  for (const auto *r : matrices) {
    auto *source = r->getValueAsDef("source");
    auto order = r->getValueAsListOfInts("operands");
    os << "{MathematicalIdentity::" << name(meaning(source))
       << ", MathematicalIdentity::" << name(meaning(r->getValueAsDef("term")))
       << ", MatrixContractionForm::" << r->getValueAsString("kind") << ", \""
       << name(r->getValueAsDef("endpoint")) << "\", \""
       << name(r->getValueAsDef("seedCombiner")) << "\", {" << order[0] << ", "
       << order[1] << ", " << (order.size() == 3 ? order[2] : 0) << "}, "
       << order.size() << ", protocol::ScalarIdentity::"
       << meaning(source)->getValueAsDef("laws")->getValueAsString(
              "leftIdentity")
       << "},\n";
  }
  os << "};\n";
  return false;
}
