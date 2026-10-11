#include "Mathematical.h"
#include "Contributions.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
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
const Record *domain(const Record *port, StringRef head) {
  if (!port->isSubClassOf("ZKC_Apply") ||
      name(port->getValueAsDef("constructor")) != head)
    return nullptr;
  auto arguments = port->getValueAsListOfDefs("arguments");
  return arguments.size() == 1 ? arguments[0] : nullptr;
}
bool ground(const Record *port, StringRef head) {
  return port->isSubClassOf("ZKC_Apply") &&
         name(port->getValueAsDef("constructor")) == head &&
         port->getValueAsListOfDefs("arguments").empty();
}
bool hasRequirement(const Record *op, StringRef capability,
                    const Record *term) {
  return any_of(op->getValueAsListOfDefs("requirements"), [&](const Record *r) {
    auto arguments = r->getValueAsListOfDefs("arguments");
    return name(r->getValueAsDef("capability")) == capability &&
           arguments.size() == 1 && arguments[0] == term;
  });
}
bool associatedScalar(const Record *scalar, const Record *group) {
  return scalar && scalar->isSubClassOf("ZKC_Project") &&
         optional(scalar, "parent") == group &&
         name(scalar->getValueAsDef("member")) == "Scalar";
}
void validateLaws(const Record *laws) {
  auto family = laws->getValueAsString("algebra");
  auto shape = laws->getValueAsString("signature");
  bool field = family == "FieldRing";
  bool group = family == "GroupModule";
  bool access = family == "Access";
  bool binary = shape == "FieldBinary" || shape == "GroupBinary";
  bool action = shape == "GroupAction";
  require((field && (shape == "FieldConstant" || shape == "FieldBinary")) ||
              (group && (shape == "GroupBinary" || action)) ||
              (access && (shape == "ElementAccess" || shape == "MatrixAccess")),
          laws, "unknown mathematical signature law");
  for (auto role : {"leftIdentity", "rightIdentity", "annihilator"}) {
    auto identity = laws->getValueAsString(role);
    bool valid = identity == "None";
    if (field && binary)
      valid |= identity == "Zero" || identity == "One";
    if (group && binary && StringRef(role) != "annihilator")
      valid |= identity == "GroupIdentity";
    if (action && StringRef(role) == "rightIdentity")
      valid |= identity == "One";
    require(valid, laws, "scalar identity law has incompatible nominal role");
  }
  require(binary || (!laws->getValueAsBit("associative") &&
                     !laws->getValueAsBit("commutative")),
          laws, "reassociation laws require homogeneous binary ports");
  require(
      laws->getValueAsBit("scalarAction") == action, laws,
      "scalar action law requires ordered group and associated scalar ports");
  auto accessRule = laws->getValueAsString("access");
  require(accessRule == (shape == "ElementAccess"  ? "Element"
                         : shape == "MatrixAccess" ? "MatrixCell"
                                                   : "None"),
          laws, "access law signature mismatch");
  require(!access || !laws->getValueAsBit("total"), laws,
          "access equation cannot grant scalar totality or reassociation");
}
void emitLaws(raw_ostream &os, const Record *laws) {
  os << "{ComputationAlgebra::" << laws->getValueAsString("algebra");
  for (auto field : {"associative", "commutative", "total"})
    os << ", " << (laws->getValueAsBit(field) ? "true" : "false");
  for (auto field : {"leftIdentity", "rightIdentity", "annihilator"})
    os << ", ScalarIdentity::" << laws->getValueAsString(field);
  os << ", " << (laws->getValueAsBit("scalarAction") ? "true" : "false")
     << "}, ";
  auto access = laws->getValueAsString("access");
  if (access == "None")
    os << "std::nullopt";
  else
    os << "AccessRule::" << access;
}
} // namespace

void validateMathematicalFacet(const Record *op, const Record *facet) {
  const auto *identity = facet->getValueAsDef("identity");
  const auto *laws = optional(identity, "laws");
  require(laws, op, "mathematical attachment requires a signature law");
  validateLaws(laws);
  auto inputs = op->getValueAsListOfDefs("inputs");
  auto outputs = op->getValueAsListOfDefs("outputs");
  require(outputs.size() == 1, op, "mathematical result arity");
  auto shape = laws->getValueAsString("signature");
  bool group = shape == "GroupBinary" || shape == "GroupAction";
  auto *root = domain(outputs[0], group ? "group" : "field");
  require(root, op, "mathematical result nominal type");
  require(hasRequirement(op, group ? "ScalarAction" : "Field", root), op,
          "mathematical capability on exact nominal domain required");
  bool valid = false;
  if (shape == "FieldConstant") {
    valid = inputs.empty() &&
            name(op->getValueAsDef("parameters")) == "FieldLiteral" &&
            optional(op, "parameterField") == root;
  } else if (shape == "FieldBinary" || shape == "GroupBinary") {
    auto head = group ? "group" : "field";
    valid = inputs.size() == 2 && domain(inputs[0], head) == root &&
            domain(inputs[1], head) == root;
  } else if (shape == "GroupAction") {
    valid = inputs.size() == 2 && domain(inputs[0], "group") == root &&
            associatedScalar(domain(inputs[1], "field"), root);
  } else if (shape == "ElementAccess" || shape == "MatrixAccess") {
    bool matrix = shape == "MatrixAccess";
    valid = inputs.size() == (matrix ? 3u : 2u) &&
            domain(inputs[0], matrix ? "matrix" : "vector") == root &&
            ground(inputs[1], "index") &&
            (!matrix || ground(inputs[2], "index"));
  }
  require(valid, op,
          "mathematical signature nominal ports or associated scalar mismatch");
  if (shape != "FieldConstant")
    require(name(op->getValueAsDef("parameters")) == "None", op,
            "mathematical signature parameter mismatch");
}

void validateLinearFacet(const Record *op, const Record *facet) {
  bool diagonal = facet->isSubClassOf("ZKC_Diagonal");
  auto inputs = op->getValueAsListOfDefs("inputs");
  auto outputs = op->getValueAsListOfDefs("outputs");
  auto factors =
      facet->getValueAsInt(diagonal ? "factorsInput" : "coefficientsInput");
  auto values = facet->getValueAsInt("valuesInput");
  auto result = diagonal ? facet->getValueAsInt("resultOutput") : 0;
  require(inputs.size() == 2 && outputs.size() == 1, op,
          "linear facet requires two inputs and one result");
  require(result >= 0 && size_t(result) < outputs.size(), op,
          "linear facet result arity");
  auto *scalar = domain(inputs[factors], "vector");
  auto *field = domain(inputs[values], "vector");
  auto *group = domain(inputs[values], "groups");
  bool valid = field ? scalar == field &&
                           domain(outputs[result],
                                  diagonal ? "vector" : "field") == field &&
                           hasRequirement(op, "Field", field)
                     : group && associatedScalar(scalar, group) &&
                           domain(outputs[result],
                                  diagonal ? "groups" : "group") == group &&
                           hasRequirement(op, "ScalarAction", group);
  require(valid, op,
          "linear facet nominal ports or associated scalar mismatch");
}

void emitMathematicalFacet(raw_ostream &os, const Record *op,
                           const Record *facet) {
  auto *identity = facet->getValueAsDef("identity");
  os << "c.mathematical = ComputationContract{\"" << name(op)
     << "\", MathematicalIdentity::" << name(identity) << ", ";
  emitLaws(os, identity->getValueAsDef("laws"));
  os << "};\n";
}

bool emitMathematicalDeclarations(raw_ostream &os,
                                  const RecordKeeper &records) {
  DeclarationOrder order(records);
  auto identities = order.sort("ZKC_MathematicalIdentity");
  auto intrinsics = order.sort("ZKC_MathematicalIntrinsic");
  std::set<std::string> names;
  for (auto [i, identity] : enumerate(identities)) {
    auto key = name(identity);
    require(
        !key.empty() && isAlpha(key.front()) &&
            all_of(key, [](char c) { return isAlnum(c); }) &&
            names.insert(key.str()).second &&
            identity->getValueAsInt("ordinal") == int64_t(i),
        identity,
        "mathematical identities require unique names and contiguous ordinals");
    if (const auto *laws = optional(identity, "laws"))
      validateLaws(laws);
  }

  names.clear();
  for (auto [i, intrinsic] : enumerate(intrinsics))
    require(
        names.insert(name(intrinsic).str()).second &&
            intrinsic->getValueAsInt("ordinal") == int64_t(i) &&
            intrinsic->getValueAsInt("naturals") >= 0 &&
            is_contained(identities, intrinsic->getValueAsDef("identity")) &&
            is_contained(ArrayRef<StringRef>{"Boolean", "Index", "Collection",
                                             "Field", "Group"},
                         intrinsic->getValueAsString("domainKind")),
        intrinsic, "invalid mathematical intrinsic");
  os << "// Generated from neutral mathematical declarations. Do not edit.\n"
        "#ifdef ZKC_MATHEMATICAL_IDENTITIES\n"
        "enum class MathematicalIdentity {\n";
  for (const auto *identity : identities)
    os << name(identity) << " = " << identity->getValueAsInt("ordinal")
       << ",\n";
  os << "};\n#endif\n#ifdef ZKC_MATHEMATICAL_INTRINSICS\n"
        "llvm::StringRef mathematicalIdentityName(MathematicalIdentity "
        "identity) {\n"
        "switch (identity) {\n";
  for (const auto *identity : identities)
    os << "case MathematicalIdentity::" << name(identity) << ": return \""
       << name(identity) << "\";\n";
  os << "} return {}; }\n"
        "llvm::ArrayRef<MathematicalIntrinsic> mathematicalIntrinsics() {\n"
        "static const MathematicalIntrinsic values[] = {\n";
  for (const auto *intrinsic : intrinsics) {
    os << "{\"" << name(intrinsic) << "\", MathematicalIdentity::"
       << name(intrinsic->getValueAsDef("identity"))
       << ", MathematicalIntrinsic::Domain::"
       << intrinsic->getValueAsString("domainKind") << ", "
       << intrinsic->getValueAsInt("naturals");
    for (auto field : {"domainPoints", "scalar"})
      os << ", " << (intrinsic->getValueAsBit(field) ? "true" : "false");
    os << "},\n";
  }
  os << "}; return values; }\n#endif\n#ifdef ZKC_MATHEMATICAL_LAWS\n"
        "const MathematicalMeaning *mathematicalMeaning(MathematicalIdentity "
        "identity) {\n"
        "static const MathematicalMeaning values[] = {\n";
  for (const auto *identity : identities)
    if (const auto *laws = optional(identity, "laws")) {
      os << "{MathematicalIdentity::" << name(identity) << ", ";
      emitLaws(os, laws);
      os << "},\n";
    }
  os << "}; for (const auto &value : values) if (value.identity == identity) "
        "return &value; return nullptr; }\n#endif\n";
  return false;
}
