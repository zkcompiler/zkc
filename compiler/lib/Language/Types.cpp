#include "zkc/Language/Types.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Project.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
using namespace llvm;
namespace zkc::language {
Type domainType(StringRef sort, StringRef identity) {
  Type result(sort == "Field"   ? Type::Kind::Field
              : sort == "Group" ? Type::Kind::Group
                                : Type::Kind::Domain,
              identity.str());
  if (result.kind == Type::Kind::Domain)
    result.sort = sort.str();
  return result;
}
StringRef domainSort(const Type &type) {
  if (type.kind == Type::Kind::Field)
    return "Field";
  if (type.kind == Type::Kind::Group)
    return "Group";
  return type.kind == Type::Kind::Domain ? StringRef(type.sort) : StringRef();
}
bool isAssetSort(StringRef sort) { return sort == "Ring" || sort == "Bundle"; }
Type assetType(StringRef sort, StringRef identity) {
  assert(isAssetSort(sort) && "asset terms have a Ring or Bundle sort");
  Type result(Type::Kind::Asset, identity.str());
  result.sort = sort.str();
  return result;
}
StringRef assetSort(const Type &type) {
  return type.kind == Type::Kind::Asset ? StringRef(type.sort) : StringRef();
}
bool isDescriptor(const Type &type) {
  return type.kind == Type::Kind::Descriptor ||
         type.kind == Type::Kind::DescriptorProduct ||
         type.kind == Type::Kind::DescriptorSequence;
}
std::optional<DescriptorContract> descriptorContract(const Type &type) {
  if (!isDescriptor(type))
    return {};
  return DescriptorContract{type};
}
const Type &descriptorType(const DescriptorContract &contract) {
  return contract.type;
}
const Type *finiteDescriptorItem(const DescriptorContract &contract) {
  const auto &type = descriptorType(contract);
  return type.kind == Type::Kind::Descriptor &&
                 type.family == DescriptorFamily::Finite &&
                 type.arguments.size() == 1 && type.domain.empty() &&
                 type.sort.empty() && !type.symbolic &&
                 type.dimension == Natural{} &&
                 type.assumptions == Permissions{} &&
                 !isStaticOnly(type.arguments.front())
             ? &type.arguments.front()
             : nullptr;
}
bool isStaticOnly(const Type &type) {
  return isDescriptor(type) || type.kind == Type::Kind::Natural ||
         type.kind == Type::Kind::Module || type.kind == Type::Kind::Domain ||
         type.kind == Type::Kind::Asset || type.kind == Type::Kind::OracleKind;
}
bool isOracleHandle(const Type &type) {
  return type.kind == Type::Kind::Oracle ||
         type.kind == Type::Kind::OracleSequence;
}
bool isLogicalValue(const Type &type) {
  return isOracleHandle(type) || type.kind == Type::Kind::LogicalRecord ||
         ((type.kind == Type::Kind::Tuple || type.kind == Type::Kind::Array) &&
          llvm::any_of(type.arguments, [](const Type &child) {
            return isLogicalValue(child);
          }));
}
bool isLogicalValue(const PlacedType &type) {
  return isLogicalValue(type.type) ||
         (type.placement &&
          std::holds_alternative<ProductPlacement>(type.placement->value));
}
StringRef frontendTypeConstructor(const Type &type) {
  if (type.kind == Type::Kind::OracleKind)
    return type.domain == "table" ? "oracle.table" : "";
  // Structural heads are spelled by installed frontend constructor forms.
  // Descriptor family identity remains separate from logical value kinds.
  if (isOracleHandle(type) || isDescriptor(type))
    for (const auto &row : protocol::frontendConstructors())
      if (logicalHeadKind(row.form) == type.kind &&
          (!isDescriptor(type) || type.family == DescriptorFamily::Finite))
        return row.name;
  return {};
}
StringRef oracleConstructor(const Type &type) {
  return type.kind == Type::Kind::OracleKind || isOracleHandle(type)
             ? frontendTypeConstructor(type)
             : StringRef();
}
StringRef typeKindName(Type::Kind kind) {
  switch (kind) {
  case Type::Kind::DescriptorProduct:
    return "descriptor_product";
  case Type::Kind::DescriptorSequence:
    return "descriptor_sequence";
  case Type::Kind::Descriptor:
    return "descriptor";
  case Type::Kind::Boolean:
    return "boolean";
  case Type::Kind::Field:
    return "field";
  case Type::Kind::Group:
    return "group";
  case Type::Kind::Index:
    return "index";
  case Type::Kind::Unit:
    return "unit";
  case Type::Kind::Tuple:
    return "tuple";
  case Type::Kind::Array:
    return "array";
  case Type::Kind::Record:
    return "record";
  case Type::Kind::LogicalRecord:
    return "logical_record";
  case Type::Kind::Variant:
    return "variant";
  case Type::Kind::Parameter:
    return "parameter";
  case Type::Kind::Associated:
    return "associated";
  case Type::Kind::Natural:
    return "natural";
  case Type::Kind::Module:
    return "module";
  case Type::Kind::Builtin:
    return "builtin";
  case Type::Kind::Formal:
    return "formal";
  case Type::Kind::Domain:
    return "domain";
  case Type::Kind::Asset:
    return "asset";
  case Type::Kind::OracleKind:
    return "oracle_kind";
  case Type::Kind::Oracle:
    return "oracle";
  case Type::Kind::OracleSequence:
    return "oracle_sequence";
  case Type::Kind::OracleProjection:
    return "oracle_projection";
  }
  llvm_unreachable("unknown source type kind");
}

std::string spelling(const Type &type) {
  using K = Type::Kind;
  switch (type.kind) {
  case K::DescriptorProduct:
  case K::DescriptorSequence: {
    // Diagnostic notation only; neither head installs a source constructor.
    std::string result = typeKindName(type.kind).str() + "(";
    for (unsigned i = 0; i < type.arguments.size(); ++i) {
      if (i)
        result += ", ";
      result += spelling(type.arguments[i]);
    }
    return result + ")";
  }
  case K::Boolean:
    return "bool";
  case K::Index:
    return "index";
  case K::Unit:
    return "()";
  case K::Natural:
    return type.dimension.spelling();
  default:
    break;
  }
  if ((type.kind == K::Domain || type.kind == K::Asset) && !type.symbolic)
    return StringRef(type.sort).lower() + "<" + type.domain + ">";
  if (type.kind == K::Builtin || type.kind == K::Formal ||
      (!type.symbolic && !frontendTypeConstructor(type).empty())) {
    std::string result =
        std::string(type.kind == K::Formal ? "formal(\"" : "builtin(\"") +
        (frontendTypeConstructor(type).empty()
             ? type.domain
             : frontendTypeConstructor(type).str()) +
        "\"";
    for (const auto &argument : type.arguments)
      result += ", " + spelling(argument);
    return result + ")";
  }
  if (type.kind == K::OracleProjection && type.arguments.size() == 1)
    return spelling(type.arguments.front()) + "::" + type.domain;
  if (type.kind == K::Array)
    return "[" + spelling(type.arguments.front()) + "; " +
           type.dimension.spelling() + "]";
  std::string result =
      type.kind == K::Tuple                     ? "("
      : type.kind == K::Field && !type.symbolic ? "field<" + type.domain + ">"
      : type.kind == K::Group && !type.symbolic ? "group<" + type.domain + ">"
                                                : type.domain;
  if (!type.arguments.empty()) {
    if (type.kind != K::Tuple)
      result += "<";
    for (unsigned i = 0; i < type.arguments.size(); ++i) {
      if (i)
        result += ", ";
      result += spelling(type.arguments[i]);
    }
    if (type.kind == K::Tuple && type.arguments.size() == 1)
      result += ",";
    result += type.kind == K::Tuple ? ")" : ">";
  }
  return result;
}
namespace {
// The plan borrows each Type head and owns only Natural/authority text.
// Subtree byte lengths are measured without materializing recursive strings.
struct KeyHead {
  const Type *type;
  std::string dimension;
  std::optional<std::string> revision;
  size_t size = 0;
};
size_t decimalWidth(size_t value) {
  size_t width = 1;
  while (value >= 10) {
    value /= 10;
    ++width;
  }
  return width;
}
size_t framedSize(StringRef value) {
  return decimalWidth(value.size()) + 1 + value.size();
}
Error typeKey(const Type &type, const NominalAuthority *authority,
              std::string &result, bool framed = false) {
  std::vector<KeyHead> heads;
  std::function<Expected<size_t>(const Type &)> measure =
      [&](const Type &term) -> Expected<size_t> {
    size_t index = heads.size();
    KeyHead head{&term, term.dimension.spelling(), {}, 0};
    size_t size = decimalWidth(unsigned(term.kind)) + 1;
    if (term.kind == Type::Kind::Natural) {
      size += framedSize(head.dimension);
    } else {
      size += 2 + framedSize(term.domain) + framedSize(head.dimension) +
              decimalWidth(term.arguments.size()) + 1;
      if (term.kind == Type::Kind::Descriptor)
        size += decimalWidth(unsigned(term.family)) + 1;
      if (term.kind == Type::Kind::Domain || term.kind == Type::Kind::Asset)
        size += framedSize(term.sort);
      if (authority && !term.symbolic &&
          (term.kind == Type::Kind::Record ||
           term.kind == Type::Kind::LogicalRecord ||
           term.kind == Type::Kind::Variant ||
           term.kind == Type::Kind::Module)) {
        auto revision = (*authority)(term.domain);
        if (!revision)
          return revision.takeError();
        if (*revision && (**revision).size() != 64)
          return error("source.authority",
                       "nominal authority must have 64 bytes");
        // Presence distinguishes an empty generated-authority frame from a
        // node that has no authority frame at all.
        head.revision = *revision ? std::move(**revision) : std::string{};
        size += framedSize(*head.revision);
      }
    }
    heads.push_back(std::move(head));
    if (term.kind != Type::Kind::Natural)
      for (const auto &argument : term.arguments) {
        auto child = measure(argument);
        if (!child)
          return child.takeError();
        size += decimalWidth(*child) + 1 + *child;
      }
    heads[index].size = size;
    return size;
  };
  auto size = measure(type);
  if (!size)
    return size.takeError();
  auto before = result.size();
  auto outer = framed ? 8 : 0;
  result.reserve(before + outer + *size);
  if (framed) {
    uint64_t bytes = *size;
    for (unsigned i = 0; i < 8; ++i)
      result.push_back(static_cast<char>(bytes >> (8 * i)));
  }
  raw_string_ostream out(result);
  auto frame = [&](StringRef value) { out << value.size() << ':' << value; };
  for (size_t i = 0; i < heads.size(); ++i) {
    const auto &head = heads[i];
    const auto &term = *head.type;
    if (i)
      out << head.size << ':';
    out << unsigned(term.kind) << ':';
    if (term.kind == Type::Kind::Natural) {
      frame(head.dimension);
      continue;
    }
    out << term.symbolic << ':';
    if (term.kind == Type::Kind::Descriptor)
      out << unsigned(term.family) << ':';
    frame(term.domain);
    if (head.revision)
      frame(*head.revision);
    if (term.kind == Type::Kind::Domain || term.kind == Type::Kind::Asset)
      frame(term.sort);
    frame(head.dimension);
    out << term.arguments.size() << ':';
  }
  assert(result.size() == before + outer + *size);
  return Error::success();
}
} // namespace
std::string typeIdentity(const Type &type) {
  std::string result;
  cantFail(typeKey(type, nullptr, result));
  return result;
}
void frameTypeIdentity(std::string &result, const Type &type) {
  cantFail(typeKey(type, nullptr, result, /*framed=*/true));
}
Expected<std::string> canonicalTypeKey(const Type &type,
                                       NominalAuthority authority) {
  const Limits limits;
  return canonicalTypeKey(type, authority, limits, limits.work,
                          [](uint64_t) { return Error::success(); });
}
Expected<std::string> canonicalTypeKey(const Type &type,
                                       NominalAuthority authority,
                                       const Limits &limits, uint64_t remaining,
                                       TypeWorkCharge charge) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  auto cost = typeComplexity(type, limits.typeNodes, limits.typeDepth,
                             std::min(remaining, limits.work), nullptr, true,
                             TypeWork::CanonicalIdentity);
  if (!cost)
    return cost.takeError();
  if (auto e = charge(*cost))
    return std::move(e);
  std::string result;
  if (auto e = typeKey(type, &authority, result))
    return std::move(e);
  return result;
}

namespace {
bool descriptorNatural(const Type &term) {
  // Natural equality and keys intentionally use the normalized polynomial.
  // No ignored candidate metadata may hide typed statics in a contract.
  return term.kind == Type::Kind::Natural && term.arguments.empty() &&
         term.sort.empty() && term.assumptions == Permissions{} &&
         term.family == DescriptorFamily::Finite &&
         term.symbolic == !term.dimension.isClosed() &&
         (term.domain.empty() ||
          (term.symbolic && term.dimension.terms().size() == 1 &&
           term.dimension.terms().begin()->second == 1 &&
           term.dimension.terms().begin()->first.size() == 1 &&
           term.dimension.terms().begin()->first.front().kind ==
               Natural::Factor::Kind::Atom &&
           term.dimension.terms().begin()->first.front().name == term.domain));
}
Error checkDescriptorHead(const Type &type, bool contract,
                          TypeReplacement replacement = nullptr) {
  auto selected = [&](const Type &child) -> const Type & {
    if (replacement)
      if (const auto *value = replacement(child))
        return *value;
    return child;
  };
  using K = Type::Kind;
  if (contract && type.kind == K::Natural && !descriptorNatural(type))
    return error("source.descriptor", "invalid descriptor natural static");
  if (contract && !isDescriptor(type) && type.kind != K::Natural) {
    const bool structural = type.kind == K::Boolean || type.kind == K::Index ||
                            type.kind == K::Unit || type.kind == K::Tuple ||
                            type.kind == K::Array;
    const bool scalar = type.kind == K::Boolean || type.kind == K::Index ||
                        type.kind == K::Unit;
    if ((type.kind != K::Domain && type.kind != K::Asset &&
         !type.sort.empty()) ||
        type.family != DescriptorFamily::Finite ||
        (structural && (!type.domain.empty() || type.symbolic)) ||
        (scalar && !type.arguments.empty()) ||
        (type.kind == K::Array && type.arguments.size() != 1) ||
        (type.kind != K::Array && type.dimension != Natural{}) ||
        ((type.kind == K::Field || type.kind == K::Group ||
          type.kind == K::Domain || type.kind == K::Asset) &&
         !type.symbolic && !type.arguments.empty()) ||
        ((type.kind == K::Oracle || type.kind == K::OracleSequence) &&
         (!type.domain.empty() || type.symbolic)))
      return error("source.descriptor", "foreign ordinary descriptor metadata");
  }
  if (isDescriptor(type)) {
    if (!type.domain.empty() || !type.sort.empty() || type.symbolic ||
        type.dimension != Natural{} || !(type.assumptions == Permissions{}) ||
        type.family != DescriptorFamily::Finite)
      return error("source.descriptor", "foreign descriptor metadata");
    if (type.kind == K::Descriptor) {
      if (type.arguments.size() != 1 ||
          isStaticOnly(selected(type.arguments.front())))
        return error("source.descriptor", "invalid Finite contract");
    } else if (type.kind == K::DescriptorProduct) {
      for (const auto &child : type.arguments)
        if (!isDescriptor(selected(child)))
          return error("source.descriptor",
                       "product child is not a descriptor");
    } else {
      if ((type.arguments.size() != 1 && type.arguments.size() != 2) ||
          !isDescriptor(selected(type.arguments.front())))
        return error("source.descriptor", "invalid sequence element contract");
      if (type.arguments.size() == 2 &&
          !descriptorNatural(selected(type.arguments.back())))
        return error("source.descriptor", "invalid sequence extent term");
    }
  } else {
    for (const auto &child : type.arguments)
      if (isDescriptor(selected(child)))
        return error("source.descriptor",
                     "descriptor in ordinary type arguments");
  }
  return Error::success();
}
} // namespace
Expected<uint64_t> typeComplexity(const Type &type, uint64_t nodes,
                                  uint64_t depth, uint64_t work,
                                  TypeReplacement replacement, bool complete,
                                  TypeWork operation,
                                  TypeComparison *comparison) {
  uint64_t cost = 0;
  auto charge = [&](uint64_t amount) {
    if (amount > work - cost)
      return false;
    cost += amount;
    return true;
  };
  std::function<Expected<uint64_t>(const Type &, uint64_t, bool, bool,
                                   const Type *)>
      visit = [&](const Type &input, uint64_t level, bool replace,
                  bool contract, const Type *expected) -> Expected<uint64_t> {
    if (replace && replacement)
      if (const auto *selected = replacement(input))
        return visit(*selected, level, false, contract, expected);
    const auto &term = input;
    contract |= isDescriptor(term);
    if (!nodes || level > depth)
      return error("source.limit", "expanded source type limit exceeded");
    --nodes;
    if (unsigned(term.kind) > unsigned(Type::Kind::DescriptorSequence))
      return error("source.type", "invalid source type kind");
    const bool identity = operation != TypeWork::Copy;
    // Copy pays for retained metadata once. The linear key writer pays for
    // its head plan/traversals, each output byte and auxiliary Natural text.
    // Measure decimal widths from the actual values before any allocation.
    if (!charge(identity ? 4 : 1) || !charge(term.domain.size()) ||
        !charge(term.sort.size()))
      return error("source.limit", "expanded type work exceeded");
    auto compareHead = [&] {
      if (expected && comparison->equal &&
          (term.kind != expected->kind || term.family != expected->family ||
           term.domain != expected->domain || term.sort != expected->sort ||
           term.symbolic != expected->symbolic ||
           !(term.assumptions == expected->assumptions) ||
           term.dimension != expected->dimension ||
           term.arguments.size() != expected->arguments.size()))
        comparison->equal = false;
    };
    auto expectedChild = [&](unsigned index) -> const Type * {
      return expected && comparison->equal ? &expected->arguments[index]
                                           : nullptr;
    };
    if (!identity) {
      for (const auto &[factors, coefficient] : term.dimension.terms()) {
        (void)coefficient;
        if (!charge(1))
          return error("source.limit", "natural copy work exceeded");
        for (const auto &factor : factors)
          if (!charge(1) || !charge(factor.name.size()) ||
              !charge(factor.member.size()))
            return error("source.limit", "natural copy work exceeded");
      }
      compareHead();
      for (unsigned i = 0; i < term.arguments.size(); ++i) {
        auto child = visit(term.arguments[i], level + 1, replace, contract,
                           expectedChild(i));
        if (!child)
          return child.takeError();
      }
      if (complete)
        if (auto e = checkDescriptorHead(term, contract,
                                         replace ? replacement : nullptr))
          return std::move(e);
      return 0;
    }
    // Static export also emits textual tags/JSON nodes and validates its
    // output.
    if (operation == TypeWork::StaticExport && !charge(32))
      return error("source.limit", "static export framing work exceeded");
    uint64_t dimensionSize = term.dimension.terms().empty() ? 1 : 0;
    bool first = true;
    for (const auto &[factors, coefficient] : term.dimension.terms()) {
      uint64_t width = decimalWidth(coefficient) + (first ? 0 : 1);
      first = false;
      if (!charge(identity ? 2 * width : 1))
        return error("source.limit", "natural identity work exceeded");
      dimensionSize += width;
      for (const auto &factor : factors) {
        width = 2 + decimalWidth(factor.name.size()) + 1 + factor.name.size();
        if (factor.kind == Natural::Factor::Kind::Projection)
          width +=
              decimalWidth(factor.member.size()) + 1 + factor.member.size();
        if (!charge(identity ? width : 1) ||
            !charge(identity ? width : factor.name.size()) ||
            !charge(identity ? 0 : factor.member.size()))
          return error("source.limit", "natural identity work exceeded");
        dimensionSize += width;
      }
    }
    if (identity && term.dimension.terms().empty() && !charge(2))
      return error("source.limit", "natural identity work exceeded");
    uint64_t size = decimalWidth(unsigned(term.kind)) + 1;
    auto frameSize = [](uint64_t n) { return decimalWidth(n) + 1 + n; };
    if (term.kind == Type::Kind::Natural) {
      size += frameSize(dimensionSize);
      if (identity && !charge(size - dimensionSize))
        return error("source.limit", "natural key framing work exceeded");
      // Natural keys omit domain/sort. Their metadata remains bounded above.
    } else {
      size += 2 + frameSize(term.domain.size()) + frameSize(dimensionSize) +
              decimalWidth(term.arguments.size()) + 1;
      if (term.kind == Type::Kind::Descriptor)
        size += decimalWidth(unsigned(term.family)) + 1;
      bool sorted =
          term.kind == Type::Kind::Domain || term.kind == Type::Kind::Asset;
      if (sorted)
        size += frameSize(term.sort.size());
      if (identity && !charge(size - term.domain.size() - dimensionSize -
                              (sorted ? term.sort.size() : 0)))
        return error("source.limit", "type key framing work exceeded");
      if (operation == TypeWork::CanonicalIdentity && !term.symbolic &&
          (term.kind == Type::Kind::Record ||
           term.kind == Type::Kind::LogicalRecord ||
           term.kind == Type::Kind::Variant ||
           term.kind == Type::Kind::Module)) {
        // The callback can supply 64 bytes or an empty generated frame. Bound
        // the larger frame and its separately owned callback result.
        if (!charge(134))
          return error("source.limit", "nominal authority work exceeded");
        size += 67;
      }
    }
    compareHead();
    for (unsigned i = 0; i < term.arguments.size(); ++i) {
      auto child = visit(term.arguments[i], level + 1, replace, contract,
                         expectedChild(i));
      if (!child)
        return child.takeError();
      auto prefix = decimalWidth(*child) + 1;
      if (identity && !charge(prefix))
        return error("source.limit", "nested key framing work exceeded");
      size += prefix + *child;
    }
    if (complete)
      if (auto e = checkDescriptorHead(term, contract,
                                       replace ? replacement : nullptr))
        return std::move(e);
    return size;
  };
  auto size =
      visit(type, 1, true, false, comparison ? &comparison->expected : nullptr);
  if (!size)
    return size.takeError();
  // Both raw keys and keys framed directly into a destination share this
  // bound. The optional outer frame never requires a temporary whole key.
  if (operation != TypeWork::Copy && !charge(8))
    return error("source.limit", "outer key framing work exceeded");
  return cost;
}

} // namespace zkc::language
