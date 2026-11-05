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
Error typeKey(const Type &type, const NominalAuthority *authority,
              std::string &result) {
  raw_string_ostream out(result);
  auto frame = [&](StringRef value) { out << value.size() << ':' << value; };
  out << static_cast<unsigned>(type.kind) << ':';
  if (type.kind == Type::Kind::Natural) {
    frame(type.dimension.spelling());
    return Error::success();
  }
  out << type.symbolic << ':';
  if (type.kind == Type::Kind::Descriptor)
    out << static_cast<unsigned>(type.family) << ':';
  frame(type.domain);
  if (authority && !type.symbolic &&
      (type.kind == Type::Kind::Record ||
       type.kind == Type::Kind::LogicalRecord ||
       type.kind == Type::Kind::Variant || type.kind == Type::Kind::Module)) {
    auto revision = (*authority)(type.domain);
    if (!revision)
      return revision.takeError();
    frame(*revision ? StringRef(**revision) : StringRef());
  }
  if (type.kind == Type::Kind::Domain || type.kind == Type::Kind::Asset)
    frame(type.sort);
  frame(type.dimension.spelling());
  out << type.arguments.size() << ':';
  for (const auto &argument : type.arguments) {
    std::string nested;
    if (auto error = typeKey(argument, authority, nested))
      return error;
    frame(nested);
  }
  return Error::success();
}
} // namespace
std::string typeIdentity(const Type &type) {
  std::string result;
  cantFail(typeKey(type, nullptr, result));
  return result;
}
Expected<std::string> canonicalTypeKey(const Type &type,
                                       NominalAuthority authority) {
  const Limits limits;
  auto cost =
      typeComplexity(type, limits.typeNodes, limits.typeDepth, limits.work);
  if (!cost)
    return cost.takeError();
  std::string result;
  if (auto error = typeKey(type, &authority, result))
    return std::move(error);
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
Error checkDescriptorHead(const Type &type, bool contract) {
  using K = Type::Kind;
  if (contract && type.kind == K::Natural && !descriptorNatural(type))
    return error("source.descriptor", "invalid descriptor natural static");
  if (isDescriptor(type)) {
    if (!type.domain.empty() || !type.sort.empty() || type.symbolic ||
        type.dimension != Natural{} || !(type.assumptions == Permissions{}) ||
        type.family != DescriptorFamily::Finite)
      return error("source.descriptor", "foreign descriptor metadata");
    if (type.kind == K::Descriptor) {
      if (type.arguments.size() != 1 || isStaticOnly(type.arguments.front()))
        return error("source.descriptor", "invalid Finite contract");
    } else if (type.kind == K::DescriptorProduct) {
      for (const auto &child : type.arguments)
        if (!isDescriptor(child))
          return error("source.descriptor",
                       "product child is not a descriptor");
    } else {
      if ((type.arguments.size() != 1 && type.arguments.size() != 2) ||
          !isDescriptor(type.arguments.front()))
        return error("source.descriptor", "invalid sequence element contract");
      if (type.arguments.size() == 2 &&
          !descriptorNatural(type.arguments.back()))
        return error("source.descriptor", "invalid sequence extent term");
    }
  } else {
    for (const auto &child : type.arguments)
      if (isDescriptor(child))
        return error("source.descriptor",
                     "descriptor in ordinary type arguments");
  }
  return Error::success();
}
} // namespace
Expected<uint64_t> typeComplexity(const Type &type, uint64_t nodes,
                                  uint64_t depth, uint64_t work,
                                  TypeReplacement replacement, bool complete,
                                  TypeWork operation) {
  uint64_t cost = 0;
  auto charge = [&](uint64_t amount) {
    if (amount > work - cost)
      return false;
    cost += amount;
    return true;
  };
  std::function<Error(const Type &, uint64_t, bool, bool)> visit =
      [&](const Type &input, uint64_t level, bool replace,
          bool contract) -> Error {
    if (replace && replacement)
      if (const auto *selected = replacement(input))
        return visit(*selected, level, false, contract);
    const auto &term = input;
    contract |= isDescriptor(term);
    if (!nodes || level > depth)
      return error("source.limit", "expanded source type limit exceeded");
    --nodes;
    if (unsigned(term.kind) > unsigned(Type::Kind::DescriptorSequence))
      return error("source.type", "invalid source type kind");
    // Copying a Type does not construct a framed identity. Key construction
    // separately accounts for each ancestor copying the nested framing.
    const bool identity = operation == TypeWork::Identity;
    auto expanded = [&](uint64_t amount) {
      auto multiplier = identity ? level : 1;
      return amount <= (work - cost) / multiplier &&
             charge(amount * multiplier);
    };
    if (!expanded(identity ? 32 : 1) || !expanded(term.domain.size()) ||
        !expanded(term.sort.size()) ||
        (identity && (term.arguments.size() > (work - cost) / level / 22 ||
                      !expanded(term.arguments.size() * 22))) ||
        ((identity && !term.symbolic &&
          (term.kind == Type::Kind::Record ||
           term.kind == Type::Kind::LogicalRecord ||
           term.kind == Type::Kind::Variant ||
           term.kind == Type::Kind::Module)) &&
         !expanded(67)))
      return error("source.limit", "expanded type identity work exceeded");
    for (auto &[factors, coefficient] : term.dimension.terms()) {
      (void)coefficient;
      if (!expanded(identity ? 24 : 1))
        return error("source.limit", "natural identity work exceeded");
      for (auto &factor : factors)
        if (!expanded(identity ? 48 : 1) || !expanded(factor.name.size()) ||
            !expanded(factor.member.size()))
          return error("source.limit", "natural identity work exceeded");
    }
    for (auto &argument : term.arguments)
      if (auto e = visit(argument, level + 1, replace, contract))
        return e;
    return complete ? checkDescriptorHead(term, contract) : Error::success();
  };
  if (auto e = visit(type, 1, true, false))
    return std::move(e);
  return cost;
}

} // namespace zkc::language
