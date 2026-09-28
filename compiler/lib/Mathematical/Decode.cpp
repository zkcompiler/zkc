#include "zkc/Mathematical/Codec.h"
#include "zkc/Mathematical/Raw.h"
#include "zkc/Support/Refusal.h"
#include <initializer_list>

using namespace llvm;
namespace zkc::mathematical::raw {
namespace {

// The canonical value boundary has already bounded recursion and allocation.
// This reader records the first shape failure and never indexes unchecked data.
class Reader {
  std::string failure;
  const json::Value absent = nullptr;
  const json::Array empty;

  void fail(StringRef code = "math-schema") {
    if (failure.empty())
      failure = code.str();
  }
  const json::Array &array(const json::Value &value) {
    if (auto result = value.getAsArray())
      return *result;
    fail();
    return empty;
  }
  const json::Value &at(const json::Array &array, size_t index) {
    if (index < array.size())
      return array[index];
    fail();
    return absent;
  }
  const json::Value &field(const json::Value &value, StringRef key) {
    if (auto object = value.getAsObject())
      if (auto result = object->get(key))
        return *result;
    fail();
    return absent;
  }
  void record(const json::Value &value, std::initializer_list<StringRef> keys) {
    auto object = value.getAsObject();
    if (!object || object->size() != keys.size()) {
      fail();
      return;
    }
    for (auto key : keys)
      if (!object->get(key))
        fail();
  }
  void size(const json::Array &value, size_t expected) {
    if (value.size() != expected)
      fail();
  }
  uint64_t natural(const json::Value &value) {
    if (auto number = value.getAsUINT64())
      return *number;
    fail("math-natural");
    return 0;
  }
  std::string string(const json::Value &value) {
    if (auto text = value.getAsString())
      return text->str();
    fail();
    return {};
  }
  template <class T> T reference(const json::Value &value) {
    return T{natural(value)};
  }
  template <class F>
  auto list(const json::Value &value, F read)
      -> std::vector<decltype(read(value))> {
    std::vector<decltype(read(value))> result;
    for (const auto &item : array(value)) {
      if (!failure.empty())
        break;
      result.push_back(read(item));
    }
    return result;
  }
  template <class T> std::vector<T> references(const json::Value &value) {
    return list(value, [&](const auto &item) { return reference<T>(item); });
  }
  Static term(const json::Value &value) {
    const auto &items = array(value);
    auto tag = string(at(items, 0));
    if (tag == "literal" || tag == "parameter") {
      size(items, 2);
      auto n = natural(at(items, 1));
      return tag == "literal" ? Static::literal(n) : Static::parameter(n);
    }
    if (tag == "add" || tag == "multiply") {
      size(items, 3);
      auto left = term(at(items, 1)), right = term(at(items, 2));
      return tag == "add" ? Static::add(std::move(left), std::move(right))
                          : Static::multiply(std::move(left), std::move(right));
    }
    if (tag == "pow2") {
      size(items, 2);
      return Static::pow2(term(at(items, 1)));
    }
    fail();
    return Static::literal(0);
  }
  std::vector<Static> statics(const json::Value &value) {
    return list(value, [&](const auto &item) { return term(item); });
  }
  TypeUse use(const json::Value &value) {
    record(value, {"type", "statics"});
    return {reference<TypeRef>(field(value, "type")),
            statics(field(value, "statics"))};
  }
  std::vector<TypeUse> uses(const json::Value &value) {
    return list(value, [&](const auto &item) { return use(item); });
  }
  Type type(const json::Value &value) {
    const auto &items = array(value);
    auto tag = string(at(items, 0));
    if (tag == "nominal") {
      size(items, 4);
      return NominalType{reference<DomainRef>(at(items, 1)),
                         string(at(items, 2)), statics(at(items, 3))};
    }
    if (tag == "product") {
      size(items, 2);
      return ProductType{uses(at(items, 1))};
    }
    if (tag == "fin") {
      size(items, 2);
      return FinType{term(at(items, 1))};
    }
    if (tag == "vector") {
      size(items, 3);
      return VectorType{use(at(items, 1)), term(at(items, 2))};
    }
    if (tag == "polynomial" || tag == "residual") {
      size(items, tag == "polynomial" ? 5 : 4);
      auto domain = reference<DomainRef>(at(items, 1));
      auto arity = term(at(items, 2)), degree = term(at(items, 3));
      if (tag == "residual")
        return ResidualType{domain, std::move(arity), std::move(degree)};
      auto convention = string(at(items, 4));
      if (convention != "individual" && convention != "total")
        fail();
      return PolynomialType{domain, std::move(arity), std::move(degree),
                            convention == "individual"
                                ? PolynomialType::Degree::Individual
                                : PolynomialType::Degree::Total};
    }
    fail();
    return ProductType{};
  }
  Identity identity(const json::Value &value) {
    record(value, {"name", "version", "digest"});
    return {string(field(value, "name")), string(field(value, "version")),
            string(field(value, "digest"))};
  }
  Manifest manifest(const json::Value &value) {
    record(value, {"domains", "operations", "wires", "services", "laws"});
    auto read = [&](const auto &item) { return identity(item); };
    return {list(field(value, "domains"), read),
            list(field(value, "operations"), read),
            list(field(value, "wires"), read),
            list(field(value, "services"), read),
            list(field(value, "laws"), read)};
  }
  CapabilityUse capabilityUse(const json::Value &value) {
    record(value, {"type", "statics"});
    return {reference<CapabilityTypeRef>(field(value, "type")),
            statics(field(value, "statics"))};
  }
  template <class T> T permission(const json::Value &value) {
    record(value, {"signature", "roles"});
    return {capabilityUse(field(value, "signature")),
            references<Role>(field(value, "roles"))};
  }
  CapabilityType capabilityType(const json::Value &value) {
    record(value, {"identity", "statics", "arguments", "result"});
    return {reference<ServiceRef>(field(value, "identity")),
            natural(field(value, "statics")), uses(field(value, "arguments")),
            use(field(value, "result"))};
  }
  Port port(const json::Value &value) {
    record(value, {"roles", "type"});
    return {references<Role>(field(value, "roles")), use(field(value, "type"))};
  }
  std::vector<Port> ports(const json::Value &value) {
    return list(value, [&](const auto &item) { return port(item); });
  }
  Operation operation(const json::Value &value) {
    record(value, {"identity", "statics", "capabilities", "arguments", "result",
                   "purity", "distinct"});
    auto purity = string(field(value, "purity"));
    if (purity != "total" && purity != "ordered")
      fail();
    return {reference<OperationIdentityRef>(field(value, "identity")),
            natural(field(value, "statics")),
            list(field(value, "capabilities"),
                 [&](const auto &item) { return capabilityUse(item); }),
            uses(field(value, "arguments")),
            use(field(value, "result")),
            purity == "total" ? Operation::Purity::Total
                              : Operation::Purity::Ordered,
            list(field(value, "distinct"), [&](const auto &item) {
              const auto &pair = array(item);
              size(pair, 2);
              return std::make_pair(natural(at(pair, 0)), natural(at(pair, 1)));
            })};
  }
  Wire wire(const json::Value &value) {
    record(value, {"identity", "statics", "type"});
    return {reference<WireIdentityRef>(field(value, "identity")),
            natural(field(value, "statics")), use(field(value, "type"))};
  }
  PureNode node(const json::Value &value) {
    const auto &items = array(value);
    auto tag = string(at(items, 0));
    if (tag == "operation") {
      size(items, 5);
      return PureOperation{reference<OperationRef>(at(items, 1)),
                           statics(at(items, 2)), at(items, 3),
                           references<RegionRef>(at(items, 4))};
    }
    if (tag == "tuple") {
      size(items, 2);
      return Tuple{references<RegionRef>(at(items, 1))};
    }
    if (tag == "project") {
      size(items, 3);
      return Project{reference<RegionRef>(at(items, 1)), natural(at(items, 2))};
    }
    if (tag == "map") {
      size(items, 3);
      return Map{term(at(items, 1)),
                 std::make_shared<const Region>(region(at(items, 2)))};
    }
    if (tag == "fold") {
      size(items, 4);
      return Fold{term(at(items, 1)), references<RegionRef>(at(items, 2)),
                  std::make_shared<const Region>(region(at(items, 3)))};
    }
    fail();
    return Tuple{};
  }
  Region region(const json::Value &value) {
    record(value, {"captures", "nodes", "outputs"});
    return {references<ValueRef>(field(value, "captures")),
            list(field(value, "nodes"),
                 [&](const auto &item) { return node(item); }),
            references<RegionRef>(field(value, "outputs"))};
  }
  Relation relation(const json::Value &value) {
    record(value, {"statics", "public", "witness", "assumptions", "body"});
    return {natural(field(value, "statics")), uses(field(value, "public")),
            uses(field(value, "witness")),
            references<LawRef>(field(value, "assumptions")),
            region(field(value, "body"))};
  }
  RelationBinding relationBinding(const json::Value &value) {
    record(value, {"relation", "statics", "public", "witness"});
    return {reference<RelationRef>(field(value, "relation")),
            statics(field(value, "statics")),
            references<ValueRef>(field(value, "public")),
            references<ValueRef>(field(value, "witness"))};
  }
  Step step(const json::Value &value) {
    const auto &items = array(value);
    auto tag = string(at(items, 0));
    if (tag == "pure") {
      size(items, 2);
      return Pure{region(at(items, 1))};
    }
    auto site = natural(at(items, 1));
    if (tag == "local") {
      size(items, 8);
      return Local{site,
                   reference<Role>(at(items, 2)),
                   reference<OperationRef>(at(items, 3)),
                   statics(at(items, 4)),
                   at(items, 5),
                   references<CapabilityPortRef>(at(items, 6)),
                   references<ValueRef>(at(items, 7))};
    }
    if (tag == "query") {
      size(items, 5);
      return Query{site, reference<Role>(at(items, 2)),
                   reference<CapabilityPortRef>(at(items, 3)),
                   references<ValueRef>(at(items, 4))};
    }
    if (tag == "guard") {
      size(items, 4);
      return Guard{site, reference<Role>(at(items, 2)),
                   reference<ValueRef>(at(items, 3))};
    }
    if (tag == "message") {
      size(items, 7);
      return Message{site,
                     reference<WireRef>(at(items, 2)),
                     statics(at(items, 3)),
                     reference<Role>(at(items, 4)),
                     reference<Role>(at(items, 5)),
                     reference<ValueRef>(at(items, 6))};
    }
    if (tag == "invoke") {
      size(items, 7);
      return Invoke{site,
                    reference<DefinitionRef>(at(items, 2)),
                    statics(at(items, 3)),
                    references<Role>(at(items, 4)),
                    references<CapabilityPortRef>(at(items, 5)),
                    references<ValueRef>(at(items, 6))};
    }
    if (tag == "repeat") {
      size(items, 7);
      return Repeat{site,
                    term(at(items, 2)),
                    ports(at(items, 3)),
                    references<ValueRef>(at(items, 4)),
                    references<ValueRef>(at(items, 5)),
                    std::make_shared<const Body>(body(at(items, 6)))};
    }
    fail();
    return Pure{};
  }
  std::variant<Return, Stop> terminal(const json::Value &value) {
    const auto &items = array(value);
    auto tag = string(at(items, 0));
    if (tag == "return") {
      size(items, 2);
      return Return{references<ValueRef>(at(items, 1))};
    }
    if (tag == "stop") {
      size(items, 4);
      auto reason = string(at(items, 3));
      StopReason stop = StopReason::Refused;
      if (reason == "reject")
        stop = StopReason::Reject;
      else if (reason == "abort")
        stop = StopReason::Abort;
      else if (reason == "exhausted")
        stop = StopReason::Exhausted;
      else if (reason == "incomplete")
        stop = StopReason::Incomplete;
      else if (reason != "refused")
        fail();
      return Stop{natural(at(items, 1)), reference<Role>(at(items, 2)), stop};
    }
    fail();
    return Return{};
  }
  Body body(const json::Value &value) {
    record(value, {"steps", "terminal"});
    return {list(field(value, "steps"),
                 [&](const auto &item) { return step(item); }),
            terminal(field(value, "terminal"))};
  }
  Definition definition(const json::Value &value) {
    record(value, {"statics", "roles", "capabilities", "arguments", "results",
                   "relations", "body"});
    return {natural(field(value, "statics")),
            natural(field(value, "roles")),
            list(field(value, "capabilities"),
                 [&](const auto &item) {
                   return permission<CapabilityParameter>(item);
                 }),
            ports(field(value, "arguments")),
            ports(field(value, "results")),
            list(field(value, "relations"),
                 [&](const auto &item) { return relationBinding(item); }),
            body(field(value, "body"))};
  }
  Entry entry(const json::Value &value) {
    record(value, {"definition", "statics", "roles", "capabilities"});
    return {reference<DefinitionRef>(field(value, "definition")),
            list(field(value, "statics"),
                 [&](const auto &item) { return natural(item); }),
            references<Role>(field(value, "roles")),
            references<RootRef>(field(value, "capabilities"))};
  }
  Module module(const json::Value &value) {
    record(value, {"roles", "types", "operations", "wires", "capabilityTypes",
                   "roots", "relations", "definitions", "entry"});
    return {list(field(value, "roles"),
                 [&](const auto &item) { return string(item); }),
            list(field(value, "types"),
                 [&](const auto &item) {
                   record(item, {"statics", "body"});
                   return TypeTemplate{natural(field(item, "statics")),
                                       type(field(item, "body"))};
                 }),
            list(field(value, "operations"),
                 [&](const auto &item) { return operation(item); }),
            list(field(value, "wires"),
                 [&](const auto &item) { return wire(item); }),
            list(field(value, "capabilityTypes"),
                 [&](const auto &item) { return capabilityType(item); }),
            list(field(value, "roots"),
                 [&](const auto &item) { return permission<Root>(item); }),
            list(field(value, "relations"),
                 [&](const auto &item) { return relation(item); }),
            list(field(value, "definitions"),
                 [&](const auto &item) { return definition(item); }),
            entry(field(value, "entry"))};
  }

public:
  Expected<Subject> read(const json::Value &value) {
    record(value, {"profile", "manifest", "module"});
    if (string(field(value, "profile")) != "zkc.math.v1")
      fail("math-profile");
    auto declarations = manifest(field(value, "manifest"));
    auto content = module(field(value, "module"));
    if (!failure.empty())
      return error(failure);
    return Subject{std::move(declarations), std::move(content)};
  }
};
} // namespace
Expected<Subject> decode(const json::Value &value) {
  auto bounded = encodeValue(value);
  if (!bounded)
    return bounded.takeError();
  return Reader().read(value);
}
} // namespace zkc::mathematical::raw
