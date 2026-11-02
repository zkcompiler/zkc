#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace generated = zkc::protocol::instances;
namespace {
std::vector<std::string> names(unsigned count, StringRef prefix) {
  std::vector<std::string> result;
  for (unsigned i = 0; i < count; ++i)
    result.push_back(prefix.str() + std::to_string(i));
  return result;
}
/// A distributed record of `roles` role parameters with one index field at
/// its first parameter, and a protocol over as many roles that takes it with
/// telescope position i applied to protocol role order[i].
std::string wide(unsigned roles, ArrayRef<unsigned> order) {
  std::vector<std::string> applied;
  for (unsigned role : order)
    applied.push_back("R" + std::to_string(role));
  return "struct Wide roles(" + join(names(roles, "A"), ", ") +
         "):\n    pub f0: index @A0\n"
         "pub protocol Fan roles(" +
         join(names(roles, "R"), ", ") + ")(w: Wide roles(" +
         join(applied, ", ") + ")) -> bool @R1:\n    return true\n";
}
std::vector<unsigned> inOrder(unsigned count) {
  std::vector<unsigned> order(count);
  for (unsigned i = 0; i < count; ++i)
    order[i] = i;
  return order;
}
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "roles.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
CheckedOriginal publish(StringRef source) {
  return take(
      prepareOriginal(take(closeNativeRun(take(check(source)), "m::Fan"))));
}
std::string refusal(Error error) { return toString(std::move(error)); }
/// The reader's refusal of an edited copy of a published interface.
std::string reread(const CheckedOriginal &original,
                   function_ref<void(json::Object &)> edit) {
  auto value = take(json::parse(original.interfaceJson()));
  edit(*value.getAsObject()->getArray("protocols")->front().getAsObject());
  auto read = readInterface(original.bytes(), zkc::printJson(value));
  require(!read, "the edited interface was admitted");
  return refusal(read.takeError());
}
} // namespace
int main() {
  Cases cases;
  cases.run("the two role limits are separate catalog rows", [] {
    static_assert(generated::recordRoleLimit == 1024 &&
                      generated::protocolRoleLimit == 1024,
                  "both role limits are 1,024 roles");
    const auto *record = generated::limit("record.roles");
    const auto *roster = generated::limit("protocol.roles");
    require(record && roster && record != roster &&
                record->value == generated::recordRoleLimit &&
                record->unit == generated::LimitUnit::Roles &&
                record->phase == generated::LimitPhase::Admission &&
                record->owner != roster->owner &&
                record->scope != roster->scope,
            "record telescope and protocol roster rows differ");
  });
  for (unsigned roles : {16u, 17u, 1024u})
    cases.run("a " + Twine(roles) +
                  "-role record telescope is checked, written and read",
              [roles] {
                auto original = publish(wide(roles, inOrder(roles)));
                auto view = take(
                    readInterface(original.bytes(), original.interfaceJson()));
                const auto &port = view.selectedProtocol().inputs.at(0);
                require(view.selectedProtocol().roles.size() == roles &&
                            port.schema->roles == names(roles, "A"),
                        "the read telescope differs");
              });
  cases.run("a permuted 17-role telescope is read in telescope order", [] {
    // Telescope position i names protocol role (i + 16) mod 17; nominal
    // role arguments are an ordered substitution, never a sorted set.
    std::vector<unsigned> order;
    for (unsigned i = 0; i < 17; ++i)
      order.push_back((i + 16) % 17);
    auto original = publish(wide(17, order));
    auto view = take(readInterface(original.bytes(), original.interfaceJson()));
    const auto &placement = view.selectedProtocol().inputs.at(0).placement;
    const auto *product =
        placement ? std::get_if<ProductPlacement>(&placement->value) : nullptr;
    require(product && product->arguments == order,
            "the reader reordered the telescope substitution");
  });
  cases.run("each role limit refuses above 1,024 at checking by name", [] {
    // A 1,025-role record alone, without a protocol over as many roles.
    auto record = check("struct Wide roles(" + join(names(1025, "A"), ", ") +
                        "):\n    pub f0: index @A0\n");
    require(!record, "a 1,025-role telescope was admitted");
    auto telescope = refusal(record.takeError());
    auto protocol =
        check("pub protocol Fan roles(" + join(names(1025, "R"), ", ") +
              ")(x: index @R0) -> bool @R1:\n    return true\n");
    require(!protocol, "a 1,025-role roster was admitted");
    auto roster = refusal(protocol.takeError());
    require(StringRef(telescope).contains("source.limit") &&
                StringRef(telescope).contains(
                    "record role telescope exceeds the record.roles limit") &&
                StringRef(roster).contains("source.limit") &&
                StringRef(roster).contains(
                    "participant roster exceeds the protocol.roles limit"),
            "unexpected refusals: " + telescope + "; " + roster);
  });
  cases.run("the reader refuses each role limit above 1,024 by name", [] {
    auto original = publish(wide(1024, inOrder(1024)));
    auto telescope = reread(original, [](json::Object &protocol) {
      (*protocol.getArray("inputs"))[0]
          .getAsObject()
          ->getObject("schema")
          ->getArray("roles")
          ->push_back("A1024");
    });
    require(StringRef(telescope).contains(
                "schema role telescope exceeds the record.roles limit"),
            "unexpected telescope refusal: " + telescope);
    auto roster = reread(original, [](json::Object &protocol) {
      protocol.getArray("roles")->push_back("R1024");
    });
    require(StringRef(roster).contains(
                "role roster exceeds the protocol.roles limit"),
            "unexpected roster refusal: " + roster);
  });
  cases.run(
      "a subject within both role limits can exceed only the "
      "publication ceiling",
      [] {
        // Admission limits and output-size limits are separate: the
        // same 1,024-role subject is checked and closed under a
        // publication ceiling one byte below its interface, and only
        // publication refuses.
        auto source = wide(1024, inOrder(1024));
        auto bytes = publish(source).interfaceJson().size();
        outs() << "1,024-role telescope interface: " << bytes << " bytes\n";
        Limits limits;
        limits.interfaceBytes = bytes - 1;
        auto closed =
            take(closeNativeRun(take(check(source, limits)), "m::Fan", limits));
        auto published = prepareOriginal(closed, limits);
        require(!published, "an interface above its ceiling published");
        auto message = refusal(published.takeError());
        require(StringRef(message).contains("source.limit") &&
                    StringRef(message).contains(
                        "interface traversal or byte limit exceeded"),
                "unexpected publication refusal: " + message);
      });
  return cases.result();
}
