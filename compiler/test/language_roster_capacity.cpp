#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
std::string roles(unsigned count, StringRef prefix = "R") {
  std::vector<std::string> names;
  for (unsigned i = 0; i < count; ++i)
    names.push_back(prefix.str() + std::to_string(i));
  return join(names, ",");
}
/// A trivial Protocol over `count` roles. Shapes: one port at R0, eight ports
/// spread across the roster, or one port placed at every role.
enum class Shape { OnePort, SparsePorts, SharedPort };
std::string many(unsigned count, Shape shape) {
  std::string ports;
  if (shape == Shape::OnePort)
    ports = "x:index@R0";
  else if (shape == Shape::SharedPort)
    ports = "x:index@(" + roles(count) + ")";
  else
    for (unsigned i = 0; i < 8; ++i)
      ports += (i ? "," : "") + ("x" + std::to_string(i)) + ":index@R" +
               std::to_string(i * count / 8);
  return "module m;protocol Many roles(" + roles(count) + ")(" + ports +
         ")->(r:bool@R1){let r@R1=true;return(r=r);}";
}
CheckedProject check(StringRef source, bool layout = false) {
  CaptureOptions options;
  options.format = layout ? "zkc-layout" : "zkc";
  return take(
      analyze(take(capture({{"m", source.str(), "roster.zkc"}}, options)))
          .checkedProject());
}
/// The least phase allowance under which `phase` succeeds.
template <typename Phase> uint64_t leastWork(Phase phase) {
  uint64_t low = 1, high = Limits{}.work;
  require(bool(phase(Limits{})), "roster phase exceeds the default allowance");
  while (low < high) {
    Limits limits;
    limits.work = low + (high - low) / 2;
    if (phase(limits))
      high = limits.work;
    else
      low = limits.work + 1;
  }
  return low;
}
uint64_t closureWork(const CheckedProject &project) {
  return leastWork([&](const Limits &limits) {
    auto closed = closeEntry(project, "m::Many", limits);
    bool success = bool(closed);
    if (!success)
      consumeError(closed.takeError());
    return success;
  });
}
uint64_t publicationWork(const ClosedEntry &entry) {
  return leastWork([&](const Limits &limits) {
    auto published = prepareOriginal(entry, limits);
    bool success = bool(published);
    if (!success)
      consumeError(published.takeError());
    return success;
  });
}
} // namespace
int main() {
  Cases cases;
  for (auto shape : {Shape::OnePort, Shape::SparsePorts, Shape::SharedPort})
    cases.run("1,024 roles close and publish within the default limits: " +
                  std::string(shape == Shape::OnePort       ? "one port"
                              : shape == Shape::SparsePorts ? "sparse ports"
                                                            : "shared port"),
              [&] {
                auto project = check(many(1024, shape));
                auto closed = take(closeEntry(project, "m::Many"));
                take(prepareOriginal(closed));
                require(closed.invocations().size() == 1 &&
                            closed.invocations().front().deployment &&
                            closed.invocations()
                                    .front()
                                    .deployment->protocol()
                                    .roles.size() == 1024,
                        "roster deployment differs");
              });
  cases.run("closure work grows linearly with the roster", [] {
    std::vector<uint64_t> work;
    for (unsigned count : {128, 256, 512}) {
      auto project = check(many(count, Shape::OnePort));
      work.push_back(closureWork(project));
      outs() << count << " roles: check " << project.checkedWork()
             << ", closure " << work.back() << ", publication "
             << publicationWork(take(closeEntry(project, "m::Many"))) << '\n';
    }
    Limits limits;
    limits.work = work[2] * 5 / 2;
    take(closeEntry(check(many(1024, Shape::OnePort)), "m::Many", limits));
  });
  cases.run("a permuted 17-role telescope keeps its order", [] {
    // Each participant receives the field placed at the record role that its
    // position in the permuted telescope names; nominal role arguments are
    // never sorted.
    std::string fields;
    for (unsigned i = 0; i < 17; ++i)
      fields += "    pub f" + std::to_string(i) + ": index @A" +
                std::to_string(i) + "\n";
    std::vector<std::string> permuted;
    for (unsigned i = 0; i < 17; ++i)
      permuted.push_back("R" + std::to_string((i + 16) % 17));
    auto project =
        check("struct Wide roles(" + roles(17, "A") + "):\n" + fields +
                  "pub protocol Many roles(" + roles(17) + ")(w: Wide roles(" +
                  join(permuted, ", ") +
                  ")) -> bool @R1:\n    return true\n"
                  "entry def Demo(inputs: Many::Inputs) -> Many::RunResult:\n"
                  "    result <- Many::run(inputs)\n    return result\n",
              true);
    unsigned checked = 0;
    for (const auto &decl : project.declarations()) {
      StringRef name = decl.qualifiedName;
      if (!decl.generated || !name.consume_front("m::Many::Inputs::R"))
        continue;
      unsigned role = 0;
      require(!name.getAsInteger(10, role) && role < 17,
              "unexpected generated member");
      // Telescope position (role + 1) mod 17 names participant R`role`.
      require(decl.fields.size() == 1 &&
                  decl.fields[0].name ==
                      "w_f" + std::to_string((role + 1) % 17) &&
                  decl.generated->ports.size() == 1 &&
                  decl.generated->ports[0].role == role &&
                  decl.generated->ports[0].path ==
                      std::vector<unsigned>{(role + 1) % 17},
              "telescope order or role substitution changed at R" +
                  std::to_string(role));
      ++checked;
    }
    require(checked == 17, "generated participant members are missing");
    auto closed = take(closeEntry(project, "m::Many"));
    take(prepareOriginal(closed));
  });
  return cases.result();
}
