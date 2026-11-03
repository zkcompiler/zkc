#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/EntryBoundary.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <filesystem>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedOriginal original(StringRef fixture = "ordinary.zkc",
                         StringRef name = "Demo", bool joint = false) {
  auto path =
      (std::filesystem::path(ZKC_ENTRY_COMPONENT_FIXTURE).parent_path() /
       fixture.str())
          .string();
  auto source = MemoryBuffer::getFile(path);
  require(bool(source), "missing component fixture");
  CaptureOptions options;
  options.format = "zkc-layout";
  auto project = take(
      analyze(take(capture({{"components", (*source)->getBuffer().str(), path}},
                           options)))
          .checkedProject());
  auto entry =
      joint ? take(closeNativeRun(project, ("components::" + name).str()))
            : take(closeEntry(project, ("components::" + name).str()));
  return take(prepareOriginal(entry));
}
json::Object &rootSchema(json::Value &document) {
  auto &protocol =
      *document.getAsObject()->getArray("protocols")->front().getAsObject();
  return *protocol.getArray("inputs")->front().getAsObject()->getObject(
      "schema");
}
json::Array &publicInputs(json::Value &document) {
  return *document.getAsObject()->getObject("job")->getArray("public");
}
} // namespace
int main(int argc, char **argv) {
  Cases cases;
  auto checked = original();
  cases.run(
      "source public paths independently expand into flat native proof indices",
      [&] {
        auto view =
            take(readInterface(checked.bytes(), checked.interfaceJson()));
        require(view.proof && view.proof->publicInputs.size() == 2 &&
                    view.proof->publicInputs[0] ==
                        EntryInputSelection{0, {0}, 1, {}} &&
                    view.proof->publicInputs[1] ==
                        EntryInputSelection{0, {2}, 1, {}},
                "exact public field/role coverage differs");
        auto policy = take(proofPolicy(checked));
        require(
            policy.publicInputs == std::vector<unsigned>{0},
            "public policy leaked witness or invented an empty native slot");
        take(admitOriginal(checked.entry(), checked.bytes(),
                           checked.interfaceJson()));
      });
  cases.run(
      "selected setup keys retain native slices and ordinary Host siblings",
      [&] {
        auto setup = original("setup.zkc");
        auto policy = take(proofPolicy(setup));
        require(policy.publicInputs == std::vector<unsigned>({0, 2}),
                "setup proof policy used a whole logical port");
        const auto &view = setup.interface();
        require(
            view.setups.size() == 1 && view.setups[0].inputs.size() == 3 &&
                view.setups[0].inputs[0].native == std::vector<unsigned>{0} &&
                view.setups[0].inputs[1].native == std::vector<unsigned>{1} &&
                view.setups[0].inputs[2].native == std::vector<unsigned>{2},
            "setup selector slices or role associations differ");
        auto host = original("setup.zkc", "Produce");
        Layouts layouts(host.entry());
        auto witness = take(layouts.get(host.entry().root().inputs[1].type));
        require(witness->fields.size() == 1 &&
                    witness->fields[0].name == "state_nonce",
                "setup association hid an ordinary sibling in the generated "
                "Host family");
      });
  cases.run(
      "independent Host comparison assembles setup below an ordinary product",
      [&] {
        auto setup = original("setup-product.zkc");
        require(take(proofPolicy(setup)).publicInputs ==
                    std::vector<unsigned>({0, 1}),
                "nested ordinary setup public expansion differs");
        auto host = original("setup-product.zkc", "Check");
        Layouts layouts(host.entry());
        auto publicType = take(layouts.get(host.entry().root().inputs[0].type));
        require(publicType->fields.size() == 1 &&
                    publicType->fields[0].name == "state_verifier_nonce",
                "nested initialized key hid an ordinary public sibling");
      });
  cases.run(
      "independent Host comparison expands a closed logical array family", [&] {
        auto host = original("array.zkc", "Run");
        require(bool(host.interface().host),
                "closed array Entry lost its Host boundary");
        Layouts layouts(host.entry());
        auto inputs = take(layouts.get(host.entry().root().inputs[0].type));
        require(inputs->fields.size() == 2 &&
                    inputs->fields[0].layout->fields[1].name ==
                        "state_1_left" &&
                    inputs->fields[1].layout->fields[1].name == "state_1_right",
                "independent child comparison reused an open generated roster");
      });
  for (StringRef mutation :
       {"integer", "missing-empty", "wrong-role", "permuted", "duplicate",
        "ancestor", "whole-logical", "extra-field"})
    cases.run("strict public selection refuses " + mutation, [&] {
      auto document = take(json::parse(checked.interfaceJson()));
      auto &inputs = publicInputs(document);
      if (mutation == "integer")
        inputs = json::Array{0};
      else if (mutation == "missing-empty")
        inputs.pop_back();
      else if (mutation == "wrong-role")
        (*inputs[1].getAsObject())["role"] = "P";
      else if (mutation == "permuted")
        std::swap(inputs[0], inputs[1]);
      else if (mutation == "duplicate")
        inputs.push_back(inputs.back());
      else if (mutation == "extra-field")
        (*inputs[0].getAsObject())["native"] = json::Array{0};
      else {
        (*inputs[0].getAsObject())["path"] = json::Array{};
        if (mutation == "whole-logical")
          inputs.pop_back();
      }
      refuses(readInterface(checked.bytes(), zkc::printJson(document)),
              "source.interface");
    });
  for (StringRef mutation :
       {"missing", "nonboolean", "private-empty", "sealed-root"})
    cases.run("zero-storage assembly metadata refuses " + mutation, [&] {
      auto document = take(json::parse(checked.interfaceJson()));
      auto &schema = rootSchema(document);
      if (mutation == "missing")
        schema.erase("sealed");
      else if (mutation == "nonboolean")
        schema["sealed"] = 0;
      else if (mutation == "sealed-root")
        schema["sealed"] = true;
      else
        (*(*schema.getArray("fields"))[2].getAsObject())["public"] = false;
      refuses(readInterface(checked.bytes(), zkc::printJson(document)),
              "source.interface");
    });
  auto result = cases.result();
  if (!result && argc == 2) {
    std::filesystem::create_directories(argv[1]);
    auto joint = original("ordinary.zkc", "Round", true);
    for (auto [name, bytes] :
         {std::pair<StringRef, StringRef>{"ordinary.mlir", checked.bytes()},
          {"ordinary.json", checked.interfaceJson()},
          {"ordinary-run.mlir", joint.bytes()},
          {"ordinary-run.json", joint.interfaceJson()}}) {
      std::error_code error;
      raw_fd_ostream out(std::string(argv[1]) + "/" + name.str(), error);
      require(!error, "cannot write component fixture");
      out << bytes;
    }
  }
  return result;
}
