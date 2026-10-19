#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
#include <algorithm>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject check(std::vector<SourceBuffer> sources) {
  return take(analyze(take(capture(std::move(sources)))).checkedProject());
}
json::Value report(const CheckedProject &project) {
  return take(json::parse(take(inspectPublicAPI(project))));
}
const json::Array &array(const json::Value &view, StringRef name) {
  auto *object = view.getAsObject();
  require(object && object->getArray(name), "missing API table: " + name);
  return *object->getArray(name);
}
const json::Object &find(const json::Array &values, StringRef key,
                         StringRef expected) {
  for (const auto &value : values)
    if (value.getAsObject()->getString(key) == expected)
      return *value.getAsObject();
  throw std::runtime_error("missing API record: " + expected.str());
}
std::vector<SourceBuffer> sources() {
  return {{"lower", R"(module lower;
    pub domain F=field("koala-bear");
    pub type Bits=[bool;2];
    pub enum Choice {Some(bool),None()}
    #[sealed] pub struct Sealed {pub flag:bool}
    pub relation Truth(statement value:bool){return value;}
    pub math fn explicit(x:bool)->bool where () {return x;}
    pub fn total(x:bool)->bool effects() where () {return x;}
    module Hidden {
      pub struct View {pub length:index, secret_payload:bool}
      pub math fn combine(x:bool,y:bool)->bool{return x&&y;}
    }
    pub use lower::Hidden::{View,combine};
    pub operator infixl(70) ⊙ = combine;
    pub module Identity {pub type Token:Copy+Drop=[bool;3];}
    pub interface Contract {math fn value()->bool;}
    pub math fn apply<C:Contract>()->bool{return C::value();}
  )",
           "lower.zkc"},
          {"facade", R"(module facade;
    pub use lower::{View,F,Bits,combine,Contract,operator ⊙};
  )",
           "facade.zkc"},
          {"client", R"(module client;
    use facade as api;
    use facade::{combine};
    pub math fn called(x:bool,y:bool)->bool{return api::combine(x,y);}
    math fn private_helper(x:bool,y:bool)->bool{return combine(x,y);}
    pub math fn apply<C:api::Contract>()->bool{return C::value();}
    pub module Generic<C:api::Contract> {
      pub math fn apply()->bool{return C::value();}
    }
  )",
           "client.zkc"}};
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "public routes reach private ancestors without exposing representation",
      [] {
        auto view = report(check(sources()));
        require(view.getAsObject()->getString("format") == "zkc.source-api/0",
                "API format missing");
        const auto &declarations = array(view, "declarations");
        const auto &record = find(declarations, "name", "lower::Hidden::View");
        require(record.getString("kind") == "record" &&
                    record.getString("constructor") == "owner" &&
                    record.getBoolean("private_fields") == true &&
                    record.getArray("fields")->size() == 1,
                "record privacy/constructor contract lost");
        auto bytes = take(inspectPublicAPI(check(sources())));
        require(bytes.find("secret_payload") == std::string::npos,
                "private field name leaked");
        const auto &token =
            find(declarations, "name", "lower::Identity::Token");
        require(token.getString("representation") == "private" &&
                    !token.get("type"),
                "associated representation leaked");
        require(find(declarations, "name", "lower::Bits").getString("kind") ==
                        "alias" &&
                    find(declarations, "name", "lower::F").getString("kind") ==
                        "domain",
                "type exports omitted");
        require(
            find(declarations, "name", "lower::Choice")
                        .getArray("alternatives")
                        ->size() == 2 &&
                find(declarations, "name", "lower::Sealed")
                        .getString("constructor") == "owner" &&
                find(declarations, "name", "lower::Truth").getString("kind") ==
                    "relation",
            "variant sealed record or relation contract missing");
        const auto &explicitContract =
            find(declarations, "name", "lower::total");
        require(explicitContract.getBoolean("requirements_written") == true &&
                    explicitContract.getBoolean("effects_written") == true &&
                    find(declarations, "name", "lower::apply")
                            .getBoolean("requirements_written") == false,
                "authored contract markers lost");
        find(array(view, "exports"), "owner", "facade");
        find(array(view, "notations"), "owner", "facade");
        for (const auto &item : declarations)
          require(item.getAsObject()->getString("name") !=
                      "client::private_helper",
                  "private helper became a public declaration");
      });
  cases.run("facade provider and canonical target remain distinct", [] {
    auto view = report(check(sources()));
    const auto &reference =
        find(array(view, "references"), "written", "api::combine");
    require(reference.getString("provider") == "facade" &&
                reference.getString("target") == "lower::Hidden::combine" &&
                reference.getString("target_module") == "lower" &&
                reference.getString("written") == "api::combine",
            "facade route replaced by lower canonical target");
    find(array(view, "references"), "owner", "client::private_helper");
    const auto &abstract =
        find(array(view, "references"), "written", "C::value");
    require(abstract.getString("target") == "lower::Contract::value" &&
                abstract.getString("abstract_module").has_value(),
            "abstract module call dependency missing");
  });
  cases.run(
      "abstract calls retain their interface binder's facade provider", [] {
        auto view = report(check(sources()));
        unsigned checked = 0;
        for (const auto &item : array(view, "references")) {
          const auto &reference = *item.getAsObject();
          if (reference.getString("written") != "C::value" ||
              !reference.getString("owner")->starts_with("client::"))
            continue;
          require(reference.getString("provider") == "facade" &&
                      reference.getString("target") ==
                          "lower::Contract::value" &&
                      reference.getString("target_module") == "lower" &&
                      reference.getString("abstract_module").has_value(),
                  "abstract call introduced a canonical lower dependency");
          ++checked;
        }
        require(checked == 2,
                "missing direct or inherited module parameter call");
      });
  cases.run("capability contracts retain an authored qualified export", [] {
    auto view = report(check({{"m", R"(module m;
      pub fn root<F:Field>(n:index)->F where zkc::algebra::TwoAdicField(F) {
        return kernel<F>("poly.domain_root",n);
      })",
                               "m.zkc"}}));
    const auto &requirements =
        *find(array(view, "declarations"), "name", "m::root")
             .getArray("requirements");
    const auto &capability = find(requirements, "kind", "capability");
    require(capability.getString("export") == "zkc::algebra::TwoAdicField",
            "qualified capability export missing");
  });
  cases.run("inspection order and repeated output are deterministic", [] {
    auto inputs = sources();
    auto first = check(inputs);
    auto expected = take(inspectPublicAPI(first));
    std::reverse(inputs.begin(), inputs.end());
    require(take(inspectPublicAPI(check(inputs))) == expected &&
                take(inspectPublicAPI(first)) == expected,
            "capture order changed the API graph");
  });
  cases.run("public aliases retain a linear graph instead of expanding paths",
            [] {
              std::vector<SourceBuffer> inputs;
              for (unsigned i = 0; i < 32; ++i) {
                auto module = "layer" + std::to_string(i);
                std::string text = "module " + module + ";";
                if (i)
                  text += "pub use layer" + std::to_string(i - 1) +
                          " as Left;pub use layer" + std::to_string(i - 1) +
                          " as Right;";
                inputs.push_back({module, text, module + ".zkc"});
              }
              auto view = report(check(std::move(inputs)));
              require(array(view, "declarations").size() == 32 &&
                          array(view, "exports").size() == 62,
                      "aliases expanded canonical graph nodes");
            });
  cases.run("byte work declaration operation and depth limits refuse", [] {
    auto project = check(sources());
    auto bytes = take(inspectPublicAPI(project));
    Limits limits;
    limits.apiInspectionBytes = bytes.size();
    require(take(inspectPublicAPI(project, limits)) == bytes,
            "exact output limit refused");
    --limits.apiInspectionBytes;
    refuses(inspectPublicAPI(project, limits), "source.limit");
    for (unsigned i = 0; i < 4; ++i) {
      limits = {};
      if (i == 0)
        limits.work = project.checkedWork() - 1;
      if (i == 1)
        limits.declarations = project.checkedDeclarations() - 1;
      if (i == 2)
        limits.operations = project.checkedOperations() - 1;
      if (i == 3)
        limits.importDepth = 1;
      refuses(inspectPublicAPI(project, limits), "source.limit");
    }
  });
  return cases.result();
}
