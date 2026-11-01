#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"

using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
int main() {
  Cases cases;
  auto checked = [] {
    return take(analyze(take(capture({{"written", R"(module written;
      pub interface I { math fn f(x:bool)->bool; }
      pub math fn f(x:bool)->bool{return x;}
      fn g(cb:fn(bool)->bool, x:bool)->bool{return cb(x);}
    )",
                                       "private/path.zkc"}})))
                    .checkedProject());
  };
  cases.run("written syntax is immutable and bounds output", [&] {
    auto project = checked();
    auto first = take(inspectWrittenSource(project));
    take(inspectPublicAPI(project));
    take(inspectNotations(project));
    require(take(inspectWrittenSource(project)) == first,
            "other inspections changed written syntax");
    require(first.find("private/path.zkc") == std::string::npos,
            "diagnostic path became source identity");
    auto limits = Limits{};
    limits.apiInspectionBytes = first.size() - 1;
    auto limited = inspectWrittenSource(project, limits);
    require(!limited, "output ceiling accepted an oversized AST");
    require(toString(limited.takeError()).find("source.limit") !=
                std::string::npos,
            "output refusal lost its limit diagnostic");
    limits.apiInspectionBytes = first.size();
    require(take(inspectWrittenSource(project, limits)) == first,
            "exact output ceiling refused");
    limits.work = project.checkedWork() - 1;
    auto work = inspectWrittenSource(project, limits);
    require(!work, "retained checking work was ignored");
    consumeError(work.takeError());
  });
  cases.run("defaults and implicit member visibility stay omitted", [&] {
    auto view = take(json::parse(take(inspectWrittenSource(checked()))));
    const auto &rows = *view.getAsObject()->getArray("declarations");
    bool member = false, callback = false;
    for (const auto &row : rows) {
      const auto &decl = *row.getAsObject();
      for (const auto &value : *decl.getArray("nodes")) {
        const auto &node = *value.getAsObject();
        if (decl.getString("owner") == "written::I::f" &&
            node.getArray("path")->empty()) {
          require(node.getBoolean("public") == false,
                  "implicit interface visibility became a pub keyword");
          member = true;
        }
        if (decl.getString("owner") == "written::g" &&
            node.getString("kind") == "port" &&
            node.getString("name") == "cb") {
          auto *signature = node.getObject("callback");
          require(signature && signature->get("effects") &&
                      signature->get("effects")->getAsNull().has_value(),
                  "default callback effects became written effects");
          callback = true;
        }
      }
    }
    require(member && callback, "written declarations were not exported");
  });
  cases.run("body-only distributed records retain authored authority", [] {
    CaptureOptions options;
    options.format = "zkc-layout";
    auto project = take(analyze(take(capture({{"written",
                                               R"(
struct State roles(A, B):
    pub value: index @A
    secret: () @B
    empty: [index @B; 0]
pub protocol Run roles(P, V)() -> index @P:
    state = State roles(P, V) {value: 7, secret: (), empty: []}
    return state.value
)",
                                               {}}},
                                             options)))
                            .checkedProject());
    auto view = take(json::parse(take(inspectWrittenSource(project))));
    bool declaration = false, visible = false, hidden = false, empty = false;
    bool placed = false;
    for (const auto &row : *view.getAsObject()->getArray("declarations")) {
      const auto &owner = *row.getAsObject();
      if (owner.getString("owner") != "written::State")
        continue;
      for (const auto &value : *owner.getArray("nodes")) {
        const auto &node = *value.getAsObject();
        if (node.getArray("path")->empty()) {
          require(node.getBoolean("public") == false &&
                      *node.getArray("roster") == json::Array{"A", "B"},
                  "private record or nominal role telescope was erased");
          declaration = true;
        }
        if (node.getString("kind") == "port") {
          if (node.getString("name") == "value")
            visible = node.getBoolean("public") == true;
          if (node.getString("name") == "secret")
            hidden = node.getBoolean("public") == false;
          if (node.getString("name") == "empty")
            empty = node.getBoolean("public") == false;
        }
        if (const auto *components = node.getArray("components"))
          placed |= *components == json::Array{"B"};
      }
    }
    require(declaration && visible && hidden && empty && placed,
            "body-only record lost private, zero-storage or placed syntax");
  });
  return cases.result();
}
