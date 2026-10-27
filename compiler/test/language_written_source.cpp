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
  return cases.result();
}
