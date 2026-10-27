#include "support/NativeCases.h"
#include "support/SourceProject.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/Json.h"
#include <map>
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
ClosedEntry close(StringRef source) {
  auto project = take(
      analyze(
          take(capture({{"written", "module written;" + source.str(), {}}})))
          .checkedProject());
  return take(closeSubject(project, "written::P"));
}
json::Value inspect(const ClosedEntry &entry) {
  return take(json::parse(take(inspectSourceInstances(entry))));
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "different closed substitutions retain the same authored template", [] {
        auto entry = close(R"(
      math fn id<T:Type>(x:T)->T{return x;}
      protocol P roles(A)(x:bool@A,y:index@A)->(ok:bool@A){
        let i=id<index>(y);let b=id<bool>(x);return(ok=b);
      }
    )");
        auto report = inspect(entry);
        std::map<std::string, std::string> selected;
        for (const auto &item : *report.getAsObject()->getArray("instances")) {
          const auto &instance = *item.getAsObject();
          const auto &origin = *instance.getObject("template");
          if (origin.getString("owner") == "written::id") {
            require(origin.getString("kind") == "declaration" &&
                        !origin.getArray("candidates")->empty(),
                    "lost authored template");
            selected.emplace(zkc::printJson(*instance.get("statics")),
                             instance.getString("symbol")->str());
          }
        }
        auto a = selected.find(R"([["T",["bool"]]])");
        auto b = selected.find(R"([["T",["index"]]])");
        require(
            a != selected.end() && b != selected.end() &&
                a->second != b->second,
            "different instances merged or static arguments became strings");
      });
  cases.run(
      "scoped helpers use written nodes and explicit capture layouts", [] {
        auto entry = close(R"(
      math fn apply(cb:math fn(bool)->bool,x:bool)->bool{return cb(x);}
      protocol P roles(A)(x:bool@A,y:bool@A)->(ok:bool@A){
        let ok=apply(fn(v)=>v&&x,y);return(ok=ok);
      }
    )");
        auto report = inspect(entry);
        auto ast =
            take(json::parse(take(inspectWrittenSource(entry.project()))));
        std::map<std::string, const json::Object *> written;
        for (const auto &decl : *ast.getAsObject()->getArray("declarations")) {
          const auto &object = *decl.getAsObject();
          for (const auto &item : *object.getArray("nodes")) {
            const auto *node = item.getAsObject();
            written.emplace(object.getString("owner")->str() + ':' +
                                zkc::printJson(*node->get("path")),
                            node);
          }
        }
        unsigned scoped = 0;
        std::string helper;
        const json::Object *application = nullptr;
        for (const auto &item : *report.getAsObject()->getArray("instances")) {
          const auto &instance = *item.getAsObject();
          const auto &origin = *instance.getObject("template");
          if (origin.getString("owner") == "written::apply")
            application = &instance;
          if (origin.getString("kind") != "scoped")
            continue;
          helper = instance.getString("symbol")->str();
          require(
              *instance.getObject("layout")->get("inputs") ==
                      json::Value(json::Array{0, 1}) &&
                  instance.getObject("layout")->getArray("captures")->empty(),
              "lambda argument and lexical capture are not helper inputs");
          ++scoped;
          require(origin.getString("owner") == "written::P" &&
                      !origin.getArray("nodes")->empty(),
                  "scoped source became an internal helper name");
          for (const auto &address : *origin.getArray("nodes")) {
            const auto &node = *address.getAsObject();
            auto found = written.find(node.getString("owner")->str() + ':' +
                                      zkc::printJson(*node.get("path")));
            require(found != written.end() &&
                        found->second->getString("kind") == "expr.lambda",
                    "scoped helper does not select its written lambda");
          }
        }
        require(scoped == 1 && application &&
                    *application->get("scoped") ==
                        json::Value(json::Array{helper}) &&
                    *application->getObject("layout")->get("inputs") ==
                        json::Value(json::Array{0}) &&
                    *application->getObject("layout")->get("captures") ==
                        json::Value(json::Array{1}),
                "callback selection or caller hidden capture layout differs");
      });
  cases.run(
      "domain substitutions preserve shared constructor graphs and own input "
      "slots",
      [] {
        auto entry = close(R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
domain fn product<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("product");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn aggregate(rows:domain<(index,index)>,initial:bool,step:math fn(bool,item:(index,index))->bool where item_from(item,rows))->bool{return fold(rows,initial,step);}
protocol P roles(A)(lo:index@A,hi:index@A,flag:bool@A)->(ok:bool@A){let ok=aggregate(product(range(lo,hi),range(lo,hi)),flag,fn(s,p)=>s);return(ok=ok);}

        )");
        auto bytes = take(inspectSourceInstances(entry));
        auto report = take(json::parse(bytes));
        unsigned domains = 0, scoped = 0;
        for (const auto &item : *report.getAsObject()->getArray("instances")) {
          const auto &instance = *item.getAsObject();
          scoped += !instance.getArray("scoped")->empty();
          for (const auto &value : *instance.getArray("domains")) {
            ++domains;
            const auto &domain = *value.getAsObject();
            const auto &nodes = *domain.getArray("nodes");
            require(domain.getInteger("result") &&
                        *domain.getInteger("result") >= 0 &&
                        uint64_t(*domain.getInteger("result")) < nodes.size(),
                    "invalid domain result");
            for (unsigned i = 0; i < nodes.size(); ++i) {
              const auto &node = *nodes[i].getAsObject();
              for (const auto &child : *node.getArray("children"))
                require(child.getAsInteger() && *child.getAsInteger() >= 0 &&
                            uint64_t(*child.getAsInteger()) < i,
                        "domain is not a closed ordered graph");
              for (const auto &operand : *node.getArray("operands"))
                require(operand.getAsInteger() &&
                            *operand.getAsInteger() >= 0 &&
                            uint64_t(*operand.getAsInteger()) <
                                domain.getArray("inputs")->size(),
                        "domain operand escaped its own input signature");
            }
          }
        }
        require(domains == 1 && scoped == 1,
                "finite wrapper lost its domain or callback substitution");
        const json::Object *aggregate = nullptr;
        for (const auto &value : *report.getAsObject()->getArray("instances"))
          if (value.getAsObject()->getObject("template")->getString("owner") ==
              "written::aggregate")
            aggregate = value.getAsObject();
        require(aggregate, "finite wrapper instance missing");
        auto &domain = *aggregate->getArray("domains")->front().getAsObject();
        auto &nodes = *domain.getArray("nodes");
        require(domain.getArray("inputs")->size() == 2 && nodes.size() == 2 &&
                    nodes[0].getAsObject()->getString("kind") == "range" &&
                    nodes[1].getAsObject()->getString("kind") == "product" &&
                    *nodes[0].getAsObject()->get("operands") ==
                        json::Value(json::Array{0, 1}) &&
                    *nodes[1].getAsObject()->get("children") ==
                        json::Value(json::Array{0, 0}) &&
                    *aggregate->getObject("layout")->get("captures") ==
                        json::Value(json::Array{1, 2}),
                "shared range graph or runtime operand mapping differs");
        require(
            bytes.find("finite-domain") == std::string::npos,
            "internal domain identity leaked instead of a constructor graph");
      });
  cases.run("complete FRI closure exports every retained closed instance", [] {
    auto project =
        take(analyze(take(capture(sourceProject(ZKC_SOURCE_PROJECT))))
                 .checkedProject());
    auto entry = take(closeSubject(project, "example::Fri"));
    auto report = inspect(entry);
    const auto &instances = *report.getAsObject()->getArray("instances");
    unsigned expected = 0;
    std::set<std::string> symbols;
    for (const auto &decl : entry.declarations())
      expected += decl.origin.has_value();
    for (const auto &instance : instances)
      require(symbols.insert(instance.getAsObject()->getString("symbol")->str())
                  .second,
              "closed instance symbol repeated");
    require(instances.size() == expected && expected > 10 &&
                symbols.count(entry.protocol().symbol),
            "full FRI instance coverage differs from the closed entry");
  });
  cases.run("source instance inspection is immutable and bounded", [] {
    auto entry =
        close("protocol P roles(A)(x:bool@A)->(ok:bool@A){return(ok=x);}");
    auto bytes = take(inspectSourceInstances(entry));
    take(inspectSourceBindings(entry.project()));
    require(take(inspectSourceInstances(entry)) == bytes,
            "inspection changed the closed source");
    auto limits = Limits{};
    limits.apiInspectionBytes = bytes.size();
    require(take(inspectSourceInstances(entry, limits)) == bytes,
            "exact instance byte limit refused");
    --limits.apiInspectionBytes;
    refuses(inspectSourceInstances(entry, limits), "source.limit");
    limits = Limits{};
    limits.work = entry.project().checkedWork() - 1;
    refuses(inspectSourceInstances(entry, limits), "source.limit");
  });
  return cases.result();
}
