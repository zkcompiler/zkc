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
CheckedProject check(StringRef body) {
  return take(analyze(take(capture({{"written", "module written;" + body.str(),
                                     "not-a-source-identity.zkc"}})))
                  .checkedProject());
}
using Nodes = std::map<std::string, const json::Object *>;
std::string key(StringRef owner, const json::Value &path) {
  return owner.str() + ':' + zkc::printJson(path);
}
Nodes nodes(const json::Value &ast) {
  Nodes result;
  for (const auto &value : *ast.getAsObject()->getArray("declarations")) {
    const auto &decl = *value.getAsObject();
    for (const auto &item : *decl.getArray("nodes")) {
      auto *node = item.getAsObject();
      result.emplace(key(*decl.getString("owner"), *node->get("path")), node);
    }
  }
  return result;
}
const json::Object &resolve(const Nodes &nodes, const json::Value &address) {
  auto &object = *address.getAsObject();
  auto found = nodes.find(key(*object.getString("owner"), *object.get("path")));
  require(found != nodes.end(), "reference does not name a written node");
  return *found->second;
}
json::Value inspected(const CheckedProject &project) {
  auto bytes = take(inspectLexicalBindings(project));
  require(bytes.find("not-a-source-identity.zkc") == std::string::npos,
          "diagnostic filename escaped");
  return take(json::parse(bytes));
}
json::Array ownReferences(const CheckedProject &project, StringRef owner) {
  auto ast = take(json::parse(take(inspectWrittenSource(project))));
  auto byAddress = nodes(ast);
  auto report = inspected(project);
  require(report.getAsObject()->getString("format") == "zkc.lexical-bindings/0",
          "wrong proposal format");
  json::Array result;
  for (const auto &item : *report.getAsObject()->getArray("references")) {
    const auto &reference = *item.getAsObject();
    for (const auto &use : *reference.getArray("uses")) {
      const auto &node = resolve(byAddress, use);
      auto kind = *node.getString("kind");
      require(kind == "expr.name" || kind == "expr.call" ||
                  kind == "pattern.name",
              "lexical use is not a written name");
    }
    for (const auto &binder : *reference.getArray("binders")) {
      const auto &node = resolve(byAddress, binder);
      require(node.getString("kind") == "port" ||
                  node.getString("kind") == "pattern.name",
              "binder is not a written binder");
    }
    if (reference.getArray("uses")->front().getAsObject()->getString("owner") ==
        owner)
      result.push_back(item);
  }
  for (const auto &item : *report.getAsObject()->getArray("unassociated")) {
    const auto &reference = *item.getAsObject();
    for (const auto &use : *reference.getArray("uses"))
      require(use.getAsObject()->getString("owner") != owner,
              "authored local use lost its binder association");
  }
  return result;
}
const json::Value &onlyPath(const json::Value &reference, StringRef field) {
  const auto &addresses = *reference.getAsObject()->getArray(field);
  require(addresses.size() == 1, "unexpected repeated written address");
  return *addresses.front().getAsObject()->get("path");
}
} // namespace
int main() {
  Cases cases;
  cases.run("shadowed names retain the binder chosen at each use", [] {
    auto project = check("fn f(x:bool)->bool {let y=x;let x=y;return x;}");
    auto refs = ownReferences(project, "written::f");
    require(refs.size() == 3, "missing lexical uses");
    require(onlyPath(refs[0], "binders") ==
                take(json::parse(R"([["input",0]])")),
            "initial use did not select its input");
    require(onlyPath(refs[1], "binders") ==
                take(json::parse(R"([["body",0],["stmt",0],["pattern",0]])")),
            "second use did not select the first let");
    require(onlyPath(refs[2], "binders") ==
                take(json::parse(R"([["body",0],["stmt",1],["pattern",0]])")),
            "return selected the shadowed input");
  });
  cases.run(
      "mutable assignment and short-circuit elaboration preserve provenance",
      [] {
        auto project = check(R"(
      fn f(x:bool)->bool {let mut y=x;y=!y;return x&&y;}
    )");
        auto refs = ownReferences(project, "written::f");
        unsigned assignments = 0;
        for (const auto &ref : refs)
          if (ref.getAsObject()->getString("kind") == "assign") {
            ++assignments;
            require(onlyPath(ref, "binders") ==
                        take(json::parse(
                            R"([["body",0],["stmt",0],["pattern",0]])")),
                    "assignment did not select mutable binder");
          }
        require(assignments == 1 && refs.size() >= 5,
                "assignment or Boolean operand uses were lost");
      });
  cases.run("callback inputs retain their written combined order", [] {
    auto project = check(R"(
      fn f(cb:fn(bool)->bool,x:bool)->bool{return cb(x);}
    )");
    auto refs = ownReferences(project, "written::f");
    bool call = false, argument = false;
    for (const auto &ref : refs) {
      bool callback = ref.getAsObject()->getString("kind") == "call";
      require(onlyPath(ref, "binders") ==
                  take(json::parse(callback ? R"([["input",0]])"
                                            : R"([["input",1]])")),
              "split signature indices escaped as written input positions");
      call |= callback;
      argument |= !callback;
    }
    require(call && argument, "callback and ordinary argument not covered");
  });
  cases.run(
      "record shorthand and loop index keep distinct written binders", [] {
        auto project = check(R"(
      struct Pair { first:bool,second:bool }
      fn f(p:Pair,n:index)->bool {
        let Pair{first,second:s}=p;
        let mut answer=first;
        for i in 0..n {let used=i;answer=s;}
        return answer;
      }
    )");
        auto refs = ownReferences(project, "written::f");
        std::set<std::string> targets;
        for (const auto &ref : refs)
          targets.insert(zkc::printJson(onlyPath(ref, "binders")));
        require(targets.size() >= 5, "record/loop/input binders collapsed");
      });
  cases.run("finite parser adapters preserve the authored binder origins", [] {
    auto project = check(R"(
      type Vector<F:Field>=builtin("vector",F);
      domain Fr=field("koala-bear");
      fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,
          step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S
          effects(stop)=finite("local.fold");
      fn sum<I:Type+Copy+Drop,F:Field>(rows:domain<I>,
          term:fn(item:I)->F effects(stop) where item_from(item,rows))->F
          effects(stop){return fold(rows,0,fn(state,item)=>state+term(item));}
      reduction ∑=sum;
      fn f(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return ∑ (x in xs)(y in ys),x*y;}
    )");
    auto refs = ownReferences(project, "written::f");
    unsigned finite = 0;
    for (const auto &ref : refs)
      if (zkc::printJson(onlyPath(ref, "binders")).find("binder") !=
          std::string::npos)
        ++finite;
    require(finite == 2,
            "finite binders were replaced by synthetic lambda paths");
  });
  cases.run(
      "alpha renaming changes spelling without changing binding paths", [] {
        auto a = ownReferences(check("fn f(x:bool)->bool{let y=x;return y;}"),
                               "written::f");
        auto b = ownReferences(
            check("fn f(input:bool)->bool{let renamed=input;return renamed;}"),
            "written::f");
        require(json::Value(std::move(a)) == json::Value(std::move(b)),
                "alpha renaming changed associations");
      });
  cases.run("complete FRI capture resolves authored local uses", [] {
    auto project =
        take(analyze(take(capture(sourceProject(ZKC_SOURCE_PROJECT))))
                 .checkedProject());
    ownReferences(project, ""); // Check every proposed address and node kind.
    auto report = inspected(project);
    require(report.getAsObject()->getArray("references")->size() > 100,
            "full capture did not exercise its local bindings");
    for (const auto &item : *report.getAsObject()->getArray("unassociated"))
      require(item.getAsObject()->getArray("uses")->empty(),
              "authored use has no binder in a complete capture");
  });
  cases.run("inspection is immutable and bounded before publication", [] {
    auto project = check("fn f(x:bool)->bool{return x;}");
    auto bytes = take(inspectLexicalBindings(project));
    take(inspectWrittenSource(project));
    take(inspectPublicAPI(project));
    require(take(inspectLexicalBindings(project)) == bytes,
            "inspection changed retained resolution");
    auto limits = Limits{};
    limits.apiInspectionBytes = bytes.size() - 1;
    refuses(inspectLexicalBindings(project, limits), "source.limit");
    limits.apiInspectionBytes = bytes.size();
    require(take(inspectLexicalBindings(project, limits)) == bytes,
            "exact byte bound refused");
    limits.work = project.checkedWork() - 1;
    refuses(inspectLexicalBindings(project, limits), "source.limit");
  });
  return cases.result();
}
