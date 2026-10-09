#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Json.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(StringRef text,
                               std::vector<AssetBuffer> assets = {}) {
  auto captured = capture({{"sample", text.str(), {}}}, std::move(assets), {});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
ClosedEntry close(StringRef text, std::vector<AssetBuffer> assets = {}) {
  return take(closeEntry(take(check(text, std::move(assets))), "sample::Demo"));
}
const Declaration &closedDeclaration(const ClosedEntry &entry, StringRef name) {
  for (const auto &decl : entry.declarations())
    if (decl.name == name && decl.origin)
      return decl;
  require(false, "missing closed declaration");
  llvm_unreachable("require throws");
}
constexpr StringLiteral generic = R"zkc(module sample;
domain G=group("bls12-381.g1");
math fn identity<F:Field>(x:F)->F{return x;}
relation DLog<H:Group>(parameter base:H, statement point:H, witness scalar:H::Scalar) {
  return point == base*identity(scalar);
}
protocol Run<H:Group> roles(P,V)(g:H@V,h:H@V,x:H::Scalar@P)->(accepted:bool@V)
 spec {target knowledge=DLog<H>(in.g,in.h,in.x) accept out.accepted;}
 {let accepted@V=true;return(accepted=accepted);}
entry Demo=Run<G>;)zkc";
std::string
clauses(StringRef clauses,
        StringRef relation =
            "relation Equal(statement x:bool,witness y:bool){return x==y;}") {
  return ("module sample;" + relation +
          "protocol Run "
          "roles(P,V)(x:bool@P,s:bool@(P,V))->(y:bool@P,ok:bool@V) spec {" +
          clauses + "}{let ok@V=true;return(y=x,ok=ok);} entry Demo=Run;")
      .str();
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run(
      "generic relation bodies and helper dependencies survive closure", [] {
        auto entry = close(generic);
        const auto &relation = closedDeclaration(entry, "DLog");
        require(
            relation.relation->kind == RelationDefinition::Kind::Formula &&
                relation.body->mode == Body::Mode::Math &&
                relation.parameters.empty() &&
                relation.inputs[0].type.domain == "bls12-381.g1" &&
                relation.inputs[2].type.domain == "bls12-381.fr" &&
                relation.relation->purposes ==
                    std::vector<RelationPurpose>{RelationPurpose::Parameter,
                                                 RelationPurpose::Statement,
                                                 RelationPurpose::Witness},
            "relation lost its mathematical body, exact domains or purposes");
        require(
            closedDeclaration(entry, "identity").body &&
                entry.protocol().specifications[0].subject.relation.index ==
                    relation.id.index &&
                entry.protocol().specifications[0].subject.operands[2].role ==
                    0 &&
                entry.protocol().specifications[0].decision->role == 1,
            "specification-only roots or participant bindings were omitted");
      });
  cases.run(
      "clause kinds retain distinct bindings without execution guards", [] {
        auto entry = close(clauses(R"(
      input initial=Equal(in.x,in.s@P);
      output final=Equal(in.x,out.y);
      continuation reduce=Equal(in.x,in.x) residual Equal(in.x,out.y) accept out.ok;
      target claim=Equal(in.s@V,in.s@P) accept out.ok;
    )"));
        const auto &spec = entry.protocol().specifications;
        require(spec.size() == 4 &&
                    spec[0].kind == SpecificationClause::Kind::Input &&
                    spec[1].kind == SpecificationClause::Kind::Output &&
                    spec[2].residual && spec[2].residual->operands[1].output &&
                    !spec[0].decision &&
                    spec[3].subject.operands[0].role == 1 &&
                    spec[3].subject.operands[1].role == 0,
                "clause meanings or role components collapsed");
        for (const auto &op : entry.protocol().body->operations)
          require(!std::holds_alternative<Require>(op.action),
                  "clause inserted a runtime guard");
      });
  cases.run(
      "malformed direction residual decision and role bindings refuse", [] {
        for (StringRef text :
             {"target x=Equal(in.x,in.x);", "input x=Equal(in.x,out.y);",
              "output x=Equal(in.x,in.x);", "continuation x=Equal(in.x,in.x);",
              "continuation x=Equal(in.x,out.y) residual Equal(in.x,out.y);",
              "continuation x=Equal(in.x,in.x) residual Equal(in.x,in.x);",
              "target x=Equal(in.x,in.x) residual Equal(in.x,out.y) accept "
              "out.ok;",
              "input x=Equal(in.x,in.x) accept out.ok;",
              "target x=Equal(in.x,in.x) accept in.x;",
              "target x=Equal(in.x,in.x) accept out.missing;",
              "input x=Equal(in.s,in.x);", "input x=Equal(in.x@V,in.x);",
              "input x=Equal(in.x);", "input x=Run(in.x,in.x);"})
          refuses(check(clauses(text)), "source.specification");
        refuses(check(clauses(
                    "input x=Equal(in.x,in.x); input x=Equal(in.x,in.x);")),
                "source.duplicate");
        refuses(check(clauses("input x=Equal(in.x@Unknown,in.x);")),
                "source.roles");
      });
  cases.run("relations are not callable execution helpers", [] {
    refuses(check(R"(module sample;
      relation Equal(statement x:bool,witness y:bool){return x==y;}
      math fn misuse(x:bool)->bool{return Equal(x,x);})"),
            "source.call");
    refuses(check(R"(module sample;fn local_eq(x:bool)->bool{return x;}
      relation Invalid(statement x:bool){return local_eq(x);})"),
            "source.mode");
    refuses(
        check(
            R"(module sample;relation Invalid(statement x:bool){return ();})"),
        "source.type");
  });
  cases.run("formula admission checks unused definitions and ordered effects", [] {
    refuses(
        check(
            R"(module sample;relation Bad(statement x:bool){require x;return x;})"),
        "source.mode");
    refuses(
        check(
            R"(module sample;relation Bad(statement x:bool){return missing;})"),
        "source.name");
    refuses(check(R"(module sample;relation Bad(x:bool){return x;})"),
            "source.relation");
  });
  cases.run("unused opaque relations require immutable nominal inputs", [] {
    refuses(check(R"(module sample; struct Token:Drop {pub value:bool}
      relation R(statement t:Token)=opaque("vendor.r/0","key","1");)"),
            "source.relation");
    take(check(R"(module sample; struct Token:Copy+Drop {pub value:bool}
      relation R(statement t:Token)=opaque("vendor.r/0","key","1");)"));
  });
  cases.run("opaque predicates retain their explicit identity", [] {
    auto entry = close(clauses(
        "target claim=Equal(in.x,in.x) accept out.ok;",
        "relation Equal(statement x:bool,witness "
        "y:bool)=opaque(\"vendor.predicate/0\",\"key\",\"revision\");"));
    const auto &relation = closedDeclaration(entry, "Equal");
    require(!relation.body &&
                relation.relation->kind == RelationDefinition::Kind::Opaque &&
                relation.relation->key == "key" &&
                relation.relation->revision == "revision",
            "opaque predicate acquired a body or different identity");
    for (StringRef kind : {"", "zkc.language.formula/0", "zkc.relation.r1cs/0",
                           "zkc.relation.air/0"})
      refuses(check(("module sample;relation Bad(statement x:bool)=opaque(\"" +
                     kind + "\",\"key\",\"r\");")
                        .str()),
              "source.relation");
  });
  cases.run("captured R1CS binds the full assignment and canonical asset", [] {
    auto relation =
        take(zkc::relation::R1CS::create("bls12-381.fr", 3, 0, 1, {}));
    AssetBuffer asset{
        "circuit", "r1cs-json", zkc::printJson(relation.encode()), {}};
    std::string source = R"(module sample;domain Fr=field("bls12-381.fr");
      relation Circuit(statement public:builtin("field_array",Fr,1),witness assignment:builtin("field_array",Fr,3))=r1cs(asset circuit);
      protocol Run roles(P,V)(public:builtin("field_array",Fr,1)@V,assignment:builtin("field_array",Fr,3)@P)->(ok:bool@V)
      spec {target proof=Circuit(in.public,in.assignment) accept out.ok;}
      {let ok@V=true;return(ok=ok);}entry Demo=Run;)";
    auto entry = close(source, {asset});
    auto &closed = closedDeclaration(entry, "Circuit");
    require(closed.relation->asset &&
                entry.project().assets()[*closed.relation->asset].identity() ==
                    relation.identity(),
            "captured asset identity was lost");
    auto wrong = source;
    auto at = wrong.find("Fr,3");
    wrong.replace(at, 4, "Fr,1");
    refuses(check(wrong, {asset}), "source.relation");
    refuses(check(source), "source.relation");
  });
  cases.run("captured AIR retains public inputs and a trace matrix", [] {
    auto relation = take(zkc::relation::AIR::create("bls12-381.fr", 2, 1, {}));
    AssetBuffer asset{
        "trace", "air-json", zkc::printJson(relation.encode()), {}};
    auto entry = close(R"(module sample;domain Fr=field("bls12-381.fr");
      relation Trace(statement public:builtin("field_array",Fr,1),witness trace:builtin("matrix",Fr))=air(asset trace);
      protocol Run roles(P,V)(public:builtin("field_array",Fr,1)@V,trace:builtin("matrix",Fr)@P)->(ok:bool@V)
      spec {target proof=Trace(in.public,in.trace) accept out.ok;}
      {let ok@V=true;return(ok=ok);}entry Demo=Run;)",
                       {asset});
    require(closedDeclaration(entry, "Trace").relation->kind ==
                    RelationDefinition::Kind::AIR &&
                entry.project().assets()[0].air()->columns() == 2,
            "AIR declaration lost captured trace meaning");
  });
  cases.run(
      "selectors retain product paths and prove generic array bounds", [] {
        std::string source = R"(module sample;
      relation Same(statement x:bool){return x;}
      struct Pair{pub a:bool,pub b:bool}
      protocol Run<N:nat> roles(P)(x:[Pair;N]@P)->(ok:bool@P) where 1<=N
      spec {target proof=Same(in.x.0.b) accept out.ok;}
      {return(ok=true);}entry Demo=Run<2>;)";
        auto entry = close(source);
        require(entry.protocol().specifications[0].subject.operands[0].path ==
                    std::vector<unsigned>{0, 1},
                "product selector path differs");
        auto at = source.find("where 1<=N");
        source.replace(at, 10, "where ()");
        refuses(check(source), "source.bound");
      });
  cases.run(
      "same native representation cannot erase nominal operand identity", [] {
        refuses(check(R"(module sample;struct A{pub x:bool}struct B{pub x:bool}
      relation R(statement x:A){return x.x;}
      protocol Run roles(P)(x:B@P)->(ok:bool@P)
      spec {target proof=R(in.x) accept out.ok;}{return(ok=true);}entry Demo=Run;)"),
                "source.specification");
      });
  cases.run(
      "zero argument formulas are legal but empty formal layouts refuse", [] {
        close(R"(module sample;relation True(){return true;}
      protocol Run roles(P)()->(ok:bool@P) spec {target proof=True() accept out.ok;}{return(ok=true);}entry Demo=Run;)");
        auto project =
            take(check(R"(module sample;relation R(statement x:()){return true;}
      protocol Run roles(P)(x:()@P)->(ok:bool@P) spec {target proof=R(in.x) accept out.ok;}{return(ok=true);}entry Demo=Run;)"));
        refuses(closeEntry(project, "sample::Demo"), "source.relation");
      });
  cases.run("inline formulas infer only explicit bound port types", [] {
    auto entry = close(R"(module sample;domain Fr=field("bls12-381.fr");
      protocol Run<F:Field> roles(P,V)(x:F@P,y:F@V)->(ok:bool@V)
      spec {target equality=relation(statement expected=in.y,witness actual=in.x){return expected==actual;} accept out.ok;}
      {let ok@V=true;return(ok=ok);}entry Demo=Run<Fr>;)");
    const auto &clause = entry.protocol().specifications[0];
    const auto &definition =
        entry.declarations()[clause.subject.relation.index];
    require(definition.parent && definition.body &&
                definition.inputs.size() == 2 &&
                definition.inputs[0].type.domain == "bls12-381.fr" &&
                clause.subject.operands[0].role == 1 &&
                clause.subject.operands[1].role == 0,
            "inline relation captured anything beyond statics and explicit "
            "operands");
    refuses(check(clauses(
                "input condition=relation(statement lhs=in.x){return x;};")),
            "source.name");
    refuses(check(clauses(
                "input condition=relation(statement lhs=in.s){return lhs;};")),
            "source.specification");
  });
  cases.run("specification-only roots obey instance limits", [] {
    auto project = take(check(generic));
    Limits limits;
    limits.instances = 1;
    refuses(closeEntry(project, "sample::Demo", limits), "source.limit");
  });
  cases.run("opaque identities have fixed exact logical signatures", [] {
    refuses(check(R"(module sample;
      relation Ext<N:nat>(statement x:[bool;N])=opaque("vendor.k/0","key","r");)"),
            "source.relation");
    for (StringRef second : {"[bool;2]", "Other"}) {
      auto text =
          ("module sample;struct Nominal{pub x:bool}struct Other{pub x:bool}"
           "relation A(statement "
           "x:Nominal)=opaque(\"vendor.k/0\",\"key\",\"r\");"
           "relation B(statement x:" +
           second + ")=opaque(\"vendor.k/0\",\"key\",\"r\");")
              .str();
      refuses(check(text), "source.relation");
    }
    take(check(R"(module sample;
      relation A(statement x:bool)=opaque("vendor.k/0","key","r");
      relation B(statement renamed:bool)=opaque("vendor.k/0","key","r");)"));
    refuses(check(R"(module sample;
      relation A(statement x:bool)=opaque("vendor.k/0","key","r");
      relation B(witness x:bool)=opaque("vendor.k/0","key","r");)"),
            "source.relation");
    refuses(check(R"(module sample;
      relation A(statement x:bool)=opaque("zkc.invalid-relation","key","r");)"),
            "source.relation");
  });
  cases.run("inline bindings cannot be hijacked or exposed by names", [] {
    std::string text = R"(module sample;
      protocol Run roles(P)(x:bool@P)->(ok:bool@P)
      spec{target t=relation(statement a=in.x){return a;} accept out.ok;}
      {return(ok=true);}entry Demo=Run;)";
    for (StringRef visibility : {"", "pub "}) {
      auto captured =
          take(capture({{"sample", text, {}},
                        {"Run",
                         ("module Run;" + visibility +
                          "relation clause_0(statement a:bool){return true;}")
                             .str(),
                         {}},
                        {"sample::Run",
                         "module sample::Run;pub relation clause_0(statement "
                         "a:bool){return true;}",
                         {}}}));
      auto entry = take(
          closeEntry(take(analyze(captured).checkedProject()), "sample::Demo"));
      auto relation = entry.protocol().specifications[0].subject.relation;
      const auto &definition = entry.declarations()[relation.index];
      require(definition.anonymous &&
                  StringRef(definition.qualifiedName)
                      .starts_with("sample::Run::<") &&
                  entry.protocol().members.empty(),
              "inline relation was hijacked or leaked template members");
      require(entry.protocol().specificationBlock.has_value(),
              "source block span omitted");
    }
    for (StringRef name :
         {"clause_0", "Run::clause_0", "sample::Run::clause_0"})
      refuses(check(text +
                    "protocol Other roles(P)(x:bool@P)->(ok:bool@P)"
                    "spec{target u=" +
                    name.str() + "(in.x) accept out.ok;}{return(ok=true);}"),
              "source.name");
  });
  cases.run("legal long clause names do not become generated identifiers", [] {
    auto name = std::string(128, 'a');
    close(clauses("target " + name +
                      "=relation(statement a=in.x){return a;} accept out.ok;",
                  ""));
    refuses(check(clauses(
                "target x=relation(statement a=in.x){return a;} accept out.ok;"
                "target x=relation(statement a=in.x){return a;} accept out.ok;",
                "")),
            "source.duplicate");
  });
  cases.run("spec is reserved and stronger constant array bounds suffice", [] {
    refuses(
        check(R"(module sample;math fn f()->bool{let spec=true;return spec;})"),
        "source.name");
    close(R"(module sample;relation Same(statement x:bool){return x;}
      protocol Run<N:nat> roles(P)(x:[bool;N]@P)->(ok:bool@P) where 2<=N
      spec{target t=Same(in.x.0) accept out.ok;}{return(ok=true);}entry Demo=Run<2>;)");
  });
  cases.run("captured asset paths use the same qualified names as capture", [] {
    auto relation =
        take(zkc::relation::R1CS::create("bls12-381.fr", 3, 0, 1, {}));
    auto entry = close(
        R"(module sample;domain Fr=field("bls12-381.fr");
      relation Circuit(statement public:builtin("field_array",Fr,1),witness assignment:builtin("field_array",Fr,3))=r1cs(asset lib::circuit);
      protocol Run roles(P,V)(public:builtin("field_array",Fr,1)@V,assignment:builtin("field_array",Fr,3)@P)->(ok:bool@V)
      spec{target proof=Circuit(in.public,in.assignment) accept out.ok;}
      {let ok@V=true;return(ok=ok);}entry Demo=Run;)",
        {{"lib::circuit", "r1cs-json", zkc::printJson(relation.encode()), {}}});
    require(entry.project().assets()[0].name() == "lib::circuit",
            "qualified asset was not retained");
  });
  cases.run("selectors preserve private field authority across modules", [] {
    auto captured = take(
        capture({{"lib", "module lib;pub struct Pair{pub a:bool,b:bool}", {}},
                 {"sample",
                  R"(module sample;relation R(statement x:bool){return x;}
       protocol Run roles(P)(x:lib::Pair@P)->(ok:bool@P)
       spec{target t=R(in.x.b) accept out.ok;}{return(ok=true);}entry Demo=Run;)",
                  {}}}));
    refuses(analyze(captured).checkedProject(), "source.private");
  });
  return cases.result();
}
