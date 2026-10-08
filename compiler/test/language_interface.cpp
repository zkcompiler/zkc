#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
constexpr StringLiteral original = R"mlir(
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{sym_name = "Transfer", roles = ["P", "V"],
      function_type = (i1, i1, !protocol.service_ref<"random.bls12-381.fr/1">) -> i1,
      input_roles = [["P"], ["P"], ["V"]], output_roles = [["V"]]}> ({
    ^bb0(%a: i1, %b: i1, %rng: !protocol.service_ref<"random.bls12-381.fr/1">):
      %c = "arith.andi"(%a, %b) : (i1, i1) -> i1
      %d = "protocol.exchange"(%c) <{sender = "P", receiver = "V", site = "message"}> : (i1) -> i1
      "protocol.return"(%d) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}
)mlir";
json::Value scalar() {
  return json::Object{
      {"type", "bool"},
      {"kind", "boolean"},
      {"identity", std::string(64, '1')},
      {"custody", false},
      {"permissions", json::Array{"Copy", "Drop", "Share", "Wire"}},
      {"leaves", json::Array{"bool"}},
      {"fields", json::Array{}},
      {"alternatives", json::Array{}}};
}
json::Value pair() {
  return json::Object{
      {"type", "sample::Pair"},
      {"kind", "record"},
      {"identity", std::string(64, '2')},
      {"custody", false},
      {"permissions", json::Array{"Copy", "Drop", "Share", "Wire"}},
      {"leaves", json::Array{"bool", "bool"}},
      {"fields",
       json::Array{
           json::Object{{"name", "left"}, {"offset", 0}, {"schema", scalar()}},
           json::Object{
               {"name", "right"}, {"offset", 1}, {"schema", scalar()}}}},
      {"alternatives", json::Array{}}};
}
json::Value document() {
  // Hand-authored interface and IR: no source checker, layout builder or
  // emitter.
  return json::Object{
      {"format", "zkc.language-interface/3"},
      {"capture", std::string(64, '0')},
      {"original", toHex(SHA256::hash(arrayRefFromStringRef(original)), true)},
      {"toolchain", compilerToolchainIdentity()},
      {"entry", "sample::Demo"},
      {"protocol", "Transfer"},
      {"roles", json::Array{"P", "V"}},
      {"inputs", json::Array{json::Object{{"name", "p"},
                                          {"type", "sample::Pair"},
                                          {"roles", json::Array{"P"}},
                                          {"index", 0},
                                          {"native", json::Array{0, 1}},
                                          {"schema", pair()}}}},
      {"outputs", json::Array{json::Object{{"name", "ok"},
                                           {"type", "bool"},
                                           {"roles", json::Array{"V"}},
                                           {"index", 0},
                                           {"native", json::Array{0}},
                                           {"schema", scalar()}}}},
      {"services",
       json::Array{json::Object{{"name", "coins"},
                                {"contract", "random.bls12-381.fr/1"},
                                {"owner", "V"},
                                {"native", 2}}}}};
}
json::Object &input(json::Value &value) {
  return *value.getAsObject()->getArray("inputs")->front().getAsObject();
}
json::Object &shape(json::Value &value) {
  return *input(value).getObject("schema");
}
void mutate(function_ref<void(json::Value &)> change) {
  auto value = document();
  change(value);
  refuses(readInterface(original, zkc::printJson(value)), "source.interface");
}
CheckedOriginal compile(StringRef code) {
  auto project = take(
      analyze(take(capture({{"sample", code.str(), {}}}))).checkedProject());
  return take(prepareOriginal(take(closeEntry(project, "sample::Demo"))));
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("hand-authored logical layout binds exact native ports", [] {
    auto view = take(readInterface(original, zkc::printJson(document())));
    require(view.inputs[0].native == std::vector<unsigned>({0, 1}) &&
                view.inputs[0].schema->fields[1].offset == 1 &&
                view.outputs[0].roles == std::vector<unsigned>{1} &&
                view.services[0].owner == 1 && view.services[0].native == 2,
            "read view lost native binding");
  });
  cases.run("string limits count decoded bytes and allow JSON escapes", [] {
    auto v = document();
    std::string label(zkc::protocol::VariantSpellingBytes, 'a');
    input(v)["type"] = label;
    shape(v)["type"] = label;
    take(readInterface(original, zkc::printJson(v)));
    auto bytes = zkc::printJson(v);
    std::string escaped;
    for (unsigned i = 0; i < label.size(); ++i)
      escaped += "\\u0061";
    auto at = bytes.find(label);
    bytes.replace(at, label.size(), escaped);
    take(readInterface(original, bytes));
    label += 'a';
    input(v)["type"] = label;
    shape(v)["type"] = label;
    refuses(readInterface(original, zkc::printJson(v)), "source.limit");
    refuses(
        readInterface(
            original,
            "[\"" +
                std::string(6 * zkc::protocol::VariantSpellingBytes + 1, 'a') +
                "\"]"),
        "source.limit");
  });
  cases.run("logical kinds constrain product and scalar structure", [] {
    for (StringRef kind : {"unknown", "formal", "boolean", "unit", "associated",
                           "array", "variant"})
      mutate([&](auto &v) { shape(v)["kind"] = kind.str(); });
    mutate([](auto &v) { shape(v).erase("kind"); });
    mutate([](auto &v) { shape(v)["identity"] = std::string(64, 'G'); });
    mutate([](auto &v) { shape(v).erase("identity"); });
    for (StringRef kind : {"record", "array", "tuple", "group", "builtin"})
      mutate([&](auto &v) {
        auto &out =
            *v.getAsObject()->getArray("outputs")->front().getAsObject();
        (*out.getObject("schema"))["kind"] = kind.str();
      });
    for (StringRef version :
         {"zkc.language-interface/1", "zkc.language-interface/2"})
      mutate([&](auto &v) { (*v.getAsObject())["format"] = version.str(); });
  });
  cases.run("type identities distinguish phantom and empty element types", [] {
    auto source = compile(R"zkc(module sample;
struct Box<T:Type>{pub value:bool}
protocol Run roles(P)(a:Box<bool>@P,b:Box<index>@P,c:[bool;0]@P,d:[index;0]@P)
  ->(x:Box<bool>@P,y:Box<index>@P,u:[bool;0]@P,v:[index;0]@P){
  return(x=a,y=b,u=c,v=d);
}
entry Demo=Run;)zkc");
    const auto &v = source.interface();
    require(v.inputs[0].schema->identity != v.inputs[1].schema->identity &&
                v.inputs[2].schema->identity != v.inputs[3].schema->identity &&
                v.inputs[0].schema == v.outputs[0].schema &&
                v.inputs[2].schema->kind == Type::Kind::Array,
            "logical identities were reduced to their native representation");
  });
  cases.run("display labels are not type identity", [] {
    auto v = document();
    auto &out = *v.getAsObject()->getArray("outputs")->front().getAsObject();
    out["type"] = "sample::Pair";
    (*out.getObject("schema"))["type"] = "sample::Pair";
    (*out.getObject("schema"))["identity"] = std::string(64, '3');
    auto view = take(readInterface(original, zkc::printJson(v)));
    require(view.inputs[0].schema->type == view.outputs[0].schema->type &&
                view.inputs[0].schema->identity !=
                    view.outputs[0].schema->identity,
            "structural view treated labels as equality authority");
    (*out.getObject("schema"))["identity"] = std::string(64, '2');
    refuses(readInterface(original, zkc::printJson(v)), "source.interface");
  });
  cases.run("array elements require the same exact logical type", [] {
    auto v = document();
    shape(v)["kind"] = "array";
    auto &fields = *shape(v).getArray("fields");
    for (unsigned i = 0; i < fields.size(); ++i)
      (*fields[i].getAsObject())["name"] = std::to_string(i);
    take(readInterface(original, zkc::printJson(v)));
    (*fields[1].getAsObject()->getObject("schema"))["identity"] =
        std::string(64, '4');
    refuses(readInterface(original, zkc::printJson(v)), "source.interface");
  });
  cases.run("custody and variants bind the logical identity digest", [] {
    for (
        StringRef code : {
            R"zkc(module sample; struct Token:Drop{} fn mint()->Token{return Token{};}
      protocol Run roles(P)()->(x:Token@P){local P let t=mint();return(x=t);}entry Demo=Run;)zkc",
            R"zkc(module sample; enum Choice{A(bool),B()}
      protocol Run roles(P)(x:Choice@P)->(y:Choice@P){return(y=x);}entry Demo=Run;)zkc"}) {
      auto source = compile(code);
      auto v = take(json::parse(source.interfaceJson()));
      auto &out = *v.getAsObject()->getArray("outputs")->front().getAsObject();
      (*out.getObject("schema"))["identity"] = std::string(64, '0');
      refuses(readInterface(source.bytes(), zkc::printJson(v)),
              "source.interface");
    }
  });
  cases.run("original identity is exact, including whitespace", [] {
    refuses(readInterface("\n" + original.str(), zkc::printJson(document())),
            "source.interface");
  });
  cases.run("unknown and duplicate members refuse before interpretation", [] {
    mutate([](auto &v) { (*v.getAsObject())["extra"] = true; });
    mutate([](auto &v) { input(v)["extra"] = true; });
    mutate([](auto &v) { shape(v)["extra"] = true; });
    auto bytes = zkc::printJson(document());
    bytes.insert(1, "\"entr\\u0079\":\"sample::Demo\",");
    refuses(readInterface(original, bytes), "source.interface");
  });
  cases.run("multiple malformed fields return a refusal without aborting", [] {
    mutate([](auto &v) {
      auto &o = *v.getAsObject();
      o["format"] = false;
      o["entry"] = false;
      o["inputs"] = false;
    });
    mutate([](auto &v) {
      shape(v)["type"] = false;
      shape(v)["permissions"] = false;
      shape(v)["fields"] = false;
    });
  });
  cases.run("native type and logical type must agree", [] {
    mutate([](auto &v) { (*shape(v).getArray("leaves"))[0] = "index"; });
    mutate([](auto &v) { input(v)["type"] = "sample::Other"; });
    mutate([](auto &v) { (*shape(v).getArray("leaves"))[0] = "not-a-type"; });
  });
  cases.run("native leaf indices are complete and ordered", [] {
    for (auto indices : {std::vector<int>{1, 0}, {0, 0}, {0, 2}, {0}})
      mutate([&](auto &v) {
        json::Array a;
        for (auto i : indices)
          a.push_back(i);
        input(v)["native"] = std::move(a);
      });
    mutate(
        [](auto &v) { *v.getAsObject()->getArray("outputs") = json::Array{}; });
  });
  cases.run("field offsets and payload coverage refuse coherent overlaps", [] {
    mutate([](auto &v) {
      (*shape(v).getArray("fields"))[1].getAsObject()->operator[]("offset") = 0;
    });
    mutate([](auto &v) { shape(v)["fields"] = json::Array{}; });
    mutate([](auto &v) {
      (*shape(v).getArray("fields"))[1].getAsObject()->operator[]("name") =
          "left";
    });
    mutate([](auto &v) { shape(v)["custody"] = true; });
  });
  cases.run("role mapping selects actual participants", [] {
    for (auto roles : {json::Array{"V"}, json::Array{"P", "P"}, json::Array{},
                       json::Array{"unknown"}})
      mutate([&](auto &v) { input(v)["roles"] = json::Array(roles); });
    mutate(
        [](auto &v) { (*v.getAsObject())["roles"] = json::Array{"V", "P"}; });
  });
  cases.run("service types owners and flat positions are checked", [] {
    for (StringRef field : {"owner", "contract", "native", "name"})
      mutate([&](auto &v) {
        auto &s = *v.getAsObject()->getArray("services")->front().getAsObject();
        if (field == "owner")
          s[field] = "P";
        if (field == "contract")
          s[field] = "random.bn254.fr/1";
        if (field == "native")
          s[field] = 1;
        if (field == "name")
          s[field] = "p";
      });
    mutate([](auto &v) { (*v.getAsObject())["services"] = json::Array{}; });
  });
  cases.run("permissions cannot exceed their children", [] {
    mutate([](auto &v) {
      (*shape(v).getArray("fields"))[0].getAsObject()->getObject("schema")->
      operator[]("permissions") = json::Array{};
    });
    mutate(
        [](auto &v) { shape(v)["permissions"] = json::Array{"Wire", "Wire"}; });
    mutate([](auto &v) { shape(v)["permissions"] = json::Array{"Invent"}; });
  });
  cases.run("work bytes and recursive layout depth are bounded", [] {
    auto bytes = zkc::printJson(document());
    for (auto member : {&Limits::work, &Limits::interfaceBytes,
                        &Limits::irBytes, &Limits::typeDepth}) {
      Limits limits;
      limits.*member = 0;
      refuses(readInterface(original, bytes, limits), "source.limit");
    }
  });
  cases.run("malformed JSON and Unicode refuse", [] {
    for (StringRef bytes : {"{", "[]", "{\"x\":\"\\uD800\"}",
                            "{\"x\":123456789012345678901234567890}"})
      refuses(readInterface(original, bytes), "source.interface");
  });
  cases.run("source agreement remains stronger than a structural interface",
            [] {
              auto source = compile(R"zkc(module sample;
protocol Run roles(P)(a:bool@P)->(b:bool@P) {return(b=a);}
entry Demo=Run;)zkc");
              auto value = take(json::parse(source.interfaceJson()));
              input(value)["name"] = "renamed";
              take(readInterface(source.bytes(), zkc::printJson(value)));
              auto checked = checkInterface(source, zkc::printJson(value));
              require(bool(checked), "renaming escaped source agreement");
              require(StringRef(toString(std::move(checked)))
                          .contains("source.interface"),
                      "wrong source refusal");
            });
  cases.run(
      "variants empty products and custody survive independent reading", [] {
        auto source = compile(R"zkc(module sample;
domain Fr=field("bls12-381.fr");
struct State:Drop {pub value:Fr}
enum Choice {Some(Fr), None()}
fn make(x:Fr)->State {return State{value:x};}
protocol Run roles(P)(choice:Choice@P, empty:[Fr;0]@P, x:Fr@P)
  ->(same:Choice@P, unit:()@P, state:State@P) {
 local P let state=make(x);
 return(same=choice,unit=(),state=state);
}
entry Demo=Run;)zkc");
        auto view = take(readInterface(source.bytes(), source.interfaceJson()));
        require(view.inputs[0].schema->alternatives.size() == 2 &&
                    view.inputs[1].native.empty() &&
                    view.outputs[1].native.empty() &&
                    view.outputs[2].schema->custody &&
                    view.outputs[2].schema->fields[0].offset == 1,
                "rich schema lost structure");
        for (unsigned mode = 0; mode < 6; ++mode) {
          auto value = take(json::parse(source.interfaceJson()));
          auto &s = *input(value).getObject("schema");
          if (mode == 0)
            (*s.getArray("alternatives"))[0].getAsObject()->operator[]("name") =
                "None";
          if (mode == 1)
            (*s.getArray("alternatives"))[0].getAsObject()->operator[](
                "fields") = json::Array{};
          if (mode == 2)
            (*s.getArray("alternatives"))[0]
                .getAsObject()
                ->getArray("fields")
                ->front()
                .getAsObject()
                ->operator[]("offset") = 1;
          if (mode == 3)
            s["custody"] = true;
          if (mode == 4)
            s["alternatives"] = json::Array{};
          if (mode == 5)
            (*value.getAsObject()->getArray("outputs"))[2]
                .getAsObject()
                ->getObject("schema")
                ->operator[]("fields") = json::Array{};
          refuses(readInterface(source.bytes(), zkc::printJson(value)),
                  "source.interface");
        }
      });
  cases.run(
      "nominal Share survives affine children at single-role outputs", [] {
        auto source = compile(R"zkc(module sample;
struct Ticket:Share {}
struct Wrapper {ticket:Ticket}
fn make()->Wrapper {return Wrapper{ticket:Ticket{}};}
protocol Run roles(P)()->(result:Wrapper@P) {local P let value=make(); return(result=value);}
entry Demo=Run;)zkc");
        auto view = take(readInterface(source.bytes(), source.interfaceJson()));
        require(view.outputs[0].schema->permissions.share &&
                    !view.outputs[0].schema->permissions.copy,
                "independent nominal permissions were collapsed");
      });
  cases.run("field names are identifiers or contiguous positional indices", [] {
    for (StringRef name : {"a.b", "x::y", "01", "1", "0"})
      mutate([&](auto &v) {
        (*shape(v).getArray("fields"))[0].getAsObject()->operator[]("name") =
            name.str();
      });
    auto v = document();
    shape(v)["kind"] = "tuple";
    for (unsigned i = 0; i < 2; ++i)
      (*shape(v).getArray("fields"))[i].getAsObject()->operator[]("name") =
          std::to_string(i);
    take(readInterface(original, zkc::printJson(v)));
  });
  cases.run("permission order is canonical", [] {
    mutate([](auto &v) {
      shape(v)["permissions"] = json::Array{"Drop", "Copy", "Share", "Wire"};
    });
  });
  cases.run("zero-leaf shared ports still require source permissions", [] {
    auto source = compile(R"zkc(module sample;
protocol Run roles(P,V)()->(empty:()@(V,P)) {return(empty=());}
entry Demo=Run;)zkc");
    auto view = take(readInterface(source.bytes(), source.interfaceJson()));
    require(view.outputs[0].native.empty() && view.outputs[0].roles.size() == 2,
            "shared unit lost");
    auto v = take(json::parse(source.interfaceJson()));
    v.getAsObject()
        ->getArray("outputs")
        ->front()
        .getAsObject()
        ->getObject("schema")
        ->operator[]("permissions") = json::Array{};
    refuses(readInterface(source.bytes(), zkc::printJson(v)),
            "source.interface");
  });
  cases.run("native admission checks custody placement before metadata", [] {
    auto source = compile(R"zkc(module sample;
struct Token:Drop {}
fn mint()->Token {return Token{};}
protocol Run roles(P,V)()->(t:Token@P) {local P let t=mint();return(t=t);}
entry Demo=Run;)zkc");
    auto v = take(json::parse(source.interfaceJson()));
    auto &port = *v.getAsObject()->getArray("outputs")->front().getAsObject();
    port.getObject("schema")->operator[]("custody") = false;
    refuses(readInterface(source.bytes(), zkc::printJson(v)),
            "source.interface");
    v = take(json::parse(source.interfaceJson()));
    auto bytes = source.bytes().str();
    std::string old = "output_roles = [[\"P\"]]";
    auto at = bytes.find(old);
    require(at != std::string::npos, "missing role mutation anchor");
    bytes.replace(at, old.size(), "output_roles = [[\"P\", \"V\"]]");
    (*v.getAsObject())["original"] =
        toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
    v.getAsObject()->getArray("outputs")->front().getAsObject()->operator[](
        "roles") = json::Array{"P", "V"};
    refuses(readInterface(bytes, zkc::printJson(v)), "target.admission");
  });
  cases.run("native nominal anchors cannot acquire two source labels", [] {
    auto source = compile(R"zkc(module sample;
struct Token:Drop {}
enum Choice {Some(bool),None()}
fn mint()->Token {return Token{};}
protocol Run roles(P)(v:Choice@P)->(a:Token@P,b:Token@P,x:Choice@P,y:Choice@P) {
 local P let a=mint(); local P let b=mint();return(a=a,b=b,x=v,y=v);
}
entry Demo=Run;)zkc");
    for (unsigned index : {1u, 3u}) {
      auto v = take(json::parse(source.interfaceJson()));
      auto &port =
          *(*v.getAsObject()->getArray("outputs"))[index].getAsObject();
      port["type"] = "sample::Other";
      port.getObject("schema")->operator[]("type") = "sample::Other";
      refuses(readInterface(source.bytes(), zkc::printJson(v)),
              "source.interface");
    }
  });
  cases.run("all installed field and group schemas remain admissible", [] {
    unsigned checked = 0;
    for (const auto &domain : zkc::protocol::installedDomains().allDomains()) {
      if (domain.sort != "Field" && domain.sort != "Group")
        continue;
      auto kind = domain.sort == "Field" ? "field" : "group";
      auto source =
          compile("module sample;domain D=" + std::string(kind) + "(\"" +
                  domain.identity +
                  "\");"
                  "protocol Run roles(P,V)(x:D@(V,P))->(result:D@(V,P)) "
                  "{return(result=x);}entry Demo=Run;");
      auto view = take(readInterface(source.bytes(), source.interfaceJson()));
      require(view.inputs[0].schema->permissions.wire &&
                  view.inputs[0].roles == std::vector<unsigned>({0, 1}),
              "installed scalar permissions or role order differ");
      ++checked;
    }
    require(checked >= 10, "domain inventory unexpectedly incomplete");
  });
  cases.run("maximum-length module still admits its qualified Entry", [] {
    std::string module;
    while (module.size() + 130 <= Limits{}.moduleBytes) {
      if (!module.empty())
        module += "::";
      module += std::string(128, 'a');
    }
    module += "::" + std::string(Limits{}.moduleBytes - module.size() - 2, 'b');
    require(module.size() == Limits{}.moduleBytes, "bad module length fixture");
    auto code = "module " + module +
                ";protocol Run "
                "roles(P)(x:bool@P)->(r:bool@P){return(r=x);}entry Demo=Run;";
    auto project =
        take(analyze(take(capture({{module, code, {}}}))).checkedProject());
    auto source =
        take(prepareOriginal(take(closeEntry(project, module + "::Demo"))));
    take(readInterface(source.bytes(), source.interfaceJson()));
  });
  cases.run("JSON key escapes cannot replace nested fields", [] {
    for (StringRef key : {"na\\u006de", "a\\\""}) {
      auto bytes = zkc::printJson(document());
      if (key.starts_with("na")) {
        auto at = bytes.find("\"left\"");
        require(at != std::string::npos, "field anchor missing");
        auto start = bytes.rfind('{', at);
        bytes.insert(start + 1, "\"" + key.str() + "\":\"left\",");
      } else
        bytes = "{\"" + key.str() + "\":0,\"" + key.str() + "\":1}";
      refuses(readInterface(original, bytes), "source.interface");
    }
    refuses(readInterface(original, R"({"\q":1})"), "source.interface");
  });
  return cases.result();
}
