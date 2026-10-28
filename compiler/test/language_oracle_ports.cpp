#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Json.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
const char *prefix = R"(
module m;
domain F=field("bls12-381.fr");
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Oracle<K:OracleKind>=builtin("oracle",K);
type O=Oracle<Fixed<F,16>>;
type Dynamic=Oracle<Table<F>>;
)";
Expected<CheckedProject> check(StringRef code) {
  auto captured =
      capture({{"m", std::string(prefix) + code.str(), "oracle.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
CheckedOriginal original(StringRef code) {
  auto project = take(check(code));
  return take(
      prepareOriginal(take(zkc::test::closeNativeRun(project, "m::Run"))));
}
const char *forward = R"(
protocol Forward<K:OracleKind> roles(B,A)(word:Oracle<K>@A->B)
  ->(out:Oracle<K>@A->B){return(out=word);}
protocol Run roles(P,V)(a:O@P->V,b:O@P->V)->(out:O@P->V,ok:bool@V){
  let out=Forward<Fixed<F,16>> roles(V,P)(b);
  let ok@V=true;return(out=out,ok=ok);
}
)";
json::Object &input(json::Value &value, const CheckedOriginal &source) {
  return *(*value.getAsObject()->getArray(
      "protocols"))[source.interface().selected]
              .getAsObject()
              ->getArray("inputs")
              ->front()
              .getAsObject();
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run(
      "one logical port expands to paired holder and anchor components", [] {
        auto source = original(R"(
      protocol Run roles(P,V)(word:O@P->V)->(ok:bool@V){let ok@V=true;return(ok=ok);}
    )");
        auto view = take(readInterface(source.bytes(), source.interfaceJson()));
        const auto &port = view.selectedProtocol().inputs.front();
        require(port.native == std::vector<unsigned>{0, 1} && port.oracle &&
                    port.oracle->holder == 0 && !port.oracle->maximumRows &&
                    port.roles == std::vector<unsigned>{0, 1},
                "paired interface was lost");
        require(port.schema->oracle && port.schema->leaves.empty() &&
                    !port.schema->constructible,
                "anchor became native input data");
        require(source.bytes().contains("protocol.oracle_input"),
                "unused root binding was erased");
        if (auto error = compareInterface(source.entry(), view))
          throw std::runtime_error(toString(std::move(error)));
      });
  cases.run(
      "generic calls and results preserve pairs and role substitution", [] {
        auto source = original(forward);
        require(source.bytes().contains("protocol.oracle_components") &&
                    source.bytes().contains("protocol.apply"),
                "call failed to expose paired components");
        const auto &ports = source.interface().selectedProtocol();
        require(ports.inputs[1].native == std::vector<unsigned>{2, 3} &&
                    ports.outputs[0].native == std::vector<unsigned>{0, 1} &&
                    ports.outputs[1].native == std::vector<unsigned>{2},
                "mixed output offsets differ");
      });
  cases.run("ordinary inputs retain offsets after paired oracle inputs", [] {
    auto source = original(R"(
      protocol Run roles(P,V)(word:O@P->V,flag:bool@V)->(ok:bool@V){return(ok=flag);}
    )");
    const auto &ports = source.interface().selectedProtocol();
    require(ports.inputs[1].native == std::vector<unsigned>{2},
            "ordinary input overlapped an oracle component");
    auto view = take(readInterface(source.bytes(), source.interfaceJson()));
    if (auto error = compareInterface(source.entry(), view))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("written ports retain holder and authored maximum", [] {
    auto project = take(check(R"(
      protocol Run roles(P,V)(word:Dynamic@P->V max 32)
        ->(ok:bool@V){let ok@V=true;return(ok=ok);}
    )"));
    auto ast = take(json::parse(take(inspectWrittenSource(project))));
    bool found = false;
    for (const auto &declaration :
         *ast.getAsObject()->getArray("declarations")) {
      const auto &decl = *declaration.getAsObject();
      if (decl.getString("owner") != "m::Run")
        continue;
      for (const auto &value : *decl.getArray("nodes")) {
        const auto &node = *value.getAsObject();
        if (node.getString("kind") == "port" &&
            node.getString("name") == "word") {
          require(node.getString("oracle_holder") == "P" &&
                      node.get("oracle_maximum") &&
                      !node.get("oracle_maximum")->getAsNull(),
                  "written port lost its holder or bound syntax");
          found = true;
        }
      }
    }
    require(found, "written oracle port was not exported");
  });
  cases.run("unsized maxima preserve full unsigned range", [] {
    auto source = original(R"(
      protocol Run roles(P,V)(word:Dynamic@P->V max 18446744073709551615)
        ->(ok:bool@V){let ok@V=true;return(ok=ok);}
    )");
    require(
        source.interface().selectedProtocol().inputs[0].oracle->maximumRows ==
            UINT64_MAX,
        "maximum narrowed");
    for (const char *bound : {"-1", "01", "18446744073709551616", "32"}) {
      auto changed = take(json::parse(source.interfaceJson()));
      input(changed, source)["maximum_rows"] = bound;
      refuses(readInterface(source.bytes(), printJson(changed)),
              "source.interface");
    }
  });
  cases.run("generic unsized bounds close on inputs and returned pairs", [] {
    auto source = original(R"(
      protocol Forward<M:nat> roles(A,B)(word:Dynamic@A->B max M)
        ->(out:Dynamic@A->B max M){return(out=word);}
      protocol Run roles(P,V)(word:Dynamic@P->V max 32)
        ->(out:Dynamic@P->V max 16){
        let out=Forward<16> roles(P,V)(word);return(out=out);
      }
    )");
    const auto &ports = source.interface().selectedProtocol();
    require(ports.inputs[0].oracle->maximumRows == 32 &&
                ports.outputs[0].oracle->maximumRows == 16,
            "closed port bounds were not retained separately");
  });
  cases.run("packed mathematical rows retain their exact kind descriptor", [] {
    auto source = original(R"(
      type Packed=Oracle<Fixed<(bool,index),8>>;
      protocol Run roles(P,V)(word:Packed@P->V)->(out:Packed@P->V){return(out=word);}
    )");
    const auto &kind =
        *source.interface().selectedProtocol().inputs[0].schema->oracle;
    require(kind.arguments.size() == 2 && kind.arguments[0].type &&
                kind.arguments[0].type->kind == "variant" &&
                kind.arguments[1].natural == 8,
            "packed row became an untyped source name");
  });
  cases.run("one holder can retain multiple receiver components", [] {
    auto source = original(R"(
      protocol Run roles(C,A,B)(word:O@A->(B,C))->(out:O@A->(B,C)){return(out=word);}
    )");
    const auto &port = source.interface().selectedProtocol().inputs[0];
    require(port.oracle->holder == 1 &&
                port.roles == std::vector<unsigned>{0, 1, 2},
            "holder was inferred from sorted availability");
  });
  for (auto [name, ports, code] :
       {std::tuple{"missing arrow", "word:O@(P,V)", "source.oracle-port"},
        {"data arrow", "word:bool@P->V", "source.oracle-port"},
        {"holder repeated", "word:O@P->P", "source.oracle-port"},
        {"many holders", "word:O@(P,V)->V", "source.oracle-port"},
        {"missing maximum", "word:Dynamic@P->V", "source.oracle-shape"},
        {"sized maximum", "word:O@P->V max 16", "source.oracle-shape"},
        {"non-natural maximum", "word:Dynamic@P->V max bool",
         "source.oracle-shape"}})
    cases.run(Twine("refuse ") + name, [ports = ports, code = code] {
      refuses(check("protocol Run roles(P,V)(" + std::string(ports) +
                    ")->(ok:bool@V){let ok@V=true;return(ok=ok);}"),
              code);
    });
  cases.run("oracle values cannot be sent through the data codec", [] {
    refuses(check(R"(
      protocol Run roles(P,V)(word:O@P->V)->(ok:bool@V){
        let invalid=send P->V(word);let ok@V=true;return(ok=ok);
      })"),
            "source.oracle-boundary");
  });
  cases.run("interface mutations cannot rebind logical kind or components", [] {
    auto source = original(forward);
    std::vector<std::function<void(json::Object &)>> edits{
        [](auto &p) { p["holder"] = "V"; },
        [](auto &p) { p["native"] = json::Array{1, 0}; },
        [](auto &p) { p["native"] = json::Array{0}; },
        [](auto &p) { p["maximum_rows"] = "16"; },
        [](auto &p) { p["roles"] = json::Array{"V"}; },
        [](auto &p) {
          p.getObject("schema")->operator[]("constructible") = true;
        },
        [](auto &p) {
          p.getObject("schema")->operator[]("leaves") =
              json::Array{"vector:bls12-381.fr"};
        },
        [](auto &p) {
          p.getObject("schema")->getObject("oracle")->operator[]("kind") =
              "unknown";
        },
        [](auto &p) {
          p.getObject("schema")->getObject("oracle")->operator[]("arguments") =
              json::Array{json::Array{"type", "field:bls12-381.fr"},
                          json::Array{"nat", "8"}};
        },
        [](auto &p) { p.getObject("schema")->operator[]("extra") = true; },
    };
    for (auto &edit : edits) {
      auto changed = take(json::parse(source.interfaceJson()));
      edit(input(changed, source));
      refuses(readInterface(source.bytes(), printJson(changed)),
              "source.interface");
    }
  });
  cases.run(
      "independent source correspondence rejects another valid anchor", [] {
        auto source = original(forward);
        mlir::DialectRegistry registry;
        registerDialects(registry);
        mlir::MLIRContext context(registry);
        context.loadAllAvailableDialects();
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
        require(bool(module), "original did not parse");
        bool changed = false;
        module->walk([&](protocol_ir::MathematicalOp function) {
          if (function.getSymName() != source.entry().protocol().symbol)
            return;
          SmallVector<protocol_ir::OracleInputOp> inputs;
          for (auto &op : function.getBody().front()) {
            if (auto input = mlir::dyn_cast<protocol_ir::OracleInputOp>(op))
              inputs.push_back(input);
            if (auto parts =
                    mlir::dyn_cast<protocol_ir::OracleComponentsOp>(op)) {
              if (!changed && inputs.size() == 2) {
                parts.getHandleMutable().assign(inputs[0].getHandle());
                changed = true;
              }
            }
          }
        });
        require(changed && mlir::succeeded(mlir::verify(*module)),
                "mutation must remain well formed");
        refuses(compareOriginal(source.entry(), *module),
                "source.correspondence");
      });
  return cases.result();
}
