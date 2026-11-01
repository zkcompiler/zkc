#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
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
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Oracle<K:OracleKind>=builtin("oracle",K);
type Oracles<K:OracleKind,M:nat>=builtin("oracle_sequence",K,M);
type O=Oracle<Fixed<F,16>>;
struct Meta{pub before:index,pub empty:(),pub after:index}
#[logical] pub struct State<K:OracleKind,M:nat>{
  secret:index,empty:(),pub left:Oracle<K>,pub meta:Meta,
  pub right:Oracle<K>,pub layers:Oracles<K,M>,tail:()
}
type S=State<Fixed<F,16>,0>;
)";
const char *relay = R"(
protocol Forward<K:OracleKind,M:nat> roles(B,A)
  (state:State<K,M>@A->B)->(out:State<K,M>@A->B){return(out=state);}
protocol Run roles(P,V)(state:S@P->V)->(out:S@P->V){
  let out=Forward<Fixed<F,16>,0> roles(V,P)(state);return(out=out);
}
)";
const char *bounded = R"(
#[logical] #[shape(left.rows,bound=L)] #[shape(right.rows,bound=R)]
#[shape(layers.rows,bound=L)]
struct Bounded<L:nat,R:nat>{
  secret:index,pub left:Oracle<Table<F>>,empty:(),
  pub right:Oracle<Table<F>>,pub layers:Oracles<Table<F>,0>
}
protocol Run roles(P,V)(state:Bounded<8,16>@P->V)
  ->(out:Bounded<8,16>@P->V){return(out=state);}
)";
CheckedProject checked(StringRef code, StringRef declarations = prefix) {
  auto project = take(capture(
      {{"m", declarations.str() + code.str(), "logical-record-layout.zkc"}}));
  return take(analyze(project).checkedProject());
}
CheckedOriginal original(StringRef code) {
  return take(prepareOriginal(
      take(zkc::test::closeNativeRun(checked(code), "m::Run"))));
}
const Declaration &run(const ClosedEntry &entry) { return entry.protocol(); }
void withModule(const CheckedOriginal &source,
                function_ref<void(mlir::ModuleOp)> body) {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
  require(bool(module), "fresh original did not parse");
  body(*module);
}
void accepted(const CheckedOriginal &source, bool structured = true) {
  auto view = take(readInterface(source.bytes(), source.interfaceJson()));
  if (auto error = compareInterface(source.entry(), view))
    throw std::runtime_error(toString(std::move(error)));
  take(admitOriginal(source.entry(), source.bytes(), source.interfaceJson()));
  withModule(source, [&](mlir::ModuleOp module) {
    take(compareOriginal(source.entry(), module));
    if (!structured) {
      refuses(protocol::exportStructuredSource(source.bytes(),
                                               run(source.entry()).symbol,
                                               *module.getContext()),
              "structured-source-product");
      return;
    }
    auto exported = take(protocol::exportStructuredSource(
        source.bytes(), run(source.entry()).symbol, *module.getContext()));
    require(!exported.bytes.empty(), "structured source export was empty");
  });
}
void logicalSchemas(json::Value &value,
                    function_ref<void(json::Object &)> change) {
  if (auto *object = value.getAsObject()) {
    for (auto &member : *object)
      logicalSchemas(member.second, change);
    if (object->getString("kind") == "logical_record")
      change(*object);
  } else if (auto *array = value.getAsArray())
    for (auto &item : *array)
      logicalSchemas(item, change);
}
json::Object &field(json::Object &schema, StringRef name) {
  for (auto &item : *schema.getArray("fields"))
    if (item.getAsObject()->getString("name") == name)
      return *item.getAsObject();
  throw std::runtime_error("missing fixture field: " + name.str());
}
void schemaMutation(const CheckedOriginal &source,
                    function_ref<void(json::Object &)> change) {
  auto document = take(json::parse(source.interfaceJson()));
  unsigned visited = 0;
  logicalSchemas(document, [&](json::Object &schema) {
    ++visited;
    change(schema);
  });
  require(visited != 0, "fixture did not export a logical record");
  refuses(readInterface(source.bytes(), printJson(document)),
          "source.interface");
}
protocol_ir::MathematicalOp root(mlir::ModuleOp module,
                                 const CheckedOriginal &source) {
  protocol_ir::MathematicalOp result;
  module.walk([&](protocol_ir::MathematicalOp function) {
    if (function.getSymName() == run(source.entry()).symbol)
      result = function;
  });
  require(bool(result), "missing native root");
  return result;
}
void readerRejectsActual(const CheckedOriginal &source, mlir::ModuleOp module) {
  std::string bytes;
  raw_string_ostream stream(bytes);
  module.print(stream);
  stream.flush();
  auto document = take(json::parse(source.interfaceJson()));
  (*document.getAsObject())["original"] =
      toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  auto result = readInterface(bytes, printJson(document));
  require(!result, "independent reader admitted changed actual transport");
  consumeError(result.takeError());
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run(
      "nominal body layout and expanded ABI retain every source field", [] {
        auto source = original(relay);
        accepted(source);
        Layouts layouts(source.entry());
        auto observed =
            take(layouts.protocolPort(run(source.entry()).inputs[0]));
        require(
            observed.body->type.kind == Type::Kind::LogicalRecord &&
                !observed.body->custody && !observed.body->oracleData &&
                observed.body->permissions == Permissions{true, true} &&
                observed.body->fields.size() == 7 &&
                observed.body->leaves.size() == 6 && observed.size() == 9,
            "logical product lost nominal fields or acquired a native carrier");
        require(observed.nativeOffsets ==
                    std::vector<unsigned>({0, 1, 3, 4, 5, 7, 9}),
                "body-to-ABI prefix differs");
        require(observed.body->fields[0].name == "secret" &&
                    observed.body->fields[1].layout->leaves.empty() &&
                    observed.body->fields[6].layout->leaves.empty(),
                "private or zero-leaf fields disappeared");
        require(observed.leaves.back().leaf.oracle()->maximum == 0 &&
                    observed.leaves.back().path == std::vector<unsigned>({5}),
                "zero-capacity sequence is not a direct logical leaf");
        refuses(layouts.packed(observed.body->type), "source.sequence");
        const auto &port = source.interface().selectedProtocol().inputs.front();
        require(port.schema->kind == Type::Kind::LogicalRecord &&
                    port.schema->leaves.empty() && !port.schema->oracleData &&
                    port.schema->fields.size() == 7 &&
                    port.native ==
                        std::vector<unsigned>({0, 1, 2, 3, 4, 5, 6, 7, 8}),
                "interface packed or omitted the logical declaration");
      });
  cases.run(
      "typed selectors distinguish body offsets, ABI offsets and anchors", [] {
        auto source = original(relay);
        Layouts layouts(source.entry());
        const auto &declaration = run(source.entry());
        auto ordinary = take(layouts.select(
            declaration,
            SpecificationSelector{false, 0, 1, {3, 2}, {}, false}));
        auto left = take(layouts.select(
            declaration, SpecificationSelector{false, 0, 0, {2}, {}, true}));
        auto right = take(layouts.select(
            declaration, SpecificationSelector{false, 0, 0, {4}, {}, true}));
        require(ordinary.offset == 4 && left.offset == 2 && right.offset == 6,
                "selector used a body offset for the expanded ABI");
        refuses(
            layouts.select(declaration,
                           SpecificationSelector{false, 0, 0, {}, {}, true}),
            "source.layout");
        refuses(
            layouts.select(declaration,
                           SpecificationSelector{false, 0, 0, {5}, {}, true}),
            "source.layout");
        // These observations grant no language access rights. The checker owns
        // whether a specification may author each private/anchor path.
      });
  cases.run("generic row bounds substitute independently of sequence capacity",
            [] {
              auto source = original(bounded);
              accepted(source);
              Layouts layouts(source.entry());
              auto observed =
                  take(layouts.protocolPort(run(source.entry()).inputs[0]));
              require(observed.body->fields[1].maximumRows == 8 &&
                          observed.body->fields[3].maximumRows == 16 &&
                          observed.body->fields[4].maximumRows == 8 &&
                          observed.leaves.back().leaf.oracle()->maximum == 0,
                      "field row bounds were conflated with sequence capacity");
              auto changed = *observed.body;
              changed.fields[1].maximumRows = 9;
              uint64_t remaining = 1000000;
              LayoutIdentities identities(remaining);
              require(take(identities.get(*observed.body)) !=
                          take(identities.get(changed)),
                      "logical schema identity omitted the field row bound");
            });
  cases.run("zero row maximum is present in both schema and actual binding",
            [] {
              auto source = original(R"(
#[logical] #[shape(word.rows,bound=Rows)]
struct Empty<Rows:nat>{hidden:(),pub word:Oracle<Table<F>>}
protocol Run roles(P,V)(state:Empty<0>@P->V)->(out:Empty<0>@P->V){return(out=state);}
)");
              accepted(source);
              require(source.interface()
                              .selectedProtocol()
                              .inputs[0]
                              .schema->fields[1]
                              .maximumRows == 0,
                      "zero row maximum was treated as absent");
            });
  cases.run(
      "generic calls with reordered roles preserve single-handle loop carries",
      [] {
        auto source = original(R"(
protocol Forward<K:OracleKind,M:nat> roles(B,A)
  (state:State<K,M>@A->B)->(out:State<K,M>@A->B){return(out=state);}
protocol Run roles(P,V)(state:S@P->V,n:index@(P,V))->(out:S@P->V){
  let mut current=state;
  for i in 0..n roles(P,V) max 2 {
    current=Forward<Fixed<F,16>,0> roles(V,P)(current);
  }
  return(out=current);
})");
        accepted(source);
        withModule(source, [&](mlir::ModuleOp module) {
          unsigned repeats = 0;
          module.walk([&](protocol_ir::RepeatOp repeat) {
            ++repeats;
            unsigned handles = 0;
            for (auto argument : repeat.getBody().front().getArguments())
              handles +=
                  bool(protocol_ir::getOracleFamilyKind(argument.getType()));
            require(handles == 3,
                    "loop carry used expanded ABI anchors as body fields");
          });
          require(repeats == 1, "fixture lost its loop");
          require(bool(mathematical::prepareProtocol(module)),
                  "record loop preparation failed");
        });
      });
  cases.run(
      "authored construction and projection reach production preparation", [] {
        auto source = original(R"(
protocol Forward roles(B,A)(state:S@A->B)->(out:S@A->B){return(out=state);}
protocol Run roles(P,V)(a:O@P->V,b:O@P->V)->(out:F@V){
  let layers=oracle.empty<Fixed<F,16>,0> roles(P,V)();
  let state=S{tail:(),right:b,meta:Meta{after:2,empty:(),before:1},
              left:a,empty:(),secret:0,layers:layers};
  let received=Forward roles(V,P)(state);
  let chosen=received.right;let out@V=query chosen at 0;return(out=out);
})");
        accepted(source);
        mlir::DialectRegistry registry;
        RunOptions options;
        options.entry = run(source.entry()).symbol;
        auto compiled = take(compileRun(
            source.bytes(), "logical-record-layout.mlir", options, registry));
        require(bool(compiled.compilation.oracleRealizationSnapshot()),
                "production did not retain checked oracle realization");
      });
  cases.run("equal-typed ordinary field swaps remain well formed and fail "
            "source correspondence",
            [] {
              auto source = original(relay);
              withModule(source, [&](mlir::ModuleOp module) {
                auto function = root(module, source);
                auto &returned = function.getBody().front().back();
                auto first = returned.getOperand(3),
                     second = returned.getOperand(4);
                returned.setOperand(3, second);
                returned.setOperand(4, first);
                require(mlir::succeeded(mlir::verify(module)),
                        "ordinary swap must remain well formed");
                refuses(compareOriginal(source.entry(), module),
                        "source.correspondence");
              });
            });
  cases.run("complete equal-typed handle pair swaps fail source correspondence",
            [] {
              auto source = original(relay);
              withModule(source, [&](mlir::ModuleOp module) {
                bool changed = false;
                root(module, source).walk([&](protocol_ir::ApplyOp call) {
                  auto data = call.getOperand(1), anchor = call.getOperand(2);
                  call->setOperand(1, call.getOperand(5));
                  call->setOperand(2, call.getOperand(6));
                  call->setOperand(5, data);
                  call->setOperand(6, anchor);
                  changed = true;
                });
                require(changed && mlir::succeeded(mlir::verify(module)),
                        "complete pair swap must remain well formed");
                readerRejectsActual(source, module);
                refuses(compareOriginal(source.entry(), module),
                        "source.correspondence");
              });
            });
  cases.run("independent reader rejects cross-paired data and anchors", [] {
    auto source = original(relay);
    withModule(source, [&](mlir::ModuleOp module) {
      bool changed = false;
      root(module, source).walk([&](protocol_ir::ApplyOp call) {
        auto anchor = call.getOperand(2);
        call->setOperand(2, call.getOperand(6));
        call->setOperand(6, anchor);
        changed = true;
      });
      require(changed, "fixture has no logical call");
      readerRejectsActual(source, module);
    });
  });
  cases.run("independent reader checks remapped component families", [] {
    auto source = original(relay);
    withModule(source, [&](mlir::ModuleOp module) {
      bool changed = false;
      root(module, source).walk([&](protocol_ir::OracleComponentsOp parts) {
        if (changed)
          return;
        mlir::OpBuilder builder(module.getContext());
        parts->setAttr("holder", builder.getStringAttr(nativeRoleName(1)));
        parts->setAttr(
            "receivers",
            builder.getArrayAttr({builder.getStringAttr(nativeRoleName(0))}));
        changed = true;
      });
      require(changed, "fixture has no logical component view");
      readerRejectsActual(source, module);
    });
  });
  cases.run("logical record roots cannot acquire a whole-port row bound", [] {
    auto source = original(relay);
    auto document = take(json::parse(source.interfaceJson()));
    for (auto &protocol : *document.getAsObject()->getArray("protocols"))
      for (StringRef direction : {"inputs", "outputs"})
        for (auto &port : *protocol.getAsObject()->getArray(direction)) {
          auto &object = *port.getAsObject();
          if (object.getObject("schema")->getString("kind") == "logical_record")
            object["maximum_rows"] = "16";
        }
    refuses(readInterface(source.bytes(), printJson(document)),
            "source.interface");
  });
  cases.run("independent reader rejects reversed equal-typed entry bindings",
            [] {
              auto source = original(relay);
              withModule(source, [&](mlir::ModuleOp module) {
                SmallVector<protocol_ir::OracleInputOp> bindings;
                for (auto binding : root(module, source)
                                        .getBody()
                                        .front()
                                        .getOps<protocol_ir::OracleInputOp>())
                  bindings.push_back(binding);
                require(bindings.size() >= 3,
                        "fixture has fewer than three handle leaves");
                bindings[0]->moveBefore(bindings[1]->getNextNode());
                readerRejectsActual(source, module);
              });
            });
  cases.run(
      "changed actual field bounds fail independent and source comparison", [] {
        auto source = original(bounded);
        withModule(source, [&](mlir::ModuleOp module) {
          bool changed = false;
          root(module, source).walk([&](protocol_ir::OracleInputOp input) {
            if (changed)
              return;
            mlir::OpBuilder builder(module.getContext());
            auto rows = builder.getIntegerAttr(
                mlir::IntegerType::get(module.getContext(), 64,
                                       mlir::IntegerType::Unsigned),
                APInt(64, 9));
            input->setAttr("shape_bounds",
                           builder.getDictionaryAttr(
                               {builder.getNamedAttr("rows", rows)}));
            changed = true;
          });
          require(changed, "fixture lost its bound handle");
          readerRejectsActual(source, module);
          refuses(compareOriginal(source.entry(), module),
                  "source.correspondence");
        });
      });
  for (StringRef mutation :
       {"bound", "missing-bound", "capacity", "missing-private", "missing-unit",
        "nominal", "invented-bound", "arbitrary-data", "missing-nested-unit",
        "construction"})
    cases.run("independent schema refusal: " + mutation, [&] {
      auto source = original(
          mutation == "bound" || mutation == "missing-bound" ? bounded : relay);
      schemaMutation(source, [&](json::Object &schema) {
        if (mutation == "bound")
          field(schema, "left")["maximum_rows"] = "9";
        else if (mutation == "missing-bound")
          field(schema, "left").erase("maximum_rows");
        else if (mutation == "capacity")
          (*field(schema, "layers").getObject("schema"))["maximum"] = "1";
        else if (mutation == "nominal") {
          schema["identity"] = std::string(64, 'a');
        } else if (mutation == "construction")
          schema["constructible"] = true;
        else if (mutation == "missing-nested-unit") {
          auto &members =
              *field(schema, "meta").getObject("schema")->getArray("fields");
          auto empty = llvm::find_if(members, [](const auto &member) {
            return member.getAsObject()->getString("name") == "empty";
          });
          require(empty != members.end(),
                  "fixture lacks an empty nested field");
          members.erase(empty);
        } else if (mutation == "invented-bound")
          field(schema, "secret")["maximum_rows"] = "8";
        else if (mutation == "arbitrary-data") {
          auto *oracle = field(schema, "left").getObject("schema");
          json::Value copy = *oracle->get("data_schema");
          auto *data = oracle->getObject("data_schema");
          (*data)["kind"] = "record";
          (*data)["identity"] = std::string(64, 'b');
          (*data)["type"] = "m::ForgedData";
          (*data)["fields"] = json::Array{json::Object{
              {"name", "value"}, {"offset", 0}, {"schema", std::move(copy)}}};
        } else {
          auto &fields = *schema.getArray("fields");
          auto name = mutation == "missing-unit" ? "tail" : "secret";
          auto found = llvm::find_if(fields, [&](const auto &item) {
            return item.getAsObject()->getString("name") == name;
          });
          require(found != fields.end(), "missing mutation field");
          fields.erase(found);
        }
      });
    });
  cases.run("logical schemas cannot nest under another logical field", [] {
    auto source = original(relay);
    schemaMutation(source, [&](json::Object &schema) {
      auto *meta = field(schema, "meta").getObject("schema");
      (*meta)["kind"] = "logical_record";
      (*meta)["leaves"] = json::Array{};
    });
  });
  cases.run(
      "ordinary variant fields retain their complete nominal payload", [] {
        auto source = original(R"(
enum Choice{Some(index,()),None()}
#[logical] struct WithChoice{hidden:(),pub choice:Choice,pub word:O}
protocol Run roles(P,V)(state:WithChoice@P->V)
  ->(out:WithChoice@P->V){return(out=state);}
)");
        accepted(source, false);
        schemaMutation(source, [&](json::Object &schema) {
          auto &alternatives = *field(schema, "choice")
                                    .getObject("schema")
                                    ->getArray("alternatives");
          auto &fields = *alternatives[0].getAsObject()->getArray("fields");
          require(fields.size() == 2,
                  "variant lost its zero-leaf payload field");
          fields.pop_back();
        });
      });
  cases.run(
      "nominal source identity changes cannot reuse equal flattened leaves",
      [] {
        auto source = original(relay);
        std::string renamed(prefix);
        size_t at = 0;
        while ((at = renamed.find("State", at)) != std::string::npos) {
          renamed.replace(at, 5, "Other");
          at += 5;
        }
        std::string renamedRelay(relay);
        at = 0;
        while ((at = renamedRelay.find("State", at)) != std::string::npos) {
          renamedRelay.replace(at, 5, "Other");
          at += 5;
        }
        auto alternate = take(zkc::test::closeNativeRun(
            checked(renamedRelay, renamed), "m::Run"));
        withModule(source, [&](mlir::ModuleOp module) {
          refuses(compareOriginal(alternate, module), "source.correspondence");
        });
      });
  cases.run("body-only logical declarations retain nominal identity", [] {
    const char *code = R"(
protocol Run roles(P,V)(a:O@P->V,b:O@P->V)->(out:F@V){
  let layers=oracle.empty<Fixed<F,16>,0> roles(P,V)();
  let state=S{secret:0,empty:(),left:a,
              meta:Meta{before:1,empty:(),after:2},right:b,layers:layers,tail:()};
  let chosen=state.right;let out@V=query chosen at 0;return(out=out);
}
)";
    auto source = original(code);
    accepted(source);
    std::string renamed(prefix);
    size_t at = 0;
    while ((at = renamed.find("State", at)) != std::string::npos) {
      renamed.replace(at, 5, "Other");
      at += 5;
    }
    auto alternate =
        take(zkc::test::closeNativeRun(checked(code, renamed), "m::Run"));
    withModule(source, [&](mlir::ModuleOp module) {
      refuses(compareOriginal(alternate, module), "source.correspondence");
    });
  });
  return cases.result();
}
