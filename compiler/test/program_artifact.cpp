#include "mlir/IR/Builders.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace sf = scopedFinite;
namespace sc = scopedComputation;
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "fixture pass refused");
}
constexpr StringLiteral fixture = R"mlir(module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:i1,%b:i1):
   %both = arith.andi %a,%b : i1
   %seen = protocol.exchange %both {site="message",sender="P",receiver="V"} : i1
   "protocol.return"(%both,%seen) : (i1,i1)->()
 }) {sym_name="main",function_type=(i1,i1)->(i1,i1),roles=["P","V"],input_roles=[["P"],["P"]],output_roles=[["P"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
program::Participants readProgram(ModuleOp module) {
  auto json = take(protocol::exportModule(module));
  auto decoded = take(program::decode(json));
  return decoded;
}
program::Function &calculation(program::Participants &program) {
  for (auto &function : program.functions)
    if (function.arguments.size() == 2)
      return function;
  throw std::runtime_error("missing calculation");
}

constexpr unsigned capacityCalls = 1024;
constexpr StringLiteral capacityFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="numerical",contract="numerical.sum",arguments=["bls12-381.fr", array<i1: false>],implementation="",function_type=(!runtime.scope, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="msb",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="dense",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks/poly.fold",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()
 func.func @work(%scope:!runtime.scope,%table:!T,%rows:ui64,%a:!F)->!exec.outcome<(!T)> attributes {no_inline,runtime.origin=["work",[]]} {
   %result = "exec.returned"(%table) : (!T)->!exec.outcome<(!T)>
   func.return %result : !exec.outcome<(!T)>
 }
 "protocol.func"() ({ ^entry(%table:!T,%rows:ui64,%a:!F):
   %r = "protocol.local_call"(%table,%rows,%a) {callee=@work,role="P",site="work"} : (!T,ui64,!F)->!T
   "protocol.return"(%r) : (!T)->()
 }) {sym_name="main",function_type=(!T,ui64,!F)->!T,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

OwningOpRef<ModuleOp> capacitySource(MLIRContext &context, StringRef body) {
  auto module = parseSourceString<ModuleOp>(capacityFixture, &context);
  require(bool(module), "capacity fixture parse refused");
  run(*module, protocol::createProjectProtocolPass(false));
  run(*module, protocol::createLowerMathPass());
  auto function = sf::function(*module, "work");
  function.getBody().dropAllReferences();
  function.getBody().getBlocks().clear();
  OpBuilder builder(&context);
  builder.setInsertionPointToEnd(function.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, function);
  auto empty = builder.getArrayAttr({});
  auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
      function, builder.getStringAttr("numerical"));
  require(bool(binding), "capacity fixture lost its binding");
  auto parameters = take(protocol::decodeInvocationParameters(
      binding.getContract(), binding.getArgumentsAttr(), {body.str()}));
  auto emit = [&](StringRef binding, ValueRange inputs, Type result,
                  StringRef site, ArrayAttr attributes) {
    return control
        .invoke("exec.apply", TypeRange{result}, control.scoped(inputs),
                {builder.getNamedAttr(
                     "binding", FlatSymbolRefAttr::get(&context, binding)),
                 builder.getNamedAttr("site", builder.getStringAttr(site)),
                 builder.getNamedAttr("parameters", attributes)})
        .front();
  };
  Value table = function.getArgument(1);
  for (unsigned i = 0; i != capacityCalls; ++i) {
    auto suffix = std::to_string(i);
    auto value =
        emit("numerical",
             ValueRange{function.getArgument(2), function.getArgument(3)},
             function.getArgument(3).getType(), "sum" + suffix, parameters);
    table = emit("msb", ValueRange{table, value}, table.getType(),
                 "msb" + suffix, empty);
    table = emit("dense", ValueRange{table, value}, table.getType(),
                 "dense" + suffix, empty);
  }
  control.returned(table);
  require(succeeded(verify(*module)), "capacity source is not well formed");
  return module;
}

void replaceSourceBodies(ModuleOp module, StringRef body, size_t count) {
  size_t seen = 0;
  ArrayAttr parameters;
  module.walk([&](exec::ApplyOp op) {
    if (sf::contract(op) == "numerical.sum" && seen++ < count) {
      if (!parameters) {
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            op, op.getBindingAttr());
        require(bool(binding), "capacity invocation lost its binding");
        parameters = take(protocol::decodeInvocationParameters(
            binding.getContract(), binding.getArgumentsAttr(), {body.str()}));
      }
      op.setParametersAttr(parameters);
    }
  });
  require(seen == capacityCalls && count <= seen,
          "capacity source lost numerical calls");
}

void replaceCarrierBodies(llvm::json::Value &carrier, StringRef body,
                          size_t count) {
  size_t seen = 0;
  for (auto &function : *(*carrier.getAsArray())[2].getAsArray())
    for (auto &instruction : *(*function.getAsArray())[4].getAsArray()) {
      auto &record = *instruction.getAsArray();
      if (record[0].getAsString() == "op" &&
          record[2].getAsString() == "numerical" && seen++ < count)
        (*record[3].getAsArray())[0] = body.str();
    }
  require(seen == capacityCalls && count <= seen,
          "capacity carrier lost numerical calls");
}

size_t carrierNodes(const llvm::json::Value &value) {
  size_t count = 1;
  if (auto *array = value.getAsArray())
    for (const auto &element : *array)
      count += carrierNodes(element);
  return count;
}

std::string printed(ModuleOp module) {
  std::string text;
  llvm::raw_string_ostream out(text);
  module->print(out, OpPrintingFlags().printGenericOpForm().enableDebugInfo());
  return text;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto module = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(module), "fixture parse refused");
  run(*module, protocol::createProjectProtocolPass(false));
  run(*module, protocol::createLowerMathPass());
  cases.run("public readers refuse unresolved mathematical requests", [&] {
    unsigned calls = 0;
    module->walk([&](exec::ComputeOp) { ++calls; });
    require(calls, "logical fixture lost its mathematical request");
    auto structural = protocol::readExecutionModel(module->getOperation());
    require(!structural, "public reader published unresolved computations");
    require(namesIdentifier(llvm::toString(structural.takeError()),
                            "execution-cfg"),
            "unresolved computation reader lost its diagnostic");
    auto exported = protocol::exportProgram(module->getOperation());
    require(!exported, "program export published unresolved computations");
    llvm::consumeError(exported.takeError());
    auto carrier = protocol::exportModule(module->getOperation());
    require(!carrier, "module export published unresolved computations");
    llvm::consumeError(carrier.takeError());
  });
  require(succeeded(protocol::lowerPhysical(*module)),
          "physical lowering refused");
  auto original = readProgram(*module);
  auto encoded = [&](const program::Participants &program) {
    if (auto e = program::checkStructure(program))
      throw std::runtime_error(llvm::toString(std::move(e)));
    if (auto e = protocol::admit(program))
      throw std::runtime_error(llvm::toString(std::move(e)));
    return printJson(program::encode(program));
  };
  cases.run("actual decoded artifact", [&] {
    auto checked =
        take(protocol::verifyProgramArtifact(*module, encoded(original)));
    require(program::encode(checked) == program::encode(original),
            "verified artifact changed on return");
  });
  cases.run(
      "loop capture aliases preserve exact actual-value correspondence", [&] {
        auto source = parseSourceString<ModuleOp>(R"mlir(
module { "protocol.module"() ({
  "protocol.participant"() ({ ^entry(%n:ui64, %x:i1, %y:i1):
    "protocol.loop"(%n,%x,%x,%y) ({ ^body(%i:ui64,%a:i1,%b:i1,%c:i1):
      "protocol.send"(%a) {site="a",schema="message",peer="Q"} : (i1)->()
      "protocol.send"(%b) {site="b",schema="message",peer="Q"} : (i1)->()
      "protocol.yield"() : ()->()
    }) {site="loop",carried=0:i64,count="",parameter=false,maximum=8:i64}
      : (ui64,i1,i1,i1)->()
    "protocol.finish"() : ()->()
  }) {sym_name="p",function_type=(ui64,i1,i1)->(),instance="example",role="P"} : ()->()
  "protocol.entry"() {sym_name="main",targets=[["P",@p]]} : ()->()
}) {profile=#protocol.profile<exec>} : ()->() }
)mlir",
                                                  &context);
        require(bool(source), "loop fixture parse refused");
        require(succeeded(protocol::lowerPhysical(*source)),
                "loop physical selection refused");
        auto actual = readProgram(*source);
        take(protocol::verifyProgramArtifact(*source, encoded(actual)));
        auto &loop =
            *actual.participants.front().body.front().get<program::Loop>();
        require(loop.captures.size() == 2, "distinct actual capture was lost");
        auto changed = actual;
        auto &changedLoop =
            *changed.participants.front().body.front().get<program::Loop>();
        changedLoop.body[1].get<program::Send>()->input = loop.captures.back();
        if (auto error = protocol::admit(changed))
          throw std::runtime_error(llvm::toString(std::move(error)));
        refuses(protocol::verifyProgramArtifact(*source, encoded(changed)),
                "artifact-correspondence");
        loop.captures.pop_back();
        if (auto error = protocol::admit(actual))
          throw std::runtime_error(llvm::toString(std::move(error)));
        refuses(protocol::verifyProgramArtifact(*source, encoded(actual)),
                "artifact-correspondence");
      });
  cases.run("current program shape retains actual arguments", [&] {
    auto artifact = program::encode(original);
    auto &root = *artifact.getAsArray();
    require(root.size() == 5 && root[0].getAsString() == "zkc.program/0",
            "wrong current root grammar");
    auto &participant = *root[3].getAsArray()->front().getAsArray();
    require(participant.size() == 8 &&
                participant[4].getAsArray()->size() ==
                    original.participants.front().arguments.size(),
            "actual participant arguments were lost");
  });
  cases.run("unknown program tag refuses with valid root arity", [&] {
    auto artifact = program::encode(original);
    (*artifact.getAsArray())[0] = "invalid.program";
    refuses(program::decode(artifact), "interactive-format");
  });
  cases.run("program root refuses an extra field", [&] {
    auto artifact = program::encode(original);
    auto &root = *artifact.getAsArray();
    root.insert(root.begin() + 2, llvm::json::Array{});
    refuses(program::decode(artifact), "interactive-shape");
  });
  cases.run("program root refuses a missing field", [&] {
    auto artifact = program::encode(original);
    auto &root = *artifact.getAsArray();
    root.pop_back();
    refuses(program::decode(artifact), "interactive-shape");
  });
  cases.run("unexpanded algorithm calls cannot enter the program carrier", [&] {
    auto candidate = original;
    auto &function = calculation(candidate);
    function.body.front().value = program::LocalApply{"callee", {}, {}};
    auto refusal = program::checkStructure(candidate);
    require(bool(refusal),
            "unexpanded algorithm request entered physical carrier");
    llvm::consumeError(std::move(refusal));
  });
  cases.run("program codecs require defined callable bodies", [&] {
    auto json = program::encode(original);
    auto &functions = *(*json.getAsArray())[2].getAsArray();
    (*functions.front().getAsArray())[4] = "external";
    auto decoded = program::decode(json);
    require(!decoded, "undefined callable passed the physical decoder");
    require(namesIdentifier(llvm::toString(decoded.takeError()),
                            "interactive-external-body"),
            "wrong undefined callable refusal");
  });
  cases.run(
      "decoder bounds programmatic strings before semantic admission", [&] {
        // Direct JSON values exercise Program's own size bound
        // independently of the text parser's byte limit. LLVM writes
        // backspace/form feed as six bytes, so these shorter strings also
        // exceed the encoded-size ceiling.
        for (char value : {'x', '\b', '\f'}) {
          auto json = program::encode(original);
          auto &functions = *(*json.getAsArray())[2].getAsArray();
          (*functions.front().getAsArray())[1] =
              std::string(value == 'x' ? program::artifactByteLimit
                                       : program::artifactByteLimit / 6 + 1,
                          value);
          refuses(program::decode(json), "source-limit");
        }
      });
  cases.run("compact node budget is independent of bytes", [&] {
    for (size_t count : {20000u, 24000u}) {
      auto candidate = original;
      auto &body = candidate.functions.front().body;
      program::Instruction release;
      release.value = program::Release{program::Names(16, "x")};
      body.assign(count, release);
      // Each release is ["release", [sixteen names]]: 19 JSON nodes.
      // Both programs remain below the byte ceiling; only the larger one
      // exceeds the node ceiling, before semantic names/custody admission.
      if (count == 20000) {
        if (auto e = program::checkStructure(candidate))
          throw std::runtime_error(llvm::toString(std::move(e)));
        require(printJson(program::encode(candidate)).size() <
                    program::artifactByteLimit,
                "node control unexpectedly exhausted bytes");
      } else {
        auto refusal = program::checkStructure(candidate);
        require(bool(refusal), "node ceiling was not enforced");
        require(
            namesIdentifier(llvm::toString(std::move(refusal)), "source-limit"),
            "unexpected node-ceiling refusal");
      }
    }
  });
  cases.run("production capacity includes escaped bodies and conversions", [&] {
    auto expression = [&](unsigned negations) {
      std::vector<ring::Node> nodes{ring::Node::slot(0)};
      for (unsigned i = 0; i != negations; ++i)
        nodes.push_back(ring::Node::neg(i));
      auto body =
          printJson(take(ring::Expression::create(
                             {{"bls12-381.fr"}}, std::move(nodes), {negations}))
                        .encode());
      require(body.size() <= protocol::NumericalLimits::bodyBytes,
              "capacity control exceeded the per-body limit");
      take(protocol::readNumericalExpression(body, "bls12-381.fr", 1));
      return body;
    };
    auto small = expression(0), large = expression(320);
    auto source = capacitySource(context, small);
    auto compact = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
    // Use the public production edge, which installs the real complete-program
    // checkProgramCapacity. No test capacity callback or numerical rewriting.
    require(succeeded(protocol::lowerPhysical(*compact)) &&
                succeeded(verify(*compact)),
            "compact production control refused");
    unsigned numerical = 0, msb = 0, dense = 0, conversions = 0;
    llvm::DenseMap<Value, exec::ApplyOp> producers;
    compact->walk([&](exec::ApplyOp op) {
      for (auto value : sc::payload(op))
        producers[value] = op;
    });
    auto implementation = [](exec::ApplyOp op) {
      auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
          op, op.getBindingAttr());
      require(bool(binding), "physical invocation lost its binding");
      return binding.getImplementation();
    };
    compact->walk([&](exec::ApplyOp op) {
      auto selected = implementation(op);
      numerical += selected == "arkworks/numerical.sum";
      conversions += selected == "arkworks/table.relayout";
      msb += selected == "arkworks-msb/poly.fold";
      dense += selected == "arkworks/poly.fold";
      if (selected == "arkworks-msb/poly.fold" ||
          selected == "arkworks/poly.fold") {
        auto crossing = producers.lookup(op.getInputs().front());
        require(crossing &&
                    implementation(crossing) == "arkworks/table.relayout",
                "pinned fold did not consume an inserted layout conversion");
      }
    });
    require(numerical == capacityCalls && msb == capacityCalls &&
                dense == capacityCalls && conversions == 2 * capacityCalls,
            "production control lost calls or representation crossings");
    auto carrier = take(protocol::exportModule(*compact));
    auto compactBytes = printJson(carrier).size();
    auto smallEscaped = printJson(llvm::json::Value(small)).size();
    auto largeEscaped = printJson(llvm::json::Value(large)).size();
    require(largeEscaped > large.size() + 2 && largeEscaped > smallEscaped &&
                compactBytes < program::artifactByteLimit,
            "capacity controls lost escaping or compact headroom");
    auto growth = largeEscaped - smallEscaped;
    auto belowCount = (program::artifactByteLimit - compactBytes) / growth;
    require(belowCount > 1 && belowCount < capacityCalls,
            "bounded body replacements do not straddle the artifact limit");

    // These JSON witnesses retain every production-selected binding, port,
    // conversion, site and SSA name. Only canonical parameter strings change.
    // They may be measured above the limit without calling Program::encode on
    // a model that has not passed checkStructure.
    auto belowCarrier = carrier;
    replaceCarrierBodies(belowCarrier, large, belowCount);
    auto belowBytes = printJson(belowCarrier).size();
    replaceCarrierBodies(carrier, large, belowCount + 1);
    auto aboveBytes = printJson(carrier).size();
    auto nodes = carrierNodes(carrier);
    require(belowBytes == compactBytes + belowCount * growth &&
                aboveBytes == belowBytes + growth &&
                belowBytes <= program::artifactByteLimit &&
                aboveBytes > program::artifactByteLimit &&
                nodes < program::artifactNodeLimit,
            "complete witnesses do not isolate the artifact byte ceiling");
    auto escapingBytes =
        (belowCount + 1) * (largeEscaped - large.size() - 2) +
        (capacityCalls - belowCount - 1) * (smallEscaped - small.size() - 2);
    require(aboveBytes - escapingBytes < program::artifactByteLimit,
            "unescaped accounting would already exhaust artifact bytes");

    auto below = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
    replaceSourceBodies(*below, large, belowCount);
    require(succeeded(verify(*below)), "below-limit source is not well formed");
    require(succeeded(protocol::lowerPhysical(*below)) &&
                succeeded(verify(*below)),
            "below-limit production lowering refused");
    require(take(protocol::exportModule(*below)) == belowCarrier,
            "production carrier differs from the measured complete witness");

    auto above = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
    replaceSourceBodies(*above, large, belowCount + 1);
    // This must pass the logical source's own byte, node and executable gates.
    // The refusal must occur after physical ports and conversions are chosen.
    require(succeeded(verify(*above)), "above-limit source is not well formed");
    auto before = printed(*above);
    std::vector<Operation *> beforeOperations;
    above->walk([&](Operation *op) { beforeOperations.push_back(op); });
    std::string diagnostic;
    std::vector<std::string> codes;
    bool refused;
    {
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &value) {
        llvm::raw_string_ostream out(diagnostic);
        value.print(out);
        out << '\n';
        for (const auto &refusal : diagnostics::refusals(value))
          codes.push_back(refusal.code);
        return success();
      });
      refused = failed(protocol::lowerPhysical(*above));
    }
    require(refused && codes == std::vector<std::string>{"source-limit"},
            "above-limit production lowering missed source-limit: " +
                diagnostic);
    std::vector<Operation *> afterOperations;
    above->walk([&](Operation *op) { afterOperations.push_back(op); });
    require(printed(*above) == before && beforeOperations == afterOperations,
            "artifact-capacity refusal changed the source module");
    llvm::outs() << "artifact capacity: " << belowCount << "/" << belowCount + 1
                 << " large bodies, " << belowBytes << "/" << aboveBytes
                 << " bytes (limit " << program::artifactByteLimit << "), "
                 << nodes << " nodes, " << conversions
                 << " inserted conversions\n";
  });
  cases.run("program text bounds use their format owner", [&] {
    auto text = encoded(original);
    text.resize(program::artifactByteLimit, ' ');
    auto parsed = take(program::parse(text));
    require(program::encode(parsed) == program::encode(original),
            "padding changed the decoded program");
    refuses(parseJson(text), "byte-limit");
    text.push_back(' ');
    refuses(program::parse(text), "byte-limit");
  });
  cases.run("native logical origin arguments round trip", [&] {
    auto candidate = original;
    calculation(candidate).origin->arguments = {{"F", "bls12-381.fr"}};
    auto json = take(parseJson(encoded(candidate)));
    auto decoded = take(program::decode(json));
    if (auto e = protocol::admit(decoded))
      throw std::runtime_error(llvm::toString(std::move(e)));
    require(program::encode(decoded) == json, "logical arguments were lost");
  });
  auto negative =
      [&](StringRef name, StringRef code,
          llvm::function_ref<void(program::Participants &)> mutate) {
        cases.run(name, [&] {
          auto candidate = original;
          mutate(candidate);
          auto bytes = encoded(candidate); // Every mutant remains executable.
          auto result = protocol::verifyProgramArtifact(*module, bytes);
          require(!result, "wrong artifact passed correspondence");
          auto diagnostic = llvm::toString(result.takeError());
          require(namesIdentifier(diagnostic, code),
                  "wrong refusal code: " + diagnostic);
        });
      };
  negative("serialized primitive uses wrong operand",
           "execution-correspondence", [&](auto &p) {
             for (auto &instruction : calculation(p).body)
               if (auto *operation =
                       instruction.template get<program::Operation>()) {
                 operation->inputs[1] = operation->inputs[0];
                 return;
               }
             throw std::runtime_error("missing primitive");
           });
  negative("serialized local argument order changed",
           "execution-correspondence", [&](auto &p) {
             auto &function = calculation(p);
             std::swap(function.arguments[0], function.arguments[1]);
           });
  negative("serialized local return changed", "execution-correspondence",
           [&](auto &p) {
             auto &function = calculation(p);
             function.body.back().template get<program::Return>()->values[0] =
                 function.arguments[0].name;
           });
  negative("serialized send uses local input", "artifact-correspondence",
           [&](auto &p) {
             for (auto &participant : p.participants)
               for (auto &instruction : participant.body)
                 if (auto *send = instruction.template get<program::Send>()) {
                   send->input = participant.arguments.front().name;
                   return;
                 }
             throw std::runtime_error("missing send");
           });
  negative("serialized entry renamed", "artifact-correspondence",
           [&](auto &p) { p.entries.front().name = "other"; });
  negative("serialized retained origin changed", "execution-correspondence",
           [&](auto &p) { calculation(p).origin->definition = "other"; });
  cases.run("consistent SSA renaming is permitted", [&] {
    auto renamed = original;
    auto &function = calculation(renamed);
    auto old = function.arguments[0].name;
    function.arguments[0].name = "renamed";
    program::walk(function.body, [&](program::Instruction &instruction) {
      if (auto *op = instruction.get<program::Operation>())
        for (auto &input : op->inputs)
          if (input == old)
            input = "renamed";
    });
    take(protocol::verifyProgramArtifact(*module, encoded(renamed)));
  });
  cases.run("removed serialized storage release", [&] {
    auto released = OwningOpRef<ModuleOp>(cast<ModuleOp>((*module)->clone()));
    require(succeeded(protocol::releaseLocalStorage(*released)),
            "storage pass refused");
    auto candidate = readProgram(*released);
    bool removed = false;
    for (auto &function : candidate.functions)
      for (auto it = function.body.begin(); it != function.body.end(); ++it)
        if (it->get<program::Release>()) {
          function.body.erase(it);
          removed = true;
          break;
        }
    require(removed, "missing released value");
    auto error = protocol::verifyProgramArtifact(*released, encoded(candidate));
    require(!error && namesIdentifier(llvm::toString(error.takeError()),
                                      "execution-correspondence"),
            "removed release escaped");
  });
  cases.run("hostile storage releases fail Program admission", [&] {
    for (unsigned mutation = 0; mutation != 5; ++mutation) {
      auto candidate = original;
      auto &function = calculation(candidate);
      const auto input = function.arguments.front().name;
      program::Instruction release{"", program::Release{{input}}};
      StringRef code;
      if (mutation == 0) {
        function.body.insert(function.body.begin(), release);
        code = "interactive-resource-reuse";
      } else if (mutation == 1) {
        function.body.insert(function.body.end() - 1, {release, release});
        code = "interactive-release-unavailable";
      } else if (mutation == 2) {
        release.get<program::Release>()->values.clear();
        function.body.insert(function.body.begin(), release);
        code = "interactive-release-empty";
      } else if (mutation == 3) {
        release.site = "unexpected";
        function.body.insert(function.body.begin(), release);
        auto refusal = program::checkStructure(candidate);
        require(bool(refusal) &&
                    namesIdentifier(llvm::toString(std::move(refusal)),
                                    "source-model-shape"),
                "unencodable release site passed structure checking");
        continue;
      } else {
        auto &body = candidate.participants.front().body;
        body.insert(body.begin(), release);
        code = "interactive-release-context";
      }
      // Exercise the portable decoder before the independent semantic gate.
      if (auto error = program::checkStructure(candidate))
        throw std::runtime_error(llvm::toString(std::move(error)));
      auto decoded = take(program::decode(program::encode(candidate)));
      auto refusal = protocol::admit(decoded);
      require(bool(refusal) &&
                  namesIdentifier(llvm::toString(std::move(refusal)), code),
              "hostile release missed its admission boundary");
    }
  });
  cases.run("participant record refuses an extra empty field", [&] {
    auto artifact = program::encode(original);
    auto &participant =
        *(*artifact.getAsArray())[3].getAsArray()->front().getAsArray();
    participant.insert(participant.begin() + 4, llvm::json::Array{});
    refuses(program::decode(artifact), "interactive-record");
  });
  cases.run("participant composition opcode is not in the carrier", [&] {
    auto artifact = program::encode(original);
    auto &participant =
        *(*artifact.getAsArray())[3].getAsArray()->front().getAsArray();
    participant[6].getAsArray()->insert(participant[6].getAsArray()->begin(),
                                        llvm::json::Array{"call", "invoke", "p",
                                                          llvm::json::Array{},
                                                          llvm::json::Array{}});
    refuses(program::decode(artifact), "interactive-instruction");
  });
  return cases.result();
}
