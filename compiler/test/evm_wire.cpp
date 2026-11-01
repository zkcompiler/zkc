#include "../lib/Target/Evm/Runtime.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Target/Evm/Target.h"
#include "zkc/Target/Evm/Wire.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
data::VariantType variant(MLIRContext &context, StringRef name,
                          ArrayRef<SmallVector<Type>> payloads) {
  SmallVector<data::AlternativeAttr> alternatives;
  for (auto [i, payload] : enumerate(payloads))
    alternatives.push_back(data::AlternativeAttr::get(
        &context, StringAttr::get(&context, "arm" + std::to_string(i)),
        payload));
  return data::VariantType::get(
      &context, data::importVariantIdentity(&context, json::Value(name)),
      alternatives);
}
Type fixture(MLIRContext &context, StringRef name) {
  if (name.consume_front("field:"))
    return algebra::FieldType::get(&context, name);
  if (name.consume_front("vector:"))
    return algebra::FieldVectorType::get(&context, name);
  if (name.consume_front("root:"))
    return commitment::VectorObjectType::get(&context, name, "commitment");
  if (name.consume_front("path:"))
    return commitment::VectorObjectType::get(&context, name, "proof");
  if (name.consume_front("array:")) {
    uint64_t length = 0;
    require(!name.getAsInteger(10, length), "bad fixed-array fixture length");
    return algebra::FieldArrayType::get(&context, "bls12-381.fr", length);
  }
  if (name == "index")
    return IntegerType::get(&context, 64, IntegerType::Unsigned);
  if (name == "bool")
    return IntegerType::get(&context, 1);
  if (name == "bytes")
    return data::BytesType::get(&context);
  if (name == "indices")
    return algebra::IndicesType::get(&context);
  if (name == "empty")
    return variant(context, "Empty", {{}});
  if (name == "nested") {
    auto item =
        variant(context, "Item",
                {{},
                 {fixture(context, "bytes"), fixture(context, "index"),
                  fixture(context, "vector:koala-bear.ext4-binomial3")}});
    return variant(context, "Envelope",
                   {{},
                    {data::SequenceType::get(&context, item),
                     fixture(context, "indices"), fixture(context, "bool")}});
  }
  if (name.consume_front("sequence:"))
    return data::SequenceType::get(&context, fixture(context, name));
  return {};
}
std::string valueNames(unsigned count) {
  std::string result;
  for (unsigned i = 0; i < count; ++i) {
    if (i)
      result += ", ";
    result += "v" + std::to_string(i);
  }
  return result;
}
constexpr StringLiteral boundarySource = R"mlir(
module { "protocol.module"() ({
  "protocol.func"() ({
    %ok = arith.constant true
    "protocol.return"(%ok) : (i1) -> ()
  }) {sym_name="main", function_type=()->i1, roles=["P","V"],
      input_roles=[], output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr StringLiteral zeroEndpoint = R"mlir(
module {
  func.func private @verify_endpoint() -> i1 attributes {
    evm.entry, evm.logical_type=()->i1, evm.output_ports=[0:i64]} {
    %ok = arith.constant true
    func.return %ok : i1
  }
})mlir";
constexpr StringLiteral managedEndpoint = R"mlir(
module {
  func.func private @verify_endpoint(%generation:i64) -> (i1,i64) attributes {
    evm.entry,
    evm.logical_type=(!runtime.capability<transcript,"hash-chain.keccak256.bls12-381.fr64be/0">)->(i1,!runtime.capability<transcript,"hash-chain.keccak256.bls12-381.fr64be/0">),
    evm.output_ports=[0:i64]} {
    %ok = arith.constant true
    func.return %ok, %generation : i1,i64
  }
})mlir";
NativeProofPolicy boundaryPolicy(bool managed) {
  NativeProofPolicy policy;
  policy.entry = "main";
  policy.producer = "P";
  policy.validator = "V";
  if (managed)
    policy.suite = "hash-chain.keccak256.bls12-381.fr64be/0";
  return policy;
}
void emitStore(MLIRContext &context, unsigned ceiling) {
  evm::NativeLayouts layouts(context);
  EvmLimits limits;
  limits.publicElements = ceiling;
  evm::WireGenerator wire(layouts, limits);
  OpBuilder builder(&context);
  Block body;
  auto loc = builder.getUnknownLoc();
  auto count = body.addArgument(builder.getI64Type(), loc);
  auto index = body.addArgument(builder.getI64Type(), loc);
  auto value = body.addArgument(builder.getI64Type(), loc);
  builder.setInsertionPointToEnd(&body);
  auto attribute = builder.getNamedAttr(
      "value_type", TypeAttr::get(fixture(context, "sequence:index")));
  auto allocation =
      evm::CheckedOp::create(builder, loc, {builder.getI64Type()},
                             "sequence.alloc", {count}, {attribute});
  auto store = evm::CheckedOp::create(
      builder, loc, {}, "sequence.set",
      {allocation.getResult(0), count, index, value}, {attribute});
  auto get = evm::CheckedOp::create(
      builder, loc, {builder.getI64Type()}, "sequence.get",
      {allocation.getResult(0), count, index}, {attribute});
  require(succeeded(allocation.verify()) && succeeded(store.verify()) &&
              succeeded(get.verify()),
          "invalid exact fresh-buffer store fixture");
  auto allocate = take(wire.operation(allocation));
  auto set = take(wire.operation(store));
  auto read = take(wire.operation(get));
  outs() << "object \"Store\" { code { datacopy(0, dataoffset(\"Runtime\"), "
            "datasize(\"Runtime\")) return(0, datasize(\"Runtime\")) }\n"
         << "object \"Runtime\" { code { {\n"
         << "let base := memoryguard(0x400) mstore(0x40, base) "
            "mstore(0x200, base)\n"
         << "let n := calldataload(0) let i := calldataload(32)\n"
         << "let p := " << allocate << "(n)\n"
         << "if calldataload(64) { evm_source(77) }\n"
         << "if iszero(calldataload(96)) { " << set << "(p, n, i, 123) }\n"
         << "let value := " << read << "(p, n, i)\n"
         << "mstore(0, value) return(0, 32)\n}\n"
         << evm::detail::runtimeHelpers(limits) << wire.definitions()
         << "} } }\n";
}
void emit(MLIRContext &context, StringRef kind, StringRef mode,
          uint64_t memory) {
  evm::NativeLayouts layouts(context);
  EvmLimits limits;
  limits.memoryBytes = memory;
  evm::WireGenerator wire(layouts, limits);
  Type type = fixture(context, kind);
  require(bool(type), "unknown test fixture");
  auto layout = take(layouts.get(type));
  auto decoder = take(wire.decoder(type));
  auto encoder = take(wire.encoder(type));
  std::string names = valueNames(layout->lanes.size());
  outs() << "object \"Wire\" { code { datacopy(0, dataoffset(\"Runtime\"), "
            "datasize(\"Runtime\")) return(0, datasize(\"Runtime\")) }\n"
         << "object \"Runtime\" { code { {\n"
         << "let base := memoryguard(0x400) mstore(0x40, base) mstore(0x200, "
            "base)\n"
         << "let n := calldatasize() let p := evm_alloc(n) calldatacopy(p, 0, "
            "n)\n";
  if (mode == "reserved")
    outs() << "pop(evm_alloc(sub(sub(" << memory << ", mload(0x40)), 512)))\n";
  outs() << "let " << names << " := " << decoder << "(p, n)\n";
  if (mode == "values") {
    if (kind == "nested") {
      // Inspect the immutable decoded graph independently of frame encoding.
      outs() << R"YUL(
let result := evm_alloc(65536) let cursor := result
mstore(cursor, mload(v0)) cursor := add(cursor, 32)
if eq(mload(v0), 1) {
  let items := mload(add(v0, 32)) let count := mload(add(v0, 64))
  mstore(cursor, count) cursor := add(cursor, 32)
  for { let i := 0 } lt(i, count) { i := add(i, 1) } {
    let item := mload(add(items, mul(i, 32)))
    let tag := mload(item) mstore(cursor, tag) cursor := add(cursor, 32)
    if eq(tag, 1) {
      let bytes := mload(add(item, 32)) let size := mload(add(item, 64))
      mstore(cursor, size) cursor := add(cursor, 32)
      mcopy(cursor, bytes, size) cursor := add(cursor, size)
      mstore(cursor, mload(add(item, 96))) cursor := add(cursor, 32)
      let values := mload(add(item, 128)) let length := mload(add(item, 160))
      mstore(cursor, length) cursor := add(cursor, 32)
      mcopy(cursor, values, mul(length, 128)) cursor := add(cursor, mul(length, 128))
    }
  }
  let indexData := mload(add(v0, 96)) let indexCount := mload(add(v0, 128))
  mstore(cursor, indexCount) cursor := add(cursor, 32)
  mcopy(cursor, indexData, mul(indexCount, 32)) cursor := add(cursor, mul(indexCount, 32))
  mstore(cursor, mload(add(v0, 160))) cursor := add(cursor, 32)
}
return(result, sub(cursor, result))
)YUL";
    } else if (layout->kind == evm::ValueLayout::Kind::Field &&
               take(layouts.field(cast<algebra::FieldType>(type)))->degree > 1)
      outs() << "return(v0, "
             << take(layouts.field(cast<algebra::FieldType>(type)))
                    ->coefficientBytes()
             << ")\n";
    else if (layout->kind == evm::ValueLayout::Kind::FieldVector ||
             layout->kind == evm::ValueLayout::Kind::FieldArray ||
             layout->kind == evm::ValueLayout::Kind::Indices)
      outs() << "return(v0, mul(v1, " << layout->collection->strideBytes
             << "))\n";
    else if (layout->kind == evm::ValueLayout::Kind::Bytes ||
             layout->kind == evm::ValueLayout::Kind::Root ||
             layout->kind == evm::ValueLayout::Kind::Path)
      outs() << "return(v0, v1)\n";
    else if (layout->kind == evm::ValueLayout::Kind::Index ||
             layout->kind == evm::ValueLayout::Kind::Boolean ||
             layout->kind == evm::ValueLayout::Kind::Field)
      outs() << "mstore(0, v0) return(0, 32)\n";
    else
      require(false, "no raw decoded-value view for fixture");
  } else {
    outs() << "let encoded, length := " << encoder << "(" << names << ")\n"
           << "return(encoded, length)\n";
  }
  outs() << "}\n"
         << evm::detail::runtimeHelpers(limits) << wire.definitions()
         << "} } }\n";
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<evm::EvmDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  if (argc == 3 && StringRef(argv[1]) == "--emit-store") {
    unsigned ceiling = 0;
    if (StringRef(argv[2]).getAsInteger(10, ceiling) || !ceiling ||
        ceiling > EvmLimits().publicElements)
      return 2;
    try {
      emitStore(context, ceiling);
    } catch (const std::exception &failure) {
      errs() << failure.what() << '\n';
      return 1;
    }
    return 0;
  }
  if (argc >= 3 && StringRef(argv[1]) == "--emit") {
    uint64_t memory = EvmLimits().memoryBytes;
    if (argc >= 5 && StringRef(argv[4]).getAsInteger(10, memory))
      return 2;
    try {
      emit(context, argv[2], argc >= 4 ? argv[3] : "roundtrip", memory);
    } catch (const std::exception &failure) {
      errs() << failure.what() << '\n';
      return 1;
    }
    return 0;
  }
  Cases cases;
  evm::NativeLayouts layouts(context);
  for (StringRef domain :
       {"bls12-381.fr", "bn254.fr", "ristretto255.scalar", "koala-bear",
        "koala-bear.ext4-binomial3", "koala-bear.ext8-binomial3", "baby-bear",
        "baby-bear.ext4-binomial11", "goldilocks",
        "goldilocks.ext2-binomial7"}) {
    cases.run("admit exact field/vector codec " + domain, [&] {
      EvmLimits limits;
      evm::WireGenerator wire(layouts, limits);
      for (StringRef constructor : {"field:", "vector:"}) {
        auto type = fixture(context, (constructor + domain).str());
        auto error = evm::verifyWireType(layouts, type);
        if (error)
          throw std::runtime_error(toString(std::move(error)));
        take(wire.decoder(type));
        take(wire.encoder(type));
      }
    });
  }
  cases.run("nested and empty native containers", [&] {
    for (StringRef name :
         {"nested", "empty", "sequence:empty", "sequence:bytes", "indices",
          "array:0", "array:4", "root:rows.merkle-keccak256.koala-bear/0",
          "path:rows.merkle-poseidon2-8.goldilocks/0"}) {
      auto failure = evm::verifyWireType(layouts, fixture(context, name));
      if (failure)
        throw std::runtime_error(toString(std::move(failure)));
    }
  });
  cases.run("inactive unsupported local payload refuses wire", [&] {
    auto local =
        algebra::FixedVectorType::get(&context, fixture(context, "index"), 0);
    take(layouts.get(local));
    auto type = variant(context, "InactiveLocal", {{}, {local}});
    auto error = evm::verifyWireType(layouts, type);
    require(bool(error), "inactive payload acquired wire permission");
    consumeError(std::move(error));
  });
  cases.run("empty sequence cannot hide unsupported element", [&] {
    auto element =
        algebra::FixedVectorType::get(&context, fixture(context, "index"), 0);
    auto type = data::SequenceType::get(&context, element);
    take(layouts.get(type));
    auto error = evm::verifyWireType(layouts, type);
    require(bool(error), "empty element acquired wire permission");
    consumeError(std::move(error));
  });
  cases.run("local binary fields do not acquire prime codec realization", [&] {
    auto failure = evm::verifyWireType(
        layouts, fixture(context, "field:gf2-64.pentanomial-4-3-1"));
    require(bool(failure), "binary field entered prime coefficient codec");
    consumeError(std::move(failure));
  });
  cases.run(
      "uninstalled extension basis refuses complete codec admission", [&] {
        auto failure = evm::verifyWireType(
            layouts, fixture(context, "field:koala-bear.ext4-binomial11"));
        require(bool(failure), "uninstalled basis acquired native codec");
        consumeError(std::move(failure));
      });
  cases.run("affine and represented CPU values refuse", [&] {
    auto type = runtime::CapabilityType::get(
        &context, runtime::CapabilityKind::Transcript,
        "hash-chain.keccak256.bls12-381.fr64be/0");
    auto failure = evm::verifyWireType(layouts, type);
    require(bool(failure), "affine capability acquired wire layout");
    consumeError(std::move(failure));
  });
  for (StringRef fixtureName :
       {"field:koala-bear.ext4-binomial3", "vector:koala-bear.ext8-binomial3",
        "nested", "bytes", "index"}) {
    cases.run("receive requires exact expected-type lanes " + fixtureName, [&] {
      Type type = fixture(context, fixtureName);
      auto layout = take(layouts.get(type));
      OpBuilder builder(&context);
      Block body;
      builder.setInsertionPointToEnd(&body);
      auto attribute = builder.getNamedAttr("value_type", TypeAttr::get(type));
      auto correct = evm::CheckedOp::create(builder, builder.getUnknownLoc(),
                                            layout->lanes, "proof.receive", {},
                                            {attribute});
      require(succeeded(correct.verify()), "exact receive signature refused");
      ScopedDiagnosticHandler handler(&context,
                                      [](Diagnostic &) { return success(); });
      auto wrong = evm::CheckedOp::create(builder, builder.getUnknownLoc(),
                                          {builder.getIntegerType(256),
                                           builder.getIntegerType(256),
                                           builder.getIntegerType(256)},
                                          "proof.receive", {}, {attribute});
      require(failed(wrong.verify()), "wrong receive lanes admitted");
      correct->removeAttr("value_type");
      require(failed(correct.verify()), "untyped receive admitted");
    });
  }
  cases.run(
      "structural helpers distinguish exact types and static selectors", [&] {
        evm::WireGenerator wire(layouts, {});
        OpBuilder builder(&context);
        Block body;
        auto loc = builder.getUnknownLoc();
        auto pointer = body.addArgument(builder.getI64Type(), loc);
        auto flag = body.addArgument(builder.getI1Type(), loc);
        builder.setInsertionPointToEnd(&body);
        auto first = variant(context, "First",
                             {{flag.getType(), flag.getType()},
                              {flag.getType(), flag.getType()}});
        auto second = variant(context, "Second",
                              {{flag.getType(), flag.getType()},
                               {flag.getType(), flag.getType()}});
        auto helper = [&](StringRef code, Type type, unsigned arm = 0,
                          unsigned payload = 0) {
          SmallVector<NamedAttribute> attributes{
              builder.getNamedAttr("value_type", TypeAttr::get(type))};
          if (code != "variant.tag")
            attributes.push_back(builder.getNamedAttr(
                "alternative", builder.getI32IntegerAttr(arm)));
          if (code == "variant.get")
            attributes.push_back(builder.getNamedAttr(
                "payload", builder.getI32IntegerAttr(payload)));
          auto op = evm::CheckedOp::create(
              builder, loc,
              {code == "variant.get" ? builder.getI1Type()
                                     : builder.getI64Type()},
              code,
              code == "variant.make" ? ValueRange{flag, flag}
                                     : ValueRange{pointer},
              attributes);
          require(succeeded(op.verify()), "invalid structural helper fixture");
          return take(wire.operation(op));
        };
        auto get = helper("variant.get", first);
        require(get == helper("variant.get", first),
                "identical operation generated another definition");
        require(get != helper("variant.get", second),
                "nominally distinct types shared a helper");
        require(get != helper("variant.get", first, 1),
                "distinct alternatives shared a helper");
        require(get != helper("variant.get", first, 0, 1),
                "distinct payload selectors shared a helper");
        auto make = helper("variant.make", first);
        auto tag = helper("variant.tag", first);
        require(get != make && get != tag && make != tag,
                "distinct opcodes shared a helper");
        require(make == helper("variant.make", first) &&
                    tag == helper("variant.tag", first),
                "constructor or tag helpers were not reused");
        require(
            StringRef(wire.definitions()).count("function evm_structure_") == 6,
            "helper definitions differ from exact distinct operations");
      });
  EvmOptions boundaryOptions;
  boundaryOptions.policy = boundaryPolicy(false);
  auto compiledBoundary = take(compileEvmProof(boundarySource, "boundary.mlir",
                                               boundaryOptions, registry));
  auto boundary = [&](ModuleOp target, const NativeProofPolicy &policy,
                      json::Value descriptor) {
    return evm::exportYul(target, boundarySource, descriptor, policy, {});
  };
  auto canonicalDescriptor = [&](const NativeProofPolicy &policy) {
    auto descriptor = compiledBoundary.descriptor();
    (*descriptor.getAsArray())[1] = encodeNativeProofPolicy(policy);
    return descriptor;
  };
  auto exportBoundary = [&](ModuleOp target, const NativeProofPolicy &policy) {
    return boundary(target, policy, canonicalDescriptor(policy));
  };
  cases.run("authored policy exports exactly zero transcript lanes", [&] {
    auto target = parseSourceString<ModuleOp>(zeroEndpoint, &context);
    auto yul = take(exportBoundary(*target, boundaryPolicy(false)));
    require(!StringRef(yul).contains("let boundState :=") &&
                !StringRef(yul).contains("mstore(0xa0, rootScope)"),
            "authored boundary acquired managed transcript initialization");
  });
  cases.run(
      "managed policy exports matching input and output capabilities", [&] {
        auto target = parseSourceString<ModuleOp>(managedEndpoint, &context);
        auto yul = take(exportBoundary(*target, boundaryPolicy(true)));
        require(
            StringRef(yul).contains("let boundState :=") &&
                StringRef(yul).contains("mstore(0xa0, rootScope)") &&
                StringRef(yul).contains(
                    "if iszero(eq(mload(0xa0), rootScope)) { evm_fault(5) }"),
            "managed boundary lost binding or final owner validation");
      });
  cases.run("managed policy refuses endpoint without capability ports", [&] {
    auto target = parseSourceString<ModuleOp>(zeroEndpoint, &context);
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    refuses(exportBoundary(*target, boundaryPolicy(true)), "evm.yul");
  });
  cases.run("empty policy refuses endpoint with capability ports", [&] {
    auto target = parseSourceString<ModuleOp>(managedEndpoint, &context);
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    refuses(exportBoundary(*target, boundaryPolicy(false)), "evm.yul");
  });
  for (bool input : {true, false}) {
    for (StringRef mismatch : {"missing", "scope", "wrong-suite", "extra"}) {
      cases.run(
          Twine("managed ") + (input ? "input " : "output ") + mismatch, [&] {
            auto target =
                parseSourceString<ModuleOp>(managedEndpoint, &context);
            auto endpoint = *target->getOps<func::FuncOp>().begin();
            auto logical = cast<FunctionType>(
                endpoint->getAttrOfType<TypeAttr>("evm.logical_type")
                    .getValue());
            SmallVector<Type> inputs(logical.getInputs());
            SmallVector<Type> outputs(logical.getResults());
            auto &changed = input ? inputs : outputs;
            if (mismatch == "missing")
              changed.pop_back();
            else if (mismatch == "extra")
              changed.push_back(changed.back());
            else if (mismatch == "scope")
              changed.back() = parseType("!runtime.scope", &context);
            else
              changed.back() = runtime::CapabilityType::get(
                  &context, runtime::CapabilityKind::Transcript,
                  "hash-chain.keccak256.koala-bear.ext4-binomial3."
                  "rejection31le/0");
            endpoint->setAttr(
                "evm.logical_type",
                TypeAttr::get(FunctionType::get(&context, inputs, outputs)));
            ScopedDiagnosticHandler handler(
                &context, [](Diagnostic &) { return success(); });
            refuses(exportBoundary(*target, boundaryPolicy(true)), "evm.yul");
          });
    }
  }
  cases.run(
      "descriptor must publish the exact selected construction policy", [&] {
        auto target = parseSourceString<ModuleOp>(managedEndpoint, &context);
        ScopedDiagnosticHandler handler(&context,
                                        [](Diagnostic &) { return success(); });
        refuses(boundary(*target, boundaryPolicy(true),
                         canonicalDescriptor(boundaryPolicy(false))),
                "evm.yul");
        auto descriptor = canonicalDescriptor(boundaryPolicy(true));
        (*descriptor.getAsArray())[0] = "zkc.native-proof/0";
        refuses(boundary(*target, boundaryPolicy(true), std::move(descriptor)),
                "evm.yul");
      });
  for (StringRef invalid :
       {"suite", "construction", "format", "services", "draws", "gates"}) {
    cases.run("export refuses unsupported construction policy " + invalid, [&] {
      auto target = parseSourceString<ModuleOp>(zeroEndpoint, &context);
      auto policy = boundaryPolicy(false);
      if (invalid == "suite")
        policy.suite =
            "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0";
      else if (invalid == "construction")
        policy.construction = "handler";
      else if (invalid == "format")
        policy.format = protocol::ProofFormat::RawBytes;
      else if (invalid == "services")
        policy.services = {0};
      else if (invalid == "draws")
        policy.draws = {{"draw", "V"}};
      else
        policy.gates = {{"block", 0}};
      ScopedDiagnosticHandler handler(&context,
                                      [](Diagnostic &) { return success(); });
      refuses(exportBoundary(*target, policy), "evm.yul");
    });
  }
  cases.run("reused structural definitions retain all ordered calls", [&] {
    auto target = parseSourceString<ModuleOp>(zeroEndpoint, &context);
    auto endpoint = *target->getOps<func::FuncOp>().begin();
    OpBuilder builder(&context);
    builder.setInsertionPointToStart(&endpoint.getBody().front());
    auto loc = builder.getUnknownLoc();
    auto type = fixture(context, "sequence:bool");
    auto attribute = builder.getNamedAttr("value_type", TypeAttr::get(type));
    auto empty = evm::CheckedOp::create(
        builder, loc, {builder.getI64Type(), builder.getI64Type()},
        "sequence.empty", {}, {attribute});
    auto flag = arith::ConstantIntOp::create(builder, loc, 1, 1);
    SmallVector<Value> arguments(empty.getResults());
    arguments.push_back(flag);
    evm::CheckedOp::create(builder, loc, empty.getResultTypes(),
                           "sequence.append", arguments, {attribute});
    evm::CheckedOp::create(builder, loc, {builder.getI64Type()},
                           "sequence.length", empty.getResults(), {attribute});
    evm::CheckedOp::create(builder, loc, empty.getResultTypes(),
                           "sequence.append", arguments, {attribute});
    auto yul = take(exportBoundary(*target, boundaryPolicy(false)));
    StringRef text(yul);
    require(text.count("function evm_structure_") == 3 &&
                text.count(" := evm_structure_1(") == 2,
            "ordered calls were removed or helper definitions duplicated");
    auto first = text.find(" := evm_structure_1(");
    auto between = text.find(" := evm_structure_2(", first);
    auto last = text.find(" := evm_structure_1(", first + 1);
    require(first < between && between < last,
            "structural helper reuse reordered calls");
  });
  for (bool managed : {false, true}) {
    cases.run(
        managed ? "full source managed proof retains capability pair"
                : "full source authored proof retains empty suite",
        [&] {
          std::string source = managed ? R"zkc(
module wire;
domain Fr=field("bls12-381.fr");
protocol Work roles(P,V)(challenges:Random<Fr>@V)->(accepted:bool@V) {
  let challenge=challenges.draw();
  let delivered=send V->P(challenge);
  return(accepted=true);
}
proof Proof=Work { prover P; verifier V; public{}; accept accepted;
  construction fiat_shamir("hash-chain.keccak256.bls12-381.fr64be/0",challenges); }
)zkc"
                                       : R"zkc(
module wire;
protocol Work roles(P,V)()->(accepted:bool@V) { return(accepted=true); }
proof Proof=Work { prover P; verifier V; public{}; accept accepted;
  construction authored; }
)zkc";
          auto project =
              take(language::analyze(
                       take(language::capture({{"wire", source, "wire.zkc"}})))
                       .checkedProject());
          auto original = take(language::prepareOriginal(
              take(language::closeEntry(project, "wire::Proof"))));
          auto compiled = take(compileEvmEntry(original));
          require(compiled.policy().suite.empty() != managed,
                  "source construction selected the wrong transcript mode");
          require(
              StringRef(compiled.yul()).contains("let boundState :=") ==
                  managed,
              "source construction lost the policy-selected binding behavior");
        });
  }
  cases.run("descriptor rows retain complete source identity", [&] {
    constexpr StringLiteral source = R"mlir(
module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a: !algebra.field<"bls12-381.fr">):
    %ok = algebra.field_equal %a, %a : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
    "protocol.return"(%ok) : (i1) -> ()
  }) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">)->i1,
      roles=["P","V"], input_roles=[["V"]], output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
    EvmOptions options;
    options.policy.entry = "main";
    options.policy.producer = "P";
    options.policy.validator = "V";
    options.policy.acceptance = 0;
    options.policy.publicInputs = {0};
    auto compiled =
        take(compileEvmProof(source, "wire-test.mlir", options, registry));
    auto target = compiled.targetSnapshot();
    take(evm::exportYul(*target, source, compiled.descriptor(),
                        compiled.policy(), compiled.limits()));
    ScopedDiagnosticHandler handler(target->getContext(),
                                    [](Diagnostic &) { return success(); });
    for (unsigned slot = 0; slot < 4; ++slot) {
      auto changed = compiled.descriptor();
      auto &row = *(*(*changed.getAsArray())[4].getAsArray())[0].getAsArray();
      row[slot] = slot == 0   ? "P"
                  : slot == 1 ? "1"
                  : slot == 2 ? "index"
                              : "zkcv.index/0";
      refuses(evm::exportYul(*target, source, changed, compiled.policy(),
                             compiled.limits()),
              "evm.yul");
    }
  });
  return cases.result();
}
