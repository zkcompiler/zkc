// Standalone, bounded LLZK relation ingress. LLVM 20 lives in this process
// only.
#include "Adapter.h"
#include "llzk/Dialect/Bool/IR/Ops.h"
#include "llzk/Dialect/Constrain/IR/Ops.h"
#include "llzk/Dialect/Felt/IR/Ops.h"
#include "llzk/Dialect/Function/IR/Ops.h"
#include "llzk/Dialect/InitDialects.h"
#include "llzk/Dialect/LLZK/IR/Attrs.h"
#include "llzk/Dialect/Struct/IR/Ops.h"
#include "llzk/Transforms/LLZKTransformationPassPipelines.h"
#include "llzk/Util/Field.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"
#include "r1cs/DialectRegistration.h"
#include "r1cs/Target/R1CSBinary.h"
#include "r1cs/Transforms/TransformationPasses.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/SHA256.h"
#include <filesystem>
#include <fstream>
#include <stdexcept>
#include <sys/resource.h>
#include <sys/stat.h>

using namespace mlir;
using namespace llvm;
namespace fs = std::filesystem;
namespace zkc::llzk_adapter {
namespace {
constexpr size_t sourceLimit = 2 * 1024 * 1024;
constexpr size_t artifactLimit = 16 * 1024 * 1024;
constexpr size_t operationLimit = 100000;
constexpr StringLiteral bls = "524358751751261904794477405081859658376905525005"
                              "27637822603658699938581184513";
constexpr StringLiteral bn = "2188824287183927522224640574525727508854836440041"
                             "6034343698204186575808495617";
using Func = llzk::function::FuncDefOp;
using Struct = llzk::component::StructDefOp;
[[noreturn]] void refuse(StringRef code, const Twine &detail = "") {
  throw std::runtime_error((code + ": " + detail).str());
}
void require(bool ok, StringRef code, const Twine &detail = "") {
  if (!ok)
    refuse(code, detail);
}
std::string hash(StringRef text) {
  auto bytes = SHA256::hash(arrayRefFromStringRef(text));
  return toHex(bytes, true);
}
std::string print(Operation *op) {
  std::string text;
  raw_string_ostream stream(text);
  op->print(stream);
  return text + "\n";
}
std::vector<std::string> list(StringRef value) {
  std::vector<std::string> result;
  if (value.empty())
    return result;
  SmallVector<StringRef> parts;
  value.split(parts, ',');
  llvm::StringSet<> seen;
  for (auto part : parts) {
    require(!part.empty() && part.size() <= 256 && seen.insert(part).second,
            "llzk-interface", "empty, duplicate or long binding");
    result.push_back(part.str());
  }
  require(result.size() <= 4096, "llzk-interface");
  return result;
}
json::Array strings(const std::vector<std::string> &values) {
  json::Array result;
  for (auto &v : values)
    result.push_back(v);
  return result;
}
std::string qualified(SymbolRefAttr name) {
  std::string out = name.getRootReference().str();
  for (auto part : name.getNestedReferences())
    out += "::" + part.getValue().str();
  return out;
}
std::string readSource(const std::string &filename) {
  struct stat st;
  require(::stat(filename.c_str(), &st) == 0 && S_ISREG(st.st_mode),
          "llzk-input", "regular file required");
  require(st.st_size >= 0 && uint64_t(st.st_size) <= sourceLimit,
          "llzk-source-limit");
  std::ifstream in(filename, std::ios::binary);
  std::string text(sourceLimit + 1, '\0');
  in.read(text.data(), text.size());
  text.resize(in.gcount());
  require(text.size() <= sourceLimit, "llzk-source-limit");
  require(!text.empty() && text.find('\0') == std::string::npos, "llzk-parse",
          "text MLIR required");
  return text;
}
void limits() {
  for (auto [kind, value] : {std::pair{RLIMIT_AS, rlim_t(2ULL << 30)},
                             {RLIMIT_CPU, rlim_t(45)},
                             {RLIMIT_CORE, rlim_t(0)}}) {
    struct rlimit old;
    require(getrlimit(kind, &old) == 0, "llzk-resource-limit");
    struct rlimit bound{std::min(old.rlim_cur, value), old.rlim_max};
    require(setrlimit(kind, &bound) == 0, "llzk-resource-limit");
  }
}
void sizeGuard(ModuleOp module) {
  size_t count = 0;
  module.walk([&](Operation *op) {
    require(++count <= operationLimit, "llzk-operation-limit");
    unsigned depth = 0;
    for (auto parent = op->getParentOp(); parent;
         parent = parent->getParentOp())
      require(++depth <= 64, "llzk-depth-limit");
  });
}

// Deliberately tiny constant proof, evaluated on parsed SSA with no rewriting.
// This suffices for the pinned Circom static gadget assertion (1 != 0).
std::optional<DynamicAPInt> constant(Value v) {
  if (auto op = v.getDefiningOp<llzk::felt::FeltConstantOp>()) {
    auto ty = dyn_cast<llzk::felt::FeltType>(v.getType());
    if (ty && ty.hasField())
      return ty.getField().reduce(op.getValueAPInt());
  }
  return std::nullopt;
}
bool provenTrue(Value v) {
  if (auto op = v.getDefiningOp<arith::ConstantOp>()) {
    auto value = dyn_cast<IntegerAttr>(op.getValue());
    return v.getType().isInteger(1) && value && value.getValue().isOne();
  }
  if (auto op = v.getDefiningOp<llzk::boolean::CmpOp>()) {
    auto a = constant(op.getOperand(0)), b = constant(op.getOperand(1));
    if (!a || !b)
      return false;
    using P = llzk::boolean::FeltCmpPredicate;
    switch (op.getPredicate()) {
    case P::EQ:
      return *a == *b;
    case P::NE:
      return *a != *b;
    case P::LT:
      return *a < *b;
    case P::LE:
      return *a <= *b;
    case P::GT:
      return *a > *b;
    case P::GE:
      return *a >= *b;
    }
  }
  return false;
}

void sourceGuard(ModuleOp module) {
  // Enumerated operation names are read from MLIR OperationName, never source
  // text. Unregistered operations remain disabled in the parser.
  const llvm::StringSet<> structure{"builtin.module", "poly.template",
                                    "struct.def", "struct.member",
                                    "function.def"};
  const llvm::StringSet<> common{
      "felt.const",  "felt.add",     "felt.sub",        "felt.mul",
      "felt.neg",    "struct.readm", "function.return", "function.call",
      "bool.assert", "bool.cmp",     "arith.constant",  "arith.subi",
      "arith.cmpi",  "cast.toindex", "array.new",       "array.read",
      "array.write", "pod.new",      "pod.read",        "pod.write",
      "scf.while",   "scf.for",      "scf.if",          "scf.condition",
      "scf.yield"};
  const llvm::StringSet<> compute{"struct.new", "struct.writem", "llzk.nondet",
                                  "felt.shr", "felt.bit_and"};
  module.walk<WalkOrder::PreOrder>([&](Operation *op) {
    StringRef name = op->getName().getStringRef();
    if (name.starts_with("constrain.") &&
        !isa<llzk::constrain::EmitEqualityOp>(op))
      refuse("llzk-source-constraint", name);
    if (auto func = dyn_cast<Func>(op)) {
      require(!func.isExternal() && func.isInStruct() &&
                  (func.nameIsConstrain() || func.nameIsCompute()),
              "llzk-source-call",
              "only defined struct compute/constrain functions");
    }
    if (structure.contains(name)) {
      require(!op->getParentOfType<Func>(), "llzk-source-operation",
              "nested definition in function");
      return;
    }
    auto func = op->getParentOfType<Func>();
    require(bool(func), "llzk-source-operation", name);
    if (isa<llzk::constrain::EmitEqualityOp>(op)) {
      require(func.nameIsConstrain(), "llzk-compute-constraint");
      return;
    }
    require(common.contains(name) ||
                (func.nameIsCompute() && compute.contains(name)),
            "llzk-source-operation", name);
    if (auto call = dyn_cast<llzk::function::CallOp>(op)) {
      require((func.nameIsCompute() && call.calleeIsStructCompute()) ||
                  (func.nameIsConstrain() && call.calleeIsStructConstrain()),
              "llzk-source-call", name);
    }
    if (auto assertion = dyn_cast<llzk::boolean::AssertOp>(op))
      require(provenTrue(assertion.getCondition()), "llzk-source-assert",
              "requires statically true constant assertion");
  });
}

void fieldGuard(ModuleOp module, StringRef name, StringRef prime) {
  llzk::FieldSet fields;
  require(succeeded(llzk::collectFields(module, fields)) && !fields.empty(),
          "llzk-field");
  auto expected = llzk::Field::tryGetField(name);
  require(succeeded(expected), "llzk-field");
  std::string actual;
  raw_string_ostream(actual) << expected->get().prime();
  require(actual == prime, "llzk-field",
          "source declaration conflicts with selected modulus");
  for (auto field : fields)
    require(field.get() == expected->get(), "llzk-field",
            "mixed or mismatched field");
  // Field declarations are claims too, including claims on otherwise dead ops.
  module.walk([&](Operation *op) {
    for (auto attr : op->getAttrs())
      attr.getValue().walk([&](Attribute a) {
        if (auto spec = dyn_cast<llzk::felt::FieldSpecAttr>(a)) {
          SmallString<100> declared;
          spec.getPrime().toString(declared, 10, false);
          require(spec.getFieldName().getValue() == name && declared == prime,
                  "llzk-field", "conflicting field annotation");
        }
      });
  });
}
Struct mainStruct(ModuleOp module) {
  auto ty = llzk::getTypeFromLlzkMainAttr(module, module->getAttr("llzk.main"));
  require(succeeded(ty), "llzk-entry");
  auto op = SymbolTable::lookupSymbolIn(module, ty->getNameRef());
  auto result = dyn_cast_or_null<Struct>(op);
  require(bool(result), "llzk-entry");
  return result;
}
std::vector<std::string> outputs(Struct main) {
  std::vector<std::string> names;
  for (auto member : main.getMemberDefs())
    if (member->hasAttr("llzk.pub"))
      names.push_back(member.getSymName().str());
  return names;
}
std::vector<std::string> publicInputs(Func func) {
  std::vector<std::string> names;
  require(bool(func) && func.getNumArguments() > 0, "llzk-interface");
  require(!func.getArgAttr(0, "llzk.pub"), "llzk-interface",
          "self must be private");
  for (unsigned i = 1; i < func.getNumArguments(); ++i) {
    require(isa<llzk::felt::FeltType>(func.getArgument(i).getType()),
            "llzk-interface", "scalar arguments required");
    if (func.getArgAttr(i, "llzk.pub")) {
      auto name = func.getArgNameAttr(i);
      names.push_back(name ? name->getValue().str()
                           : "#" + std::to_string(i - 1));
    }
  }
  return names;
}
size_t scalarGuard(ModuleOp module, Struct main) {
  size_t structs = 0, equations = 0;
  module.walk([&](Struct) { ++structs; });
  require(structs == 1, "llzk-scalar-shape");
  for (auto member : main.getMemberDefs())
    require(isa<llzk::felt::FeltType>(member.getType()) && !member.getColumn(),
            "llzk-scalar-member");
  auto func = main.getConstrainFuncOp();
  require(func && func.getBody().hasOneBlock() && func.getNumResults() == 0,
          "llzk-scalar-shape");
  for (Operation &op : func.getBody().front()) {
    require(op.getNumRegions() == 0, "llzk-scalar-operation",
            op.getName().getStringRef());
    if (isa<llzk::felt::FeltConstantOp, llzk::felt::AddFeltOp,
            llzk::felt::SubFeltOp, llzk::felt::MulFeltOp,
            llzk::felt::NegFeltOp>(&op)) {
      for (auto ty : op.getResultTypes())
        require(isa<llzk::felt::FeltType>(ty), "llzk-scalar-type");
    } else if (auto read = dyn_cast<llzk::component::MemberReadOp>(op)) {
      require(read.getComponent() == func.getArgument(0) &&
                  !read.getTableOffset(),
              "llzk-scalar-read");
    } else if (isa<llzk::constrain::EmitEqualityOp>(op)) {
      for (auto ty : op.getOperandTypes())
        require(isa<llzk::felt::FeltType>(ty), "llzk-scalar-type");
      ++equations;
    } else if (auto assertion = dyn_cast<llzk::boolean::AssertOp>(op)) {
      require(provenTrue(assertion.getCondition()), "llzk-scalar-assert");
    } else if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
      require(isa<IntegerAttr>(constant.getValue()), "llzk-scalar-constant");
    } else if (isa<llzk::function::ReturnOp>(op)) {
      require(op.getNumOperands() == 0, "llzk-scalar-return");
    } else
      refuse("llzk-scalar-operation", op.getName().getStringRef());
  }
  return equations;
}
void runPasses(ModuleOp module, PassManager &pm) {
  pm.enableVerifier(true);
  require(succeeded(pm.run(module)), "llzk-normalization");
  sizeGuard(module);
}
void write(const fs::path &file, StringRef data) {
  require(data.size() <= artifactLimit, "llzk-artifact-limit");
  std::ofstream out(file, std::ios::binary);
  out.write(data.data(), data.size());
  out.close();
  require(bool(out), "llzk-output", file.string());
}
} // namespace

size_t validateScalarModule(ModuleOp module) {
  return scalarGuard(module, mainStruct(module));
}

int run(int argc, char **argv) {
  try {
    if (argc == 2 && StringRef(argv[1]) == "--version") {
      outs() << "zkc-llzk/v1 LLVM/20.1.8 LLZK/" ZKC_LLZK_REVISION "\n";
      return 0;
    }
    require(argc == 12, "llzk-cli",
            "SOURCE --field NAME --entry SYMBOL --outputs CSV --public-inputs "
            "CSV --output NEW_DIRECTORY");
    StringMap<std::string> opts;
    for (int i = 2; i < argc; i += 2)
      require(opts.try_emplace(argv[i], argv[i + 1]).second, "llzk-cli");
    for (StringRef key :
         {"--field", "--entry", "--outputs", "--public-inputs", "--output"})
      require(opts.contains(key), "llzk-cli", key);
    StringRef field = opts["--field"];
    require(field == "bls12381" || field == "bn254", "llzk-field",
            "supported names: bls12381, bn254");
    StringRef prime = field == "bls12381" ? bls : bn;
    auto expectedOutputs = list(opts["--outputs"]),
         expectedInputs = list(opts["--public-inputs"]);
    require(!opts["--entry"].empty() && opts["--entry"].size() <= 256,
            "llzk-entry");
    require(!fs::exists(opts["--output"]), "llzk-output-exists");
    limits();
    std::string source = readSource(argv[1]);
    require(zkc::mlirNestingWithinLimit(source), "llzk-depth-limit");
    DialectRegistry registry;
    llzk::registerAllDialects(registry);
    r1cs::registerAllDialects(registry);
    MLIRContext context(registry, MLIRContext::Threading::DISABLED);
    MLIRContext lowerContext(registry, MLIRContext::Threading::DISABLED);
    // LLZK caches field specs globally, and reports even identical
    // redeclarations as errors. Parse a self-declaring source first. Only if
    // parsing fails and BLS is still undefined, register our exact modulus and
    // retry from scratch. No normalization or acceptance occurs during either
    // parsing attempt.
    std::string diagnostics;
    bool parsed = false;
    bool parseError = false;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
      if (!parsed && d.getSeverity() == DiagnosticSeverity::Error)
        parseError = true;
      if (parsed) {
        d.print(errs());
        errs() << "\n";
      }
      if (diagnostics.size() < 8192) {
        raw_string_ostream stream(diagnostics);
        d.print(stream);
        stream << '\n';
      }
      return success();
    });
    auto module =
        parseSourceString<ModuleOp>(source, ParserConfig(&context, false));
    bool registered = false;
    if (!module && field == "bls12381" &&
        failed(llzk::Field::tryGetField(field))) {
      llzk::Field::addField("bls12381", bls, nullptr);
      diagnostics.clear();
      parseError = false;
      registered = true;
      module =
          parseSourceString<ModuleOp>(source, ParserConfig(&context, false));
    }
    require(bool(module) && !parseError, "llzk-parse", diagnostics);
    parsed = true;
    sizeGuard(*module);
    fieldGuard(*module, field, prime);
    // Name-only preflight before verification as well: unsupported includes or
    // external dialect operations must not gain effects through their verifier.
    module->walk([&](Operation *op) {
      auto ns = op->getName().getDialectNamespace();
      require(ns != "include" && ns != "verif" && ns != "global" && ns != "ram",
              "llzk-source-operation", op->getName().getStringRef());
    });
    require(succeeded(verify(*module)), "llzk-verify", diagnostics);
    sourceGuard(*module); // MUST precede every possibly erasing pass.
    auto main = mainStruct(*module);
    require(qualified(main.getFullyQualifiedName()) == opts["--entry"],
            "llzk-entry");
    require(outputs(main) == expectedOutputs, "llzk-public-outputs");
    require(publicInputs(main.getConstrainFuncOp()) == expectedInputs,
            "llzk-public-inputs");
    auto argumentCount = main.getConstrainFuncOp().getNumArguments();
    PassManager inlinePM(&context);
    llzk::buildFullStructInliningPipeline(inlinePM, {});
    runPasses(*module, inlinePM);
    main = mainStruct(*module);
    json::Array demoted;
    for (auto member : main.getMemberDefs()) {
      if (member->hasAttr("llzk.pub") &&
          !is_contained(expectedOutputs, member.getSymName().str())) {
        demoted.push_back(member.getSymName().str());
        member->removeAttr("llzk.pub");
      }
    }
    require(outputs(main) == expectedOutputs, "llzk-public-outputs");
    // Round-trip only our own normalized IR, in a fresh context. The pinned
    // transfer fixture fails scalarization if we reuse the first context.
    // Validated field specs are globally registered; the final snapshot
    // receives a fresh exact BLS declaration, avoiding duplicate-registration
    // errors.
    (*module)->removeAttr("llzk.fields");
    auto inlineText = print(*module);
    require(inlineText.size() <= artifactLimit, "llzk-artifact-limit");
    require(zkc::mlirNestingWithinLimit(inlineText), "llzk-depth-limit");
    module = parseSourceString<ModuleOp>(inlineText, &lowerContext);
    require(bool(module), "llzk-normalized-parse");

    // Finish scalar/degree normalization, before strict body admission.

    PassManager polynomialPM(&lowerContext);
    llzk::FullPolyLoweringConfig config;
    config.polyLowering.maxDegree = 2;
    llzk::buildFullPolyLoweringPipeline(polynomialPM, config);
    runPasses(*module, polynomialPM);
    main = mainStruct(*module);
    fieldGuard(*module, field, prime);
    auto equations = scalarGuard(*module, main);
    require(outputs(main) == expectedOutputs, "llzk-public-outputs");
    require(publicInputs(main.getConstrainFuncOp()) == expectedInputs &&
                main.getConstrainFuncOp().getNumArguments() == argumentCount,
            "llzk-public-inputs");
    json::Array members;
    for (auto member : main.getMemberDefs())
      members.push_back(member.getSymName().str());
    json::Array arguments;
    auto constrain = main.getConstrainFuncOp();
    for (unsigned i = 1; i < constrain.getNumArguments(); ++i) {
      auto name = constrain.getArgNameAttr(i);
      arguments.push_back(json::Object{
          {"index", i - 1},
          {"name", name ? name->getValue().str() : "#" + std::to_string(i - 1)},
          {"public", bool(constrain.getArgAttr(i, "llzk.pub"))}});
    }
    if (field == "bls12381")
      (*module)->setAttr(
          "llzk.fields",
          llzk::felt::FieldSpecAttr::get(&lowerContext, "bls12381", 256, bls));
    auto normalized = print(*module);
    PassManager r1csPM(&lowerContext);
    r1csPM.addPass(r1cs::createR1CSLoweringPass());
    // Preserve even unused public signal definitions: upstream CSE treats
    // r1cs.def as pure and can erase an unconstrained public output.
    runPasses(*module, r1csPM);
    std::string binary;
    raw_string_ostream stream(binary);
    require(succeeded(r1cs::exportR1CSBinary(*module, stream, prime)),
            "llzk-export", diagnostics);
    require(binary.size() <= artifactLimit &&
                normalized.size() <= artifactLimit,
            "llzk-artifact-limit");
    // Field declarations remain in memory and the receipt. Direct binary export
    // avoids llzk-translate's missing felt-dialect registration altogether.
    json::Object receipt{
        {"schema", "zkc-llzk-receipt/v1"},
        {"status", "Exported"},
        {"llzk_revision", ZKC_LLZK_REVISION},
        {"llvm_version", "20.1.8"},
        {"source_sha256", hash(source)},
        {"normalized_sha256", hash(normalized)},
        {"r1cs_sha256", hash(binary)},
        {"field", field},
        {"prime", prime},
        {"source_entry", opts["--entry"]},
        {"public_outputs", strings(expectedOutputs)},
        {"public_inputs", strings(expectedInputs)},
        {"normalized_members", std::move(members)},
        {"normalized_arguments", std::move(arguments)},
        {"demoted_component_outputs", std::move(demoted)},
        {"source_guard_before_lowering", true},
        {"fresh_context_after_inlining", true},
        {"final_cse", false},
        {"normalized_field_declaration", field == "bls12381"},
        {"registered_missing_field", registered},
        {"scalar_equations", equations},
        {"zero_equations", equations == 0},
        {"witness_execution", false},
        {"trust",
         "Pinned frontend, MLIR parser, LLZK normalization and R1CS "
         "lowering/export; no universal preservation or adequacy proof"}};
    auto directory = fs::path(opts["--output"]);
    require(fs::create_directory(directory), "llzk-output-exists");
    write(directory / "normalized.llzk", normalized);
    write(directory / "relation.r1cs", binary);
    write(directory / "receipt.json",
          formatv("{0:2}\n", json::Value(std::move(receipt))).str());
    return 0;
  } catch (const std::exception &e) {
    errs() << "Refused " << e.what() << '\n';
    return 2;
  }
}

} // namespace zkc::llzk_adapter
