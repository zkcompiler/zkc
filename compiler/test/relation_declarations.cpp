#include "mlir/Interfaces/CallInterfaces.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace zkc;

int main() {
  DialectRegistry registry;
  registry.insert<relation::RelationDialect, algebra::AlgebraDialect,
                  local::LocalDialect, data::DataDialect, func::FuncDialect>();
  MLIRContext context(registry), otherContext(registry);
  std::string refusal;
  auto handler = [&](Diagnostic &diagnostic) {
    llvm::raw_string_ostream stream(refusal);
    diagnostic.print(stream);
    return success();
  };
  ScopedDiagnosticHandler first(&context, handler),
      second(&otherContext, handler);
  unsigned failures = 0;
  auto require = [&](bool condition, llvm::StringRef message) {
    if (!condition) {
      llvm::errs() << message << ": " << refusal << '\n';
      ++failures;
    }
  };
  const std::string declaration = R"mlir(
relation.declare @predicate {
  kind = "external", key = "example/echo", revision = "0",
  signature = (!algebra.field<"bls12-381.fr">) -> i1,
  purposes = ["statement"]
}
)mlir";
  auto parse = [&](const std::string &text, MLIRContext &ctx) {
    refusal.clear();
    return parseSourceString<ModuleOp>("module {" + text + "}", &ctx);
  };
  auto a = parse(declaration, context);
  auto b = parse(declaration, otherContext);
  require(bool(a) && bool(b), "valid declaration refused");
  if (!a || !b)
    return 1;
  auto op = *a->getOps<relation::DeclareOp>().begin();
  require(!isa<CallableOpInterface>(op.getOperation()),
          "relation became callable");
  require(!context.getLoadedDialect("protocol"), "relation loaded protocol");
  require(succeeded(relation::verifyDeclarationConsistency(
              {a->getOperation(), b->getOperation()})),
          "equal cross-context schemas refused");

  auto changed = declaration;
  changed.replace(changed.find("statement"), 9, "witness");
  auto c = parse(changed, context);
  require(bool(c), "explicit witness declaration refused");
  require(c &&
              failed(relation::verifyDeclarationConsistency(
                  {a->getOperation(), c->getOperation()})) &&
              refusal.find("relation-declaration-conflict") !=
                  std::string::npos,
          "conflicting purpose accepted");
  changed = declaration;
  const std::string fieldType = "!algebra.field<\"bls12-381.fr\">";
  changed.replace(changed.find(fieldType), fieldType.size(), "i1");
  auto d = parse(changed, context);
  require(bool(d), "Boolean signature fixture refused");
  require(d && failed(relation::verifyDeclarationConsistency(
                   {a->getOperation(), d->getOperation()})),
          "conflicting signature accepted");
  // Kind is an exact part of the external identity, not a case-normalized
  // annotation. Unrelated identity namespaces may have different schemas.
  changed = declaration;
  changed.replace(changed.find("external"), 8, "different-kind");
  changed.replace(changed.find("statement"), 9, "witness");
  auto distinct = parse(changed, context);
  require(distinct && succeeded(relation::verifyDeclarationConsistency(
                          {a->getOperation(), distinct->getOperation()})),
          "distinct identity kinds incorrectly merged");
  changed = declaration;
  changed.replace(changed.find("statement"), 9, "secret");
  require(!parse(changed, context) &&
              refusal.find("relation-declaration-purpose") != std::string::npos,
          "inferred or unknown purpose accepted");
  changed = declaration;
  changed.replace(changed.find("[\"statement\"]"), 13, "[]");
  require(!parse(changed, context) &&
              refusal.find("relation-declaration-signature") !=
                  std::string::npos,
          "missing purpose accepted");
  changed = declaration;
  changed.replace(changed.find("example/echo"), 12, "");
  require(!parse(changed, context) &&
              refusal.find("relation-declaration-identity") !=
                  std::string::npos,
          "empty external identity accepted");

  auto schema = [&](const std::string &type) {
    auto text = declaration;
    text.replace(text.find(fieldType), fieldType.size(), type);
    return text;
  };
  auto variant = [&](llvm::StringRef name,
                     std::vector<protocol::VariantAlternative> arms) {
    auto encoded = protocol::encodeVariant({name.str(), std::move(arms)});
    require(bool(encoded), "variant fixture failed");
    return "!local.variant<\"" + encoded.value_or("") + "\">";
  };
  const std::string record =
      variant("RelationData",
              {{"Record", {"matrix:bls12-381.fr", "vector:bls12-381.fr"}}});
  const std::string optional = variant(
      "Optional", {{"None", {}}, {"Some", {"sequence<vector:bls12-381.fr>"}}});
  for (const auto &type : std::vector<std::string>{
           "ui64", "tensor<0x" + fieldType + ">", "tensor<3x" + fieldType + ">",
           "tensor<?x" + fieldType + ">", "tensor<?x?x" + fieldType + ">",
           "tensor<?xui64>", "tensor<?x!algebra.group<\"bls12-381.g1\">>",
           "!data.sequence<!data.sequence<" + record + ">>", record,
           optional}) {
    auto left = parse(schema(type), context);
    auto right = parse(schema(type), otherContext);
    require(left && right, "structured declaration refused: " + type);
    if (left && right)
      require(succeeded(relation::verifyDeclarationConsistency(
                  {left->getOperation(), right->getOperation()})),
              "equal structured cross-context schemas refused: " + type);
  }
  for (auto [leftType, rightType] :
       std::vector<std::pair<std::string, std::string>>{
           {"tensor<2x" + fieldType + ">", "tensor<3x" + fieldType + ">"},
           {"tensor<2x" + fieldType + ">", "tensor<?x" + fieldType + ">"},
           {"tensor<?x" + fieldType + ">", "tensor<?x?x" + fieldType + ">"},
           {"!data.sequence<" + fieldType + ">", "!data.sequence<i1>"},
           {"tensor<?x" + fieldType + ">",
            "tensor<?x!algebra.field<\"bn254.fr\">>"},
           {record, variant("OtherData", {{"Record",
                                           {"matrix:bls12-381.fr",
                                            "vector:bls12-381.fr"}}})},
           {record, variant("RelationData", {{"Record",
                                              {"vector:bls12-381.fr",
                                               "matrix:bls12-381.fr"}}})},
           {optional,
            variant("Optional",
                    {{"None", {}},
                     {"Some", {"sequence<groups:bls12-381.g1>"}}})}}) {
    auto left = parse(schema(leftType), context);
    auto right = parse(schema(rightType), otherContext);
    require(left && right, "conflict fixture refused");
    require(left && right &&
                failed(relation::verifyDeclarationConsistency(
                    {left->getOperation(), right->getOperation()})) &&
                refusal.find("relation-declaration-conflict") !=
                    std::string::npos,
            "structured identity collision accepted");
  }
  for (const auto &type : std::vector<std::string>{
           "i64", "tensor<2x2x" + fieldType + ">", "memref<2xi1>",
           "!algebra.fixed_vector<" + fieldType + ", 3>",
           "!local.capability<\"rng:bls12-381.fr\">",
           variant("HiddenResource",
                   {{"None", {}}, {"Some", {"rng:bls12-381.fr"}}}),
           variant("HiddenKey",
                   {{"None", {}},
                    {"Some", {"verifier_key:multilinear.kzg.bls12-381/0"}}})})
    require(!parse(schema(type), context) &&
                refusal.find("relation-declaration-signature") !=
                    std::string::npos,
            "unsupported or resource-bearing signature accepted: " + type);
  require(!context.getLoadedDialect("protocol"),
          "structured relation loaded protocol dialect");

  const std::string field = "!algebra.field<\"bls12-381.fr\">";
  auto pureCall = declaration + "func.func @bad(%x: " + field +
                  ") -> i1 { %r = func.call @predicate(%x) : (" + field +
                  ") -> i1 return %r : i1 }";
  require(!parse(pureCall, context) &&
              refusal.find("valid function") != std::string::npos,
          "pure call accepted relation symbol");
  auto localCall = declaration + "local.func @bad(%x: " + field +
                   ") -> i1 { %r = apply @predicate(%x) {site=\"call\"} : (" +
                   field + ") -> i1 return %r : i1 }";
  require(!parse(localCall, context) &&
              refusal.find("interactive-symbol-kind") != std::string::npos,
          "local apply accepted relation symbol");
  return failures != 0;
}
