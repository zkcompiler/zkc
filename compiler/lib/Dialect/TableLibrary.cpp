#include "zkc/Dialect/TableLibrary.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Interfaces/SourceLibrary.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace llvm;
using namespace mlir;
namespace zkc {
namespace {
class TableLibrary final : public SourceLibraryInterface {
public:
  using SourceLibraryInterface::SourceLibraryInterface;
  json::Value dependencies() const final {
    return json::Array{json::Array{"table-protocol", "1"}};
  }
  Type conditionType(Builder &b) const final { return b.getI1Type(); }
  Expected<Type> decodeType(const json::Value &, Builder &) const final;
  Expected<json::Value> encodeType(Type) const final;
  Expected<ResolvedOperation> resolveOperation(const json::Value &,
                                               Builder &) const final;
};

static Expected<StringRef> domain(const json::Value &json) {
  auto name = json.getAsString();
  if (!name || (*name != "f2" && *name != "f7"))
    return error("unknown-domain");
  return *name;
}
Expected<Type> TableLibrary::decodeType(const json::Value &json,
                                        Builder &b) const {
  b.getContext()->getOrLoadDialect<PIRDialect>();
  b.getContext()->getOrLoadDialect<AlgebraDialect>();
  b.getContext()->getOrLoadDialect<PolynomialDialect>();
  auto *a = json.getAsArray();
  if (!a || a->empty() || !(*a)[0].getAsString())
    return error("unknown-type");
  auto tag = *(*a)[0].getAsString();
  if (a->size() == 1) {
    if (tag == "bool")
      return Type(b.getI1Type());
    if (tag == "digest")
      return Type(DigestType::get(b.getContext()));
    if (tag == "summary")
      return Type(SummaryType::get(b.getContext()));
  }
  if ((tag == "scalar" || tag == "point") && a->size() == 2) {
    auto d = domain((*a)[1]);
    if (!d)
      return d.takeError();
    if (tag == "scalar")
      return Type(FieldType::get(b.getContext(), *d));
    return Type(PointType::get(b.getContext(), *d));
  }
  if ((tag == "table" || tag == "residual") && a->size() == 3) {
    auto d = domain((*a)[1]);
    if (!d)
      return d.takeError();
    auto n = natural((*a)[2]);
    if (!n)
      return n.takeError();
    if (tag == "table")
      return Type(TableType::get(b.getContext(), *d, *n));
    return Type(ResidualType::get(b.getContext(), *d, *n));
  }
  return error("unknown-type");
}
Expected<json::Value> TableLibrary::encodeType(Type type) const {
  auto selectedDomain =
      llvm::TypeSwitch<Type, StringRef>(type)
          .Case<FieldType, PointType, TableType, ResidualType>(
              [](auto t) { return t.getDomain(); })
          .Default(StringRef());
  if (!selectedDomain.empty() && selectedDomain != "f2" &&
      selectedDomain != "f7")
    return error("unknown-domain");
  if (type.isSignlessInteger(1))
    return json::Value(json::Array{"bool"});
  if (isa<DigestType>(type))
    return json::Value(json::Array{"digest"});
  if (isa<SummaryType>(type))
    return json::Value(json::Array{"summary"});
  if (auto t = dyn_cast<FieldType>(type))
    return json::Value(json::Array{"scalar", t.getDomain()});
  if (auto t = dyn_cast<PointType>(type))
    return json::Value(json::Array{"point", t.getDomain()});
  if (auto t = dyn_cast<TableType>(type))
    return json::Value(
        json::Array{"table", t.getDomain(), naturalValue(t.getRank())});
  if (auto t = dyn_cast<ResidualType>(type))
    return json::Value(
        json::Array{"residual", t.getDomain(), naturalValue(t.getRank())});
  return error("unknown-type");
}
Expected<ResolvedOperation>
TableLibrary::resolveOperation(const json::Value &json, Builder &b) const {
  b.getContext()->getOrLoadDialect<PIRDialect>();
  b.getContext()->getOrLoadDialect<AlgebraDialect>();
  b.getContext()->getOrLoadDialect<PolynomialDialect>();
  auto *a = json.getAsArray();
  if (!a || a->empty() || !(*a)[0].getAsString())
    return error("unknown-operation");
  StringRef tag = *(*a)[0].getAsString();
  auto *c = b.getContext();
  Type flag = b.getI1Type(), f7 = FieldType::get(c, "f7"),
       digest = DigestType::get(c);
  if ((tag == "view" || tag == "restrict" || tag == "evaluate") &&
      a->size() == 3) {
    auto d = domain((*a)[1]);
    if (!d)
      return d.takeError();
    auto n = natural((*a)[2]);
    if (!n)
      return n.takeError();
    Type t = TableType::get(c, *d, *n), v = ResidualType::get(c, *d, *n);
    if (tag == "view")
      return ResolvedOperation{"poly.view", {t}, v, {}, false};
    if (tag == "restrict")
      return ResolvedOperation{
          "poly.restrict", {v, FieldType::get(c, *d)}, v, {}, true};
    return ResolvedOperation{"poly.evaluate",
                             {v, PointType::get(c, *d)},
                             FieldType::get(c, *d),
                             {},
                             true};
  }
  if ((tag == "add" || tag == "record" || tag == "abort_write") &&
      a->size() == 2) {
    auto d = domain((*a)[1]);
    if (!d)
      return d.takeError();
    Type f = FieldType::get(c, *d);
    if (tag == "add")
      return ResolvedOperation{"algebra.add", {f, f}, f, {}, false};
    return ResolvedOperation{tag == "record" ? "pir.record" : "pir.abort_write",
                             {f},
                             flag,
                             {},
                             true};
  }
  if ((tag == "parent" || tag == "endpoint_point") && a->size() == 2) {
    auto value = (*a)[1].getAsBoolean();
    if (!value)
      return error("invalid-shape");
    if (tag == "parent")
      return ResolvedOperation{"pir.parent",
                               {digest, digest},
                               digest,
                               {b.getNamedAttr("left", b.getBoolAttr(*value))},
                               false};
    return ResolvedOperation{"poly.endpoint_point",
                             {},
                             PointType::get(c, "f7"),
                             {b.getNamedAttr("atOne", b.getBoolAttr(*value))},
                             false};
  }
  if (a->size() != 1)
    return error("unknown-operation");
  if (tag == "ordered_pair")
    return ResolvedOperation{
        "pir.ordered_pair", {digest, digest}, digest, {}, false};
  if (tag == "pack")
    return ResolvedOperation{"pir.pack",
                             {FieldType::get(c, "f2"), f7, digest},
                             SummaryType::get(c),
                             {},
                             false};
  if (tag == "send")
    return ResolvedOperation{"pir.send", {f7, f7}, flag, {}, true};
  if (tag == "draw")
    return ResolvedOperation{"pir.draw", {}, f7, {}, true};
  if (tag == "linear")
    return ResolvedOperation{"poly.linear", {f7, f7, f7}, f7, {}, false};
  if (tag == "point")
    return ResolvedOperation{
        "poly.point", {f7}, PointType::get(c, "f7"), {}, false};
  if (tag == "equal")
    return ResolvedOperation{"algebra.equal", {f7, f7}, flag, {}, false};
  if (tag == "digest_equal")
    return ResolvedOperation{
        "pir.digest_equal", {digest, digest}, flag, {}, false};
  return error("unknown-operation");
}
} // namespace
void registerTableLibrary(DialectRegistry &registry) {
  registry.addExtension(+[](MLIRContext *, PIRDialect *dialect) {
    dialect->addInterfaces<TableLibrary>();
  });
}
} // namespace zkc
