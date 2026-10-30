#include "LayoutReader.h"
using namespace llvm;
namespace zkc::language::detail {
Error LayoutReader::oracleShapes(SyntaxDeclaration &decl) {
  for (auto attribute : attributes) {
    if (auto error = work.charge(decl.inputs.size() + decl.outputs.size() +
                                     decl.oracleShapes.size() + 1,
                                 span(attribute)))
      return error;
    auto nodes = parts(attribute, 2, 2);
    if (!nodes)
      return nodes.takeError();
    auto attributeName = name((*nodes)[0]);
    if (!attributeName)
      return attributeName.takeError();
    if (*attributeName != "shape")
      return fail(attribute, "protocol attributes must name an oracle shape",
                  "source.oracle-shape");
    auto args = parts((*nodes)[1], 2, 2);
    if (!args)
      return args.takeError();
    auto target = argument((*args)[0]);
    if (!target)
      return target.takeError();
    if (kind(*target) != K::Projection)
      return fail(*target, "shape must select port.dimension",
                  "source.oracle-shape");
    auto selected = parts(*target, 2, 2);
    if (!selected)
      return selected.takeError();
    auto port = name((*selected)[0]);
    if (!port)
      return port.takeError();
    auto dimension = name((*selected)[1]);
    if (!dimension)
      return dimension.takeError();
    if (between((*selected)[0], (*selected)[1]) != "." || *dimension != "rows")
      return fail(*target, "the installed table dimension is rows",
                  "source.oracle-shape");
    auto bound = parts((*args)[1], 2, 2);
    if (!bound)
      return bound.takeError();
    auto label = name((*bound)[0]);
    if (!label)
      return label.takeError();
    if (*label != "bound" || between((*bound)[0], (*bound)[1]) != "=")
      return fail((*args)[1], "shape requires bound = static natural",
                  "source.oracle-shape");
    auto maximum = type((*bound)[1]);
    if (!maximum)
      return maximum.takeError();
    unsigned matches = 0;
    for (const auto *ports : {&decl.inputs, &decl.outputs})
      for (const auto &candidate : *ports)
        if (candidate.name == *port && candidate.oracleHolder)
          ++matches;
    if (matches != 1)
      return fail(*target, "shape must select one custody port",
                  "source.oracle-shape");
    for (const auto &shape : decl.oracleShapes)
      if (shape.port == *port && shape.dimension == *dimension)
        return fail(attribute, "oracle shape bound was already specified",
                    "source.oracle-shape");
    decl.oracleShapes.push_back({std::move(*port), std::move(*dimension),
                                 std::move(*maximum), span(attribute)});
  }
  return Error::success();
}
Expected<Expression> LayoutReader::oracleSend(Id id, SyntaxDeclaration &decl) {
  auto nodes = parts(id, 2, 4);
  if (!nodes)
    return nodes.takeError();
  if (nodes->size() != 2 && nodes->size() != 4)
    return fail(id, "dynamic oracle delivery requires both rows and maximum",
                "source.oracle-shape");
  if (kind((*nodes)[0]) != K::Send)
    return fail(id, "oracle delivery requires a send", "source.oracle-action");
  auto delivery = parts((*nodes)[0], 2, SIZE_MAX);
  if (!delivery)
    return delivery.takeError();
  if (delivery->size() < 3 || between((*delivery)[0], (*delivery)[1]) != "from")
    return fail(id, "oracle delivery requires an explicit holder after from",
                "source.oracle-role");
  Expression result;
  result.kind = Expression::Kind::OracleSend;
  result.span = span(id);
  result.scope = scope;
  result.roles.emplace();
  for (auto role : delivery->drop_front()) {
    auto value = name(role);
    if (!value)
      return value.takeError();
    result.roles->push_back(std::move(*value));
  }
  auto data = expression((*delivery)[0], decl);
  if (!data)
    return data.takeError();
  result.children.push_back(*data);
  auto oracleKind = type((*nodes)[1]);
  if (!oracleKind)
    return oracleKind.takeError();
  result.arguments.push_back(std::move(*oracleKind));
  if (nodes->size() == 4) {
    auto rows = expression((*nodes)[2], decl);
    if (!rows)
      return rows.takeError();
    result.children.push_back(*rows);
    auto maximum = type((*nodes)[3]);
    if (!maximum)
      return maximum.takeError();
    result.arguments.push_back(std::move(*maximum));
  }
  return result;
}
} // namespace zkc::language::detail
