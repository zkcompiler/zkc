#include "zkc/Compiler/SourceLocations.h"
#include "mlir/IR/BuiltinAttributes.h"

using namespace mlir;
namespace zkc {
SourceLocations::SourceLocations(const source::Document &document,
                                 MLIRContext &context)
    : document(document), context(&context),
      fallback(document.text().empty()
                   ? Location(UnknownLoc::get(&context))
                   : Location(FileLineColLoc::get(&context, document.filename(),
                                                  1, 1))) {}

Location SourceLocations::operator()(const source::Node &node) const {
  auto span = node.location;
  if (!span || span->offset > document.text(span->file).size() ||
      span->length > document.text(span->file).size() - span->offset)
    return fallback;
  auto [line, column] = document.lineColumn(span->offset, span->file);
  return FileLineColLoc::get(context, document.filename(span->file), line,
                             column);
}
} // namespace zkc
