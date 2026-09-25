#include "zkc/Compiler/Source.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Source/Codec.h"
#include "zkc/Transforms/Algorithms.h"
namespace zkc {
llvm::Expected<source::Document>
lowerSource(const frontend::Analysis &analysis) {
  auto content = analysis.lower();
  if (!content)
    return content.takeError();
  if (auto e = source::checkStructure(*content))
    return std::move(e);
  std::vector<source::File> files;
  if (const auto *project = analysis.project())
    for (const auto &library : project->libraries())
      for (const auto &file : library.sources)
        files.push_back({file.input.text().str(), file.input.filename().str()});
  if (files.empty())
    files.push_back({analysis.sourceText().str(), analysis.filename().str()});
  return source::Document(std::move(*content), std::move(files));
}
llvm::Expected<source::Content> prepareSource(const source::Document &document,
                                              mlir::MLIRContext &context) {
  if (!document.module()) {
    if (auto e = frontend::checkProtocolDocument(document))
      return std::move(e);
    return document.root();
  }
  const source::Node *failure = nullptr;
  auto prepared = document.module()->isLibrary()
                      ? generic::prepareLibrary(*document.module(), &failure)
                      : llvm::Expected<source::Module>(*document.module());
  if (!prepared)
    return sourceDiagnostic(document, prepared.takeError(), failure);
  bool calls = false;
  for (const auto &fn : prepared->functions)
    if (fn.body)
      source::walk(*fn.body, [&](const source::Instruction &ins) {
        calls |= ins.get<source::AlgorithmCall>() != nullptr;
      });
  if (calls) {
    auto expanded = protocol::expandAlgorithms(*prepared, context);
    if (!expanded)
      return expanded.takeError();
    return source::Content(std::move(expanded->source));
  }
  if (auto e = protocol::admit(*prepared, false))
    return std::move(e);
  return source::Content(std::move(*prepared));
}
} // namespace zkc
