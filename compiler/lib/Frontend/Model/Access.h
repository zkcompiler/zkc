#ifndef ZKC_FRONTEND_MODEL_ACCESS_H
#define ZKC_FRONTEND_MODEL_ACCESS_H

#include "Module.h"
#include "zkc/Frontend/Analysis.h"

namespace zkc::frontend::model {
struct AnalysisAccess {
  static const model::Module &get(const Analysis &analysis) {
    return *analysis.model;
  }
  static std::shared_ptr<const model::LibraryReport>
  libraries(const Analysis &analysis) {
    return analysis.model->libraries;
  }
  /// Consume the only mutable owner. Published queries cannot retain a mutable
  /// alias to the model they observe.
  static Analysis freeze(std::unique_ptr<model::Module> model) {
    return Analysis(std::shared_ptr<const model::Module>(std::move(model)));
  }
};
} // namespace zkc::frontend::model
#endif
