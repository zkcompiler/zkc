#ifndef ZKC_FRONTEND_TOOLING_ACCESS_H
#define ZKC_FRONTEND_TOOLING_ACCESS_H

#include "../Model/Module.h"
#include "zkc/Frontend/Analysis.h"

namespace zkc::frontend::semantics {
struct AnalysisAccess {
  static const model::Module &get(const Analysis &analysis) {
    return *analysis.model;
  }
  static std::shared_ptr<const LibraryReport>
  libraries(const Analysis &analysis) {
    return analysis.model->libraries;
  }
  static Analysis make(std::shared_ptr<const model::Module> model) {
    return Analysis(std::move(model));
  }
};
} // namespace zkc::frontend::semantics
#endif
