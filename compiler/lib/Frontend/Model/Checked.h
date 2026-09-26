#ifndef ZKC_FRONTEND_MODEL_CHECKED_H
#define ZKC_FRONTEND_MODEL_CHECKED_H
#include "Module.h"
namespace zkc::frontend::semantics {
struct SourceAnalysisBuilder;
}
namespace zkc::frontend::lowering {
struct SourceEmitter;
}
namespace zkc::frontend::model {
/// A source formation result. Only the semantic checker creates this product;
/// common emission and independent PIR admission remain separate obligations.
class CheckedSource {
  std::unique_ptr<Module> value;
  explicit CheckedSource(std::unique_ptr<Module> model)
      : value(std::move(model)) {}
  friend struct semantics::SourceAnalysisBuilder;

public:
  const Module &get() const { return *value; }
  std::unique_ptr<Module> takeModel() && { return std::move(value); }
};
/// A completed emission keeps its checked input and emitted names together.
/// Only lowering can create it; failed lowering leaves its input available for
/// diagnostic queries.
class EmittedSource {
  std::unique_ptr<Module> model;
  source::Content content;
  EmittedSource(std::unique_ptr<Module> model, source::Content content)
      : model(std::move(model)), content(std::move(content)) {}
  friend struct lowering::SourceEmitter;
  friend struct AnalysisAccess;
};
/// Publication owns both checked query data and structurally checked output.
class CompletedAnalysis {
  CompletedAnalysis(Module model, source::Content content)
      : model(std::move(model)), content(std::move(content)) {}
  friend struct AnalysisAccess;

public:
  const Module model;
  const source::Content content;
};
} // namespace zkc::frontend::model
#endif
