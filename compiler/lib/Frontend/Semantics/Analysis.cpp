#include "Analysis.h"
#include "../Instantiation/Select.h"
#include "../Resolution/Project.h"
#include "Check.h"
#include "Provenance.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::frontend::semantics {
struct SourceAnalysisBuilder {
  static model::CheckedSource finish(std::unique_ptr<model::Module> model) {
    return model::CheckedSource(std::move(model));
  }
};
SourceCheck checkStaged(const syntax::Content &original,
                        const instantiation::Selection &staged,
                        const LibraryEmission &linked,
                        std::shared_ptr<const model::LibraryReport> libraries,
                        std::shared_ptr<const resolution::Context> context,
                        StringRef text, StringRef filename,
                        bool resolutionComplete) {
  auto model = std::make_unique<model::Module>();
  model->text = text.str();
  model->filename = filename.str();
  assert(context && "semantic checking requires resolved project input");
  model->resolution = std::move(context);
  model->resolutionComplete = resolutionComplete;
  model->libraries = std::move(libraries);
  const bool checked = check(*model, staged.content, original, linked);
  for (const auto &[name, value] : staged.constants) {
    auto id = model->lookup({0}, name);
    if (id.valid() &&
        model->declarations[id.index].kind == Declaration::Kind::Constant) {
      auto &declaration = model->declarations[id.index];
      declaration.constantValue = value;
      declaration.sort = "index";
      declaration.signatureChecked = true;
    }
  }
  for (const auto &specialization : staged.specializations) {
    Instantiation origin;
    origin.definition = model->lookup({0}, specialization.definition);
    origin.emitted = model->lookup({0}, specialization.emitted);
    origin.location = specialization.location;
    if (!origin.definition.valid() || !origin.emitted.valid())
      continue;
    auto scope = model->declarations[origin.definition.index].members;
    for (const auto &argument : specialization.arguments)
      origin.bindings.push_back({model->lookup(scope, argument.name),
                                 model->internDomain(argument.domain, {0})});
    if (checked) {
      const auto definition = model->declarations[origin.definition.index];
      const auto emitted = model->declarations[origin.emitted.index];
      std::map<DeclId, DomainId> substitution;
      bool agrees = definition.kind == Declaration::Kind::Protocol &&
                    emitted.kind == Declaration::Kind::Protocol &&
                    definition.roles == emitted.roles &&
                    definition.naturalParameters == emitted.naturalParameters;
      for (const auto &binding : origin.bindings)
        agrees &=
            binding.parameter.valid() &&
            substitution.emplace(binding.parameter, binding.argument).second;
      agrees &= substitution.size() == definition.parameters.size();
      auto portsAgree = [&](const auto &before, const auto &after) {
        if (before.size() != after.size())
          return false;
        for (size_t i = 0; i < before.size(); ++i)
          if (before[i].name != after[i].name ||
              before[i].role != after[i].role ||
              model->substitute(before[i].type, substitution) != after[i].type)
            return false;
        return true;
      };
      agrees &= portsAgree(definition.inputs, emitted.inputs) &&
                portsAgree(definition.outputs, emitted.outputs);
      // Staging emits a specialization by substituting its arguments into
      // the definition; one that changes the interface is a staging defect.
      if (!agrees)
        report_fatal_error(
            "specialized protocol does not preserve its nominal interface");
    }
    model->instantiations.push_back(std::move(origin));
  }
  if (checked)
    return SourceAnalysisBuilder::finish(std::move(model));
  return model;
}
} // namespace zkc::frontend::semantics
