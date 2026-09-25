#include "zkc/Frontend/Compile.h"
#include "Instantiation/Select.h"
#include "Lowering/PIR.h"
#include "Resolution/Declarations.h"
#include "Resolution/Project.h"
#include "Semantics/Check.h"
#include "Tooling/Access.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::frontend {
Expected<source::Content> lower(const CheckedModule &module) {
  return lowering::lower(*module.model);
}
Analysis analyzeProtocol(const Input &input) {
  return analyzeProject(ProjectInput::single(input));
}
Expected<source::Content> compileProject(const ProjectInput &input) {
  return analyzeProject(input).lower();
}
Expected<source::Construction>
bindConstruction(const ProjectInput &input, const source::Module &source,
                 source::Construction descriptor) {
  if (descriptor.draws.size() > 32768)
    return zkc::error("construction-descriptor-limit");
  auto resolved = resolution::resolve(input, true);
  if (!resolved.diagnostics.empty()) {
    const auto &d = resolved.diagnostics.front();
    return diagnostic(input, d);
  }
  // Printed carrier text is another spelling of the closed JSON subject.
  // It has no authoring aliases; its descriptor already uses carrier names.
  if (const auto *module = std::get_if<syntax::Module>(&resolved.content);
      module && module->carrier)
    return descriptor;
  std::set<std::string> functions;
  std::map<std::string, std::string> functionOrigins;
  std::set<std::string> sharedOrigins, authoredGroups, ambiguousFunctions;
  // A function declared under this name, as opposed to the copies and entries
  // that linking and imports emit under an existing origin.
  auto authored = [&](const std::string &name) {
    auto found = resolved.context->selectors.find(name);
    if (found == resolved.context->selectors.end())
      return false;
    const auto &d = resolved.context->declarations[found->second];
    return d.kind == resolution::Declaration::Kind::Function &&
           d.symbol == name;
  };
  for (const auto &function : source.functions) {
    functions.insert(function.name);
    if (function.origin) {
      functionOrigins.emplace(function.name, function.origin->definition);
      if (function.origin->definition != function.name) {
        sharedOrigins.insert(function.origin->definition);
        if (authored(function.name))
          authoredGroups.insert(function.origin->definition);
      }
    }
  }
  // A function whose name is also an origin other functions share names two
  // selections: the function alone, and that group. Its own copies share the
  // origin as expanded copies do; another declared function sharing it makes a
  // group the function belongs to, which its selector would also reach.
  for (const auto &[name, logical] : functionOrigins)
    if (sharedOrigins.count(name) &&
        (name != logical || authoredGroups.count(name)))
      ambiguousFunctions.insert(name);
  auto bind = [&](std::string &name, bool origin) -> Error {
    if (!origin) {
      auto entry = resolved.context->entrySelectors.find(name);
      if (entry != resolved.context->entrySelectors.end()) {
        name = resolved.context->declarations[entry->second].symbol;
        return Error::success();
      }
    }
    auto head = name;
    std::string suffix;
    for (;;) {
      if (resolved.context->ambiguousOrigins.count(head))
        return zkc::error("construction-source-selector-ambiguous");
      auto found = resolved.context->selectors.find(head);
      if (found != resolved.context->selectors.end()) {
        const auto &d = resolved.context->declarations[found->second];
        // A definition selector follows all its instantiations; a configure
        // selector names one closed instance. Ordinary functions are direct
        // selectors, including explicit group members. Generic functions are
        // emitted as definitions under their origins.
        const bool direct =
            d.kind == resolution::Declaration::Kind::Configuration ||
            (d.kind == resolution::Declaration::Kind::Function &&
             functions.count(d.symbol));
        // An imported function's emitted entry can hold no primitive: its body
        // is a copy made where it is linked, and every such copy shares the
        // origin allocated to its declaration, which nothing else claims. Its
        // selector binds to that origin to reach them. An application-root
        // function keeps its own symbol, which group siblings do not share.
        const bool imported =
            d.kind == resolution::Declaration::Kind::Function &&
            !authored(d.symbol);
        name = (origin && (!direct || imported) ? d.origin : d.symbol) + suffix;
        // A logical name other declared functions share is valid source, but
        // this two-field carrier selector cannot encode just the direct
        // declaration.
        if (origin && direct && ambiguousFunctions.count(name))
          return zkc::error("construction-source-selector-ambiguous");
        return Error::success();
      }
      auto dot = head.rfind('.');
      if (dot == std::string::npos)
        return Error::success(); // An exact closed selector is admitted
                                 // downstream.
      suffix = head.substr(dot) + suffix;
      head.resize(dot);
    }
  };
  if (auto e = bind(descriptor.entry, false))
    return std::move(e);
  for (auto &draw : descriptor.draws)
    if (auto e = bind(draw.first, true))
      return std::move(e);
  // Construction selects every copy a selector reaches, and normalized site
  // resolution renames a selector's site through its declaration's site map
  // (docs/spec/profiles/compiler/local-algorithms.md): a generic definition's
  // map is shared by its instantiations, a function's is its own. An explicit
  // origin group names no declaration and has no site map, so under normalized
  // identity its selector is written out as the functions carrying the site,
  // each then resolved through its own map.
  if (descriptor.identity != source::Construction::Identity::Normalized)
    return descriptor;
  using Key = std::pair<std::string, std::string>;
  std::set<std::string> declared;
  for (const auto &function : source.functions)
    declared.insert(function.name);
  for (const auto &definition : source.definitions)
    declared.insert(definition.name);
  for (const auto &configuration : source.configurations)
    declared.insert(configuration.name);
  // Index actual occurrences, not every function in a group, so a member
  // without the site is not selected.
  std::map<Key, std::vector<std::string>> occurrences;
  size_t work = 0;
  for (const auto &function : source.functions) {
    if (!function.body || !function.origin ||
        function.origin->definition == function.name)
      continue;
    source::walk(*function.body, [&](const source::Instruction &instruction) {
      if (++work > 1000000 || instruction.site.empty())
        return;
      occurrences[{function.origin->definition, instruction.site}].push_back(
          function.name);
    });
    if (work > 1000000)
      return zkc::error("construction-analysis-limit");
  }
  // Naming one selector twice is malformed. Check the bound selectors before
  // writing any out, so that writing out cannot hide a repeat.
  if (std::set<Key>(descriptor.draws.begin(), descriptor.draws.end()).size() !=
      descriptor.draws.size())
    return zkc::error("construction-draw-selector");
  auto draws = std::move(descriptor.draws);
  descriptor.draws.clear();
  std::set<Key> written;
  for (const auto &draw : draws) {
    auto found =
        declared.count(draw.first) ? occurrences.end() : occurrences.find(draw);
    // A selector with no occurrence is kept; normalized site resolution
    // diagnoses it with source-site-selection before construction.
    const std::vector<std::string> own{draw.first};
    for (const auto &function :
         found == occurrences.end() ? own : found->second) {
      if (found != occurrences.end() && ambiguousFunctions.count(function))
        return zkc::error("construction-source-selector-ambiguous");
      if (!written.insert({function, draw.second}).second)
        continue;
      if (descriptor.draws.size() == 32768)
        return zkc::error("construction-descriptor-limit");
      descriptor.draws.emplace_back(function, draw.second);
    }
  }
  return descriptor;
}
Analysis analyzeProject(const ProjectInput &input) {
  auto resolved = resolution::resolve(input);
  const auto *root = input.file(
      resolved.context->owners.empty() ? 0 : resolved.context->owners[0].root);
  StringRef text = root ? root->text() : StringRef();
  StringRef filename = root ? root->filename() : StringRef("<project>");
  const bool resolutionComplete = resolved.diagnostics.empty();
  std::shared_ptr<const semantics::LibraryReport> retainedLibraries;
  auto failure = [&](std::shared_ptr<model::Module> model = nullptr) {
    if (!model)
      model = std::make_shared<model::Module>();
    model->project = input;
    model->resolution = resolved.context;
    model->resolutionComplete = resolutionComplete;
    model->text = text.str();
    model->filename = filename.str();
    model->diagnostics.insert(model->diagnostics.begin(),
                              resolved.diagnostics.begin(),
                              resolved.diagnostics.end());
    model->syntaxPartial = resolved.syntaxPartial;
    model->complete = false;
    for (auto &d : model->declarations)
      d.loweredName.reset();
    if (!model->libraries)
      model->libraries = retainedLibraries;
    if (const auto *m = std::get_if<syntax::Module>(&resolved.content))
      resolution::declarations(*m, [&](const auto &d, auto kind) {
        using K = resolution::Declaration::Kind;
        auto semanticKind =
            kind == K::Protocol                    ? Declaration::Kind::Protocol
            : kind == K::Record || kind == K::Enum ? Declaration::Kind::Record
            : kind == K::Constant                  ? Declaration::Kind::Constant
            : kind == K::Relation                  ? Declaration::Kind::Relation
            : kind == K::View          ? Declaration::Kind::RelationView
            : kind == K::Instance      ? Declaration::Kind::Instance
            : kind == K::Entry         ? Declaration::Kind::Entry
            : kind == K::Configuration ? Declaration::Kind::Configuration
            : kind == K::Binding       ? Declaration::Kind::Binding
            : kind == K::Bundle        ? Declaration::Kind::Bundle
                                       : Declaration::Kind::Function;
        if (!model->lookup({0}, d.name).valid()) {
          auto id = model->add(semanticKind, {0}, d.name, d.location);
          if constexpr (std::is_same_v<std::decay_t<decltype(d)>,
                                       syntax::Function> ||
                        std::is_same_v<std::decay_t<decltype(d)>,
                                       syntax::Protocol>) {
            auto &stub = model->declarations[id.index];
            stub.generic = d.generic;
            stub.hasBody = bool(d.body);
            stub.bodyState = d.body ? Declaration::BodyState::Deferred
                                    : Declaration::BodyState::External;
          }
        }
      });
    model->retainQueryMetadata();
    return semantics::AnalysisAccess::make(std::move(model));
  };
  if (!resolutionComplete && !resolved.recoverable)
    return failure();
  // Only resolution may select a safe subset: checking the original content
  // after a visibility failure could otherwise manufacture an invalid result.
  const auto &content =
      resolutionComplete ? resolved.content : *resolved.recoverable;
  auto staged =
      instantiation::select(content, text, filename, &retainedLibraries);
  if (!staged) {
    handleAllErrors(
        staged.takeError(),
        [&](const SourceDiagnostic &d) {
          resolved.diagnostics.push_back(
              {d.code, d.message, d.location, d.related, d.causes});
        },
        [&](const Refusal &e) {
          resolved.diagnostics.push_back({e.code, e.detail, {}});
        });
    return failure();
  }
  auto analysis = semantics::analyzeStaged(content, *staged, text, filename);
  if (!resolutionComplete)
    return failure(std::make_shared<model::Module>(
        semantics::AnalysisAccess::get(analysis)));
  return analysis;
}
Analysis analyzeProtocol(StringRef text, StringRef filename) {
  return analyzeProtocol(Input(text.str(), filename.str()));
}

} // namespace zkc::frontend

namespace zkc::frontend::semantics {
Analysis analyzeStaged(const syntax::Content &original,
                       const instantiation::Selection &staged, StringRef text,
                       StringRef filename, ArrayRef<Diagnostic> diagnostics) {
  auto model = std::make_shared<model::Module>();
  model->text = text.str();
  model->filename = filename.str();
  if (const auto *module = std::get_if<syntax::Module>(&original))
    if (module->project) {
      model->project = module->project->input;
      model->resolution = module->project;
    }
  model->resolutionComplete = true;
  model->libraries = staged.libraries;
  model->syntaxPartial = !diagnostics.empty();
  check(*model, staged.content, original);
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
    if (model->complete) {
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
  model->diagnostics.insert(model->diagnostics.begin(), diagnostics.begin(),
                            diagnostics.end());
  model->complete &= model->diagnostics.empty();
  if (model->complete) {
    auto emitted = lowering::lower(*model);
    if (!emitted) {
      handleAllErrors(
          emitted.takeError(),
          [&](const SourceDiagnostic &d) {
            model->diagnostics.push_back(
                {d.code, d.message, d.location, d.related, d.causes});
          },
          [&](const Refusal &e) {
            model->diagnostics.push_back({e.code, e.detail, {}});
          });
      model->complete = false;
    } else if (const auto *emittedModule =
                   std::get_if<source::Module>(&*emitted)) {
      for (const auto &plan : model->bodies) {
        if (!plan.emit)
          continue;
        auto &d = model->declarations.at(plan.declaration.index);
        auto name = d.name;
        const bool genericFunction =
            d.generic && d.kind != Declaration::Kind::Protocol;
        if (genericFunction && model->resolution)
          if (const auto *origin = model->resolution->lookup(d.name))
            name = model->resolution->origin(origin->identity);
        auto hasName = [&](const auto &declarations) {
          return llvm::any_of(
              declarations, [&](const auto &out) { return out.name == name; });
        };
        if (d.kind == Declaration::Kind::Protocol
                ? hasName(emittedModule->protocols)
            : genericFunction ? hasName(emittedModule->definitions)
                              : hasName(emittedModule->functions))
          d.loweredName = std::move(name);
      }
    }
  }
  model->retainQueryMetadata();
  return semantics::AnalysisAccess::make(std::move(model));
}
} // namespace zkc::frontend::semantics
