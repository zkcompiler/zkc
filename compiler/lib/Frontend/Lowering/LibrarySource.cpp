#include "LibrarySource.h"
#include "../Library/Diagnostic.h"
#include "../Resolution/Project.h"
#include "../Syntax/Types.h"
#include "../Work.h"
#include "Library.h"
#include "OutputWork.h"
#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::frontend::lowering {
namespace {
namespace lib = library;
/// Preserve source nominal formation and constructor authority at the entry
/// boundary. The library's internal functions are already typed common bodies;
/// only aggregate entry adapters still go through the ordinary source checker.
class EntryAdapter {
  const resolution::Context &project;
  const lib::Environment &environment;
  WorkBudget &budget;

public:
  EntryAdapter(const resolution::Context &project,
               const lib::Environment &environment, WorkBudget &budget)
      : project(project), environment(environment), budget(budget) {}
  // A closed alias is still an authored function boundary. Reintroduce its
  // product/record ports before the ordinary argument binder sees it; only
  // the wrapper's call to the already checked body uses flattened leaves.
  Expected<LibraryEntry> adapt(const lib::LinkedFunction &linked,
                               const source::Function &flat, StringRef alias) {
    if (auto error = work::charge(budget, WorkAccount::GeneratedSource))
      return error;
    LibraryEntry entry;
    auto &result = entry.header;
    result.name = alias.str();
    const auto *declaration = project.lookup(alias);
    if (!declaration)
      report_fatal_error("linked alias is absent from the captured project");
    result.location = declaration->location;
    result.origin =
        source::LogicalOrigin{project.origin(declaration->identity), {}};
    auto &forwarding = entry.forwarding;
    forwarding.name = result.name;
    forwarding.origin = result.origin;
    auto leafType = [&](StringRef spelling) -> Expected<syntax::Type> {
      auto [kind, domain] = spelling.split(':');
      syntax::Type t, argument;
      t.location = argument.location = result.location;
      argument.name = domain.str();
      argument.quoted = true;
      if (kind == "field" || kind == "group") {
        t = argument;
        t.members = {"Element"};
      } else if (kind == "vector" || kind == "groups" || kind == "matrix") {
        syntax::Type element = argument;
        element.members = {"Element"};
        t.name = kind == "matrix" ? "Matrix" : "Vector";
        t.arguments.push_back(std::move(element));
      } else if (kind == "resource_unit") {
        t.name = "ResourceUnit";
        t.arguments.push_back(std::move(argument));
      } else {
        for (const auto &name : typeSpellings)
          if (name.constructor == kind)
            t.name = name.surface.str();
        // Lowering admitted every leaf as a bound type, and every bound
        // constructor has a source spelling.
        if (t.name.empty())
          report_fatal_error("linked leaf type has no source spelling");
        if (!domain.empty())
          t.arguments.push_back(std::move(argument));
      }
      return t;
    };
    std::function<Expected<syntax::Type>(const lib::Type &, const lib::Layout &,
                                         const source::Names &,
                                         std::vector<unsigned>)>
        shape;
    shape = [&](const lib::Type &type, const lib::Layout &layout,
                const source::Names &spellings,
                std::vector<unsigned> path) -> Expected<syntax::Type> {
      if (auto error = work::charge(budget, WorkAccount::GeneratedSource))
        return error;
      for (size_t i = 0; i < layout.leaves.size(); ++i)
        if (layout.leaves[i].path == path)
          return leafType(spellings[i]);
      syntax::Type t;
      t.location = result.location;
      if (type.kind == lib::Type::Kind::Record) {
        const auto *resolved = project.lookup(type.declaration);
        // Resolution registers every struct of every captured module.
        if (!resolved)
          report_fatal_error(
              "linked record is absent from the captured project");
        t.name = resolved->symbol;
        return t;
      }
      // Zero-length arrays still retain their element type even though no
      // physical leaf supplies its spelling.
      if (type.kind == lib::Type::Kind::Logical) {
        std::string spelling = type.name;
        if (!type.arguments.empty()) {
          auto domain =
              lib::resolvedDomain(type.arguments.front(), environment);
          if (!domain)
            return domain.takeError();
          spelling += ":" + *domain;
        }
        return leafType(spelling);
      }
      // Linking closes parameters and abstract members, and entries with a
      // variant port keep their flat boundary.
      if (type.kind != lib::Type::Kind::Product &&
          type.kind != lib::Type::Kind::Array)
        report_fatal_error("linked entry port has no source shape");
      const bool array = type.kind == lib::Type::Kind::Array;
      t.product = !array;
      const size_t count =
          array ? type.arguments.front().number : type.elements.size();
      if (array) {
        auto child = path;
        child.push_back(0);
        auto element = shape(type.elements.front(), layout, spellings, child);
        if (!element)
          return element.takeError();
        t.name = "Array";
        syntax::Type extent;
        extent.location = result.location;
        extent.natural = true;
        extent.name = std::to_string(count);
        t.arguments = {std::move(*element), std::move(extent)};
        return t;
      }
      for (size_t i = 0; i < count; ++i) {
        auto child = path;
        child.push_back(i);
        auto element =
            shape(type.elements[array ? 0 : i], layout, spellings, child);
        if (!element)
          return element.takeError();
        t.arguments.push_back(std::move(*element));
      }
      return t;
    };
    auto projection = [](const lib::Type &type, StringRef root,
                         const std::vector<unsigned> &path) {
      std::string name = root.str();
      const lib::Type *at = &type;
      for (auto index : path) {
        name +=
            "." + (at->kind == lib::Type::Kind::Record ? at->fields.at(index)
                                                       : std::to_string(index));
        at = &at->elements.at(at->kind == lib::Type::Kind::Array ? 0 : index);
      }
      return name;
    };
    source::AlgorithmCall call;
    call.callee = flat.name;
    size_t offset = 0;
    for (size_t port = 0; port < linked.body.inputs.size(); ++port) {
      const auto &layout = linked.values.at(linked.body.inputs[port].id.index);
      if (auto error = work::charge(budget, WorkAccount::GeneratedSource,
                                    layout.leaves.size()))
        return error;
      source::Names spellings;
      for (size_t i = 0; i < layout.leaves.size(); ++i)
        spellings.push_back(flat.arguments.at(offset++).type);
      auto t = shape(layout.concreteType, layout, spellings, {});
      if (!t)
        return t.takeError();
      const auto name = linked.body.signature.inputLabels.empty()
                            ? "arg" + std::to_string(port)
                            : linked.body.signature.inputLabels[port];
      result.arguments.push_back({name, std::move(*t)});
      for (size_t i = 0; i < layout.leaves.size(); ++i) {
        auto value =
            projection(layout.concreteType, name, layout.leaves[i].path);
        call.inputs.push_back(value);
        forwarding.arguments.push_back({std::move(value), spellings[i]});
      }
    }
    std::string prefix = "__link_result_";
    while (llvm::any_of(result.arguments, [&](const auto &p) {
      return StringRef(p.name).starts_with(prefix);
    }))
      prefix += "_";
    if (auto error = work::charge(budget, WorkAccount::GeneratedSource,
                                  flat.results.size()))
      return error;
    for (size_t i = 0; i < flat.results.size(); ++i)
      call.outputs.push_back(prefix + std::to_string(i));
    offset = 0;
    for (const auto &layout : linked.results) {
      if (auto error = work::charge(budget, WorkAccount::GeneratedSource,
                                    layout.leaves.size()))
        return error;
      source::Names spellings;
      for (size_t i = 0; i < layout.leaves.size(); ++i)
        spellings.push_back(flat.results.at(offset + i));
      auto t = shape(layout.concreteType, layout, spellings, {});
      if (!t)
        return t.takeError();
      result.results.push_back(std::move(*t));
      source::Names paths;
      for (const auto &leaf : layout.leaves) {
        auto path = projection(layout.concreteType, "", leaf.path);
        paths.push_back(path.empty() ? path : path.substr(1));
      }
      entry.resultPaths.push_back(std::move(paths));
      offset += layout.leaves.size();
    }
    forwarding.results = flat.results;
    source::Instruction invoke, ret;
    invoke.site = "invoke";
    invoke.value = call;
    ret.value = source::Return{call.outputs};
    forwarding.body = source::Body{std::move(invoke), std::move(ret)};
    return entry;
  }
};
} // namespace
Expected<LibrarySource>
emitLibrarySource(syntax::Module out, const library::Environment &environment,
                  ArrayRef<library::LinkedProgram> programs,
                  const std::map<std::string, source::Names> &entryAliases,
                  const std::set<std::string> &names,
                  const resolution::Context &project, WorkBudget &budget) {
  source::Module linked;
  std::vector<LibraryEntry> entries;
  std::set<std::string> emitted;
  if (programs.empty())
    return LibrarySource{std::move(out),
                         {std::move(linked), std::move(entries)}};
  auto atSource = [&](Error error, std::optional<source::Span> location) {
    return handleErrors(
        std::move(error),
        [&](const Refusal &e) {
          return diagnostic(project.input,
                            Diagnostic{e.code, e.detail, location});
        },
        [&](const lib::Diagnostic &e) {
          return diagnostic(project.input,
                            Diagnostic{e.code, e.message, location});
        });
  };
  auto atAlias = [&](Error error, StringRef alias) {
    const auto *declaration = project.lookup(alias);
    if (!declaration)
      report_fatal_error("linked alias is absent from the captured project");
    return atSource(std::move(error), declaration->location);
  };
  // All requested links share one layout world and resource-slot allocator.
  auto concrete = lib::lower(
      programs, [&](const auto &id) { return project.origin(id); }, budget);
  if (!concrete)
    return atSource(concrete.takeError(), out.location);
  if (concrete->library || !concrete->definitions.empty() ||
      !concrete->configurations.empty() || !concrete->relations.empty() ||
      !concrete->relationViews.empty() || !concrete->protocols.empty() ||
      !concrete->instances.empty() || !concrete->entries.empty())
    report_fatal_error("library lowering produced a module section other than "
                       "functions and bindings");
  for (const auto &binding : concrete->bindings) {
    auto existing = llvm::find_if(
        out.bindings, [&](const auto &b) { return b.name == binding.name; });
    if (existing != out.bindings.end()) {
      if (existing->application.contract != binding.application.contract ||
          existing->application.arguments != binding.application.arguments ||
          existing->application.implementation !=
              binding.application.implementation)
        return diagnostic(
            project.input,
            Diagnostic{"library-source-collision",
                       "lowered binding collides with a different binding",
                       existing->location});
    } else
      out.bindings.push_back(binding);
  }
  std::set<std::string> wrappedEntries;
  for (const auto &program : programs) {
    const auto entryPosition =
        llvm::find_if(program.functions(), [&](const auto &f) {
          return f.symbol == program.entry();
        });
    if (entryPosition == program.functions().end())
      report_fatal_error("linked program has no entry function");
    const auto &entry = *entryPosition;
    auto aggregate = [](const lib::Layout &layout) {
      return layout.leaves.size() != 1 || !layout.leaves.front().path.empty();
    };
    bool needsWrapper = llvm::any_of(entry.results, aggregate);
    for (const auto &input : entry.body.inputs)
      needsWrapper |= aggregate(entry.values.at(input.id.index));
    if (!needsWrapper || wrappedEntries.count(program.entry()))
      continue;
    const auto flatPosition =
        llvm::find_if(concrete->functions,
                      [&](const auto &f) { return f.name == program.entry(); });
    if (flatPosition == concrete->functions.end())
      report_fatal_error("library lowering dropped a linked entry");
    const auto &flat = *flatPosition;
    // The ordinary checker has no source spelling for closed variant
    // descriptors. Preserve its existing flat boundary; project integration
    // must register the retained logical layouts to bind aggregate variants.
    // A variant inside an empty array has no flat leaf, so the concrete
    // types the wrapper would spell decide as well; the logical signature
    // would miss a variant hidden behind a component's abstract member.
    std::function<bool(const lib::Type &)> variant = [&](const lib::Type &t) {
      return t.kind == lib::Type::Kind::Variant ||
             llvm::any_of(t.elements, variant);
    };
    bool variantPort =
        llvm::any_of(flat.arguments,
                     [](const auto &p) {
                       return StringRef(p.type).starts_with("variant:");
                     }) ||
        llvm::any_of(flat.results, [](const auto &t) {
          return StringRef(t).starts_with("variant:");
        });
    for (const auto &input : entry.body.inputs)
      variantPort |= variant(entry.values.at(input.id.index).concreteType);
    for (const auto &result : entry.results)
      variantPort |= variant(result.concreteType);
    if (variantPort)
      continue;
    wrappedEntries.insert(program.entry());
    for (const auto &alias : entryAliases.at(program.entry())) {
      auto wrapper =
          EntryAdapter(project, environment, budget).adapt(entry, flat, alias);
      if (!wrapper)
        return atAlias(wrapper.takeError(), alias);
      entries.push_back(std::move(*wrapper));
    }
  }
  std::map<std::string, std::string> rename;
  for (const auto &[symbol, aliases] : entryAliases)
    if (!wrappedEntries.count(symbol))
      rename.emplace(symbol, aliases.front());
  std::set<std::string> foundEntries;
  for (const auto &original : concrete->functions) {
    source::Names aliases{original.name};
    if (auto entry = entryAliases.find(original.name);
        entry != entryAliases.end()) {
      if (!wrappedEntries.count(entry->first))
        aliases = entry->second;
      foundEntries.insert(entry->first);
    }
    for (const auto &alias : aliases) {
      if (auto error =
              chargeFunction(budget, WorkAccount::GeneratedSource, original))
        return error;
      auto f = original;
      f.name = alias;
      const bool publicEntry = entryAliases.count(original.name) &&
                               !wrappedEntries.count(original.name);
      // Internal link symbols are cache locators, not authored occurrence
      // names. Keep the checked member's logical definition; distinct call
      // sites retain instance identity in the expansion path. Public aliases
      // name entry roots.
      if (f.origin && publicEntry)
        f.origin->definition = project.origin(project.qualify(f.name));
      if (!emitted.insert(f.name).second ||
          (!publicEntry && names.count(f.name))) {
        auto error = zkc::error(
            "library-source-collision",
            "lowered function name collides with another declaration");
        if (publicEntry)
          return atAlias(std::move(error), alias);
        if (const auto *declaration = project.lookup(f.name))
          return atSource(std::move(error), declaration->location);
        return atSource(std::move(error), out.location);
      }
      if (f.body)
        source::walk(*f.body, [&](source::Instruction &instruction) {
          if (auto *call = instruction.get<source::AlgorithmCall>()) {
            auto target = rename.find(call->callee);
            if (target != rename.end())
              call->callee = target->second;
          }
        });
      linked.functions.push_back(std::move(f));
    }
  }
  if (foundEntries.size() != entryAliases.size())
    report_fatal_error("library lowering dropped a linked entry");
  return LibrarySource{std::move(out), {std::move(linked), std::move(entries)}};
}
} // namespace zkc::frontend::lowering
