#include "zkc/Language/Authoring.h"
#include "State.h"
#include <algorithm>
#include <functional>

using namespace llvm;
namespace zkc::language {
namespace {
bool contains(Span span, SourceId source, uint32_t offset) {
  return span.source.index == source.index && span.begin <= offset &&
         offset < span.end;
}
bool narrower(Span a, Span b) { return a.end - a.begin < b.end - b.begin; }
std::string signature(const Declaration &decl) {
  std::string result = decl.qualifiedName;
  if (!decl.parameters.empty()) {
    result += '<';
    for (const auto &parameter : decl.parameters) {
      if (result.back() != '<')
        result += ", ";
      result += parameter.name;
    }
    result += '>';
  }
  if (!decl.inputs.empty() || !decl.services.empty() || !decl.outputs.empty() ||
      decl.body) {
    result += '(';
    auto data = [&](unsigned index) {
      const auto &port = decl.inputs[index];
      if (result.back() != '(')
        result += ", ";
      result += port.name + ": " + spelling(port.type);
    };
    auto service = [&](unsigned index) {
      const auto &port = decl.services[index];
      if (result.back() != '(')
        result += ", ";
      result += port.name + ": Random<" + spelling(port.field) + ">";
    };
    if (decl.inputOrder.empty()) {
      for (unsigned i = 0; i < decl.inputs.size(); ++i)
        data(i);
      for (unsigned i = 0; i < decl.services.size(); ++i)
        service(i);
    } else
      for (const auto &slot : decl.inputOrder)
        if (slot.kind == Declaration::InputSlot::Kind::Data)
          data(slot.index);
        else if (slot.kind == Declaration::InputSlot::Kind::Service)
          service(slot.index);
    result += ")";
    if (!decl.outputs.empty()) {
      result += " -> ";
      for (unsigned i = 0; i < decl.outputs.size(); ++i) {
        if (i)
          result += ", ";
        result += spelling(decl.outputs[i].type);
      }
    }
  }
  return result;
}
std::string valueText(const Value &value, const Declaration &decl,
                      Body::Mode mode) {
  std::string result = spelling(value.type);
  if (mode == Body::Mode::Protocol) {
    result += "\nAvailable at: ";
    for (unsigned i = 0; i < value.components.size(); ++i) {
      if (i)
        result += ", ";
      auto role = value.components[i];
      if (role < decl.roles.size())
        result += decl.roles[role];
    }
  }
  return result;
}
void visitValues(const Body &body, const Declaration &decl,
                 const std::function<void(const Value &, Body::Mode)> &visit) {
  for (const auto &value : body.values)
    visit(value, body.mode);
  for (const auto &operation : body.operations) {
    if (auto *control = std::get_if<LocalControl>(&operation.action))
      for (const auto &region : control->regions)
        visitValues(*region, decl, visit);
    if (auto *repeat = std::get_if<ProtocolRepeat>(&operation.action))
      visitValues(*repeat->region, decl, visit);
  }
}
} // namespace

Authoring::Authoring(CheckedProject checked)
    : view(checked.storage->authoring) {
  initializeSelections();
}
Authoring::Authoring(const Analysis &analysis)
    : view(analysis.storage->authoring) {
  if (!view)
    view = std::make_shared<detail::AuthoringStorage>();
  initializeSelections();
}
bool Authoring::hasSemanticContext() const { return bool(view->names); }
std::string Authoring::detail(const Declaration &declaration) const {
  return view->signatures[declaration.id.index]
             ? signature(declaration)
             : declaration.qualifiedName + " (signature unavailable)";
}
void Authoring::initializeSelections() {
  for (const auto &tree : view->layoutBodies) {
    if (!tree)
      continue;
    for (unsigned i = 0; i < tree->nodes().size(); ++i) {
      syntax::NodeId id{i};
      if (syntax::category(tree->node(id).kind) !=
          syntax::Category::Declaration)
        continue;
      for (auto child : tree->children(id))
        if (tree->node(child).kind == syntax::Kind::Name) {
          selections.emplace(
              std::make_pair(tree->sourceId().index, tree->span(id).begin),
              tree->span(child));
          break;
        }
    }
  }
}
Span Authoring::selection(const Declaration &decl) const {
  auto found =
      selections.lower_bound({decl.span.source.index, decl.span.begin});
  // Resource attributes can extend the retained declaration's start. The
  // first declaration-name view inside that span is still its own name.
  if (found != selections.end() &&
      found->first.first == decl.span.source.index &&
      found->second.end <= decl.span.end)
    return found->second;
  return decl.span;
}
std::vector<SourceSymbol> Authoring::symbols(SourceId source) const {
  std::vector<SourceSymbol> result;
  for (const auto &decl : view->declarations)
    if (decl.span.source.index == source.index && !decl.generated &&
        !decl.anonymous && decl.parent)
      result.push_back(
          {decl.name, detail(decl), decl.kind, decl.span, selection(decl)});
  return result;
}
std::optional<Span> Authoring::definition(SourceId source,
                                          uint32_t offset) const {
  std::optional<Span> use, target;
  auto consider = [&](Span span, Span definition) {
    if (contains(span, source, offset) && (!use || narrower(span, *use))) {
      use = span;
      target = definition;
    }
  };
  for (const auto &lexical : view->lexicalResolutions)
    if (contains(lexical.declaration, source, offset)) {
      for (const auto &reference : lexical.references)
        consider(reference.span, reference.definition);
      for (const auto &binding : lexical.bindings)
        consider(binding.definition, binding.definition);
    }
  for (const auto &reference : view->api.references)
    consider(reference.span,
             selection(view->declarations[reference.target.index]));
  return target;
}
std::optional<SourceHover> Authoring::hover(SourceId source,
                                            uint32_t offset) const {
  std::optional<SourceHover> result;
  for (const auto &decl : view->declarations) {
    if (decl.generated || !contains(decl.span, source, offset))
      continue;
    auto name = selection(decl);
    if (contains(name, source, offset))
      result = SourceHover{name, detail(decl)};
    if (decl.body)
      visitValues(*decl.body, decl, [&](const Value &value, Body::Mode mode) {
        if (contains(value.span, source, offset) &&
            (!result || narrower(value.span, result->span)))
          result = SourceHover{value.span, valueText(value, decl, mode)};
      });
    for (const auto &service : decl.services)
      if (contains(service.span, source, offset))
        result = SourceHover{
            service.span, service.name + ": Random<" + spelling(service.field) +
                              ">\nOwned by: " + decl.roles[service.owner]};
  }
  if (!result) {
    for (const auto &lexical : view->lexicalResolutions)
      if (contains(lexical.declaration, source, offset))
        for (const auto &reference : lexical.references)
          if (contains(reference.span, source, offset) &&
              !contains(reference.definition, source, offset)) {
            auto target =
                hover(reference.definition.source, reference.definition.begin);
            if (target)
              result = SourceHover{reference.span, target->text};
          }
  }
  if (!result) {
    const detail::ReferenceRecord *selected = nullptr;
    for (const auto &reference : view->api.references)
      if (contains(reference.span, source, offset) &&
          (!selected || narrower(reference.span, selected->span)))
        selected = &reference;
    if (selected)
      result = SourceHover{selected->span,
                           detail(view->declarations[selected->target.index])};
  }
  if (result)
    for (const auto &spec : view->pendingSpecifications)
      if (contains(view->declarations[spec.protocol.index].span, source,
                   offset)) {
        if (!StringRef(result->text).contains("Assurance: open"))
          result->text +=
              "\nAssurance: open (spec retained; Lean checking pending)";
        break;
      }
  return result;
}
std::vector<SourceCompletion> Authoring::completion(SourceId source,
                                                    uint32_t offset,
                                                    StringRef prefix) const {
  std::map<std::string, SourceCompletion> candidates;
  const Declaration *context = nullptr;
  for (const auto &decl : view->declarations)
    if (!decl.generated && contains(decl.span, source, offset) &&
        (!context || narrower(decl.span, context->span)))
      context = &decl;
  if (context && view->names) {
    auto owner = (context->kind == Declaration::Kind::Module ||
                  context->kind == Declaration::Kind::Interface)
                     ? std::optional(context->id)
                     : context->parent;
    for (; owner; owner = view->declarations[owner->index].parent)
      for (const auto &[name, binding] : view->names->visible[owner->index]) {
        if (!StringRef(name).starts_with(prefix))
          continue;
        const auto &decl = view->declarations[binding.target.index];
        candidates.emplace(
            name, SourceCompletion{name, detail(decl), selection(decl)});
      }
  }
  std::map<std::string, unsigned> depths;
  std::map<uint32_t, std::string> localTypes;
  if (context && context->body)
    visitValues(*context->body, *context,
                [&](const Value &value, Body::Mode mode) {
                  if (value.span.source.index == source.index)
                    localTypes.emplace(value.span.begin,
                                       valueText(value, *context, mode));
                });
  for (const auto &lexical : view->lexicalResolutions)
    if (contains(lexical.declaration, source, offset))
      for (const auto &binding : lexical.bindings)
        if (contains(binding.visible, source, offset) &&
            StringRef(binding.name).starts_with(prefix)) {
          auto found = depths.find(binding.name);
          if (found != depths.end() && found->second > binding.depth)
            continue;
          depths[binding.name] = binding.depth;
          auto info = localTypes.find(binding.definition.begin);
          candidates.insert_or_assign(binding.name,
                                      SourceCompletion{binding.name,
                                                       info != localTypes.end()
                                                           ? info->second
                                                           : "local binding",
                                                       binding.definition});
        }
  std::vector<SourceCompletion> result;
  for (auto &[_, candidate] : candidates) {
    if (result.size() == 256)
      break;
    result.push_back(std::move(candidate));
  }
  return result;
}
std::optional<syntax::Snapshot> Authoring::syntaxTree(SourceId source) const {
  return source.index < view->layoutBodies.size()
             ? view->layoutBodies[source.index]
             : std::nullopt;
}
syntax::FormatResult
Authoring::format(SourceId source, source::Cancellation cancellation) const {
  if (auto tree = syntaxTree(source); tree && !tree->headersOnly())
    return syntax::format(*tree, {}, cancellation);
  return {
      "", false, {{"source.format", "layout syntax is unavailable", {}, {}}}};
}
} // namespace zkc::language
