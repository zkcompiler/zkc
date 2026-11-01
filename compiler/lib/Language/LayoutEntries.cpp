#include "LayoutReader.h"
#include "llvm/ADT/STLExtras.h"
#include <set>
using namespace llvm;
namespace zkc::language::detail {
Error LayoutReader::proofEntry(Id id, SyntaxDeclaration &parent,
                               SyntaxDeclaration result) {
  auto words_ = words(id);
  if (!words_)
    return words_.takeError();
  size_t keyword = visible(id) ? 1 : 0;
  if (words_->size() <= keyword || (*words_)[keyword] != "scheme")
    return fail(id, "expected a scheme declaration",
                "source.layout-unavailable");
  auto nodes = children(id);
  if (nodes.size() != 3 || kind(nodes[2]) != K::Suite)
    return fail(id, "invalid proof declaration", "source.entry");
  auto target = type(nodes[1]);
  if (!target || target->kind != SyntaxType::Kind::Name)
    return target ? fail(id, "proof target requires a protocol name",
                         "source.entry")
                  : target.takeError();
  result.kind = Declaration::Kind::Entry;
  result.entryKind = EntryKind::Proof;
  result.entryBlock = true;
  result.target = target->name;
  result.targetArguments = target->arguments;
  result.targetLabels = target->labels;
  SyntaxProofEntry proof;
  proof.span = span(id);
  std::set<std::string> choices;
  auto selector = [&](Id value) -> Expected<SyntaxInputSelector> {
    auto text = name(value);
    if (!text)
      return text.takeError();
    SyntaxInputSelector selected;
    selected.span = span(value);
    StringRef rest(*text);
    selected.port = rest.split('.').first.str();
    rest = rest.drop_front(selected.port.size());
    while (!rest.empty()) {
      rest = rest.drop_front();
      auto part = rest.split('.').first;
      if (part.empty())
        return fail(value, "empty public field path", "source.entry");
      selected.path.push_back(part.str());
      rest = rest.drop_front(part.size());
    }
    return selected;
  };
  for (auto choice : children(nodes[2])) {
    auto key = head(choice);
    auto parts_ = children(choice);
    if (key == "setup" && kind(choice) == K::Selection && parts_.size() == 2) {
      auto slotName = name(parts_[0]);
      if (!slotName)
        return slotName.takeError();
      SyntaxSetupSlot slot{
          SyntaxName{*slotName, span(parts_[0])}, {}, span(choice)};
      for (auto item : children(parts_[1])) {
        auto selected = selector(item);
        if (!selected)
          return selected.takeError();
        SyntaxSelector input;
        input.port = selected->port;
        input.path = selected->path;
        input.span = selected->span;
        slot.inputs.push_back(std::move(input));
      }
      result.setups.push_back(std::move(slot));
      continue;
    }
    if (kind(choice) != K::Selection || parts_.size() != 1 ||
        !choices.insert(key.str()).second)
      return fail(choice, "unknown or duplicate proof choice", "source.entry");
    auto value = parts_.front();
    if (key == "public") {
      for (auto item : children(value)) {
        auto selected = selector(item);
        if (!selected)
          return selected.takeError();
        proof.publicInputs.push_back(std::move(*selected));
      }
    } else if (key == "accept" || key == "complete") {
      auto selected = selector(value);
      if (!selected)
        return selected.takeError();
      if (selected->port == "out") {
        if (selected->path.empty())
          return fail(value, "accept requires an output", "source.entry");
        selected->port = selected->path.front();
        selected->path.erase(selected->path.begin());
      }
      SyntaxSelector output;
      output.output = true;
      output.port = selected->port;
      output.path = selected->path;
      output.span = selected->span;
      if (key == "accept")
        proof.acceptance = std::move(output);
      else
        proof.completion = std::move(output);
    } else if (key == "prover" || key == "verifier" || key == "target") {
      auto text = name(value);
      if (!text)
        return text.takeError();
      SyntaxName named{*text, span(value)};
      if (key == "prover")
        proof.prover = named;
      else if (key == "verifier")
        proof.verifier = named;
      else
        proof.target = named;
    } else if (key == "construction") {
      if (head(value) == "authored")
        proof.construction = ProofEntry::Construction::Authored;
      else if (head(value) == "fiat_shamir") {
        auto call = children(value);
        if (kind(value) != K::Call || call.size() != 2 ||
            children(call[1]).size() != 2)
          return fail(value, "fiat_shamir requires a suite and service",
                      "source.entry");
        auto args = children(call[1]);
        auto suite = name(args[0]);
        auto service = name(args[1]);
        if (!suite)
          return suite.takeError();
        if (!service)
          return service.takeError();
        if (suite->size() < 2 || suite->front() != '"' || suite->back() != '"')
          return fail(args[0], "expected a suite string", "source.entry");
        proof.construction = ProofEntry::Construction::FiatShamir;
        proof.suite = suite->substr(1, suite->size() - 2);
        proof.service = SyntaxName{*service, span(args[1])};
      } else {
        auto selected = type(value);
        if (!selected)
          return selected.takeError();
        proof.selectedConstruction = std::move(*selected);
      }
    } else
      return fail(choice, "unknown proof choice", "source.entry");
  }
  for (StringRef required :
       {"prover", "verifier", "public", "accept", "construction"})
    if (!choices.count(required.str()))
      return fail(id, "missing proof choice", "source.entry");
  if (auto error = work.count(work.declarations, work.limits.declarations,
                              "declaration count", result.span))
    return error;
  result.proof = std::move(proof);
  parent.members.push_back(std::move(result));
  return Error::success();
}
} // namespace zkc::language::detail
