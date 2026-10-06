#include "ArtifactJson.h"
#include "Run.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include <map>
#include <set>
using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
using Coordinate = std::pair<std::string, std::string>;
// This reader visits the retained mathematical body, never the projection's
// action list or Schedule's output model. Prior edge checks establish operand
// correspondence; here we establish the published source order and coordinates.
class RunCorrespondence {
  struct Role {
    const source::Participant *program;
    std::vector<const source::Instruction *> code;
    size_t position = 0;
  };
  struct Cursor {
    const json::Array &steps;
    size_t position = 0;
    const json::Object *next() {
      return position < steps.size() ? steps[position++].getAsObject()
                                     : nullptr;
    }
    bool done() const { return position == steps.size(); }
  };
  std::vector<Role> roles;
  std::map<std::string, unsigned> roleIndex;
  std::map<Coordinate, std::string> calculations;
  std::set<Coordinate> guards;
  size_t anchor = 0, remaining = 1000000;
  bool charge() { return remaining && (--remaining, true); }
  const source::Instruction *next(unsigned role) const {
    const auto &r = roles[role];
    return r.position < r.code.size() ? r.code[r.position] : nullptr;
  }
  bool step(Cursor &cursor, unsigned role, std::optional<size_t> source) {
    auto *record = cursor.next();
    if (!charge() || !record || record->size() != 3 ||
        record->getInteger("role") != role ||
        record->getInteger("instruction") != int64_t(roles[role].position))
      return false;
    auto *value = record->get("anchor");
    if (!value ||
        (source ? value->getAsUINT64() != *source : !value->getAsNull()))
      return false;
    ++roles[role].position;
    return true;
  }
  bool prefix(Cursor &cursor, unsigned role, std::optional<size_t> source) {
    auto *instruction = next(role);
    if (!instruction)
      return false;
    Coordinate key{roles[role].program->name, instruction->site};
    auto found = calculations.find(key);
    if (found == calculations.end() || guards.count(key))
      return true;
    auto *call = instruction->get<source::LocalCall>();
    if (!call || call->callee != found->second)
      return false;
    calculations.erase(found);
    return step(cursor, role, source);
  }
  std::optional<unsigned> index(StringRef role) const {
    auto found = roleIndex.find(role.str());
    return found == roleIndex.end() ? std::nullopt
                                    : std::optional<unsigned>(found->second);
  }
  bool action(Cursor &cursor, Operation &op, StringRef name, size_t source,
              bool receive = false) {
    auto role = index(name);
    if (!role || (!receive && !prefix(cursor, *role, source)))
      return false;
    const auto *instruction = next(*role);
    if (!instruction ||
        instruction->site != op.getAttrOfType<StringAttr>("site").getValue())
      return false;
    bool matches = false;
    if (auto exchange = dyn_cast<pir::ExchangeOp>(op)) {
      if (receive) {
        auto *r = instruction->get<source::Receive>();
        matches = r && r->peer == exchange.getSender() &&
                  r->schema == exchange.getSite();
      } else {
        auto *r = instruction->get<source::Send>();
        matches = r && r->peer == exchange.getReceiver() &&
                  r->schema == exchange.getSite();
      }
    } else if (auto query = dyn_cast<pir::QueryOp>(op)) {
      auto *r = instruction->get<source::ServiceQuery>();
      matches = r && r->method == query.getMethod();
    } else if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
      auto *r = instruction->get<source::LocalCall>();
      matches = r && r->callee == call.getCallee();
    } else if (isa<pir::FinishIfOp>(op)) {
      matches = instruction->get<source::ReturnIf>();
    } else if (isa<pir::GuardOp>(op)) {
      Coordinate key{roles[*role].program->name, instruction->site};
      auto found = calculations.find(key);
      auto *r = instruction->get<source::LocalCall>();
      matches = r && found != calculations.end() && r->callee == found->second;
      if (matches)
        calculations.erase(found);
    }
    return matches && step(cursor, *role, source);
  }
  bool body(Block &block, Cursor &cursor, unsigned depth) {
    if (depth > 64)
      return false;
    for (auto &op : block) {
      if (!charge())
        return false;
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        size_t source = anchor++;
        auto *group = cursor.next();
        if (!group || group->size() != 3 || !group->getArray("loop") ||
            !group->getArray("body") || !group->getArray("yield"))
          return false;
        Cursor enter{*group->getArray("loop")};
        SmallVector<unsigned> owners;
        for (auto owner : repeat.getRoles()) {
          auto role = index(cast<StringAttr>(owner).getValue());
          if (!role || !prefix(enter, *role, source))
            return false;
          auto *instruction = next(*role);
          auto *loop = instruction ? instruction->get<source::Loop>() : nullptr;
          if (!loop || instruction->site != repeat.getSite() ||
              loop->count.kind != source::LoopCount::Kind::Value ||
              loop->count.maximum != repeat.getMaximum() ||
              !step(enter, *role, source))
            return false;
          owners.push_back(*role);
        }
        Cursor inner{*group->getArray("body")};
        if (!enter.done() ||
            !body(repeat.getBody().front(), inner, depth + 1) || !inner.done())
          return false;
        Cursor exit{*group->getArray("yield")};
        for (auto role : owners) {
          if (!prefix(exit, role, std::nullopt))
            return false;
          auto *instruction = next(role);
          if (!instruction || !instruction->get<source::Yield>() ||
              !step(exit, role, std::nullopt))
            return false;
        }
        if (!exit.done())
          return false;
      } else if (auto exchange = dyn_cast<pir::ExchangeOp>(op)) {
        size_t source = anchor++;
        if (!action(cursor, op, exchange.getSender(), source) ||
            !action(cursor, op, exchange.getReceiver(), source, true))
          return false;
      } else if (auto query = dyn_cast<pir::QueryOp>(op)) {
        if (!action(cursor, op, query.getOwner(), anchor++))
          return false;
      } else if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
        if (!action(cursor, op, call.getRole(), anchor++))
          return false;
      } else if (auto guard = dyn_cast<pir::GuardOp>(op)) {
        if (!action(cursor, op, guard.getOwner(), anchor++))
          return false;
      } else if (auto finish = dyn_cast<pir::FinishIfOp>(op)) {
        if (!action(cursor, op, finish.getOwner(), anchor++))
          return false;
      }
      // The prepared profile admits only total expressions, statements and
      // terminators outside the ordered action classes above.
    }
    return true;
  }

public:
  bool check(pir::MathematicalOp source, pir::ProjectionOp projection,
             const source::Participants &program, const json::Object &bundle) {
    auto *names = bundle.getArray("roles");
    auto *steps = bundle.getArray("steps");
    if (!names || !steps || names->size() != source.getRoles().size())
      return false;
    const source::ParticipantEntry *entry = nullptr;
    for (const auto &e : program.entries)
      if (e.name == source.getSymName())
        entry = &e;
    if (!entry || entry->participants.size() != names->size())
      return false;
    for (auto [i, owner] : enumerate(source.getRoles())) {
      auto name = cast<StringAttr>(owner).getValue();
      if ((*names)[i].getAsString() != name ||
          !roleIndex.emplace(name.str(), i).second)
        return false;
      const source::Participant *participant = nullptr;
      for (const auto &mapping : entry->participants)
        if (mapping.first == name)
          for (const auto &p : program.participants)
            if (p.name == mapping.second)
              participant = &p;
      if (!participant || participant->role != name ||
          participant->instance != source.getSymName())
        return false;
      Role role{participant, {}, 0};
      source::walk(participant->body, [&](const source::Instruction &op) {
        role.code.push_back(&op);
      });
      roles.push_back(std::move(role));
    }
    for (auto item : projection.getCalculations()) {
      auto row = cast<DictionaryAttr>(item);
      auto name = row.getAs<FlatSymbolRefAttr>("participant").getValue();
      if (any_of(roles, [&](const Role &r) { return r.program->name == name; }))
        if (!calculations
                 .emplace(
                     Coordinate{name.str(),
                                row.getAs<StringAttr>("site").str()},
                     row.getAs<FlatSymbolRefAttr>("callee").getValue().str())
                 .second)
          return false;
    }
    source.walk([&](pir::GuardOp guard) {
      auto role = index(guard.getOwner());
      if (role)
        guards.emplace(roles[*role].program->name, guard.getSite().str());
    });
    Cursor cursor{*steps};
    if (!body(source.getBody().front(), cursor, 0))
      return false;
    for (unsigned i = 0; i < roles.size(); ++i) {
      if (!prefix(cursor, i, std::nullopt))
        return false;
      auto *instruction = next(i);
      if (!instruction || !instruction->get<source::Return>() ||
          !step(cursor, i, std::nullopt) ||
          roles[i].position != roles[i].code.size())
        return false;
    }
    return cursor.done() && calculations.empty();
  }
  bool exhausted() const { return !remaining; }
};
} // namespace
Error verifyRunBundle(ModuleOp prepared, ModuleOp physical, StringRef bytes,
                      StringRef entry) {
  if (!prepared || failed(verify(prepared)) || !physical ||
      failed(verify(physical)))
    return error("run-correspondence-subject");
  auto parsed = parseArtifactJson(bytes);
  if (!parsed)
    return parsed.takeError();
  auto *bundle = parsed->getAsObject();
  if (!bundle || bundle->size() != 5 ||
      bundle->getString("format") != "zkc.run/1" ||
      bundle->getString("entry") != entry || !bundle->getString("candidate"))
    return error("run-correspondence");
  auto candidate = *bundle->getString("candidate");
  if (auto e = protocol::verifyProgramArtifact(physical, candidate))
    return e;
  auto carrier = parseJson(candidate);
  if (!carrier)
    return carrier.takeError();
  auto decoded = source::decode(*carrier);
  if (!decoded)
    return decoded.takeError();
  auto *program = std::get_if<source::Participants>(&*decoded);
  pir::MathematicalOp source;
  prepared.walk([&](pir::MathematicalOp op) {
    if (op.getSymName() == entry)
      source = op;
  });
  pir::ProjectionOp projection;
  physical.walk([&](pir::ProjectionOp op) { projection = op; });
  if (!source || !projection || !program)
    return error("run-correspondence-subject");
  RunCorrespondence check;
  if (!check.check(source, projection, *program, *bundle))
    return error(check.exhausted() ? "run-correspondence-limit"
                                   : "run-correspondence");
  return Error::success();
}
} // namespace zkc::detail
