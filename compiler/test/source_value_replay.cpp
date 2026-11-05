#include "../lib/Language/ScopedWitness.h"
#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
#include <algorithm>
#include <functional>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject check(StringRef text) {
  auto captured = take(
      capture({{"sample", ("module sample;" + text).str(), "values.zkc"}}));
  return take(analyze(captured).checkedProject());
}
Body &body(const CheckedProject &project) {
  for (const auto &declaration : project.declarations())
    if (declaration.name == "Run" && declaration.body)
      return const_cast<Body &>(*declaration.body);
  throw std::runtime_error("missing Run body");
}
HostInvocation runInvocation(const CheckedProject &project) {
  for (const auto &declaration : project.declarations())
    if (declaration.name == "Run")
      return {HostInvocation::Kind::Run, declaration.id, {}, {}};
  throw std::runtime_error("missing Run protocol");
}
void specialized(const ClosedEntry &entry) {
  if (auto error = checkScopedSpecialization(entry))
    throw std::runtime_error(toString(std::move(error)));
}
void witnessRefusal(Error error) {
  require(bool(error), "mutated literal passed closed replay");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, "source.binding-witness"), message);
}
std::string recipeSource(bool mutableCount = false, bool nested = false) {
  std::string text = R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
fn ignore(rows:domain<index>,value:bool)->bool{return value;}
protocol Run roles(P,Q,R)(x:bool@P,n:index@(P,Q,R),other:index@(P,Q,R))->(r:bool@P){
)";
  text += mutableCount
              ? "let mut count@(P,Q,R)=n;let rows=range(0,count);count=3;"
              : "let rows=range(0,n);";
  text += "let mut result@P=x;";
  if (nested)
    text += "for _ in 0..n roles(P,Q) max 4{";
  text += "for _ in 0..n roles(P) max 4{result=ignore(rows,result);}";
  if (nested)
    text += "}";
  return text + "return result;}";
}
void replay(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
void rejects(const CheckedProject &project, StringRef earlierRefusal = {}) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "mutated source values passed replay");
  auto message = toString(std::move(error));
  require(
      namesIdentifier(message, "source.binding-witness") ||
          namesIdentifier(message, "source.scoped-witness") ||
          (!earlierRefusal.empty() && namesIdentifier(message, earlierRefusal)),
      message);
}
std::string stateSource(unsigned kind, StringRef result = "()") {
  const bool protocol = kind % 2, branch = kind >= 2;
  std::string text = protocol ? "protocol Run roles(P)(go:bool@P,n:index@P,"
                                "a:bool@P,b:bool@P)->(r:bool@P){"
                              : "fn Run(go:bool,n:index,a:bool,b:bool)->bool{";
  text += "let mut s=a;s=b;";
  text +=
      branch ? ("let _=if go{s=true;" + result + "}else{" + result + "};").str()
      : protocol ? "for _ in 0..n roles(P) max 8{s=true;}"
                 : "for _ in 0..n{s=true;}";
  return text + "return s;}";
}
Operation &control(Body &root) {
  auto found = llvm::find_if(root.operations, [](const auto &operation) {
    return std::holds_alternative<Control>(operation.action) ||
           std::holds_alternative<ProtocolRepeat>(operation.action);
  });
  require(found != root.operations.end(), "missing control");
  return *found;
}
// Insert aliases before the final recipe restriction, retaining its eager root.
// An optional proper-subset restriction exercises composition with aliases.
std::vector<ValueId> recipeIdentityChain(Body &root, unsigned length,
                                         bool restrictFirst = false) {
  auto &repeat = std::get<ProtocolRepeat>(control(root).action);
  auto result = repeat.captures.back();
  auto at = llvm::find_if(root.operations, [&](const auto &op) {
    return op.results.size() == 1 && op.results.front().index == result.index;
  });
  require(at != root.operations.end(), "missing recipe restriction");
  auto &restriction = std::get<Restriction>(at->action);
  auto input = restriction.input;
  const auto position = at - root.operations.begin();
  const auto span = at->span;
  auto value = root.values[input.index];
  std::vector<Operation> operations;
  if (restrictFirst) {
    value.components = {0, 1};
    value.placement = DataPlacement{{0, 1}};
    auto restricted = ValueId{uint32_t(root.values.size())};
    root.values.push_back(value);
    operations.push_back(
        Operation{Restriction{input, {0, 1}}, {restricted}, span, 0});
    input = restricted;
  }
  std::vector<ValueId> aliases;
  for (unsigned i = 0; i < length; ++i) {
    auto alias = ValueId{uint32_t(root.values.size())};
    root.values.push_back(value);
    operations.push_back(Operation{Projection{input, {}}, {alias}, span, 0});
    aliases.push_back(alias);
    input = alias;
  }
  restriction.input = input;
  root.operations.insert(root.operations.begin() + position, operations.begin(),
                         operations.end());
  return aliases;
}
} // namespace
int main() {
  Cases cases;
  for (bool local : {false, true})
    for (StringRef type : {"bool", "index", "Fr", "F"}) {
      std::vector<StringRef> mutations = {"static", "parameters"};
      if (local)
        mutations.insert(mutations.end(), {"binding", "asset", "origin"});
      for (auto mutation : mutations)
        cases.run(
            "complete literal envelope " + Twine(local) + "/" + type + "/" +
                mutation,
            [&] {
              const auto payload = type == "bool" ? "true" : "1";
              auto project = check(("domain Fr=field(\"koala-bear\");" +
                                    std::string(local ? "fn" : "math fn") +
                                    " Run" + (type == "F" ? "<F:Field>" : "") +
                                    "()->" + type + "{return " + payload + ";}")
                                       .str());
              replay(project);
              auto &root = body(project);
              auto at = llvm::find_if(root.operations, [&](const auto &op) {
                return local ? std::holds_alternative<LocalPrimitive>(op.action)
                             : std::holds_alternative<MathValue>(op.action);
              });
              require(at != root.operations.end(), "missing literal");
              auto saved = at->action;
              Type nine(Type::Kind::Natural);
              nine.dimension = Natural::constant(9);
              if (local) {
                auto &constant = std::get<LocalPrimitive>(at->action);
                if (mutation == "static")
                  constant.staticArguments = {nine};
                else if (mutation == "parameters")
                  constant.parameters.push_back("9");
                else if (mutation == "binding")
                  constant.bindingArguments.emplace();
                else if (mutation == "asset")
                  constant.assetReferences.push_back({0, nine});
                else
                  constant.origin = LocalPrimitive::Origin::Kernel;
              } else {
                auto &constant = std::get<MathValue>(at->action);
                if (mutation == "static")
                  constant.staticArguments = {nine};
                else
                  constant.parameters = {"9"};
              }
              rejects(project);
              at->action = std::move(saved);
              replay(project);
            });
    }
  for (bool local : {false, true})
    for (StringRef type : {"bool", "index", "Fr", "F"})
      cases.run(
          "literal original mutant restored closure " + Twine(local) + "/" +
              type,
          [&] {
            const auto payload = type == "bool" ? "true" : "3";
            const auto literal = type == "F" ? "1" : payload;
            auto project =
                check(("domain Fr=field(\"koala-bear\");" +
                       std::string(local ? "fn" : "math fn") + " number" +
                       (type == "F" ? "<F:Field>" : "") + "()->" + type +
                       "{return " + literal + ";}protocol Run roles(P)()->(r:" +
                       (type == "F" ? "Fr" : type) + "@P){return number" +
                       (type == "F" ? "<Fr>" : "") + "();}")
                          .str());
            replay(project);
            auto invocation = runInvocation(project);
            auto original = take(closeInvocation(project, invocation));
            specialized(original);
            auto checkPayload = [&](const ClosedEntry &entry) {
              bool found = false;
              for (const auto &decl : entry.declarations())
                if (decl.body)
                  for (const auto &op : decl.body->operations) {
                    if (local) {
                      if (const auto *p =
                              std::get_if<LocalPrimitive>(&op.action)) {
                        require(p->parameters ==
                                    std::vector<std::string>{literal},
                                "closed Local payload changed");
                        found = true;
                      }
                    } else if (const auto *p =
                                   std::get_if<MathValue>(&op.action)) {
                      require(p->literal == literal,
                              "closed Math payload changed");
                      found = true;
                    }
                  }
              require(found, "missing closed literal");
            };
            checkPayload(original);
            Operation *producer = nullptr;
            for (const auto &decl : project.declarations())
              if (decl.name == "number" && decl.body)
                for (const auto &op : decl.body->operations)
                  if ((local &&
                       std::holds_alternative<LocalPrimitive>(op.action)) ||
                      (!local && std::holds_alternative<MathValue>(op.action)))
                    producer = &const_cast<Operation &>(op);
            require(producer, "missing authored literal");
            auto saved = producer->action;
            Type nine(Type::Kind::Natural);
            nine.dimension = Natural::constant(9);
            if (local)
              std::get<LocalPrimitive>(producer->action).staticArguments = {
                  nine};
            else
              std::get<MathValue>(producer->action).staticArguments = {nine};
            rejects(project);
            auto mutant = closeInvocation(project, invocation);
            require(!mutant, "mutated literal closed successfully");
            witnessRefusal(mutant.takeError());
            witnessRefusal(checkScopedSpecialization(original));
            producer->action = std::move(saved);
            replay(project);
            specialized(original);
            auto restored = take(closeInvocation(project, invocation));
            specialized(restored);
            checkPayload(restored);
          });
  for (bool local : {false, true})
    cases.run(
        "authored natural index static remains supported " + Twine(local), [&] {
          auto project = check(
              (std::string(local ? "fn" : "math fn") +
               " number<N:nat>()->index{return index<N>();}"
               "protocol Run roles(P)()->(r:index@P){return number<9>();}"));
          replay(project);
          auto closed = take(closeInvocation(project, runInvocation(project)));
          specialized(closed);
        });
  for (StringRef type : {"bool", "index", "Fr"})
    for (bool parameters : {false, true})
      cases.run(
          "protocol literal envelope " + type + "/" + Twine(parameters), [&] {
            auto project = check(("domain Fr=field(\"koala-bear\");"
                                  "protocol Run roles(P,Q)()->(r:" +
                                  type + "@(P,Q)){return " +
                                  (type == "bool" ? "true" : "3") + ";}")
                                     .str());
            replay(project);
            auto &root = body(project);
            auto at = llvm::find_if(root.operations, [](const auto &op) {
              return std::holds_alternative<MathValue>(op.action);
            });
            require(at != root.operations.end(), "missing protocol literal");
            auto &constant = std::get<MathValue>(at->action);
            Type nine(Type::Kind::Natural);
            nine.dimension = Natural::constant(9);
            if (parameters)
              constant.parameters = {"9"};
            else
              constant.staticArguments = {nine};
            rejects(project);
          });
  for (unsigned kind = 0; kind != 4; ++kind)
    for (bool moved : {false, true})
      cases.run("source ordered incoming state " + Twine(kind) + "/" +
                    Twine(moved),
                [&] {
                  auto project = check(stateSource(kind));
                  replay(project);
                  auto &root = body(project);
                  std::optional<ValueId> first, assigned;
                  unsigned assignment = 0;
                  for (unsigned i = 0; i < root.operations.size(); ++i) {
                    auto &op = root.operations[i];
                    auto *p = std::get_if<Projection>(&op.action);
                    if (!p || !p->path.empty())
                      continue;
                    if (p->input.index == 2 && !first)
                      first = op.results.front();
                    if (p->input.index == 3 && !assigned) {
                      assigned = op.results.front();
                      assignment = i;
                    }
                  }
                  auto &op = control(root);
                  unsigned selected = &op - root.operations.data();
                  require(first && assigned && assignment < selected,
                          "missing assignment generations");
                  if (auto *c = std::get_if<Control>(&op.action))
                    for (auto &operand : c->operands)
                      if (operand.index == assigned->index)
                        operand = *first;
                  if (auto *c = std::get_if<ProtocolRepeat>(&op.action))
                    for (auto *list : {&c->carried, &c->captures})
                      for (auto &operand : *list)
                        if (operand.index == assigned->index)
                          operand = *first;
                  if (moved) {
                    auto assignmentOp = std::move(root.operations[assignment]);
                    root.operations.erase(root.operations.begin() + assignment);
                    root.operations.insert(root.operations.begin() + selected,
                                           std::move(assignmentOp));
                  }
                  rejects(project);
                });
  for (bool protocol : {false, true})
    for (StringRef mutation : {"arity", "field", "non-tuple", "projection"})
      cases.run("typed explicit and state carrier " + Twine(protocol) + "/" +
                    mutation,
                [&] {
                  auto project = check(stateSource(2 + protocol, "a"));
                  replay(project);
                  auto &root = body(project);
                  auto &op = control(root);
                  auto &selected = std::get<Control>(op.action);
                  if (mutation == "projection") {
                    auto result = root.expressionValues.at(*op.expression);
                    root.values[result.index].type = Type(Type::Kind::Index);
                  } else {
                    Type type(Type::Kind::Tuple);
                    type.arguments = {Type{}};
                    if (mutation == "field")
                      type.arguments.push_back(Type(Type::Kind::Index));
                    if (mutation == "non-tuple")
                      type = Type{};
                    root.values[op.results.front().index].type = type;
                    for (auto &region : selected.regions) {
                      auto &arm = const_cast<Body &>(*region);
                      arm.values[arm.results.front().index].type = type;
                    }
                  }
                  rejects(project);
                });
  for (bool protocol : {false, true})
    cases.run(
        "unused incoming state retains its source binding " + Twine(protocol),
        [&] {
          std::string source =
              protocol ? "protocol Run "
                         "roles(P)(go:bool@P,a:bool@P,b:bool@P)->(r:bool@P){"
                       : "fn Run(go:bool,a:bool,b:bool)->bool{";
          source += "let mut s=a;let t=b;let _=if "
                    "go{s=true;()}else{s=false;()};return s;}";
          auto project = check(source);
          replay(project);
          auto &root = body(project);
          std::optional<ValueId> replacement;
          for (const auto &op : root.operations)
            if (const auto *p = std::get_if<Projection>(&op.action);
                p && p->path.empty() && p->input.index == 2)
              replacement = op.results.front();
          require(bool(replacement), "missing other binding");
          auto &selected = std::get<Control>(control(root).action);
          require(selected.operands.size() == 2, "wrong initial state fixture");
          selected.operands[1] = *replacement;
          rejects(project);
        });
  for (StringRef source :
       {"fn Run(n:index)->index{for _ in 0..n{}return n;}",
        "fn Run(n:index)->index{for _ in n..8{}return n;}",
        "protocol Run roles(P)(n:index@P)->(r:index@P){for _ in 0..3 "
        "roles(P) max 8{}return n;}",
        "fn Run()->index{let unused:index=3;return 5;}",
        "math fn Run()->index{return 3;}",
        "math fn Run<F:Field>()->F{return 1;}",
        "domain Fr=field(\"bls12-381.fr\");math fn Run()->Fr{return 3;}",
        "fn apply(f:fn()->index)->index{return f();}fn Run()->index{"
        "return apply(fn()=>3);}"})
    for (StringRef mutation : {"payload", "erase-map", "payload-no-hint"})
      cases.run("authored numeric literal " + source + "/" + mutation, [&] {
        auto project = check(source);
        replay(project);
        bool changed = false;
        std::function<void(Body &)> mutate = [&](Body &root) {
          for (auto &op : root.operations) {
            if (changed)
              break;
            auto *local = std::get_if<LocalPrimitive>(&op.action);
            auto *math = std::get_if<MathValue>(&op.action);
            if ((local && (local->contract == "index.constant" ||
                           local->contract == "field.constant")) ||
                (math &&
                 (math->identity == zkc::MathematicalIdentity::IndexConstant ||
                  math->identity ==
                      zkc::MathematicalIdentity::FieldConstant))) {
              if (mutation == "erase-map") {
                for (auto it = root.expressionValues.begin();
                     it != root.expressionValues.end();)
                  if (it->second.index == op.results.front().index)
                    it = root.expressionValues.erase(it);
                  else
                    ++it;
              } else if (local)
                local->parameters.front() = "4";
              else
                math->literal = "4";
              if (mutation != "payload")
                op.expression.reset();
              changed = true;
            }
          }
          for (auto &binding : root.scopedBindings)
            if (binding.computation)
              mutate(const_cast<Body &>(*binding.computation->body));
        };
        mutate(body(project));
        require(changed, "missing numeric constant");
        rejects(project);
      });
  for (bool protocol : {false, true})
    for (StringRef mutation :
         {"arity", "field", "non-tuple", "identity-cycle", "pack-cycle"})
      cases.run(
          "typed state-only tuple " + Twine(protocol) + "/" + mutation, [&] {
            std::string source =
                protocol
                    ? "protocol Run roles(P)(go:bool@P,a:bool@P)->(r:bool@P){"
                    : "fn Run(go:bool,a:bool)->bool{";
            source += "let mut s=a;let mut t=a;let _=if go{"
                      "s=true;t=false;()}else{()};return s;}";
            auto project = check(source);
            replay(project);
            auto &root = body(project);
            auto &op = control(root);
            auto &selected = std::get<Control>(op.action);
            if (mutation == "pack-cycle") {
              auto &arm = const_cast<Body &>(*selected.regions.front());
              auto found =
                  llvm::find_if(arm.operations, [&](const auto &candidate) {
                    return candidate.results.size() == 1 &&
                           candidate.results.front().index ==
                               arm.results.front().index;
                  });
              require(found != arm.operations.end(), "missing state pack");
              std::get<Construct>(found->action).operands.back() =
                  arm.results.front();
            } else if (mutation == "identity-cycle") {
              auto &arm = const_cast<Body &>(*selected.regions.front());
              auto result = ValueId{uint32_t(arm.values.size())};
              arm.values.push_back(arm.values[arm.results.front().index]);
              Operation identity{Projection{result, {}}, {result}, op.span, 0};
              arm.operations.push_back(std::move(identity));
              arm.results.front() = result;
            } else {
              Type type(Type::Kind::Tuple);
              type.arguments = {Type{}};
              if (mutation == "field")
                type.arguments.push_back(Type(Type::Kind::Index));
              if (mutation == "non-tuple")
                type = Type{};
              root.values[op.results.front().index].type = type;
              for (auto &region : selected.regions) {
                auto &arm = const_cast<Body &>(*region);
                arm.values[arm.results.front().index].type = type;
              }
            }
            rejects(project);
          });
  for (StringRef source :
       {"fn Run()->(index,index){return (1,2);}",
        "fn Run()->index{return 0003;}",
        "math fn Run()->index{return 18446744073709551615;}",
        "fn Run(go:bool)->((),()){let mut s=();let mut t=();let _=if "
        "go{s=();t=();()}else{()};return (s,t);}",
        "fn Run(go:bool,n:index,a:bool,b:bool)->bool{let mut s=a;s=b;"
        "for _ in {s=a;0}..{s=b;n}{let _=if go{s=a;()}else{()};}return s;}",
        "#[affine] struct Token{}fn Run(go:bool,t:Token)->bool{let mut s=t;"
        "consume s;let _=if go{s=Token{};()}else{s=Token{};()};consume s;"
        "return true;}",
        "#[affine] struct Token{}fn Run(go:bool,t:Token)->bool{let mut s=t;"
        "let _=if go{s=Token{};consume s;()}else{s=Token{};()};return true;}",
        "fn apply(f:fn()->bool,b:bool)->bool{return f();}fn Run()->bool{"
        "let mut s=false;return apply(fn()=>s,{s=true;true});}"})
    cases.run("authentic source events and carriers " + source,
              [&] { replay(check(source)); });
  cases.run("independent administrative operations can reorder", [&] {
    auto project = check("fn Run()->(index,index){return (1,2);}");
    replay(project);
    auto &root = body(project);
    require(root.operations.size() >= 3, "missing independent constants");
    std::swap(root.operations[0], root.operations[1]);
    replay(project);
  });
  cases.run("typed state packs retain identity chains", [&] {
    auto project = check(stateSource(2, "a"));
    replay(project);
    auto &op = control(body(project));
    for (auto &region : std::get<Control>(op.action).regions) {
      auto &arm = const_cast<Body &>(*region);
      for (unsigned i = 0; i != 3; ++i) {
        auto result = ValueId{uint32_t(arm.values.size())};
        arm.values.push_back(arm.values[arm.results.front().index]);
        Operation identity{
            Projection{arm.results.front(), {}}, {result}, op.span, 0};
        arm.operations.push_back(std::move(identity));
        arm.results.front() = result;
      }
    }
    replay(project);
  });
  for (StringRef payload : {"04", "18446744073709551616"})
    cases.run("candidate index payload must be canonical " + payload, [&] {
      auto project = check("fn Run()->index{return 4;}");
      replay(project);
      auto &root = body(project);
      auto &constant = std::get<LocalPrimitive>(root.operations.front().action);
      constant.parameters = {payload.str()};
      rejects(project);
    });
  cases.run("resolved literal type cannot follow candidate type", [&] {
    auto project = check("domain Fr=field(\"bls12-381.fr\");"
                         "math fn Run()->Fr{return 1;}");
    replay(project);
    auto &root = body(project);
    auto &op = root.operations.front();
    root.values[op.results.front().index].type = Type(Type::Kind::Index);
    std::get<MathValue>(op.action).identity =
        zkc::MathematicalIdentity::IndexConstant;
    rejects(project);
  });
  cases.run("resolved numeric literal retains its exact field carrier", [&] {
    auto project = check("domain Fr=field(\"bls12-381.fr\");"
                         "domain Other=field(\"koala-bear\");"
                         "math fn Run(a:Other)->Fr{return 1;}");
    replay(project);
    auto &root = body(project);
    root.values[root.operations.front().results.front().index].type =
        root.values.front().type;
    rejects(project);
  });
  cases.run("Unit administrative carriers retain their zero arity", [&] {
    auto project = check("fn Run(go:bool)->(){return if go{()}else{()};}");
    replay(project);
    auto &root = body(project);
    auto &selected = control(root);
    Type malformed(Type::Kind::Unit);
    malformed.arguments.push_back(Type{});
    root.values[selected.results.front().index].type = malformed;
    for (auto &region : std::get<Control>(selected.action).regions) {
      auto &arm = const_cast<Body &>(*region);
      arm.values[arm.results.front().index].type = malformed;
    }
    rejects(project);
  });
  for (StringRef source :
       {"fn Run()->index{return 3;}", "math fn Run<F:Field>()->F{return 1;}",
        "protocol Run roles(P)()->(r:index@P){return 3;}"})
    cases.run("numeric producer hint remains optional " + source, [&] {
      auto project = check(source);
      replay(project);
      for (auto &op : body(project).operations)
        op.expression.reset();
      replay(project);
    });
  cases.run("unused numeric producer cannot disappear with its map", [&] {
    auto project = check("fn Run(a:bool)->bool{let _:index=3;return a;}");
    replay(project);
    auto &root = body(project);
    require(root.operations.size() == 1, "missing isolated unused literal");
    auto result = root.operations.front().results.front();
    root.operations.clear();
    for (auto it = root.expressionValues.begin();
         it != root.expressionValues.end();)
      if (it->second.index == result.index)
        it = root.expressionValues.erase(it);
      else
        ++it;
    rejects(project);
  });
  for (bool protocol : {false, true})
    cases.run(
        "an unused state join still belongs to its source " + Twine(protocol),
        [&] {
          auto text = stateSource(2 + protocol);
          text.replace(text.rfind("return s;"), 9, "return a;");
          auto project = check(text);
          replay(project);
          auto &root = body(project);
          auto &selected = control(root);
          root.values[selected.results.front().index].type =
              Type(Type::Kind::Unit);
          for (auto &region : std::get<Control>(selected.action).regions) {
            auto &arm = const_cast<Body &>(*region);
            auto empty = llvm::find_if(arm.operations, [](const auto &op) {
              const auto *pack = std::get_if<Construct>(&op.action);
              return pack && pack->kind == Construct::Kind::Aggregate &&
                     pack->operands.empty();
            });
            require(empty != arm.operations.end(), "missing arm Unit");
            arm.results.front() = empty->results.front();
          }
          rejects(project);
        });
  for (StringRef text :
       {"math fn Run()->index{return 18446744073709551616;}",
        "domain Fr=field(\"bls12-381.fr\");math fn Run()->Fr{return 03;}",
        "domain Fr=field(\"bls12-381.fr\");math fn Run()->Fr{return "
        "999999999999999999999999999999999999999999999999999999999999999999"
        "999999999999999999999999999999999999999999999999999999999999;}",
        "math fn Run<F:Field>()->F{return 3;}"})
    cases.run("ordinary formation refuses invalid numeric source " + text, [&] {
      auto captured = take(capture(
          {{"sample", ("module sample;" + text).str(), "literal.zkc"}}));
      refuses(analyze(captured).checkedProject(), "source.literal");
    });
  for (unsigned mutation = 0; mutation != 3; ++mutation)
    cases.run("recipe snapshots retain resolved eager operands " +
                  Twine(mutation),
              [&] {
                auto project = check(R"(
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn ignore(rows:domain<Fr>,value:Fr)->Fr{return value;}
protocol Run roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,x:Fr@P,n:index@P)->(r:Fr@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P) max 4{result=ignore(rows,result);}
 return result;
})");
                replay(project);
                auto &root = body(project);
                auto &repeat = std::get<ProtocolRepeat>(control(root).action);
                require(repeat.captures.size() == 1 &&
                            repeat.captures.back().index == 0,
                        "missing isolated recipe capture");
                if (mutation == 0)
                  repeat.captures.back() = ValueId{1};
                else if (mutation == 1)
                  repeat.captures.clear();
                else
                  repeat.captures.push_back(ValueId{1});
                rejects(project, mutation ? "source.scoped-domain" : "");
              });
  for (bool mutated : {false, true})
    cases.run("recipe snapshots preserve earlier generations and constants " +
                  Twine(mutated),
              [&] {
                auto project = check(R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
fn ignore(rows:domain<index>,value:bool)->bool{return value;}
protocol Run roles(P)(x:bool@P,n:index@P)->(r:bool@P){
 let mut count@P=n;let rows=range(0,count);count=3;
 let mut result@P=x;
 for _ in 0..count roles(P) max 4{result=ignore(rows,result);}
 return result;
})");
                replay(project);
                if (mutated) {
                  auto &repeat =
                      std::get<ProtocolRepeat>(control(body(project)).action);
                  require(repeat.captures.size() == 2,
                          "missing range recipe operands");
                  repeat.captures.back() = repeat.count;
                  rejects(project);
                }
              });
  cases.run("resolved recipe references allow typed identity chains", [&] {
    auto project = check(R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
fn ignore(rows:domain<index>,value:bool)->bool{return value;}
protocol Run roles(P)(x:bool@P,n:index@P)->(r:bool@P){
 let rows=range(0,n);let mut result@P=x;
 for _ in 0..n roles(P) max 4{result=ignore(rows,result);}
 return result;
})");
    replay(project);
    auto &root = body(project);
    auto &selected = control(root);
    auto &repeat = std::get<ProtocolRepeat>(selected.action);
    require(repeat.captures.size() == 2, "missing recipe operands");
    auto input = repeat.captures.front();
    auto result = ValueId{uint32_t(root.values.size())};
    root.values.push_back(root.values[input.index]);
    repeat.captures.front() = result;
    Operation identity{Projection{input, {}}, {result}, selected.span, 0};
    auto at = &selected - root.operations.data();
    root.operations.insert(root.operations.begin() + at, std::move(identity));
    replay(project);
  });
  for (bool mutableCount : {false, true})
    for (bool nested : {false, true})
      cases.run("proper subset eager recipes " + Twine(mutableCount) + "/" +
                    Twine(nested),
                [&] {
                  auto project = check(recipeSource(mutableCount, nested));
                  replay(project);
                  auto closed =
                      take(closeInvocation(project, runInvocation(project)));
                  specialized(closed);
                });
  for (StringRef mutation :
       {"wrong-source", "missing", "extra", "type", "roles", "participants",
        "placement", "holder", "cycle", "forward", "generation"})
    cases.run("restricted eager recipe refuses " + mutation, [&] {
      auto project = check(recipeSource(mutation == "generation"));
      replay(project);
      auto &root = body(project);
      auto &repeat = std::get<ProtocolRepeat>(control(root).action);
      require(repeat.captures.size() == 2,
              "missing restricted recipe operands");
      auto result = repeat.captures.back();
      auto at = llvm::find_if(root.operations, [&](const auto &op) {
        return op.results.size() == 1 &&
               op.results.front().index == result.index;
      });
      require(at != root.operations.end(), "missing recipe restriction");
      auto &restriction = std::get<Restriction>(at->action);
      auto saved = restriction;
      auto savedValue = root.values[result.index];
      auto captures = repeat.captures;
      if (mutation == "wrong-source")
        restriction.input = ValueId{2};
      else if (mutation == "missing")
        repeat.captures.pop_back();
      else if (mutation == "extra")
        repeat.captures.push_back(result);
      else if (mutation == "type")
        root.values[result.index].type = Type{};
      else if (mutation == "roles" || mutation == "participants") {
        restriction.roles = mutation == "roles" ? std::vector<unsigned>{0, 3}
                                                : std::vector<unsigned>{1};
        root.values[result.index].components = restriction.roles;
        root.values[result.index].placement = DataPlacement{restriction.roles};
      } else if (mutation == "placement")
        root.values[result.index].placement = DataPlacement{{1}};
      else if (mutation == "holder")
        root.values[result.index].oracleHolder = 0;
      else if (mutation == "cycle")
        restriction.input = result;
      else if (mutation == "forward") {
        auto first = repeat.captures.front();
        auto earlier = llvm::find_if(root.operations, [&](const auto &op) {
          return op.results.size() == 1 &&
                 op.results.front().index == first.index;
        });
        require(earlier < at, "wrong restriction order");
        std::get<Restriction>(earlier->action).input = result;
      } else {
        auto current = llvm::find_if(root.operations, [](const auto &op) {
          auto *constant = std::get_if<MathValue>(&op.action);
          return constant && constant->literal == "3";
        });
        require(current != root.operations.end(), "missing current generation");
        restriction.input = current->results.front();
      }
      rejects(project, "source.scoped-domain");
      if (mutation != "forward") {
        restriction = saved;
        root.values[result.index] = savedValue;
        repeat.captures = captures;
        replay(project);
      }
    });
  for (bool gainsParticipants : {false, true})
    cases.run(
        "recipe restrictions compose with typed identities " +
            Twine(gainsParticipants),
        [&] {
          auto project = check(recipeSource());
          replay(project);
          auto &root = body(project);
          auto &repeat = std::get<ProtocolRepeat>(control(root).action);
          auto result = repeat.captures.back();
          auto at = llvm::find_if(root.operations, [&](const auto &op) {
            return op.results.size() == 1 &&
                   op.results.front().index == result.index;
          });
          auto &restriction = std::get<Restriction>(at->action);
          auto input = restriction.input;
          auto restricted = ValueId{uint32_t(root.values.size())};
          auto value = root.values[input.index];
          value.components = {0, 1};
          value.placement = DataPlacement{{0, 1}};
          root.values.push_back(value);
          auto identity = ValueId{uint32_t(root.values.size())};
          if (gainsParticipants) {
            value.components = {0, 1, 2};
            value.placement = DataPlacement{{0, 1, 2}};
          }
          root.values.push_back(value);
          restriction.input = identity;
          const auto position = at - root.operations.begin();
          const auto span = at->span;
          root.operations.insert(
              root.operations.begin() + position,
              Operation{Restriction{input, {0, 1}}, {restricted}, span, 0});
          root.operations.insert(
              root.operations.begin() + position + 1,
              Operation{Projection{restricted, {}}, {identity}, span, 0});
          if (gainsParticipants)
            rejects(project);
          else {
            replay(project);
            specialized(take(closeInvocation(project, runInvocation(project))));
          }
        });
  for (bool nested : {false, true})
    for (bool restrictFirst : {false, true})
      cases.run("recipe identity chain retains eager generations " +
                    Twine(nested) + "/" + Twine(restrictFirst),
                [&] {
                  auto project = check(recipeSource(true, nested));
                  replay(project);
                  recipeIdentityChain(body(project), 4, restrictFirst);
                  replay(project);
                  specialized(
                      take(closeInvocation(project, runInvocation(project))));
                });
  for (StringRef boundary : {"source", "closure", "closed-source"})
    for (StringRef mutation :
         {"participants", "component-order", "holder", "placement",
          "placement-kind", "placement-absence", "unavailable", "later"})
      cases.run(
          "recipe identity restored endpoint refuses " + mutation + "/" +
              boundary,
          [&] {
            auto project = check(recipeSource(true, true));
            replay(project);
            auto &root = body(project);
            auto aliases = recipeIdentityChain(root, 3);
            replay(project);
            auto closed =
                take(closeInvocation(project, runInvocation(project)));
            specialized(closed);
            const auto savedValues = root.values;
            const auto savedOperations = root.operations;
            auto &intermediate = root.values[aliases.front().index];
            if (mutation == "participants")
              intermediate.components = {1};
            else if (mutation == "component-order")
              intermediate.components = {2, 1, 0};
            else if (mutation == "holder")
              intermediate.oracleHolder = 0;
            else if (mutation == "placement")
              intermediate.placement = DataPlacement{{1}};
            else if (mutation == "placement-kind")
              intermediate.placement = OraclePlacement{0, {0, 1, 2}};
            else if (mutation == "placement-absence")
              intermediate.placement.reset();
            else {
              auto at = llvm::find_if(root.operations, [&](const auto &op) {
                return op.results.size() == 1 &&
                       op.results.front().index == aliases.front().index;
              });
              require(at != root.operations.end(), "missing first alias");
              if (mutation == "later")
                std::get<Projection>(at->action).input = aliases.back();
              else {
                auto missing = ValueId{uint32_t(root.values.size())};
                root.values.push_back(intermediate);
                std::get<Projection>(at->action).input = missing;
              }
            }
            if (boundary == "source")
              rejects(project);
            else if (boundary == "closure")
              refuses(closeInvocation(project, runInvocation(project)),
                      "source.binding-witness");
            else
              witnessRefusal(checkScopedSpecialization(closed));
            root.values = savedValues;
            root.operations = savedOperations;
            replay(project);
            specialized(closed);
            specialized(take(closeInvocation(project, runInvocation(project))));
          });
  for (unsigned length : {8, 256, 1024})
    cases.run(
        "recipe identity chain cumulative exact allowance " + Twine(length),
        [&] {
          auto project = check(recipeSource(true, true));
          recipeIdentityChain(body(project), length, true);
          std::vector<SourceWorkBudget> observed;
          if (auto error = checkScopedElaboration(project, {}, &observed))
            throw std::runtime_error(toString(std::move(error)));
          require(observed.size() == 1, "missing alias work ledger");
          const auto work = observed.front().ledger.total;
          outs() << "recipe identity length=" << length << " replay=" << work
                 << '\n';
          require(work == observed.front().ledger.used(
                              SourceWorkPhase::ScopedElaboration),
                  "alias work escaped cumulative replay ledger");
          for (bool oneShort : {false, true}) {
            namespace detail = zkc::language::detail;
            Limits limits;
            limits.work = work - oneShort;
            detail::Work bounded{limits};
            detail::Work::Scope phase(bounded,
                                      SourceWorkPhase::ScopedElaboration);
            auto error = detail::checkScopedSources(
                detail::DeclarationAccess::storage(project), bounded);
            if (oneShort) {
              require(bool(error), "one-short alias chain passed");
              auto message = toString(std::move(error));
              require(namesIdentifier(message, "source.limit"), message);
            } else {
              if (error)
                throw std::runtime_error(toString(std::move(error)));
              require(bounded.used == work,
                      "exact alias allowance was not consumed");
            }
          }
          Limits originalAllowance;
          originalAllowance.work = project.checkedWork();
          auto exhausted = checkScopedElaboration(project, originalAllowance);
          if (length == 1024) {
            require(bool(exhausted), "long aliases escaped original cap");
            auto message = toString(std::move(exhausted));
            require(namesIdentifier(message, "source.limit"), message);
          } else
            consumeError(std::move(exhausted));
          replay(project);
          specialized(take(closeInvocation(project, runInvocation(project))));
        });
  for (bool nested : {false, true})
    cases.run("restricted recipe exact allowance and one short " +
                  Twine(nested),
              [&] {
                auto project = check(recipeSource(true, nested));
                std::vector<SourceWorkBudget> observed;
                if (auto error = checkScopedElaboration(project, {}, &observed))
                  throw std::runtime_error(toString(std::move(error)));
                require(observed.size() == 1, "missing recipe work ledger");
                const auto work = observed.front().ledger.total;
                outs() << "recipe budget nested=" << nested
                       << " checked=" << project.checkedWork()
                       << " replay=" << work << '\n';
                require(work == observed.front().ledger.used(
                                    SourceWorkPhase::ScopedElaboration),
                        "recipe replay work escaped its ledger");
                // The public API also enforces the earlier formation budget.
                // Check the replay's own exact allowance independently of
                // that (larger) admission floor.
                for (bool oneShort : {false, true}) {
                  namespace detail = zkc::language::detail;
                  Limits replayLimits;
                  replayLimits.work = work - oneShort;
                  detail::Work bounded{replayLimits};
                  detail::Work::Scope phase(bounded,
                                            SourceWorkPhase::ScopedElaboration);
                  auto error = detail::checkScopedSources(
                      detail::DeclarationAccess::storage(project), bounded);
                  if (oneShort) {
                    require(bool(error), "one-short recipe replay passed");
                    auto message = toString(std::move(error));
                    require(namesIdentifier(message, "source.limit"), message);
                  } else {
                    if (error)
                      throw std::runtime_error(toString(std::move(error)));
                    require(bounded.used == work,
                            "exact recipe allowance was not consumed");
                  }
                }
                Limits limits;
                limits.work = std::max(project.checkedWork(), work);
                if (auto error = checkScopedElaboration(project, limits))
                  throw std::runtime_error(toString(std::move(error)));
                --limits.work;
                auto error = checkScopedElaboration(project, limits);
                require(bool(error), "one-short recipe allowance passed");
                auto message = toString(std::move(error));
                require(namesIdentifier(message, "source.limit"), message);
                replay(project);
              });
  cases.run("source event and carrier work admits exact allowance and retry",
            [&] {
              auto project = check(stateSource(2, "a"));
              std::vector<SourceWorkBudget> observed;
              if (auto error = checkScopedElaboration(project, {}, &observed))
                throw std::runtime_error(toString(std::move(error)));
              require(observed.size() == 1, "missing replay work ledger");
              const auto work = observed.front().ledger.total;
              require(work == observed.front().ledger.used(
                                  SourceWorkPhase::ScopedElaboration),
                      "source replay work escaped its ledger");
              Limits limits;
              limits.work = std::max(project.checkedWork(), work);
              if (auto error = checkScopedElaboration(project, limits))
                throw std::runtime_error(toString(std::move(error)));
              --limits.work;
              auto error = checkScopedElaboration(project, limits);
              require(bool(error), "one-short replay allowance passed");
              auto message = toString(std::move(error));
              require(namesIdentifier(message, "source.limit"), message);
              replay(project);
            });
  return cases.result();
}
