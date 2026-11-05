#include "../lib/Language/ScopedWitness.h"
#include "../lib/Language/State.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/DeclarationIndex.h"
#include "zkc/Language/Project.h"
#include <algorithm>
#include <set>
#include <type_traits>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject checked(StringRef code) {
  return take(analyze(take(capture({{"m", code.str(), "invocations.zkc"}})))
                  .checkedProject());
}
Body &body(const CheckedProject &project, StringRef name) {
  auto found = llvm::find_if(project.declarations(), [&](const auto &decl) {
    return decl.name == name;
  });
  require(found != project.declarations().end() && found->body,
          "missing body: " + name);
  return const_cast<Body &>(*found->body);
}
void rejected(const CheckedProject &project) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "coordinated mutation was accepted");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, "source.binding-witness"),
          "unexpected diagnostic: " + message);
}
void accepted(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
const char *protocol = R"(
module m;domain F=field("bls12-381.fr");
protocol relay roles(A)(left:bool@A,right:bool@A,first:Random<F>@A,second:Random<F>@A)->(out:bool@A){return left;}
protocol Run roles(P)(left:bool@P,right:bool@P,first:Random<F>@P,second:Random<F>@P)->(out:bool@P){let out=relay roles(P)(left,right,first,second);return out;}
)";
} // namespace
int main() {
  Cases cases;
  for (unsigned collection = 0; collection < 5; ++collection)
    for (bool syntax : {false, true})
      cases.run(
          "malformed retained source " + Twine(collection) + " " +
              Twine(syntax),
          [&] {
            auto project = checked(R"(
module m;
fn identity(x:bool)->bool{return x;}
fn apply(x:bool,callback:fn(bool)->bool effects())->bool effects(){return callback(x);}
fn dormant(x:bool)->bool effects(){return apply(identity(x),fn(y)=>y);}
#[linear] struct Ticket{value:bool}
fn observe(x:Ticket)->(Ticket,bool){let pair=inspect_record(x);return(pair.0,pair.1.0);}
)");
            accepted(project);
            auto &storage = const_cast<zkc::language::detail::CheckedStorage &>(
                zkc::language::detail::DeclarationAccess::storage(project));
            auto remove = [&](auto &handle) {
              require(bool(handle), "missing positive source handle");
              if (!syntax) {
                handle.reset();
                return;
              }
              using Source = std::remove_const_t<
                  typename std::decay_t<decltype(handle)>::element_type>;
              auto copy = std::make_shared<Source>(*handle);
              copy->syntax.reset();
              handle = std::move(copy);
            };
            StringRef diagnostic = "source.binding-witness";
            if (collection == 0) {
              require(!storage.scopedCalls.empty(), "missing ordinary call");
              remove(storage.scopedCalls.front());
            } else if (collection == 1) {
              require(!storage.intrinsicCalls.empty(),
                      "missing intrinsic call");
              remove(storage.intrinsicCalls.front());
            } else if (collection == 2) {
              require(!storage.scopedInvocations.empty(),
                      "missing scoped invocation");
              remove(storage.scopedInvocations.front());
              diagnostic = "source.scoped-witness";
            } else if (collection == 3) {
              require(!storage.scopedSources.empty(),
                      "missing callback source");
              remove(storage.scopedSources.front());
              diagnostic = "source.scoped-witness";
            } else {
              require(!storage.bodySources.empty(), "missing body source");
              remove(storage.bodySources.begin()->second);
            }
            auto error = checkScopedElaboration(project);
            require(bool(error), "malformed source handle passed replay");
            auto message = toString(std::move(error));
            require(namesIdentifier(message, diagnostic),
                    "unexpected malformed-source refusal: " + message);
          });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run("protocol coordinated mutation " + Twine(mutation), [&] {
      auto project = checked(protocol);
      auto &operations = body(project, "Run").operations;
      auto found = llvm::find_if(operations, [](const auto &op) {
        return std::holds_alternative<ProtocolApplication>(op.action);
      });
      require(found != operations.end() && found->binding,
              "missing protocol application");
      auto &action = std::get<ProtocolApplication>(found->action);
      auto &binding = *found->binding;
      if (mutation == 0) {
        std::swap(action.services[0], action.services[1]);
        std::swap(binding.services[0], binding.services[1]);
      } else {
        std::swap(binding.argumentOrder[0], binding.argumentOrder[1]);
        if (mutation == 2) {
          std::swap(action.operands[0], action.operands[1]);
          std::swap(binding.operands[0], binding.operands[1]);
        }
      }
      rejected(project);
    });
  cases.run(
      "coordinated swaps cannot select a different live random history", [] {
        auto project = checked(R"(
module m;domain F=field("bls12-381.fr");
protocol draw roles(A)(first:Random<F>@A,second:Random<F>@A)->(out:F@A){let unused=second.draw();let out=first.draw();return out;}
protocol Run roles(P)(first:Random<F>@P,second:Random<F>@P)->(out:F@P){let previous=first.draw();let out=draw roles(P)(first,second);return out;}
)");
        accepted(project);
        auto &checkedBody = body(project, "Run");
        require(checkedBody.services.size() == 2 &&
                    checkedBody.services[0].field ==
                        checkedBody.services[1].field &&
                    checkedBody.services[0].owner ==
                        checkedBody.services[1].owner,
                "fixture needs equal-typed services at one owner");
        bool advanced = false, changed = false;
        for (auto &op : checkedBody.operations) {
          if (const auto *query = std::get_if<ServiceQuery>(&op.action))
            advanced |= query->service.index == 0;
          if (auto *action = std::get_if<ProtocolApplication>(&op.action)) {
            require(advanced,
                    "the histories must already have different prefixes");
            std::swap(action->services[0], action->services[1]);
            std::swap(op.binding->services[0], op.binding->services[1]);
            changed = true;
          }
        }
        require(changed, "missing live-history invocation");
        rejected(project);
      });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run("balanced intrinsic exchange " + Twine(mutation), [&] {
      std::string source = R"(
module m;#[linear] struct Ticket{value:bool}
fn observe(left:Ticket,right:Ticket)->(Ticket,Ticket,bool,bool){
 let a=inspect_record(left);let b=inspect_record(right);
 return(a.0,b.0,a.1.0,b.1.0);
}
)";
      if (mutation == 2) {
        auto at = source.find("let a=");
        source.insert(at, "let first=left;let second=right;");
        at = source.find("inspect_record(left)");
        source.replace(at, std::string("inspect_record(left)").size(),
                       "inspect_record(first)");
        at = source.find("inspect_record(right)");
        source.replace(at, std::string("inspect_record(right)").size(),
                       "inspect_record(second)");
      }
      if (mutation == 3) {
        auto at = source.find("inspect_record(left)");
        source.replace(at, std::string("inspect_record(left)").size(),
                       "inspect_record({left})");
        at = source.find("inspect_record(right)");
        source.replace(at, std::string("inspect_record(right)").size(),
                       "inspect_record({right})");
      }
      auto project = checked(source);
      std::vector<Operation *> inspections;
      for (auto &op : body(project, "observe").operations)
        if (auto *construct = std::get_if<Construct>(&op.action);
            construct && construct->kind == Construct::Kind::Inspect)
          inspections.push_back(&op);
      require(inspections.size() == 2, "missing inspection pair");
      std::swap(std::get<Construct>(inspections[0]->action).operands[0],
                std::get<Construct>(inspections[1]->action).operands[0]);
      std::swap(inspections[0]->binding->operands[0],
                inspections[1]->binding->operands[0]);
      auto &checkedBody = body(project, "observe");
      if (mutation == 1) {
        auto first = inspections[0]->binding->operands[0];
        auto second = inspections[1]->binding->operands[0];
        for (auto &[expression, value] : checkedBody.expressionValues) {
          if (value.index == first.index)
            value = second;
          else if (value.index == second.index)
            value = first;
        }
      }
      if (mutation == 2) {
        // Restore the call operands, but exchange the actual lexical reads.
        std::swap(std::get<Construct>(inspections[0]->action).operands[0],
                  std::get<Construct>(inspections[1]->action).operands[0]);
        std::swap(inspections[0]->binding->operands[0],
                  inspections[1]->binding->operands[0]);
        std::vector<Projection *> reads;
        for (auto &op : checkedBody.operations)
          if (auto *projection = std::get_if<Projection>(&op.action);
              projection && projection->input.index < checkedBody.inputs)
            reads.push_back(projection);
        require(reads.size() == 2, "missing lexical reads");
        std::swap(reads[0]->input, reads[1]->input);
      }
      if (mutation == 3) {
        std::optional<uint32_t> left, right;
        for (auto [expression, value] : checkedBody.expressionValues) {
          if (value.index == 0)
            left = expression;
          if (value.index == 1)
            right = expression;
        }
        require(left && right, "missing block result mappings");
        std::swap(checkedBody.expressionValues.at(*left),
                  checkedBody.expressionValues.at(*right));
      }
      rejected(project);
    });
  cases.run("protocol roots cannot be relabeled to certify a swap", [] {
    auto project = checked(protocol);
    auto &checkedBody = body(project, "Run");
    std::swap(checkedBody.services[0], checkedBody.services[1]);
    for (const auto &decl : project.declarations())
      if (decl.name == "Run") {
        auto &services = const_cast<Declaration &>(decl).services;
        std::swap(services[0], services[1]);
      }
    for (auto &op : checkedBody.operations)
      if (auto *action = std::get_if<ProtocolApplication>(&op.action)) {
        std::swap(action->services[0], action->services[1]);
        std::swap(op.binding->services[0], op.binding->services[1]);
      }
    rejected(project);
  });
  cases.run("zero-result protocol calls authenticate role order", [] {
    auto project = checked(R"(
module m;protocol relay roles(A,B)()->(){return ();}
protocol Run roles(P,V)()->(){relay roles(P,V)();return ();}
)");
    for (auto &op : body(project, "Run").operations)
      if (auto *action = std::get_if<ProtocolApplication>(&op.action)) {
        std::swap(action->roles[0], action->roles[1]);
        std::swap(op.binding->roles[0], op.binding->roles[1]);
      }
    rejected(project);
  });
  cases.run("closed and source actions cannot co-certify swapped services", [] {
    auto project = checked(protocol);
    auto closed = take(closeNativeRun(project, "m::Run"));
    auto swap = [](Body &checkedBody) {
      for (auto &op : checkedBody.operations)
        if (auto *action = std::get_if<ProtocolApplication>(&op.action)) {
          std::swap(action->services[0], action->services[1]);
          std::swap(op.binding->services[0], op.binding->services[1]);
        }
    };
    swap(body(project, "Run"));
    for (const auto &decl : closed.declarations())
      if (decl.body)
        swap(const_cast<Body &>(*decl.body));
    auto error = checkScopedSpecialization(closed);
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "source.binding-witness"),
            "closed and source invocations certified one another");
  });
  cases.run("named data and service arguments preserve written order", [] {
    auto source = std::string(protocol);
    auto begin = source.find("relay roles(P)(left,right,first,second)");
    require(begin != std::string::npos, "missing invocation source");
    source.replace(
        begin, std::string("relay roles(P)(left,right,first,second)").size(),
        "relay roles(P)(second=second,right=right,first=first,left=left)");
    auto project = checked(source);
    accepted(project);
    auto closed = take(closeNativeRun(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("immutable service aliases resolve to exact original roots", [] {
    auto source = std::string(protocol);
    auto at = source.find("let out=relay");
    require(at != std::string::npos, "missing invocation");
    source.insert(at, "let alias=first;let forwarded=alias;");
    at = source.find("(left,right,first,second)");
    source.replace(at, std::string("(left,right,first,second)").size(),
                   "(left,right,forwarded,second)");
    auto project = checked(source);
    accepted(project);
    auto closed = take(closeNativeRun(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
    for (auto &op : body(project, "Run").operations)
      if (auto *action = std::get_if<ProtocolApplication>(&op.action)) {
        std::swap(action->services[0], action->services[1]);
        std::swap(op.binding->services[0], op.binding->services[1]);
      }
    rejected(project);
  });
  cases.run("service roots survive nested protocol regions", [] {
    auto project = checked(R"(
module m;domain F=field("bls12-381.fr");
protocol relay roles(A)(left:bool@A,right:bool@A,first:Random<F>@A,second:Random<F>@A)->(out:bool@A){return left;}
protocol Run roles(P)(left:bool@P,right:bool@P,first:Random<F>@P,second:Random<F>@P,n:index@P)->(out:bool@P){
 for i in 0..n roles(P) max 2 {let ignored=relay roles(P)(left,right,first,second);}
 return left;
}
)");
    accepted(project);
    auto closed = take(closeNativeRun(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
    bool changed = false;
    for (const auto &op : body(project, "Run").operations)
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
        for (auto &nested : const_cast<Body &>(*repeat->region).operations)
          if (auto *application =
                  std::get_if<ProtocolApplication>(&nested.action)) {
            std::swap(application->services[0], application->services[1]);
            std::swap(nested.binding->services[0], nested.binding->services[1]);
            changed = true;
          }
    require(changed, "missing nested invocation");
    rejected(project);
  });
  cases.run(
      "source target survives coordinated action and binding changes", [] {
        auto source = std::string(protocol);
        auto at = source.find("protocol Run");
        source.insert(at, R"(
protocol other roles(A)(left:bool@A,right:bool@A,first:Random<F>@A,second:Random<F>@A)->(out:bool@A){return right;}
)");
        auto project = checked(source);
        auto other =
            llvm::find_if(project.declarations(), [](const auto &decl) {
              return decl.name == "other";
            });
        require(other != project.declarations().end(),
                "missing alternative target");
        for (auto &op : body(project, "Run").operations)
          if (auto *action = std::get_if<ProtocolApplication>(&op.action)) {
            action->callee = other->id;
            op.binding->target.declaration = other->id;
          }
        rejected(project);
      });
  cases.run("dormant callback parameter maps cannot certify each other", [] {
    auto project = checked(R"(
module m;#[linear] struct Ticket{value:bool}
fn apply(left:Ticket,right:Ticket,body:fn(Ticket,Ticket)->(Ticket,Ticket,bool,bool) effects(stop))->(Ticket,Ticket,bool,bool) effects(stop){return body(left,right);}
fn dormant(left:Ticket,right:Ticket)->(Ticket,Ticket,bool,bool){
 return apply(left,right,fn(a,b)=>{let first=inspect_record(a);let second=inspect_record(b);(first.0,second.0,first.1.0,second.1.0)});
}
)");
    accepted(project);
    auto &bindings = body(project, "dormant").scopedBindings;
    auto at = llvm::find_if(bindings, [](const auto &binding) {
      return bool(binding.computation);
    });
    require(at != bindings.end(), "missing dormant computation");
    auto &callback = const_cast<Body &>(*at->computation->body);
    std::vector<Operation *> inspections;
    for (auto &op : callback.operations)
      if (auto *construct = std::get_if<Construct>(&op.action);
          construct && construct->kind == Construct::Kind::Inspect)
        inspections.push_back(&op);
    require(inspections.size() == 2, "missing callback inspections");
    auto first = inspections[0]->binding->operands[0];
    auto second = inspections[1]->binding->operands[0];
    std::swap(std::get<Construct>(inspections[0]->action).operands[0],
              std::get<Construct>(inspections[1]->action).operands[0]);
    std::swap(inspections[0]->binding->operands[0],
              inspections[1]->binding->operands[0]);
    for (auto &[expression, value] : callback.expressionValues)
      if (value.index == first.index)
        value = second;
      else if (value.index == second.index)
        value = first;
    rejected(project);
  });
  cases.run("unused source bodies remain required", [] {
    auto project = checked("module m;fn dormant(x:bool)->bool{return x;}");
    for (const auto &decl : project.declarations())
      if (decl.name == "dormant")
        const_cast<Declaration &>(decl).body.reset();
    rejected(project);
  });
  cases.run("written argument evaluation order remains required", [] {
    auto project = checked(R"(
module m;
fn checked(x:bool)->bool{require x;return x;}
fn pair(left:bool,right:bool)->bool{return left;}
fn dormant(left:bool,right:bool)->bool{return pair(right=checked(right),left=checked(left));}
)");
    auto &operations = body(project, "dormant").operations;
    std::vector<unsigned> calls;
    for (unsigned i = 0; i < operations.size(); ++i)
      if (operations[i].binding)
        calls.push_back(i);
    require(calls.size() == 3, "missing ordered argument calls");
    std::swap(operations[calls[0]], operations[calls[1]]);
    rejected(project);
  });
  cases.run("an older value of the same binding cannot certify a call", [] {
    auto project = checked(R"(
module m;fn choose(x:bool)->bool{return x;}
fn dormant(left:bool,right:bool)->bool{let mut current=left;current=right;return choose(current);}
)");
    auto &checkedBody = body(project, "dormant");
    std::optional<ValueId> previous;
    for (const auto &op : checkedBody.operations)
      if (const auto *projection = std::get_if<Projection>(&op.action);
          projection && projection->input.index == 0 &&
          projection->path.empty())
        previous = op.results.front();
    require(bool(previous), "missing initial lexical version");
    for (auto &op : checkedBody.operations)
      if (auto *call = std::get_if<HelperCall>(&op.action)) {
        auto current = call->operands.front();
        call->operands.front() = *previous;
        op.binding->operands.front() = *previous;
        for (auto &[expression, value] : checkedBody.expressionValues)
          if (value.index == current.index)
            value = *previous;
      }
    rejected(project);
  });
  cases.run("qualified generic scoped methods preserve lexical authority", [] {
    auto project = checked(R"(
module m;#[linear] struct Ticket<N:nat>{value:bool}
fn apply<N:nat>(self:Ticket<N>,body:fn(Ticket<N>)->Ticket<N> effects(stop))->Ticket<N> effects(stop){return body(self);}
fn advance<N:nat>(x:Ticket<N>)->Ticket<N>{return x.apply(fn(value)=>{let parts=zkc::records::inspect_record(value);zkc::records::repack_record(parts.0,parts.1)});}
fn make()->Ticket<3>{return Ticket<3>{value:true};}
fn finish(x:Ticket<3>)->(){let fields=zkc::records::unpack(x);return ();}
protocol Run roles(P)()->(){let x@P=make();let y@P=advance(x);let done@P=finish(y);return ();}
)");
    accepted(project);
    auto closed = take(closeNativeRun(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("qualified and method homonyms keep ordinary call identity", [] {
    auto project = checked(R"(
module m;struct Box{pub value:bool}
math fn inspect_record(self:Box)->bool{return self.value;}
protocol Run roles(P)(x:Box@P)->(out:bool@P){return m::inspect_record(x)&&x.inspect_record();}
)");
    accepted(project);
    auto closed = take(closeNativeRun(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("generic module calls retain definition-site callback scope", [] {
    auto project = checked(R"(
module m;domain F=field("koala-bear");
interface Transform<T:Type+Copy+Drop>{fn run(x:T,body:fn(T)->T effects(stop))->T effects(stop);}
module Identity<T:Type+Copy+Drop>:Transform<T>{fn run(x:T,body:fn(T)->T effects(stop))->T effects(stop){return body(x);}}
fn through<T:Type+Copy+Drop,C:Transform<T>>(x:T,body:fn(T)->T effects(stop))->T effects(stop){return C::run(x,body);}
fn named(x:F)->F{return through<F,Identity<F>>(body=fn(v)=>v+1,x=x);}
protocol Run roles(P)(x:F@P)->(out:F@P){return named(x);}
)");
    accepted(project);
    auto closed = take(closeNativeRun(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  const char *queries = R"(
module m;domain F=field("koala-bear.ext4-binomial3");
protocol Run roles(P,V)(first:Random<F>@V,second:Random<F>@V)->(){
 let alias=first;let forwarded=alias;
 let a=forwarded.draw();let b=first.index<8>();let c=first.indices(8,3);
 let d=second.draw();return ();
}
)";
  auto queriesIn = [](Body &checkedBody) {
    std::vector<Operation *> result;
    for (auto &op : checkedBody.operations)
      if (std::holds_alternative<ServiceQuery>(op.action))
        result.push_back(&op);
    return result;
  };
  cases.run(
      "indexed queries retain one normal binding per authored occurrence", [&] {
        auto project = checked(queries);
        accepted(project);
        auto operations = queriesIn(body(project, "Run"));
        require(operations.size() == 4, "missing managed operations");
        std::set<unsigned> occurrences;
        for (auto *op : operations) {
          require(op->binding && op->binding->scopedSource &&
                      op->binding->target.reference.category ==
                          ResolutionCategory::ServiceMethod,
                  "managed query lacks an indexed call occurrence");
          require(occurrences.insert(*op->binding->scopedSource).second,
                  "managed source occurrence was reused");
          const auto &target =
              project.declarations()[op->binding->target.declaration.index];
          const auto *method =
              project.declarationIndex().serviceAssociation(target.id);
          require(method && method->name == target.name && target.parent &&
                      project.declarationIndex()
                              .association(*target.parent)
                              ->identity == method->constructor,
                  "managed declaration has the wrong constructor association");
        }
        auto closed = take(closeNativeRun(project, "m::Run"));
        if (auto error = checkScopedSpecialization(closed))
          throw std::runtime_error(toString(std::move(error)));
      });
  for (unsigned mutation = 0; mutation < 17; ++mutation)
    cases.run("managed authored query mutation " + Twine(mutation), [&] {
      auto project = checked(queries);
      accepted(project);
      auto &run = body(project, "Run");
      auto operations = queriesIn(run);
      auto &draw = *operations[0];
      auto &index = *operations[1];
      auto &block = *operations[2];
      if (mutation == 0) {
        std::get<ServiceQuery>(draw.action).service = {1};
        draw.binding->services[0] = {1};
      } else if (mutation == 1) {
        std::get<ServiceQuery>(index.action).bound = Natural::constant(9);
        index.binding->arguments[1].dimension = Natural::constant(9);
      } else if (mutation == 2) {
        std::get<ServiceQuery>(block.action).count = Natural::constant(4);
        block.binding->arguments[2].dimension = Natural::constant(4);
      } else if (mutation == 3) {
        draw.binding->target = index.binding->target;
      } else if (mutation == 4) {
        draw.binding->target.reference.provider =
            project.declarations().front().id;
      } else if (mutation == 5) {
        draw.binding.reset();
      } else if (mutation == 6) {
        index.binding->scopedSource = draw.binding->scopedSource;
      } else if (mutation == 7) {
        run.operations.erase(llvm::find_if(run.operations, [](const auto &op) {
          return std::holds_alternative<ServiceQuery>(op.action);
        }));
      } else if (mutation == 8) {
        run.services[0].constructor = {};
      } else if (mutation == 9) {
        std::swap(run.services[0], run.services[1]);
        for (const auto &decl : project.declarations())
          if (decl.name == "Run")
            std::swap(const_cast<Declaration &>(decl).services[0],
                      const_cast<Declaration &>(decl).services[1]);
        for (auto *op : operations) {
          auto &query = std::get<ServiceQuery>(op->action);
          query.service.index = 1 - query.service.index;
          op->binding->services[0] = query.service;
        }
      } else if (mutation == 10) {
        std::get<ServiceQuery>(block.action).bound = Natural::constant(9);
        block.binding->arguments[1].dimension = Natural::constant(9);
      } else {
        auto &result =
            run.values[operations[(mutation - 11) / 2]->results.front().index];
        if ((mutation - 11) % 2 == 0) {
          require(result.type != Type{}, "query result already Boolean");
          result.type = Type{};
        } else {
          require(result.components == std::vector<unsigned>{1},
                  "query result must belong to V");
          result.components = {0};
        }
      }
      rejected(project);
    });
  cases.run(
      "generic managed bound and count close through normal bindings", [] {
        auto project = checked(R"(
module m;domain F=field("koala-bear.ext4-binomial3");
protocol sample<N:nat,Q:nat> roles(V)(coins:Random<F>@V)->(){
 let a=coins.index<N>();let b=coins.indices(N,Q);return ();
}
protocol Run roles(V)(coins:Random<F>@V)->(){sample<8,3>(coins);return ();}
)");
        accepted(project);
        auto closed = take(closeNativeRun(project, "m::Run"));
        if (auto error = checkScopedSpecialization(closed))
          throw std::runtime_error(toString(std::move(error)));
        bool saw = false;
        for (const auto &decl : closed.declarations())
          if (decl.body)
            for (const auto &op : decl.body->operations)
              if (const auto *query = std::get_if<ServiceQuery>(&op.action);
                  query && query->count) {
                require(op.binding && op.binding->arguments.size() == 3 &&
                            op.binding->arguments[1].dimension ==
                                Natural::constant(8) &&
                            op.binding->arguments[2].dimension ==
                                Natural::constant(3),
                        "query call statics did not close");
                saw = true;
              }
        require(saw, "missing closed block query");
      });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run("nested managed root capture mutation " + Twine(mutation), [&] {
      auto project = checked(R"(
module m;domain F=field("koala-bear.ext4-binomial3");
protocol Run roles(P,V)(go:bool@V,n:index@V,first:Random<F>@V,second:Random<F>@V)->(){
 let alias=second;
 for i in 0..n roles(V) max 2 {
   let local=alias;
   if go roles(V) {let a=local.draw();let b=first.index<8>();let c=local.indices(8,3);}
   else {let a=first.draw();let b=local.index<8>();let c=first.indices(8,3);}
 }
 return ();
}
)");
      accepted(project);
      auto closed = take(closeNativeRun(project, "m::Run"));
      if (auto error = checkScopedSpecialization(closed))
        throw std::runtime_error(toString(std::move(error)));
      bool changed = false;
      for (auto &op : body(project, "Run").operations)
        if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
          auto &region = const_cast<Body &>(*repeat->region);
          if (mutation == 0) {
            std::swap(repeat->services[0], repeat->services[1]);
            std::swap(region.services[0], region.services[1]);
            changed = true;
          }
          for (auto &nested : region.operations)
            if (auto *control = std::get_if<Control>(&nested.action)) {
              if (mutation == 1) {
                std::swap(control->services[0], control->services[1]);
                for (const auto &arm : control->regions)
                  std::swap(const_cast<Body &>(*arm).services[0],
                            const_cast<Body &>(*arm).services[1]);
                changed = true;
              } else if (mutation >= 2) {
                auto &arm = const_cast<Body &>(*control->regions.front());
                auto at = llvm::find_if(arm.operations, [](const auto &op) {
                  return std::holds_alternative<ServiceQuery>(op.action);
                });
                require(at != arm.operations.end(), "missing captured query");
                if (mutation == 2) {
                  auto &query = std::get<ServiceQuery>(at->action);
                  query.service.index = 1 - query.service.index;
                  at->binding->services[0] = query.service;
                } else {
                  arm.services[0].name = "forged";
                  arm.services[0].owner = 0;
                }
                changed = true;
              }
            }
        }
      require(changed, "missing nested managed control");
      rejected(project);
    });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run("region-relative root is reconstructed from ordered captures " +
                  Twine(mutation),
              [&] {
                auto project = checked(R"(
module m;domain F=field("koala-bear.ext4-binomial3");
protocol Run roles(P,V)(go:bool@V,n:index@V,first:Random<F>@P,second:Random<F>@V)->(){
 let alias=second;
 for i in 0..n roles(V) max 2 {
   let inner=alias;
   if go roles(V) {let a=inner.draw();let b=inner.index<8>();let c=inner.indices(8,3);}
   else {let a=inner.draw();}
 }
 return ();
}
)");
                accepted(project);
                auto closed = take(closeNativeRun(project, "m::Run"));
                if (auto error = checkScopedSpecialization(closed))
                  throw std::runtime_error(toString(std::move(error)));
                bool changed = false;
                auto &run = body(project, "Run");
                for (auto &op : run.operations)
                  if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
                    require(
                        repeat->services.size() == 1 &&
                            repeat->services[0].index == 1,
                        "repeat did not remap the second declaration input");
                    auto &region = const_cast<Body &>(*repeat->region);
                    if (mutation == 0) {
                      repeat->services[0] = {0};
                      region.services[0] = run.services[0];
                      changed = true;
                    } else if (mutation == 1) {
                      region.services[0].owner = 0;
                      changed = true;
                    } else {
                      auto &decl = *llvm::find_if(
                          project.declarations(),
                          [](const auto &decl) { return decl.name == "Run"; });
                      const_cast<Declaration &>(decl).services[1].owner = 0;
                      run.services[1].owner = 0;
                      region.services[0].owner = 0;
                      changed = true;
                    }
                  }
                require(changed, "missing one-root repeat");
                rejected(project);
              });
  cases.run("ordinary home methods retain identity beside managed row names",
            [] {
              auto project = checked(R"(
module m;struct Box{pub value:bool}
math fn draw(self:Box)->bool{return self.value;}
math fn indices(self:Box)->bool{return self.value;}
protocol Run roles(P)(box:Box@P)->(out:bool@P){return box.draw()&&box.indices();}
)");
              accepted(project);
              for (const auto &op : body(project, "Run").operations)
                require(!std::holds_alternative<ServiceQuery>(op.action),
                        "ordinary homonym became a service query");
            });
  for (bool coordinated : {false, true})
    cases.run(
        coordinated ? "managed facade provider cannot be relabeled"
                    : "managed facade provider is source identity",
        [&] {
          auto project = take(
              analyze(
                  take(capture(
                      {{"facade",
                        "module facade;pub use zkc::prelude::{Random};",
                        "facade.zkc"},
                       {"other", "module other;pub use zkc::prelude::{Random};",
                        "other.zkc"},
                       {"m",
                        R"(module m;domain F=field("koala-bear.ext4-binomial3");
protocol Run roles(V)(coins:facade::Random<F>@V)->(){let a=coins.draw();return ();})",
                        "m.zkc"}})))
                  .checkedProject());
          accepted(project);
          auto owner =
              llvm::find_if(project.declarations(), [](const auto &decl) {
                return decl.name == "Run";
              });
          require(owner != project.declarations().end(),
                  "missing facade query owner");
          auto method = project.declarationIndex().lookup(
              SourceAccess{owner->id}, "other::Random::draw");
          auto constructor = project.declarationIndex().lookup(
              SourceAccess{owner->id}, "other::Random");
          require(std::holds_alternative<ResolvedReference>(method) &&
                      std::holds_alternative<ResolvedReference>(constructor),
                  "missing alternate facade path");
          auto &run = body(project, "Run");
          auto operations = queriesIn(run);
          operations.front()->binding->target.reference =
              std::get<ResolvedReference>(method);
          if (coordinated) {
            run.services.front().constructor =
                std::get<ResolvedReference>(constructor);
            const_cast<Declaration &>(*owner).services.front().constructor =
                std::get<ResolvedReference>(constructor);
          }
          rejected(project);
        });
  cases.run(
      "closed managed statics have an independent specialization check", [&] {
        auto project = checked(queries);
        accepted(project);
        auto closed = take(closeNativeRun(project, "m::Run"));
        if (auto error = checkScopedSpecialization(closed))
          throw std::runtime_error(toString(std::move(error)));
        bool changed = false;
        for (const auto &decl : closed.declarations())
          if (decl.body)
            for (auto &op : const_cast<Body &>(*decl.body).operations)
              if (auto *query = std::get_if<ServiceQuery>(&op.action);
                  query && query->count) {
                query->count = Natural::constant(4);
                op.binding->arguments[2].dimension = Natural::constant(4);
                changed = true;
              }
        require(changed, "missing specialized managed query");
        auto error = checkScopedSpecialization(closed);
        require(bool(error) && namesIdentifier(toString(std::move(error)),
                                               "source.scoped-specialization"),
                "closed managed statics certified one another");
      });
  for (bool chained : {false, true})
    for (bool call : {false, true})
      for (bool keepExpression : {false, true})
        cases.run(
            "alias redirection cannot erase its source obligation " +
                Twine(chained) + " " + Twine(call) + " " +
                Twine(keepExpression),
            [&] {
              std::string code = R"(
module m;
fn identity(value:index)->index{return value;}
fn Run(source:index,other:index)->index{let first=source;
)";
              if (chained)
                code += "let second=first;";
              std::string result = chained ? "second" : "first";
              code += "return " + (call ? "identity(" + result + ")" : result) +
                      ";}";
              auto project = checked(code);
              accepted(project);
              auto &run = body(project, "Run");
              auto found = llvm::find_if(run.operations, [](const auto &op) {
                const auto *projection = std::get_if<Projection>(&op.action);
                return projection && projection->path.empty();
              });
              require(found != run.operations.end() &&
                          found->results.size() == 1,
                      "missing authored alias");
              std::get<Projection>(found->action).input = ValueId{1};
              found->span.begin = code.rfind("first");
              found->span.end = found->span.begin + 5;
              run.values.at(found->results.front().index).span = found->span;
              if (!keepExpression)
                found->expression.reset();
              rejected(project);
            });
  for (StringRef mode : {"math fn", "fn", "protocol"})
    for (bool alias : {false, true})
      cases.run(
          "ordinary control selector source edge " + mode +
              (alias ? " alias" : " direct"),
          [&] {
            const bool protocol = mode == "protocol";
            std::string source = mode.str() + " Run";
            source += protocol
                          ? " roles(P)(go:bool@P,other:bool@P)->(r:bool@P){"
                          : "(go:bool,other:bool)->bool{";
            source +=
                alias ? "let selected=go;return if selected{true}else{false};}"
                      : "return if go{true}else{false};}";
            auto project = checked("module m;" + source);
            accepted(project);
            auto &root = body(project, "Run");
            auto found = llvm::find_if(root.operations, [](const auto &op) {
              return std::holds_alternative<Control>(op.action);
            });
            require(found != root.operations.end(), "missing selected control");
            std::get<Control>(found->action).operands.front() = ValueId{1};
            rejected(project);
          });
  for (unsigned bound : {0u, 1u})
    cases.run("local loop bound source edge " + Twine(bound), [&] {
      auto project = checked("module m;"
                             "fn Run(lo:index,hi:index)->index{for _ in lo..hi{"
                             "let _:index=7;}return hi;}");
      accepted(project);
      auto &root = body(project, "Run");
      auto found = llvm::find_if(root.operations, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(found != root.operations.end(), "missing loop control");
      auto &control = std::get<Control>(found->action);
      control.operands[bound] = control.operands[1 - bound];
      rejected(project);
    });
  cases.run("protocol loop count source edge", [&] {
    auto project =
        checked("module m;"
                "protocol Run roles(P)(n:index@P,other:index@P)->(r:index@P){"
                "for _ in 0..n roles(P) max 8{}return n;}");
    accepted(project);
    auto &root = body(project, "Run");
    auto found = llvm::find_if(root.operations, [](const auto &op) {
      return std::holds_alternative<ProtocolRepeat>(op.action);
    });
    require(found != root.operations.end(), "missing protocol repeat");
    std::get<ProtocolRepeat>(found->action).count = ValueId{1};
    rejected(project);
  });

  for (StringRef mode : {"math fn", "fn", "protocol"})
    for (bool eraseMap : {false, true})
      cases.run("root return source edge " + mode + " " + Twine(eraseMap), [&] {
        bool protocol = mode == "protocol";
        std::string code = "module m;" + mode.str() + " Run";
        code += protocol ? " roles(P)(go:bool@P,other:bool@P)->(r:bool@P){"
                         : "(go:bool,other:bool)->bool{";
        code += "return if go{true}else{false};}";
        auto project = checked(code);
        accepted(project);
        auto &root = body(project, "Run");
        auto found = llvm::find_if(root.operations, [](const auto &op) {
          return std::holds_alternative<Control>(op.action);
        });
        require(found != root.operations.end() && found->expression,
                "missing selected return");
        root.results.front() = ValueId{1};
        if (eraseMap)
          root.expressionValues.erase(*found->expression);
        rejected(project);
      });
  for (StringRef mode : {"math fn", "fn", "protocol"})
    cases.run("selected arm yield source edge " + mode, [&] {
      bool protocol = mode == "protocol";
      std::string code = "module m;" + mode.str() + " Run";
      code += protocol ? " roles(P)(go:bool@P,other:bool@P)->(r:bool@P){"
                       : "(go:bool,other:bool)->bool{";
      code += "return if go{let unused=other;true}else{false};}";
      auto project = checked(code);
      accepted(project);
      auto &root = body(project, "Run");
      auto found = llvm::find_if(root.operations, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(found != root.operations.end(), "missing selected yield");
      auto &arm =
          const_cast<Body &>(*std::get<Control>(found->action).regions.front());
      require(arm.inputs && arm.values.front().type.kind == Type::Kind::Boolean,
              "missing captured Boolean");
      arm.results.front() = ValueId{0};
      rejected(project);
    });
  cases.run("control yield packing retains its explicit result", [&] {
    auto project = checked(R"(
module m;fn Run(go:bool,other:bool)->bool{
  let mut state=other;
  let answer=if go{state=false;true}else{state=true;false};
  return answer && state;
})");
    accepted(project);
    auto &root = body(project, "Run");
    auto found = llvm::find_if(root.operations, [](const auto &op) {
      return std::holds_alternative<Control>(op.action);
    });
    require(found != root.operations.end(), "missing mutable-state selection");
    auto &arm =
        const_cast<Body &>(*std::get<Control>(found->action).regions.front());
    auto pack = llvm::find_if(arm.operations, [&](const auto &op) {
      return op.results.size() == 1 &&
             op.results.front().index == arm.results.front().index;
    });
    require(pack != arm.operations.end() &&
                std::holds_alternative<Construct>(pack->action),
            "missing selected result/state packing");
    auto &fields = std::get<Construct>(pack->action).operands;
    require(fields.size() == 2, "unexpected selected result/state packing");
    fields.front() = fields.back();
    rejected(project);
  });
  cases.run("named protocol return order is independently reconstructed", [&] {
    auto project = checked(R"(
module m;protocol Run roles(P)(left:bool@P,right:bool@P)->(a:bool@P,b:bool@P){
  return(b=right,a=left);
})");
    accepted(project);
    auto &root = body(project, "Run");
    std::swap(root.results[0], root.results[1]);
    rejected(project);
  });
  cases.run("all-stopped selected arms do not invent a returned value", [&] {
    auto project = checked(R"(
module m;fn Run(go:bool)->bool{return if go{stop "reject";}else{stop "abort";};}
)");
    accepted(project);
  });

  return cases.result();
}
