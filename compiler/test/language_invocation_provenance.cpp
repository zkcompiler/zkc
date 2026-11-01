#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Project.h"
#include <algorithm>
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
  return cases.result();
}
