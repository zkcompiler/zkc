#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Transforms/RegionUtils.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Language/DeclarationIndex.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/Json.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject checked(StringRef code) {
  return take(analyze(take(capture({{"m", code.str(), "custody.zkc"}})))
                  .checkedProject());
}
CheckedOriginal original(StringRef code) {
  return take(prepareOriginal(take(closeNativeRun(checked(code), "m::Run"))));
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  auto found = llvm::find_if(project.declarations(), [&](const auto &decl) {
    return decl.name == name;
  });
  require(found != project.declarations().end(), "missing declaration");
  return *found;
}
void withModule(const CheckedOriginal &source,
                function_ref<void(mlir::ModuleOp)> body) {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
  require(bool(module), "original did not parse");
  body(*module);
}
bool contract(exec::ApplyOp op, StringRef name) {
  auto binding = mlir::dyn_cast_or_null<runtime::BindingOp>(
      mlir::SymbolTable::lookupNearestSymbolFrom(op, op.getBindingAttr()));
  return binding && binding.getContract() == name;
}
void accepted(const CheckedOriginal &source) {
  auto view = take(readInterface(source.bytes(), source.interfaceJson()));
  if (auto error = compareInterface(source.entry(), view))
    throw std::runtime_error(toString(std::move(error)));
  take(admitOriginal(source.entry(), source.bytes(), source.interfaceJson()));
  withModule(source, [&](mlir::ModuleOp module) {
    auto exported = take(protocol::exportStructuredSource(
        source.bytes(), source.entry().protocol().symbol,
        *module.getContext()));
    require(!exported.bytes.empty(), "custody lost its structured descriptor");
  });
  for (auto options :
       {EntryOptions{}, EntryOptions{false}, EntryOptions{true, true}})
    take(compileEntry(source, options));
}
const char *empty = R"(
module m;
#[linear] struct Ticket<N:nat>{empty:(),phantom:[bool;0]}
fn make()->Ticket<1>{return Ticket<1>{empty:(),phantom:[]};}
fn forward(x:Ticket<1>)->Ticket<1>{return x;}
fn finish(x:Ticket<1>)->(){consume x;return ();}
protocol Run roles(P)()->(){
 let x@P=make();let y@P=forward(x);let done@P=finish(y);return();
}
)";
} // namespace
int main() {
  Cases cases;
  cases.run("explicit restrictions retain empty and nested nominal units", [] {
    auto project = checked(R"(
module m;
#[linear] struct Linear<N:nat>{empty:(),phantom:[bool;0]}
#[affine] struct Affine{}
#[linear] struct Nested{child:Linear<1>,empty:()}
struct Shared{private:bool,empty:()}
fn one(x:Linear<1>)->Linear<1>{return x;}
fn two(x:Linear<2>)->Linear<2>{return x;}
fn affine(x:Affine)->Affine{return x;}
fn nested(x:Nested)->Nested{return x;}
fn shared(x:Shared)->Shared{return x;}
)");
    Layouts layouts(project);
    auto layout = [&](StringRef name) {
      return take(layouts.get(named(project, name).outputs.front().type));
    };
    auto one = layout("one"), two = layout("two"), affine = layout("affine"),
         nested = layout("nested"), shared = layout("shared");
    require(one->custody && one->leaves.size() == 1 &&
                one->fields.size() == 2 && one->fields[0].offset == 1 &&
                one->fields[1].offset == 1 &&
                one->fields[0].layout->leaves.empty() &&
                one->fields[1].layout->leaves.empty() &&
                !one->permissions.copy && !one->permissions.drop,
            "empty linear schema or permissions were erased");
    require(*one->leaves[0].data() != *two->leaves[0].data(),
            "phantom argument did not distinguish custody");
    require(affine->custody && affine->leaves.size() == 1 &&
                !affine->permissions.copy && affine->permissions.drop,
            "empty affine wrapper lost its restriction");
    require(nested->custody && nested->leaves.size() == 2 &&
                nested->fields[0].offset == 1 &&
                *nested->leaves[0].data() != *nested->leaves[1].data(),
            "nested wrappers lost separate nominal units");
    require(!shared->custody && shared->permissions.copy &&
                shared->permissions.drop && !shared->constructible,
            "private shared payload was confused with custody");
  });
  cases.run(
      "public observations do not seal or discharge restricted wrappers", [] {
        for (StringRef restriction : {"linear", "affine"}) {
          const auto declarations =
              "module m; module home {#[" + restriction.str() + R"(]
 pub struct Ticket {pub value:bool}
 pub fn make()->Ticket{return Ticket{value:true};}
 pub fn finish(x:Ticket)->(){consume x;return ();}
}
)";
          auto project = checked(declarations + R"(
fn observe(x:home::Ticket)->(home::Ticket,bool){let value=x.value;return(x,value);}
)");
          const auto &ticket = named(project, "Ticket");
          require(!ticket.sealed && ticket.resource.has_value(),
                  "resource restriction acquired sealing");
          Layouts layouts(project);
          auto layout =
              take(layouts.get(Type(Type::Kind::Record, "m::home::Ticket")));
          require(!layout->sealed && !layout->constructible &&
                      layout->custodyCount == 1,
                  "public observations granted constructor or erased custody");
          accepted(original(declarations + R"(
fn observe(x:home::Ticket)->(home::Ticket,bool){let value=x.value;return(x,value);}
protocol Run roles(P)()->(){
 let x@P=home::make();let observed@P=observe(x);
 let done@P=home::finish(observed.0);return();
}
)"));
          auto reject = [&](StringRef code, StringRef diagnostic) {
            refuses(analyze(take(capture({{"m", declarations + code.str(),
                                           "restriction.zkc"}})))
                        .checkedProject(),
                    diagnostic);
          };
          reject("fn forge()->home::Ticket{return home::Ticket{value:true};}",
                 "source.private");
          reject("fn open(x:home::Ticket)->(bool,){return unpack(x);}",
                 "source.private");
          if (restriction == "linear")
            reject("fn forget(x:home::Ticket)->bool{return x.value;}",
                   "source.drop");
        }
      });
  cases.run("explicit sealing still prevents public field access", [] {
    refuses(analyze(take(capture({{"m", R"(
module m;
module home {#[sealed] #[linear] pub struct Ticket {pub value:bool}}
fn observe(x:home::Ticket)->(home::Ticket,bool){let value=x.value;return(x,value);}
)",
                                   "sealed.zkc"}})))
                .checkedProject(),
            "source.private");
  });
  cases.run(
      "creation calls consumption and independent interfaces retain units",
      [] { accepted(original(empty)); });
  cases.run("unpacking retires outer custody and transfers mandatory children",
            [] {
              accepted(original(R"(
module m;
#[linear] struct Child{}
#[linear] struct Parent{left:Child,right:Child,empty:()}
fn make()->Parent{return Parent{left:Child{},right:Child{},empty:()};}
fn forward(x:Parent)->Parent{return x;}
fn finish(x:Parent)->(){
 let children=unpack(x);consume children.0;consume children.1;return ();
}
protocol Run roles(P)(n:index@P)->(){
 let mut current@P=make();
 for _ in 0..n roles(P) max 3{let next@P=forward(current);current=next;}
 let done@P=finish(current);return();
}
)"));
            });
  cases.run(
      "interface custody omission duplication and phantom changes refuse", [] {
        // The selected protocol has no record ports; use an internally created
        // output to expose the complete schema without allowing root
        // fabrication.
        auto exported = original(R"(
module m;
#[linear] struct Ticket<N:nat>{empty:(),phantom:[bool;0]}
fn make()->Ticket<1>{return Ticket<1>{empty:(),phantom:[]};}
protocol Run roles(P)()->(out:Ticket<1>@P){let x@P=make();return x;}
)");
        for (unsigned mutation = 0; mutation != 4; ++mutation) {
          auto document = take(json::parse(exported.interfaceJson()));
          auto &schema = *document.getAsObject()
                              ->getArray("protocols")
                              ->front()
                              .getAsObject()
                              ->getArray("outputs")
                              ->front()
                              .getAsObject()
                              ->getObject("schema");
          if (mutation == 0)
            schema["custody"] = false;
          else if (mutation == 1)
            schema.getArray("leaves")->push_back(
                schema.getArray("leaves")->front());
          else if (mutation == 2)
            schema["type"] = "different phantom instance";
          else
            schema.getArray("fields")->pop_back();
          auto error = checkInterface(exported, printJson(document));
          require(bool(error), "mutated custody schema escaped comparison");
          require(StringRef(toString(std::move(error)))
                      .contains("source.interface"),
                  "unexpected interface refusal");
        }
      });
  cases.run(
      "candidate sealing metadata remains bound to authored declarations", [] {
        auto source = original(empty);
        withModule(source, [&](mlir::ModuleOp module) {
          unsigned changes = 0;
          module.walk([&](mlir::Operation *op) {
            auto attribute = op->getAttr("source_declarations");
            if (!attribute)
              return;
            auto declarations = take(exportDeclarationData(attribute));
            auto &record = *declarations.getAsArray()
                                ->front()
                                .getAsArray()
                                ->front()
                                .getAsArray();
            record[2] = !*record[2].getAsBoolean();
            op->setAttr(
                "source_declarations",
                take(importDeclarationData(module.getContext(), declarations)));
            ++changes;
          });
          require(changes == 1, "missing exact retained declaration owner");
          require(succeeded(mlir::verify(module)),
                  "sealing mutation must remain formed");
          refuses(compareOriginal(source.entry(), module),
                  "source.correspondence");
        });
      });
  cases.run(
      "missing native consumption refuses independent body comparison", [] {
        auto source = original(empty);
        withModule(source, [&](mlir::ModuleOp module) {
          exec::ApplyOp consume;
          module.walk([&](exec::ApplyOp op) {
            if (contract(op, "resource_unit.consume"))
              consume = op;
          });
          require(bool(consume), "empty record emitted no native consumption");
          auto dispatch = mlir::cast<exec::DispatchOp>(consume->getNextNode());
          auto *continuation = dispatch.getReturned();
          auto *before = consume->getBlock();
          auto *region = consume->getParentRegion();
          mlir::IRRewriter rewriter(module.getContext());
          rewriter.eraseOp(dispatch);
          rewriter.eraseOp(consume);
          rewriter.mergeBlocks(continuation, before);
          (void)mlir::eraseUnreachableBlocks(rewriter, *region);
          require(succeeded(mlir::verify(module)),
                  "missing consume must be formed");
          refuses(compareOriginal(source.entry(), module),
                  "source.correspondence");
        });
      });
  cases.run("extra native creation refuses actual candidate admission", [] {
    auto source = original(empty);
    withModule(source, [&](mlir::ModuleOp module) {
      exec::ApplyOp create;
      module.walk([&](exec::ApplyOp op) {
        if (contract(op, "resource_unit.create"))
          create = op;
      });
      require(bool(create), "empty record emitted no native creation");
      mlir::OpBuilder builder(create);
      builder.clone(*create);
      refuses(compareOriginal(source.entry(), module), "target.admission");
    });
  });
  cases.run("identity calls preserve local and common zero-trip carries", [] {
    accepted(original(R"(
module m;
#[linear] struct Ticket{}
fn make()->Ticket{return Ticket{};}
fn forward(x:Ticket)->Ticket{return x;}
fn local_loop(x:Ticket,n:index)->Ticket{
 let mut current=x;for _ in 0..n{current=forward(current);}return current;
}
fn finish(x:Ticket)->(){consume x;return ();}
protocol Run roles(P)(n:index@P)->(){
 let mut current@P=make();
 for _ in 0..n roles(P) max 3 {let next@P=local_loop(current,n);current=next;}
 let done@P=finish(current);return();
}
)"));
  });
  cases.run("stopped arms supply no custody while continuing arms forward it",
            [] {
              accepted(original(R"(
module m;
#[linear] struct Ticket{}
fn make()->Ticket{return Ticket{};}
fn step(x:Ticket,go:bool)->Ticket{
 return if go{x}else{stop "reject";};
}
fn finish(x:Ticket)->(){consume x;return ();}
protocol Run roles(P)(n:index@P,go:bool@P)->(){
 let mut current@P=make();
 for _ in 0..n roles(P) max 3 {let next@P=step(current,go);current=next;}
 let done@P=finish(current);return();
}
)"));
            });
  cases.run("explicit inspection and repacking preserve exact loop successors",
            [] {
              accepted(original(R"(
module m;
#[linear] struct Ticket<N:nat>{value:bool,empty:(),phantom:[bool;0]}
fn make()->Ticket<1>{return Ticket<1>{value:true,empty:(),phantom:[]};}
fn advance(x:Ticket<1>,go:bool)->Ticket<1>{
 let opened=inspect_record(x);
 return if go{repack_record(opened.0,opened.1)}else{stop "reject";};
}
fn local_loop(x:Ticket<1>,n:index,go:bool)->Ticket<1>{
 let mut current=x;for _ in 0..n{current=advance(current,go);}return current;
}
fn finish(x:Ticket<1>)->(){let payload=unpack(x);return ();}
protocol Run roles(P)(n:index@P,go:bool@P)->(){
 let mut current@P=make();
 for _ in 0..n roles(P) max 3 {let next@P=local_loop(current,n,go);current=next;}
 let done@P=finish(current);return();
}
)"));
            });
  cases.run("empty reconstruction retains a unit without creating a fresh root",
            [] {
              auto source = original(R"(
module m;
#[linear] struct Ticket{}
fn make()->Ticket{return Ticket{};}
fn advance(x:Ticket)->Ticket{let opened=inspect_record(x);return repack_record(opened.0,());}
fn finish(x:Ticket)->(){consume x;return ();}
protocol Run roles(P)(n:index@P)->(){
 let mut current@P=make();
 for _ in 0..n roles(P) max 3 {let next@P=advance(current);current=next;}
 let done@P=finish(current);return();
}
)");
              accepted(source);
              withModule(source, [&](mlir::ModuleOp module) {
                unsigned creates = 0, passes = 0;
                module.walk([&](exec::ApplyOp op) {
                  creates += contract(op, "resource_unit.create");
                  passes += contract(op, "resource_unit.pass");
                });
                require(creates == 1 && passes == 1,
                        "empty successor silently created a fresh resource");
              });
            });
  cases.run("inspection is a consuming observation with a required successor",
            [] {
              refuses(analyze(take(capture({{"m", R"(
module m;
#[linear] struct Ticket{value:bool}
fn invalid(x:Ticket)->bool{let observed=inspect_record(x);return observed.1.0;}
)",
                                             "custody.zkc"}})))
                          .checkedProject(),
                      "source.drop");
              refuses(analyze(take(capture({{"m", R"(
module m;
#[linear] struct Ticket{value:bool}
fn invalid(x:Ticket)->(Ticket,Ticket){let observed=inspect_record(x);return(x,observed.0);}
)",
                                             "custody.zkc"}})))
                          .checkedProject(),
                      "source.move");
            });
  cases.run("custody reconstruction cannot erase noncopyable child obligations",
            [] {
              refuses(analyze(take(capture({{"m", R"(
module m;
#[linear] struct Child{}
#[linear] struct Parent{child:Child}
fn invalid(x:Parent)->Parent{let observed=inspect_record(x);return observed.0;}
)",
                                             "custody.zkc"}})))
                          .checkedProject(),
                      "source.permission");
            });
  for (StringRef operation : {"inspect_record(x)", "repack_record(x,())"}) {
    cases.run("succession rejects an unrestricted wrapper: " + operation, [&] {
      refuses(
          analyze(take(capture(
                      {{"m",
                        "module m;struct Plain{}fn invalid(x:Plain)->(){let "
                        "unused=" +
                            operation.str() + ";return ();}",
                        "custody.zkc"}})))
              .checkedProject(),
          "source.type");
    });
    cases.run(
        "succession requires home constructor authority: " + operation, [&] {
          refuses(
              analyze(take(capture(
                          {{"home", "module home;#[affine]pub struct Ticket{}",
                            "home.zkc"},
                           {"m",
                            "module m;use home::{Ticket};fn "
                            "invalid(x:Ticket)->(){let "
                            "unused=" +
                                operation.str() + ";return ();}",
                            "custody.zkc"}})))
                  .checkedProject(),
              "source.private");
        });
  }
  cases.run("authorized specification fields account for the custody prefix",
            [] {
              accepted(original(R"(
module m;
#[linear] struct Ticket{value:bool,empty:()}
relation Truth(statement value:bool){return value;}
fn make()->Ticket{return Ticket{value:true,empty:()};}
fn finish(x:Ticket)->(){consume x;return ();}
protocol Forward roles(P)(x:Ticket@P)->(out:Ticket@P) where () spec {
 continuation obligation=Truth(in.x.value) residual Truth(out.out.value);
}{return x;}
protocol Run roles(P)()->(){
 let x@P=make();let y=Forward(x);let done@P=finish(y);return();
}
)"));
            });
  cases.run("actual same-typed successor operands cannot be exchanged", [] {
    auto source = original(R"(
module m;
#[linear] struct Ticket{}
fn make()->Ticket{return Ticket{};}
fn advance(x:Ticket,y:Ticket)->(Ticket,Ticket){return(repack_record(x,()),repack_record(y,()));}
fn finish(x:Ticket)->(){consume x;return ();}
protocol Run roles(P)()->(){
 let x@P=make();let y@P=make();let pair@P=advance(x,y);
 let a@P=finish(pair.0);let b@P=finish(pair.1);return();
}
)");
    withModule(source, [&](mlir::ModuleOp module) {
      SmallVector<exec::ApplyOp> passes;
      module.walk([&](exec::ApplyOp op) {
        if (contract(op, "resource_unit.pass"))
          passes.push_back(op);
      });
      require(passes.size() == 2, "fixture needs two exact successors");
      auto first = passes[0].getInputs().front();
      passes[0].getInputsMutable().assign(passes[1].getInputs());
      passes[1].getInputsMutable().assign(first);
      require(succeeded(mlir::verify(module)),
              "exchanged roots should preserve native use/shape formation");
      refuses(compareOriginal(source.entry(), module), "source.correspondence");
    });
  });
  cases.run("fresh same-typed replacement cannot establish an exact loop root",
            [] {
              auto project = checked(R"(
module m;
#[linear] struct Ticket{}
fn make()->Ticket{return Ticket{};}
fn fresh(x:Ticket)->Ticket{consume x;return Ticket{};}
fn finish(x:Ticket)->(){consume x;return ();}
protocol Run roles(P)(n:index@P)->(){
 let mut current@P=make();
 for _ in 0..n roles(P) max 3 {let next@P=fresh(current);current=next;}
 let done@P=finish(current);return();
}
)");
              refuses(prepareOriginal(take(closeNativeRun(project, "m::Run"))),
                      "mathematical-formation");
            });
  for (StringRef spelling : {"unpack", "inspect_record", "repack_record"}) {
    for (StringRef route : {"plain", "qualified", "method", "import"}) {
      cases.run(
          "authored homonym retains its declaration: " + spelling + "/" + route,
          [&] {
            std::string name = spelling.str();
            std::string code =
                "module m;struct Box{pub value:bool}fn " + name +
                "(x:Box)->bool{stop \"reject\";}fn run(x:Box)->bool{return ";
            if (route == "method")
              code += "x." + name + "()";
            else if (route == "qualified")
              code += "m::" + name + "(x)";
            else
              code += name + "(x)";
            code += ";}";
            CheckedProject project =
                route == "import"
                    ? take(analyze(take(capture(
                                       {{"home",
                                         "module home;pub struct Box{pub "
                                         "value:bool}pub fn " +
                                             name +
                                             "(x:Box)->bool{stop \"reject\";}",
                                         "home.zkc"},
                                        {"m",
                                         "module m;use home::{Box," + name +
                                             "};fn run(x:Box)->bool{return " +
                                             name + "(x);}",
                                         "main.zkc"}})))
                               .checkedProject())
                    : checked(code);
            const auto &run = named(project, "run");
            const auto &target = named(project, spelling);
            require(!project.declarationIndex().association(target.id),
                    "captured homonym acquired an installed association");
            bool found = false;
            for (const auto &op : run.body->operations)
              if (const auto *call = std::get_if<HelperCall>(&op.action))
                found |= call->callee.index == target.id.index && op.binding &&
                         !op.binding->installedSignature;
            require(found,
                    "declared guard was bypassed by intrinsic interception");
          });
    }
    cases.run("scoped homonym remains a callback: " + spelling, [&] {
      auto project = checked(
          "module m;fn apply(" + spelling.str() +
          ":fn(bool)->bool effects(stop),x:bool)->bool effects(stop){return " +
          spelling.str() +
          "(x);}protocol Run roles(P)(x:bool@P)->(out:bool@P){let "
          "y@P=apply(fn(v)=>{require v;v},x);return y;}");
      auto source =
          take(prepareOriginal(take(closeNativeRun(project, "m::Run"))));
      accepted(source);
    });
  }
  cases.run("only rule-elaborated installed definitions are bodiless", [] {
    auto project = checked("module m;fn value(x:bool)->bool{return x;}");
    const auto &index = project.declarationIndex();
    auto id = [&](StringRef path) {
      auto found = index.canonical(path);
      require(bool(found), "missing declaration " + path.str());
      return *found;
    };
    for (StringRef path :
         {"zkc::records::unpack", "zkc::records::inspect_record",
          "zkc::records::repack_record", "zkc::prelude::Random"})
      require(index.ruleAssociation(id(path)) &&
                  index.ruleAssociation(id(path)) ==
                      index.association(id(path)),
              "rule association lost: " + path.str());
    auto primitive = id("zkc::prelude::field_add");
    require(index.association(primitive) && !index.ruleAssociation(primitive),
            "installed primitive became bodiless");
    require(!index.ruleAssociation(id("m::value")),
            "written declaration acquired a rule association");
  });
  cases.run(
      "installed aliases preserve canonical association and caller authority",
      [] {
        auto project = checked(R"(
module m;
use zkc::records as records;
use zkc::records::{inspect_record,repack_record};
#[linear] struct Ticket<N:nat>{value:bool}
fn make()->Ticket<7>{return Ticket<7>{value:true};}
fn advance(x:Ticket<7>)->Ticket<7>{let parts=inspect_record(x);return repack_record(parts.0,parts.1);}
fn finish(x:Ticket<7>)->(){let parts=records::unpack(x);return ();}
protocol Run roles(P)()->(){let x@P=make();let y@P=advance(x);let done@P=finish(y);return ();}
)");
        unsigned calls = 0;
        for (const auto &decl : project.declarations())
          if (decl.body)
            for (const auto &op : decl.body->operations)
              if (op.binding && op.binding->installedSignature) {
                ++calls;
                require(op.binding->lexicalOwner &&
                            op.binding->lexicalOwner->index == decl.id.index &&
                            project.declarationIndex().association(
                                op.binding->target.declaration),
                        "intrinsic lost canonical target or lexical caller");
              }
        require(calls == 3, "installed invocation coverage differs");
        accepted(
            take(prepareOriginal(take(closeNativeRun(project, "m::Run")))));
      });
  for (unsigned mutation = 0; mutation < 5; ++mutation)
    cases.run(
        "independent intrinsic witness refuses mutation " + Twine(mutation),
        [&] {
          auto project = checked(R"(
module m;#[linear] struct Ticket{}fn advance(x:Ticket)->Ticket{let p=zkc::records::inspect_record(x);return zkc::records::repack_record(p.0,());}
)");
          auto &body = const_cast<Body &>(*named(project, "advance").body);
          auto at = llvm::find_if(body.operations, [](const auto &op) {
            return op.binding && op.binding->installedSignature;
          });
          require(at != body.operations.end(), "missing intrinsic witness");
          if (mutation == 0)
            at->binding.reset();
          if (mutation == 1)
            at->binding->lexicalOwner = at->binding->target.declaration;
          if (mutation == 2)
            at->binding->installedSignature =
                protocol::FrontendSignature::RecordUnpack;
          if (mutation == 3)
            at->binding->target.declaration = named(project, "advance").id;
          if (mutation == 4)
            std::get<Construct>(at->action).kind = Construct::Kind::Unpack;
          auto error = checkScopedElaboration(project);
          require(bool(error),
                  "independent witness accepted forged intrinsic invocation");
          require(namesIdentifier(toString(std::move(error)),
                                  "source.binding-witness"),
                  "wrong intrinsic mutation diagnostic");
        });
  for (StringRef operation :
       {"unpack(x)", "inspect_record(x)", "repack_record(x,())"})
    cases.run("intrinsic module grants no foreign constructor authority: " +
                  operation,
              [&] {
                auto captured = take(capture(
                    {{"home", "module home;#[linear] pub struct Ticket{}",
                      "home.zkc"},
                     {"m",
                      "module m;use "
                      "zkc::records::{unpack,inspect_record,repack_record};fn "
                      "foreign(x:home::Ticket)->(){let value=" +
                          operation.str() + ";stop \"reject\";}",
                      "main.zkc"}}));
                refuses(analyze(captured).checkedProject(), "source.private");
              });
  cases.run("installed marker signature drift independently refuses", [] {
    auto project = checked("module m;fn value(x:bool)->bool{return x;}");
    auto target =
        project.declarationIndex().canonical("zkc::records::inspect_record");
    require(bool(target), "missing installed intrinsic declaration");
    auto &decl =
        const_cast<Declaration &>(project.declarations()[target->index]);
    decl.outputs.front().type = Type(Type::Kind::Unit);
    auto error = checkScopedElaboration(project);
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "source.installation"),
            "independent checker accepted installed signature drift");
  });
  for (StringRef name : {"unpack", "inspect_record", "repack_record"})
    cases.run("domain factory homonym retains its category: " + name, [&] {
      auto project = checked(
          "module m;pub domain fn " + name.str() +
          "(lo:index,hi:index)->domain<index>=domain(\"range\");"
          "fn "
          "fold(rows:domain<index>,initial:index,step:fn(index,item:index)->"
          "index effects(stop) where item_from(item,rows))->index "
          "effects(stop)=finite(\"local.fold\");"
          "fn run(n:index)->index{let rows=" +
          name.str() +
          "(index<0>(),n);return fold(rows,index<0>(),fn(s,item)=>item);}");
      require(!named(project, "run").body->descriptorBindings.empty(),
              "domain homonym was replaced by a record intrinsic");
    });
  cases.run(
      "generic and scoped custody invocations preserve lexical authority", [] {
        auto project = checked(R"(
module m;
#[linear] struct Ticket<N:nat>{value:bool}
fn apply<N:nat>(x:Ticket<N>,body:fn(Ticket<N>)->Ticket<N> effects(stop))->Ticket<N> effects(stop){return body(x);}
fn advance<N:nat>(x:Ticket<N>)->Ticket<N>{return apply(x,fn(value)=>{let parts=zkc::records::inspect_record(value);zkc::records::repack_record(parts.0,parts.1)});}
fn make()->Ticket<3>{return Ticket<3>{value:true};}
fn finish(x:Ticket<3>)->(){let fields=zkc::records::unpack(x);return ();}
protocol Run roles(P)()->(){let x@P=make();let y@P=advance(x);let done@P=finish(y);return ();}
)");
        auto entry = take(closeNativeRun(project, "m::Run"));
        accepted(take(prepareOriginal(entry)));
        bool changed = false;
        for (const auto &decl : entry.declarations())
          if (decl.origin && decl.body)
            for (auto &op : const_cast<Body &>(*decl.body).operations)
              if (!changed && op.binding && op.binding->installedSignature) {
                op.binding->lexicalOwner = op.binding->target.declaration;
                changed = true;
              }
        require(changed, "closed intrinsic authority was not retained");
        auto error = checkScopedSpecialization(entry);
        require(bool(error) && namesIdentifier(toString(std::move(error)),
                                               "source.scoped-specialization"),
                "closed intrinsic accepted changed lexical authority");
      });
  for (bool services : {false, true})
    cases.run(
        services ? "protocol invocation rejects changed service root witness"
                 : "protocol invocation rejects changed role witness",
        [&] {
          auto project = checked(R"(
module m;domain F=field("bls12-381.fr");
protocol relay roles(A,B)(x:bool@A,coins:Random<F>@B)->(out:bool@A){return x;}
protocol Run roles(P,V)(x:bool@P,coins:Random<F>@V)->(out:bool@P){let y@P=relay roles(P,V)(x,coins);return y;}
)");
          auto &body = const_cast<Body &>(*named(project, "Run").body);
          auto at = llvm::find_if(body.operations, [](const auto &op) {
            return std::holds_alternative<ProtocolApplication>(op.action);
          });
          require(
              at != body.operations.end() && at->binding &&
                  at->binding->roles == std::vector<unsigned>({0, 1}) &&
                  at->binding->services.size() == 1,
              "protocol application lacks common typed invocation evidence");
          if (services)
            at->binding->services.front().index = 99;
          else
            std::swap(at->binding->roles[0], at->binding->roles[1]);
          auto error = checkScopedElaboration(project);
          require(bool(error) && namesIdentifier(toString(std::move(error)),
                                                 "source.binding-witness"),
                  "independent checker accepted a forged protocol invocation");
        });
  for (StringRef name : {"unpack", "inspect_record", "repack_record"})
    cases.run(
        "a module homonym cannot become a record intrinsic: " + name, [&] {
          refuses(
              analyze(take(capture({{"m",
                                     "module m;module " + name.str() +
                                         "{}#[linear] struct Ticket{}fn "
                                         "bad(x:Ticket)->(){let y=" +
                                         name.str() + "(x);stop \"reject\";}",
                                     "homonym.zkc"}})))
                  .checkedProject(),
              "source.call");
        });
  return cases.result();
}
