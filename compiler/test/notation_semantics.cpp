#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(StringRef text) {
  auto input = capture({{"m", "module m;" + text.str(), {}}});
  if (!input)
    return input.takeError();
  return analyze(*input).checkedProject();
}
const Declaration &decl(const CheckedProject &project, StringRef name) {
  for (const auto &value : project.declarations())
    if (value.qualifiedName == name)
      return value;
  throw std::runtime_error("missing declaration: " + name.str());
}
const CallBinding &lastBinding(const Declaration &value) {
  require(value.body && !value.body->operations.empty() &&
              value.body->operations.back().binding.has_value(),
          "call binding is missing");
  return *value.body->operations.back().binding;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  const std::string field = "domain F=field(\"bls12-381.fr\");";
  cases.run("prefix and postfix calls retain unary descriptors", [&] {
    auto project = take(check(field + R"(
      math fn identity(x:F)->F{return x;}
      operator prefix(80) ⊖ = identity;
      operator postfix(80) ⊗ = identity;
      fn before(x:F)->F{return ⊖x;}
      fn after(x:F)->F{return x⊗;}
    )"));
    for (StringRef name : {"m::before", "m::after"}) {
      const auto &binding = lastBinding(decl(project, name));
      require(binding.notation && binding.notation->arity == 1 &&
                  binding.operands.size() == 1 &&
                  binding.target.declaration.index ==
                      decl(project, "m::identity").id.index,
              "unary call changed its target or arity");
      require(binding.notation->position ==
                  (name == "m::before" ? NotationDescriptor::Position::Prefix
                                       : NotationDescriptor::Position::Postfix),
              "unary call lost its position");
    }
  });
  cases.run(
      "local prefix replacement preserves the inherited infix family", [&] {
        auto project = take(check(field + R"(
      math fn identity(x:F)->F{return x;}
      math fn twice(x:F)->F{return x+x;}
      math fn difference(x:F,y:F)->F{return x-y;}
      operator prefix(80) ⊖ = identity;
      operator infixl(65) ⊖ = difference;
      fn f(x:F,y:F)->F{
        operator prefix(80) ⊖ = twice;
        return ⊖x ⊖ y;
      }
    )"));
        const auto &body = *decl(project, "m::f").body;
        require(
            body.operations.size() == 2 && body.operations.front().binding &&
                body.operations.front().binding->target.declaration.index ==
                    decl(project, "m::twice").id.index &&
                lastBinding(decl(project, "m::f")).target.declaration.index ==
                    decl(project, "m::difference").id.index,
            "local prefix replaced another position's callable family");
      });
  cases.run(
      "a failing local notation target cannot fall back to an outer target",
      [&] {
        refuses(check(field + R"(
      math fn outer(x:F)->F{return x;}
      fn inner(x:index)->index{return x;}
      operator prefix(80) ⊖ = outer;
      fn f(x:F)->F{operator prefix(80) ⊖ = inner;return ⊖x;}
    )"),
                "source.operator");
      });
  cases.run("delimited calls and named calls retain the same selected target",
            [&] {
              auto project = take(check(field + R"(
      math fn combine(a:F,b:F,c:F)->F{return a+b+c;}
      notation ⟪ a,b,c ⟫ = combine(a,b,c);
      fn named(a:F,b:F,c:F)->F{return combine(a,b,c);}
      fn written(a:F,b:F,c:F)->F{return ⟪a,b,c⟫;}
    )"));
              const auto &named = lastBinding(decl(project, "m::named"));
              const auto &written = lastBinding(decl(project, "m::written"));
              require(!named.notation && written.notation &&
                          written.notation->arity == 3 &&
                          written.notation->closing == "⟫" &&
                          named.target.declaration.index ==
                              written.target.declaration.index &&
                          named.arguments == written.arguments &&
                          written.operands.size() == 3,
                      "delimiter introduced another callable meaning");
              for (unsigned i = 0; i < written.operands.size(); ++i)
                require(named.operands[i].index == written.operands[i].index,
                        "delimiter changed authored operand order");
            });
  cases.run(
      "delimited operands produce effects exactly once in authored order", [&] {
        auto project = take(check(R"(
      fn first(x:index)->index{return x+1;}
      fn second(x:index)->index{return x+2;}
      fn third(x:index)->index{return x+3;}
      fn combine(a:index,b:index,c:index)->(index,index,index){return(c,a,b);}
      notation ⟪ a,b,c ⟫ = combine(a,b,c);
      fn f(x:index)->(index,index,index){return ⟪first(x),second(x),third(x)⟫;}
    )"));
        const auto &body = *decl(project, "m::f").body;
        const std::vector<std::string> expected{"m::first", "m::second",
                                                "m::third", "m::combine"};
        require(body.mayStop && body.operations.size() == expected.size(),
                "operand effects were duplicated or lost");
        for (unsigned i = 0; i < expected.size(); ++i) {
          const auto *call =
              std::get_if<HelperCall>(&body.operations[i].action);
          require(call &&
                      call->callee.index == decl(project, expected[i]).id.index,
                  "operand effects were emitted out of authored order");
          if (i < 3)
            require(lastBinding(decl(project, "m::f")).operands[i].index ==
                        body.operations[i].results.front().index,
                    "notation did not consume the once-evaluated operand");
        }
        const auto &wrapper = *decl(project, "m::combine").body;
        const auto *tuple =
            std::get_if<Construct>(&wrapper.operations.back().action);
        require(tuple && tuple->operands.size() == 3 &&
                    tuple->operands[0].index == 2 &&
                    tuple->operands[1].index == 0 &&
                    tuple->operands[2].index == 1,
                "wrapper did not retain its explicit parameter permutation");
      });
  cases.run("unary notation preserves affine consumption", [&] {
    const std::string source = R"(
      struct Token:Drop {value:bool}
      fn move(x:Token)->Token{return x;}
      operator prefix(80) ⊖ = move;
    )";
    take(check(source + "fn good(x:Token)->Token{return ⊖x;}"));
    refuses(check(source + "fn bad(x:Token){let y=⊖x;return(y,x);}"),
            "source.move");
  });
  cases.run("delimiter notation preserves affine consumption", [&] {
    const std::string source = R"(
      struct Token:Drop {value:bool}
      fn gather(a:Token,b:Token,c:Token)->(Token,Token,Token){return(a,b,c);}
      notation ⟪ a,b,c ⟫ = gather(a,b,c);
    )";
    take(check(source + "fn good(a:Token,b:Token,c:Token){return ⟪a,b,c⟫;}"));
    refuses(check(source + "fn bad(a:Token,b:Token){return ⟪a,b,a⟫;}"),
            "source.move");
  });
  cases.run("delimiter literal inference remains one statement problem", [&] {
    auto project = take(check(field + R"(
      math fn fields(a:F,b:F,c:F)->F{return a+b+c;}
      fn indices(a:index,b:index,c:index)->index{return a+b+c;}
      notation ⟪ a,b,c ⟫ = fields(a,b,c);
      notation ⟪ a,b,c ⟫ = indices(a,b,c);
      fn f()->index{return ⟪1,2,3⟫;}
    )"));
    require(lastBinding(decl(project, "m::f")).target.declaration.index ==
                decl(project, "m::indices").id.index,
            "result context failed to constrain literal input types");
  });
  cases.run(
      "delimiter result context cannot choose between fixed-input meanings",
      [&] {
        refuses(check(field + R"(
      math fn fields(a:F,b:F,c:F)->F{return a+b+c;}
      math fn boolean(a:F,b:F,c:F)->bool{return true;}
      notation ⟪ a,b,c ⟫ = fields(a,b,c);
      notation ⟪ a,b,c ⟫ = boolean(a,b,c);
      fn f(a:F,b:F,c:F)->F{return ⟪a,b,c⟫;}
    )"),
                "source.operator");
      });
  cases.run("unary execution modes do not resolve semantic ambiguity", [&] {
    refuses(check(field + R"(
      math fn total(x:F)->F{return x;}
      fn stopping(x:F)->F{stop "reject";}
      operator prefix(80) ⊖ = total;
      operator prefix(80) ⊖ = stopping;
      math fn f(x:F)->F{return ⊖x;}
    )"),
            "source.operator");
  });
  cases.run("selected local notation obeys mathematical mode restrictions",
            [&] {
              refuses(check(field + R"(
      fn ordered(x:F)->F{return x;}
      operator prefix(80) ⊖ = ordered;
      math fn f(x:F)->F{return ⊖x;}
    )"),
                      "source.mode");
            });
  for (StringRef declaration :
       {"operator prefix(80) ⊖ = binary;", "operator postfix(80) ⊖ = binary;",
        "operator infixl(65) ⊖ = unary;",
        "notation ⟪ a,b,c ⟫ = binary(a,b,c);"})
    cases.run("notation target arity: " + declaration, [&] {
      refuses(check(field + R"(
        math fn unary(x:F)->F{return x;}
        math fn binary(x:F,y:F)->F{return x+y;}
      )" + declaration.str()),
              "source.operator");
    });
  cases.run("custom equality-like notation may return a field", [&] {
    take(check(field + R"(
      math fn choose(a:F,b:F)->F{return a;}
      operator infix(50) ≡ = choose;
      fn f(a:F,b:F)->F{return a ≡ b;}
    )"));
    refuses(check(field + R"(
      math fn choose(a:F,b:F)->F{return a;}
      operator == = choose;
    )"),
            "source.operator");
  });
  cases.run(
      "Boolean elaboration preserves notation scopes in generated regions",
      [&] {
        take(check(R"(
      math fn identity(x:bool)->bool{return x;}
      operator prefix(80) ⊖ = identity;
      fn f(a:bool,b:bool)->bool{return a && ⊖b;}
      protocol Run roles(P)(a:bool@P,b:bool@P)->(out:bool@P){return a && ⊖b;}
    )"));
      });
  cases.run(
      "component notation keeps its definition binding during specialization",
      [&] {
        auto project = take(check(field + R"(
      interface Unary<T:Field>{math fn apply(x:T)->T;}
      component Identity<T:Field>:Unary<T>{math fn apply(x:T)->T{return x;}}
      math fn invoke<T:Field,A:Unary<T>>(x:T)->T{
        operator prefix(80) ⊖ = A::apply;
        return ⊖x;
      }
      math fn other(x:F)->F{return x+x;}
      protocol Run roles(P)(x:F@P)->(out:F@P){
        operator prefix(80) ⊖ = other;
        return invoke<T=F,A=Identity<F>>(x);
      }
      run Demo=Run;
    )"));
        const auto &definition = lastBinding(decl(project, "m::invoke"));
        auto closed = take(closeEntry(project, "m::Demo"));
        unsigned retained = 0;
        for (const auto &value : closed.declarations())
          if (value.body)
            for (const auto &op : value.body->operations)
              if (op.binding && op.binding->notation) {
                ++retained;
                require(op.binding->notation == definition.notation &&
                            op.binding->family == definition.family &&
                            op.binding->target.declaration.index ==
                                definition.target.declaration.index,
                        "specialization rebound definition-site notation");
              }
        require(retained == 1,
                "specialization lost its retained notation binding");
      });
  return cases.result();
}
