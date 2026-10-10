#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"m", "module m;" + source.str(), {}}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
void compile(StringRef source) {
  auto entry = take(closeEntry(take(check(source)), "m::Demo"));
  auto original = take(prepareOriginal(entry));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
} // namespace
int main() {
  zkc::test::Cases cases;
  const std::string pair =
      "fn pair<A:Type,B:Type>(left:A,right:B){return(left,right);}";
  for (StringRef arguments :
       {"<A = bool>(right = n, left = x)", "<B=index>(x,right=n)",
        "<bool>(right=n,left=x)", "<B=_,A=bool>(right=n,left=x)",
        "(right // named argument\n = n, left = x)"})
    cases.run("named and inferred application: " + arguments, [&] {
      compile(pair + "fn f(x:bool,n:index)->(bool,index){return pair" +
              arguments.str() +
              " ;}"
              "protocol Run roles(P)(x:bool@P,n:index@P)->(r:(bool,index)@P){"
              "return f(n=n,x=x);}run Demo=Run;");
    });
  for (StringRef arguments :
       {"(missing=x,right=n)", "(left=x,left=x)", "(x,left=x)", "(right=n,x)",
        "(left=x)", "(x,n,x)"})
    cases.run("invalid value binding: " + arguments, [&] {
      refuses(check(pair + "fn f(x:bool,n:index){return pair" +
                    arguments.str() + ";}"),
              "source.call");
    });
  for (StringRef arguments :
       {"<Wrong=bool>", "<A=bool,A=bool>", "<bool,A=bool>", "<B=index,bool>",
        "<bool,index,bool>"})
    cases.run("invalid static binding: " + arguments, [&] {
      refuses(check(pair + "fn f(x:bool,n:index){return pair" +
                    arguments.str() + "(x,n);}"),
              "source.generic");
    });
  cases.run("explicit choices constrain inference", [&] {
    refuses(check(pair + "fn f(x:bool,n:index){return pair<A=index>(x,n);}"),
            "source.type");
    refuses(check("fn empty<N:nat>(){return ();}fn f(){return empty();}"),
            "source.inference");
  });
  cases.run("nested nominal static bindings and closed Entries", [] {
    compile(R"(
      struct Box<T:Type> {pub value:T}
      fn f(x:Box<T=bool>){return x.value;}
      protocol Run<T:Type+Copy+Drop+Share> roles(P)(x:T@P)->(r:T@P){return x;}
      run Demo=Run<T=Box<T=bool>>;
    )");
    take(check(R"(
      enum Choice<T:Type>{Some(T),None()}
      fn f(x:bool){return Choice::Some<T=bool>(x);}
    )"));
    refuses(check("struct Box<T:Type,N:nat>{pub value:T}fn "
                  "f(x:Box<T=bool>){return x;}"),
            "source.generic");
    refuses(check("struct Box<T:Type>{pub value:T}fn f(x:Box<T=_>){return x;}"),
            "source.inference");
    refuses(check("fn f(){return index<N=2>();}"), "source.call");
    refuses(check("fn f(x:bool){return unpack(value=x);}"), "source.call");
    refuses(check("enum C{Some(bool)}fn f(x:bool){return C::Some(value=x);}"),
            "source.call");
  });
  cases.run("interface names and concrete names bind their own contracts", [] {
    compile(R"(
      interface Ops<T:Type>{fn use_value(first:T,second:index)->(T,index);}
      component Impl<T:Type>:Ops<T>{
        fn use_value(a:T,b:index)->(T,index){return(a,b);}
      }
      fn abstract_call<C:Ops<bool>>(x:bool,n:index){
        return C::use_value(second=n,first=x);
      }
      fn concrete_call(x:bool,n:index){
        return Impl::use_value<T=bool>(b=n,a=x);
      }
      protocol Run roles(P)(x:bool@P,n:index@P)->(r:(bool,index)@P){
        let unused=concrete_call(n=n,x=x);
        return abstract_call<C=Impl<T=bool>>(n=n,x=x);
      }run Demo=Run;
    )");
    refuses(check(R"(
      interface Ops<T:Type>{fn f(x:T)->T;}
      fn wrapper<C:Ops<bool>>(x:bool){return C::f<T=bool>(x);}
    )"),
            "source.generic");
  });
  cases.run("named protocol service and data ports", [] {
    compile(R"(
      domain F=field("bls12-381.fr");
      protocol Draw<T:Field> roles(P)
          (first:Random<T>@P, flag:bool@P, second:Random<T>@P)->(r:T@P){
        let a=first.draw();let b=second.draw();return a-b;
      }
      protocol Run roles(P)(x:bool@P,a:Random<F>@P,b:Random<F>@P)->(r:F@P){
        let r=Draw(second=a,flag=x,first=b);return r;
      }run Demo=Run;
    )");
  });
  cases.run("named calls preserve participant constraints", [] {
    compile(R"(
      math fn select(a:bool,b:bool){return a;}
      fn id(x:bool){return x;}
      protocol Run roles(P,V)(a:bool@P,b:bool@V)->(r:bool@P){
        return select(b=b,a=id(a));
      }run Demo=Run;
    )");
    refuses(check(R"(
      fn both(a:bool,b:bool){return a==b;}
      protocol Run roles(P,V)(a:bool@P,b:bool@V)->(r:bool@P){
        return both(b=b,a=a);
      }
    )"),
            "source.roles");
    refuses(check(R"(
      math fn first(a:bool,b:bool){return a;}
      protocol Run roles(P,V)(a:bool@P,b:bool@V)->(r:bool@V){
        return first(b=b,a=a);
      }
    )"),
            "source.roles");
  });
  cases.run("written argument order governs affine moves", [] {
    const std::string declarations = R"(
      struct Ticket:Drop{}
      fn take(s:(Ticket,index))->index{let(t,n)=s;consume t;return n;}
      fn pair(a:index,b:index){return(a,b);}
    )";
    take(check(declarations +
               "fn work(s:(Ticket,index)){return pair(a=s.1,b=take(s));}"));
    refuses(check(declarations +
                  "fn work(s:(Ticket,index)){return pair(b=take(s),a=s.1);}"),
            "source.move");
  });
  cases.run("named statics retain heterogeneous nominal slots", [] {
    compile(R"(
      struct Box<T:Type,N:nat>{pub values:[T;N]}
      enum Choice<T:Type,N:nat>{Some([T;N]),None()}
      fn f(x:bool){
        let value=Box<N=2,T=bool>{values:[x,x]};
        let choice=Choice::Some<N=2,T=bool>(value.values);
        return match choice{Some(values)=>{values[0]},None()=>{false}};
      }
      protocol Run roles(P)(x:bool@P)->(r:bool@P){return f(x=x);}run Demo=Run;
    )");
    refuses(check("domain F=field(\"bls12-381.fr\");"
                  "protocol Run "
                  "roles(P)(coins:Random<F=F>@P)->(r:bool@P){return true;}"),
            "source.service");
    refuses(check("interface I{fn f(x:bool,x:bool)->bool;}"),
            "source.duplicate");
    refuses(check(R"(
      interface I{type Value:Drop;}
      component Impl<T:Type+Drop,N:nat>:I{type Value:Drop=[T;N];}
      fn f(x:bool){return Impl::Value<N=2,T=bool>([x,x]);}
    )"),
            "source.generic");
    refuses(check(R"(
      interface I{type Value:Drop;fn make(x:bool)->Value;}
      component Impl:I{
        type Value:Drop=bool;
        fn make(x:bool)->Value{return Value<Wrong=bool>(x);}
      }
    )"),
            "source.generic");
    compile(R"(
      domain F=field("bls12-381.fr");
      relation Same<T:Field>(statement x:T,witness y:T){return x==y;}
      protocol Run roles(P)(x:F@P)->(r:bool@P)
        spec{target claim=Same<T=F>(in.x,in.x) accept out.r;}
        {return true;}
      run Demo=Run;
    )");
    take(check(R"(
      domain F=field("bls12-381.fr");
      fn f(x:F,i:index){return(x,i);}
      fn g(x:F){return f(i=1,x=x);}
    )"));
  });
  cases.run("named map arguments keep each modes with their values", [] {
    compile(R"(
      domain F=field("bls12-381.fr");
      type Vector<T:Field>=builtin("vector",T);
      math fn affine<T:Field>(x:T,y:T,r:T){return x+(y-x)*r;}
      fn mapped(xs:Vector<F>,ys:Vector<F>,r:F){
        return map affine(r=r,y=each ys,x=each xs);
      }
      protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P,r:F@P)
          ->(result:Vector<F>@P){return mapped(r=r,ys=ys,xs=xs);}
      run Demo=Run;
    )");
    const std::string declarations = R"(
      domain F=field("bls12-381.fr");
      type Vector<T:Field>=builtin("vector",T);
      math fn add<T:Field>(x:T,y:T){return x+y;}
    )";
    for (StringRef arguments : {"(z=each xs,y=each xs)",
                                "(x=each xs,x=each xs)", "(y=each xs,each xs)"})
      refuses(check(declarations + "fn f(xs:Vector<F>){return map add" +
                    arguments.str() + ";}"),
              "source.call");
    refuses(
        check(declarations +
              "fn f(xs:Vector<F>){return map add<Bad=F>(each xs,each xs);}"),
        "source.generic");
  });
  return cases.result();
}
