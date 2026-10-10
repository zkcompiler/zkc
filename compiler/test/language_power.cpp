#include "zkc/Compiler/Language.h"
#include "zkc/Language/Project.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace zkc::language;
namespace {
template <class T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
Expected<CheckedProject> check(StringRef body) {
  return analyze(
             take(capture(
                 {{"m",
                   ("module m;domain F=field(\"bls12-381.fr\");" + body).str(),
                   "power.zkc"}})))
      .checkedProject();
}
void refuse(StringRef body, StringRef code) {
  auto result = check(body);
  if (result) {
    errs() << "accepted: " << body << '\n';
    std::exit(1);
  }
  auto message = toString(result.takeError());
  if (!StringRef(message).contains(code)) {
    errs() << message << '\n';
    std::exit(1);
  }
}
} // namespace
int main() {
  auto source = take(check(R"(
    math fn identity<N:nat>(x:[F;pow2(N)])->[F;pow2(N)]{return x;}
    math fn normalized<N:nat,M:nat>(x:[F;pow2(N+M)])->[F;pow2(N)*pow2(M)]{return x;}
    math fn shifted<N:nat>(x:[F;2*pow2(N)])->[F;pow2(N+1)]{return identity<N+1>(x);}
    math fn coefficients<N:nat>(x:[F;pow2(2*N+3)])->[F;8*pow2(N)*pow2(N)]{return x;}
    math fn bound<N:nat>(x:[F;pow2(N)])->F where 1<=pow2(N){return x[0];}
    math fn relay<N:nat>(x:[F;pow2(N)])->F where 1<=pow2(N){return bound<N>(x);}
    protocol Run roles(P)(x:[F;4]@P)->(r:[F;4]@P){let y=shifted<1>(x);return(r=y);}
    run Demo=Run;
  )"));
  auto original = take(prepareOriginal(take(closeEntry(source, "m::Demo"))));
  take(compileEntry(original));
  refuse("type Bad=[F;pow2(F)];", "source.natural");
  refuse("type Bad=[F;pow2(64)];", "source.natural");
  refuse("type Bad<N:nat>=[F;pow2(N*N)];", "source.natural");
  refuse("type Bad<N:nat>=[F;pow2(pow2(N))];", "source.natural");
  refuse(R"(
    math fn accept<N:nat>(x:[F;pow2(N)])->[F;pow2(N)]{return x;}
    math fn bad<M:nat>(x:[F;M])->[F;M]{return accept<M*M>(x);}
  )",
         "source.natural");
  refuse(R"(
    math fn accept<N:nat>(x:[F;pow2(N)])->[F;pow2(N)]{return x;}
    math fn bad(x:[F;4])->[F;4]{return accept(x);}
  )",
         "source.inference");
  refuse(R"(
    math fn needs<N:nat>(x:[F;pow2(N)])->F where 1<=pow2(N){return x[0];}
    math fn bad<N:nat>(x:[F;pow2(N)])->F where () {return needs<N>(x);}
  )",
         "source.bound");
  auto bodyOnly = take(check(R"(
    math fn ignore<N:nat>(x:F)->F{return x;}
    math fn inner<N:nat>(x:F)->F{return ignore<pow2(N)>(x);}
    math fn outer<M:nat>(x:F)->F{return inner<pow2(M)>(x);}
    protocol Run<M:nat> roles(P)(x:F@P)->(r:F@P){let y=outer<M>(x);return(r=y);}
    run Good=Run<5>;
    run Overflow=Run<6>;
  )"));
  take(compileEntry(
      take(prepareOriginal(take(closeEntry(bodyOnly, "m::Good"))))));
  auto overflow = closeEntry(bodyOnly, "m::Overflow");
  if (overflow ||
      !StringRef(toString(overflow.takeError())).contains("source.natural")) {
    errs() << "body-only power overflow escaped closing\n";
    return 1;
  }
  outs() << "bounded source power shapes passed\n";
}
