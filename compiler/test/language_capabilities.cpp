#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(StringRef body, const Limits &limits = {}) {
  auto source = capture({{"m", "module m;" + body.str(), {}}});
  if (!source)
    return source.takeError();
  return analyze(*source, limits).checkedProject();
}
ClosedEntry close(StringRef source) {
  return take(closeEntry(take(check(source)), "m::Demo"));
}
constexpr StringLiteral root = R"(
  fn root<F:Field>(n:index)->F where zkc::algebra::TwoAdicField(F) {
    return kernel<F>("poly.domain_root",n);
  }
)";
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("installed domains sustain the generic capability assumptions", [] {
    const auto &catalog = zkc::protocol::installedDomains();
    for (const auto &domain : catalog.allDomains()) {
      if (domain.sort == "Field" || domain.sort == "Group")
        require(catalog.hasFact(domain.sort, {domain.identity}),
                "installed sort lacks its inherent fact: " + domain.identity);
      for (const auto &rule : zkc::protocol::boundCapabilityRules())
        if (catalog.hasFact(rule.premise, {domain.identity}))
          require(
              catalog.hasFact(rule.conclusion, {domain.identity}),
              "installed facts are not closed under generic implications: " +
                  domain.identity);
    }
  });
  cases.run("generic bounds reach kernels and are removed after closure", [] {
    auto entry = close((root + R"(
      domain K=field("koala-bear");
      protocol Run<F:Field> roles(P)(n:index@P)->(r:F@P)
          where zkc::algebra::TwoAdicField(F) {
        let r @P =root<F>(n);return(r=r);
      }
      entry Demo=Run<K>;
    )")
                           .str());
    for (const auto &decl : entry.declarations())
      if (decl.origin)
        require(decl.capabilityBounds.empty(),
                "closed declaration retained bounds");
    take(compileEntry(take(prepareOriginal(entry))));
  });
  cases.run("calls require the caller's bounds on the exact argument", [] {
    refuses(check((root + R"(
      fn caller<F:Field>(n:index)->F{return root<F>(n);}
    )")
                      .str()),
            "source.capability");
    refuses(check((root + R"(
      fn caller<F:Field,G:Field>(n:index)->F
          where zkc::algebra::TwoAdicField(G) {return root<F>(n);}
    )")
                      .str()),
            "source.capability");
    take(check((root + R"(
      fn caller<F:Field>(n:index)->F where zkc::algebra::TwoAdicField(F) {
        return root<F>(n);
      }
    )")
                   .str()));
  });
  cases.run("catalog implications and inherent domain facts are shared", [] {
    take(check(R"(
      fn ring<F:Field>(x:F)->F where zkc::algebra::CommRing(F) {return x;}
      fn caller<F:Field>(x:F)->F{return ring(x);}
      fn redundant<F:Field,G:Group>(x:F,y:G)->F
          where zkc::algebra::Field(F),zkc::curve::Group(G){return x;}
      fn transcript<T:Transcript>()->() where zkc::transcript::TranscriptCapability(T) {return ();}
      fn stronger<T:Transcript>()->() where zkc::transcript::FieldTranscript(T) {return transcript<T>();}
    )"));
    refuses(check(R"(
      fn transcript<T:Transcript>()->() where zkc::transcript::TranscriptCapability(T) {return ();}
      fn caller<T:Transcript>()->() {return transcript<T>();}
    )"),
            "source.capability");
  });
  cases.run("closed declarations and Entries use installed facts only", [] {
    take(check(R"(
      domain K=field("koala-bear");
      fn good()->() where zkc::algebra::TwoAdicField(K) {return ();}
    )"));
    refuses(check(R"(
      domain Fr=field("bls12-381.fr");
      fn unused()->() where zkc::algebra::TwoAdicField(Fr) {return ();}
    )"),
            "source.capability");
    refuses(check((root + R"(
      domain Fr=field("bls12-381.fr");
      protocol Run<F:Field> roles(P)(n:index@P)->(r:F@P)
          where zkc::algebra::TwoAdicField(F) {
        let r @P =root<F>(n);return(r=r);
      } entry Demo=Run<Fr>;
    )")
                      .str()),
            "source.capability");
  });
  cases.run("capability names arity and sorts are checked", [] {
    for (StringRef bound :
         {"TwoAdicField(F)", "zkc::algebra::Missing(F)",
          "zkc::algebra::TwoAdicField()", "zkc::algebra::TwoAdicField(F,F)",
          "zkc::algebra::TwoAdicField(bool)", "zkc::pcs::MultilinearOpening(F)",
          "Field(F)"})
      refuses(
          check(
              ("fn bad<F:Field>()->() where " + bound + " {return ();}").str()),
          "source.capability");
  });
  cases.run("associated arguments retain their normalized identity", [] {
    take(check((root + R"(
      fn call<C:Commitment>(n:index)->C::ValueField
          where zkc::algebra::TwoAdicField(C::ValueField) {
        return root<C::ValueField>(n);
      }
      interface HasField{type Scalar:Field;}
      fn via<T:HasField>(n:index)->T::Scalar
          where zkc::algebra::TwoAdicField(T::Scalar) {
        return root<T::Scalar>(n);
      }
    )")
                   .str()));
  });
  cases.run("component bounds are inherited and enforced on application", [] {
    const std::string implementation = (root + R"(
      interface Roots<F:Field>{fn get(n:index)->F;}
      component Impl<F:Field>:Roots<F> where zkc::algebra::TwoAdicField(F) {
        fn get(n:index)->F {return root<F>(n);}
      }
      fn invoke<F:Field,T:Roots<F>>(n:index)->F{return T::get(n);}
    )")
                                           .str();
    take(check(implementation + R"(
      fn call<F:Field>(n:index)->F where zkc::algebra::TwoAdicField(F) {
        return invoke<F,Impl<F>>(n);
      }
    )"));
    refuses(check(implementation + R"(
      fn call<F:Field>(n:index)->F{return invoke<F,Impl<F>>(n);}
    )"),
            "source.capability");
    refuses(check(R"(
      interface Roots<F:Field>{fn get(n:index)->F;}
      component Impl<F:Field>:Roots<F> {
        fn get(n:index)->F where zkc::algebra::TwoAdicField(F) {
          return kernel<F>("poly.domain_root",n);
        }
      }
    )"),
            "source.conformance");
  });
  cases.run("member bounds substitute interface parameters and self", [] {
    take(check(R"(
      interface Roots<F:Field>{fn get(n:index)->F where zkc::algebra::TwoAdicField(F);}
      component Impl<F:Field>:Roots<F> {
        fn get(n:index)->F where zkc::algebra::TwoAdicField(F) {
          return kernel<F>("poly.domain_root",n);
        }
      }
    )"));
    take(check(R"(
      domain K=field("koala-bear");
      interface Roots{type Scalar:Field;fn get(n:index)->Scalar where zkc::algebra::TwoAdicField(Scalar);}
      component Impl:Roots{type Scalar:Field=K;
        fn get(n:index)->K{return kernel<K>("poly.domain_root",n);}
      }
      fn invoke<T:Roots>(n:index)->T::Scalar
          where zkc::algebra::TwoAdicField(T::Scalar){return T::get(n);}
    )"));
    refuses(check(R"(
      domain Fr=field("bls12-381.fr");
      interface Roots{type Scalar:Field;fn get(n:index)->Scalar where zkc::algebra::TwoAdicField(Scalar);}
      component Impl:Roots{type Scalar:Field=Fr;fn get(n:index)->Fr{return 1;}}
    )"),
            "source.conformance");
  });
  cases.run("requirements are checked against the complete where clause", [] {
    for (StringRef bounds :
         {"zkc::algebra::CommRing(Checked<F>),zkc::algebra::TwoAdicField(F)",
          "zkc::algebra::TwoAdicField(F),zkc::algebra::CommRing(Checked<F>)"})
      take(check((R"(
        type Checked<F:Field> where zkc::algebra::TwoAdicField(F)=F;
        fn copy<F:Field>(x:F)->F where )" +
                  bounds + " {return x;}")
                     .str()));
  });
  cases.run("normalized aliases cannot hide their formation obligations", [] {
    refuses(check(R"(
      type Checked<F:Field> where zkc::algebra::TwoAdicField(F)=F;
      fn copy<F:Field>(x:F)->F where zkc::algebra::CommRing(Checked<F>) {return x;}
    )"),
            "source.capability");
    refuses(check(R"(
      domain B=field("bn254.fr");
      type Const<F:Field> where zkc::algebra::TwoAdicField(F)=B;
      fn copy<F:Field>(x:F)->F where zkc::algebra::CommRing(Const<F>) {return x;}
    )"),
            "source.capability");
    refuses(
        check(
            R"(interface HasField<F:Field>{type Scalar:Field where zkc::algebra::TwoAdicField(F);})"),
        "source.unsupported");
    auto source = take(capture({{"m", "module m::Field;", {}}}));
    refuses(analyze(source).checkedProject(), "source.name");
  });
  cases.run("capability search bounds its finite term space", [] {
    const auto source = (root + R"(
      fn call<F:Field>(n:index)->F where zkc::algebra::TwoAdicField(F) {
        return root<F>(n);
      }
    )")
                            .str();
    take(check(source));
    std::string many = "fn bounded<";
    for (unsigned i = 0; i < 129; ++i)
      many += (i ? "," : "") + std::string("F") + std::to_string(i) + ":Field";
    many += ">(n:index)->F0 where ";
    for (unsigned i = 0; i < 129; ++i)
      many += (i ? "," : "") + std::string("zkc::algebra::TwoAdicField(F") +
              std::to_string(i) + ")";
    many += "{return root<F0>(n);}";
    auto result = check(root.str() + many);
    require(!result, "unbounded capability terms were accepted");
    auto message = toString(result.takeError());
    require(StringRef(message).contains("source.limit") &&
                StringRef(message).contains("capability term limit"),
            "refusal did not reach bounded capability checking: " + message);
  });

  cases.run(
      "generic PCS operations keep typed local keys and opening state", [] {
        const std::string library = R"(
      type Commit<C:Commitment>=builtin("commitment",C);
      type Proof<C:Commitment>=builtin("proof",C);
      type ProverKey<C:Commitment>=builtin("prover_key",C);
      type VerifierKey<C:Commitment>=builtin("verifier_key",C);
      type Table<F:Field>=builtin("table",F);
      type Point<F:Field>=builtin("point",F);
      fn round<C:Commitment>(pk:ProverKey<C>,vk:VerifierKey<C>,
          data:Table<C::ValueField>,point:Point<C::PointField>)->bool
          where zkc::pcs::MultilinearOpening(C) {
        let committed=kernel<C>("pcs.commit",pk,data);
        let opened=kernel<C>("pcs.open",committed.1,point);
        return kernel<C>("pcs.check",vk,committed.0,point,opened.0,opened.1);
      }
      domain Kzg=commitment("multilinear.kzg.bls12-381/0");
      domain Rows=commitment("rows.merkle-keccak256.koala-bear/0");
      fn concrete(pk:ProverKey<Kzg>,vk:VerifierKey<Kzg>,
          data:Table<Kzg::ValueField>,point:Point<Kzg::PointField>)->bool {
        return round<Kzg>(pk,vk,data,point);
      }
    )";
        take(check(library));
        auto unbounded = library;
        auto bound = unbounded.find("where zkc::pcs::MultilinearOpening(C)");
        require(bound != std::string::npos, "PCS bound anchor missing");
        unbounded.erase(
            bound, StringRef("where zkc::pcs::MultilinearOpening(C)").size());
        refuses(check(unbounded), "source.kernel");
        refuses(check(library + R"(
          fn false_bound()->() where zkc::pcs::MultilinearOpening(Rows) {return ();}
        )"),
                "source.capability");
        auto entry = close(library + R"(
      fn equal<C:Commitment>(a:Commit<C>,b:Commit<C>)->bool
          where zkc::pcs::MultilinearOpening(C) {
        return kernel<C>("pcs.equal",a,b);
      }
      protocol Run<C:Commitment> roles(P,V)(a:Commit<C>@P,b:Commit<C>@V)->(accepted:bool@V)
          where zkc::pcs::MultilinearOpening(C) {
        let sent=send P->V(a);let ok @V =equal<C>(sent,b);return(accepted=ok);
      } entry Demo=Run<Kzg>{setup pcs{a,b};}
    )");
        take(compileEntry(take(prepareOriginal(entry))));
        for (StringRef head : {"prover_key", "verifier_key", "opening_state",
                               "opening_states", "commitments"}) {
          StringRef domain = head == "opening_states" || head == "commitments"
                                 ? "Rows"
                                 : "Kzg";
          refuses(check((library + "type Local=builtin(\"" + head + "\"," +
                         domain + R"();
        protocol Bad roles(P,V)(key:Local@P)->(out:Local@V){
          let sent=send P->V(key);return(out=sent);
        }
      )")
                            .str()),
                  "source.permission");
        }
        for (StringRef head :
             {"commitment", "proof", "prover_key", "opening_state"})
          refuses(check((library + "type Local=builtin(\"" + head + R"(",Kzg);
        math fn bad(x:Local)->Local{return x;}
      )")
                            .str()),
                  "source.mode");
      });

  cases.run("each finite capability search charges its pair work", [] {
    std::string header = "fn bounded<";
    for (unsigned i = 0; i < 128; ++i)
      header +=
          (i ? "," : "") + std::string("F") + std::to_string(i) + ":Field";
    header += ">(n:index)->F0 where ";
    for (unsigned i = 0; i < 128; ++i)
      header += (i ? "," : "") + std::string("zkc::algebra::TwoAdicField(F") +
                std::to_string(i) + ")";
    auto once = take(check(root.str() + header + "{return root<F0>(n);}"));
    auto twice = take(check(root.str() + header +
                            "{let unused=root<F0>(n);return root<F0>(n);}"));
    require(twice.checkedWork() >= once.checkedWork() + 2 * 128 * 128,
            "another finite search omitted its quadratic work charge");
  });

  return cases.result();
}
