module

public import Zkc.Core.Admission.Admit
public import Zkc.Core.Scheme.Deploy.Compile
public import Zkc.Core.Statements

@[expose] public section

/-!
Deployment-specific public contract statements (`SchemeStatements`), separated from
`Zkc.Core.Statements` so written-only and admission consumers do not transitively import
`Zkc.Core.Scheme.Deploy.Compile`.
-/

namespace Zkc.Core

namespace SchemeStatements

variable {V : Vocabulary}

/-- Progress: streaming completeness for `deploy enc` under the selected-function suite law
`Deployed.SuiteLawfulFor enc M` (charging ONLY the `findSuiteDerive`-selected function for each
law, never shadowed fallback defaults in `suite.members`). -/
def completeStreaming (enc : VocabEncoder V) : Prop :=
  ∀ named assoc (a : Admitted V), admit named assoc = .ok a →
    ∀ declaration (d : Deployed V), deploy enc a declaration = .ok d →
      declaration.interactive = false →
      declaration.retry = none →
      declaration.samples = none →
      (∀ l, declaration.layout = some l → l.recover = []) →
      ∀ (prover verifier : Role), d.roles = some (prover, verifier) →
      ∀ (first : Stack.Takes (d.stack prover) = [])
        (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
        (M : Model V) (ins : HList (LVal M) d.entry.ins),
        ins.All (fun a v => M.Valid a.ty v) →
        d.SuiteLawfulFor enc M →
        d.LayoutLawful M →
        (∀ source, Lawful M source (protocolMeaning M d.admitted.program d.callee [] ins) → ∀ e,
          GExec M source (protocolMeaning M d.admitted.program d.callee [] ins) e →
          ∃ out, e = .returned out) →
        ∀ source, LawfulPrivate M source (protocolMeaning M d.admitted.program d.callee [] ins) →
          Fed M source (protocolMeaning M d.admitted.program d.callee [] ins) →
          ∃ outP gives recordP outV givesV recordV,
            Alone M source prover
              (d.run M prover (hideAll M prover ins)
                (cast (congrArg (HList M.Val) first.symm) .nil))
              recordP (.returned (outP, gives)) ∧
            Alone M source verifier
              (d.run M verifier (hideAll M verifier ins)
                (cast (congrArg (HList M.Val) matched) gives))
              recordV (.returned (outV, givesV)) ∧
            ∃ source' out,
              Lawful M source' (protocolMeaning M d.admitted.program d.callee [] ins) ∧
              (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
              GExec M source' (protocolMeaning M d.admitted.program d.callee [] ins)
                (.returned out) ∧
              outP = hideAll M prover out.1 ∧ outV = hideAll M verifier out.1

/-- Execution and state: ideal random-oracle verifier linkage on non-carry streaming ideal
deployments without retry. Starting from the canonical initial ideal transcript path `st0`
(pinned to the resolved session bytes and every statement input in signature order), answering
`serviceKey` requests with any partial random oracle `ro` that answers the protocol's verifier
draws makes the deployed ideal verifier return `outV` on a valid proof if and only if the bare
verifier role program `roleMeaning` satisfies `BareIdealReturn` from `(st0, proof, 0)`. -/
def idealLink (enc : VocabEncoder V) : Prop :=
  ∀ (M : Model V) (serviceKey : Key) (a : Admitted V) (declaration : Declaration)
    (suite : ModuleRef) (sessionTag : Option (List Nat)) (layout : Layout) (dIdeal : Deployed V),
    deployIdeal enc serviceKey a declaration = .ok dIdeal →
    declaration.construction = .derived suite sessionTag →
    declaration.layout = some layout →
    declaration.retry = none →
    layout.carry = [] →
    layout.recover = [] →
    ∀ (prover verifier : Role), dIdeal.roles = some (prover, verifier) →
    ∀ (ins : HList (RV M verifier) dIdeal.entry.ins), ins.All (RV.Valid M verifier) →
      ∃ (suiteUnitTy unitTy : V.Ty)
        (hSuiteFree : Ty.isLinear V suiteUnitTy = false)
        (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
        (st0 : M.Val (LayerBuild.idealPathTy suiteUnitTy))
        (hTakes : Stack.Takes (dIdeal.stack verifier) = [.seq unitTy none]),
        findSuiteUnit a suite = some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩ ∧
        resolveSessionBytes enc a declaration sessionTag = .ok ⟨sessBytes, hSess⟩ ∧
        idealInitialPath M a suite suiteUnitTy prover verifier sessBytes ins = some st0 ∧
        ∀ (proof : List (M.Val unitTy)), M.Valid (.seq unitTy none) proof →
          ∀ (source : Source M) (ro : LayerBuild.IdealRO M suiteUnitTy),
            ro.AnswersDraws M prover verifier (dIdeal.entry.shape.events [] id) →
            ∀ (outV : HList (RV M verifier) dIdeal.entry.outs),
              (∃ record givesV,
                Alone M source verifier
                  (Process.answerService serviceKey (LayerBuild.IdealRO.asOracle M ro)
                    (dIdeal.run M verifier ins
                      (cast (congrArg (HList M.Val) hTakes.symm) (.cons proof .nil))))
                  record (.returned (outV, givesV))) ↔
              BareIdealReturn M a suite layout serviceKey prover verifier
                (dIdeal.entry.shape.eventsWithAbsorb prover verifier [] id false)
                source ro
                (roleMeaning M dIdeal.admitted.program dIdeal.callee verifier [] ins)
                st0 proof 0 outV

end SchemeStatements

end Zkc.Core
