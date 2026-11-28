module

public import Zkc.Core.Run.Execute
public import Zkc.Core.Run.Specialize.Sound
public import Zkc.Runtime.Source

@[expose] public section
set_option autoImplicit false

/-!
Unified execution engine for `ZkcRuntime`:
1. **`runDeployed`**: executes a `Core.Deployed V` via `Core.execute` (`d.run`).
2. **`runClosed`**: executes a specialized `Core.ClosedRole` directly without building intermediate
   `Handler` stacks, walking `ClosedTerm` and `ClosedProcs` directly with exact attempt-frame
   tracking (`markOwn`) and fuel-bounded effect stepping.
3. **Ergonomic scheme drivers**: `proveDeployed`, `verifyDeployed`, `proveClosed`, `verifyClosed`,
   and `runInteractiveDeployed` for interactive two-party protocols.
-/

namespace Zkc.Runtime

open Zkc.Core

/-! ## Direct executor for specialized `ClosedRole` (`runClosed`) -/

section ClosedExecutor
variable {V : Vocabulary} (M : Model V)

/-- Execution result of a `ClosedTerm` stepping directly against `source` and `fuel`. -/
inductive ClosedEval (A : Type) where
  | done (val : A) (remFuel : Nat) (record : List (Happened M))
  | halt (why : Stop) (record : List (Happened M))
  | blocked (at_ : Occurrence) (record : List (Happened M))
  | limit (record : List (Happened M))

instance {A : Type} : Inhabited (ClosedEval M A) := ⟨.limit []⟩

/-- Direct local-term evaluation helper (since `Local` has no role effects). -/
def runLocal {A : Type} : Local A → Except Stop A
  | .done a => .ok a
  | .halt why => .error why
  | .call op _ => nomatch op

/-- Prepend active attempt frames (matching `Process.markOwn`) onto an occurrence for `.own` effects. -/
def applyMarks (marks : List Frame) (occ : Occurrence) : Occurrence :=
  { occ with path := marks ++ occ.path }

/-- Evaluate a single residual `ClosedTerm.effect` directly against `source`, `marks`, and `fuel`. -/
def execResidualEffect (source : Source M) (r : Role) (marks : List Frame)
    {ins res : List V.Ty} (occ : Occurrence) (op : ResidualOp V ins res)
    (vals : HList M.Val ins) (fuel : Nat) : ClosedEval M (HList M.Val res) :=
  match op, vals with
  | .get _ _ _, .nil => .blocked occ []
  | .give kind getters τ, .cons x .nil =>
      match fuel with
      | 0 => .limit []
      | n + 1 => .done .nil n [.gave r kind getters occ τ x]
  | .own kind _ _ τ, _ =>
      match fuel with
      | 0 => .limit []
      | n + 1 =>
          let markedOcc := applyMarks marks occ
          match source markedOcc τ with
          | some v => .done (.cons v .nil) n [.owned r kind markedOcc τ v]
          | none => .limit []
  | .hear kind owner τ, .nil =>
      match fuel with
      | 0 => .limit []
      | n + 1 =>
          match source occ τ with
          | some v => .done (.cons v .nil) n [.heard r kind owner occ τ v]
          | none => .limit []
  | .begin, .nil =>
      match fuel with
      | 0 => .limit []
      | n + 1 => .done (.cons (0 : Nat) .nil) n [.began r occ]
  | .settle, .nil =>
      match fuel with
      | 0 => .limit []
      | n + 1 => .done .nil n [.settled r occ]

/-- Lookup and evaluate a procedure inside `ClosedProcs`. -/
def lookupClosedProc {fns : List (FnHeader V)} :
    {procs : List (ClosedProcSig V)} → ClosedProcs V fns procs →
    (sig : ClosedProcSig V) → Member procs sig →
    (restProcs : List (ClosedProcSig V)) × ClosedProcs V fns restProcs ×
      (inputs : Names sig.ins) ×
      ClosedTerm V fns restProcs sig.states (Ctx.empty.extend inputs) sig.outs
  | [], .nil, _, m => nomatch m
  | _ :: _, .cons inputs body tail, _, .head => ⟨_, tail, inputs, body⟩
  | _ :: _, .cons _ _ tail, _, .tail m => lookupClosedProc tail _ m

/-- Direct fuel-bounded evaluation of `ClosedTerm` + `ClosedProcs` (no intermediate `Process`
monad or `Handler` stack). Structurally mirrors `ClosedTerm.denote` + `runProcess` 1-for-1. -/
partial def evalClosedTerm {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
    (fnTable : FnTable M fns) (procDefs : ClosedProcs V fns procs)
    (source : Source M) (r : Role) (marks : List Frame) :
    {σ : List V.Ty} → {Γ : Ctx V.Ty} → {outs : List V.Ty} →
    ClosedTerm V fns procs σ Γ outs → List Frame → Env M.Val Γ → HList M.Val σ → Nat →
    ClosedEval M (HList M.Val outs × HList M.Val σ)
  | _, _, _, .ret exit, _, env, st, fuel =>
      .done (env.all exit, st) fuel []
  | _, _, _, .letBind first results rest, path, env, st, fuel =>
      match evalClosedTerm fnTable procDefs source r marks first path env st fuel with
      | .done (v1, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results v1) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .seq first second, path, env, st, fuel =>
      match evalClosedTerm fnTable procDefs source r marks first path env st fuel with
      | .done (v1, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks second path env st1 fuel1 with
          | .done (_, st2) fuel2 rec2 => .done (v1, st2) fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .alias x name rest, path, env, st, fuel =>
      evalClosedTerm fnTable procDefs source r marks rest path (env.insert name (env.get x)) st fuel
  | _, _, _, .localOp _ o operands results rest, path, env, st, fuel =>
      match runLocal (localOp M fnTable o (env.all operands)) with
      | .ok vs =>
          evalClosedTerm fnTable procDefs source r marks rest path (env.extend results vs) st fuel
      | .error why => .halt why []
  | _, _, _, .guard key c why rest, path, env, st, fuel =>
      if env.get c then
        evalClosedTerm fnTable procDefs source r marks rest path env st fuel
      else
        .halt (.declared why ⟨path, key⟩) []
  | _, _, _, .choose _ c onTrue onFalse results rest, path, env, st, fuel =>
      let branch := if env.get c then onTrue else onFalse
      match evalClosedTerm fnTable procDefs source r marks branch path env st fuel with
      | .done (mid, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results mid) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .cases (alts := alts) _ x arms results rest, path, env, st, fuel =>
      match evalClosedArms fnTable procDefs source r marks arms path env st (Tys.pick M alts (env.get x)) fuel with
      | .done (mid, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results mid) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .loop (carried := carried) (each := each) key times initial idxName carriedNames
      body results rest, path, env, st, fuel =>
      let total := times.eval M env
      let rec goLoop (rem idx : Nat) (cVals : HList M.Val carried)
          (eVals : HList (fun τ => List (M.Val τ)) each) (curSt : HList M.Val _)
          (curFuel : Nat) (accRec : List (Happened M)) :
          ClosedEval M ((HList M.Val carried × HList (fun τ => List (M.Val τ)) each) × HList M.Val _) :=
        match rem with
        | 0 => .done ((cVals, eVals), curSt) curFuel accRec
        | rem' + 1 =>
            let iterPath := path ++ [.iteration key idx]
            let iterEnv := loopBodyEnv M env idxName idx carriedNames cVals
            match evalClosedTerm fnTable procDefs source r marks body iterPath iterEnv curSt curFuel with
            | .done (out1, st1) fuel1 rec1 =>
                let sp := HList.split carried out1
                goLoop rem' (idx + 1) sp.1 (eVals.push sp.2) st1 fuel1 (accRec ++ rec1)
            | .halt why rec1 => .halt why (accRec ++ rec1)
            | .blocked at_ rec1 => .blocked at_ (accRec ++ rec1)
            | .limit rec1 => .limit (accRec ++ rec1)
      match goLoop total 0 (env.all initial) (HList.empties each) st fuel [] with
      | .done ((cFinal, eFinal), st1) fuel1 rec1 =>
          let allRes := cFinal.append (closedCollected M times.size eFinal)
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results allRes) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .block key number body results rest, path, env, st, fuel =>
      match evalClosedTerm fnTable procDefs source r marks body (path ++ [.iteration key number]) env st fuel with
      | .done (mid, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results mid) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .frame appKey args inputs body results rest, path, env, st, fuel =>
      let subPath := match appKey with | some k => path ++ [.application k] | none => path
      match evalClosedTerm fnTable procDefs source r marks body subPath (Env.empty.extend inputs (env.all args)) st fuel with
      | .done (mid, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results mid) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .call appKey callee args results rest, path, env, st, fuel =>
      let subPath := match appKey with | some k => path ++ [Frame.application k] | none => path
      let ⟨_, subDefs, pInputs, pBody⟩ := lookupClosedProc procDefs _ callee
      match evalClosedTerm fnTable subDefs source r marks pBody subPath (Env.empty.extend pInputs (env.all args)) st fuel with
      | .done (mid, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results mid) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _ :: _, _, _, .withLayer (mid := mid) args inputs body, path, env, .cons mine below, fuel =>
      let subEnv := Env.empty.extend inputs ((env.all args).append (.cons mine .nil))
      match evalClosedTerm fnTable procDefs source r marks body path subEnv below fuel with
      | .done (out1, below1) fuel1 rec1 =>
          let sp := HList.split mid out1
          .done (sp.1, .cons sp.2.single below1) fuel1 rec1
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _ :: _, _, _, .underLayer inner, path, env, .cons mine below, fuel =>
      match evalClosedTerm fnTable procDefs source r marks inner path env below fuel with
      | .done (out1, below1) fuel1 rec1 => .done (out1, .cons mine below1) fuel1 rec1
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | [], _, _, .effect key op operands, path, env, .nil, fuel =>
      match execResidualEffect M source r marks ⟨path, key⟩ op (env.all operands) fuel with
      | .done res fuel1 rec1 => .done (res, .nil) fuel1 rec1
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
  | _, _, _, .retry key bound again inputs body results rest, path, env, st, fuel =>
      let exhausted : Stop := .declared .exhausted ⟨path, key⟩
      let rec goRetry (rem idx : Nat) (curSt : HList M.Val _) (curFuel : Nat)
          (accRec : List (Happened M)) : ClosedEval M (HList M.Val _ × HList M.Val _) :=
        match rem with
        | 0 => .halt exhausted accRec
        | rem' + 1 =>
            let bodyEnv := env.extend inputs (.cons idx .nil)
            let marks' := .attempt key idx :: marks
            match evalClosedTerm fnTable procDefs source r marks' body path bodyEnv curSt curFuel with
            | .done res fuel1 rec1 => .done res fuel1 (accRec ++ rec1)
            | .blocked at_ rec1 => .blocked at_ (accRec ++ rec1)
            | .limit rec1 => .limit (accRec ++ rec1)
            | .halt why rec1 =>
                if Stop.isAbort why then
                  match rem' with
                  | 0 => .halt exhausted (accRec ++ rec1)
                  | _ + 1 =>
                      match StackAgain.eval M fnTable again (idx + 1) st curSt with
                      | .ok nextSt => goRetry rem' (idx + 1) nextSt curFuel (accRec ++ rec1)
                      | .error why2 => .halt why2 (accRec ++ rec1)
                else .halt why (accRec ++ rec1)
      match goRetry bound 0 st fuel [] with
      | .done (mid, st1) fuel1 rec1 =>
          match evalClosedTerm fnTable procDefs source r marks rest path (env.extend results mid) st1 fuel1 with
          | .done res fuel2 rec2 => .done res fuel2 (rec1 ++ rec2)
          | .halt why rec2 => .halt why (rec1 ++ rec2)
          | .blocked at_ rec2 => .blocked at_ (rec1 ++ rec2)
          | .limit rec2 => .limit (rec1 ++ rec2)
      | .halt why rec1 => .halt why rec1
      | .blocked at_ rec1 => .blocked at_ rec1
      | .limit rec1 => .limit rec1
where
  evalClosedArms {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
      (fnTable : FnTable M fns) (procDefs : ClosedProcs V fns procs)
      (source : Source M) (r : Role) (marks : List Frame) :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {mid payloads : List V.Ty} →
      ClosedArms V fns procs σ Γ mid payloads → List Frame → Env M.Val Γ → HList M.Val σ →
      Pick M.Val payloads → Nat →
      ClosedEval M (HList M.Val mid × HList M.Val σ)
    | _, _, _, _, .cons inputs arm _, path, env, st, .here v, fuel =>
        evalClosedTerm fnTable procDefs source r marks arm path (env.extend inputs (.cons v .nil)) st fuel
    | _, _, _, _, .cons _ _ rest, path, env, st, .there p, fuel =>
        evalClosedArms fnTable procDefs source r marks rest path env st p fuel

/-- Direct evaluation of `StackInit` (pure local operations). -/
def evalStackInit {fns : List (FnHeader V)} (fnTable : FnTable M fns) {heldIns : List V.Ty} :
    {σ taken : List V.Ty} → StackInit V fns heldIns σ taken →
    HList M.Val heldIns → HList M.Val taken → Except Stop (HList M.Val σ)
  | [], [], .nil, _, .nil => .ok .nil
  | _ :: _, _, .cons (takes := takes) st rest, ins, taken => do
      let parts := HList.split takes taken
      let first ← runLocal (st.denote (localSem M fns fnTable) []
        (Env.positional (HList.append parts.1 ins)))
      let others ← evalStackInit fnTable rest ins parts.2
      pure (.cons first.single others)

/-- Direct evaluation of `StackFinish` (pure local operations). -/
def evalStackFinish {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
    {σ gives : List V.Ty} → StackFinish V fns σ gives →
    HList M.Val σ → Except Stop (HList M.Val gives)
  | [], [], .nil, .nil => .ok .nil
  | _ :: _, _, .cons fin rest, .cons s states => do
      let mine ← runLocal (fin.denote (localSem M fns fnTable) [] (Env.positional (.cons s .nil)))
      let others ← evalStackFinish fnTable rest states
      pure (HList.append mine others)

/-- Execute a specialized `ClosedRole` directly against `source` and `limit`, without allocating
any `Handler` stack or intermediate `Process` tree. Matches `Core.execute (d.run)` semantics
(which `specialize_deploy_sound` proves equal to `(specialize d r).denote`). -/
def runClosedHeld {fns : List (FnHeader V)} {r : Role}
    {ins outs : List (LTy V)} {taken gives : List V.Ty}
    (fnTable : FnTable M fns) (cr : ClosedRole V fns r ins outs taken gives)
    (heldIns : HList M.Val (held r ins)) (takenVals : HList M.Val taken)
    (source : Source M) (limit : Nat) :
    Outcome (HList M.Val (held r outs)) (HList M.Val gives) × List (Happened M) :=
  match evalStackInit M fnTable cr.start heldIns takenVals with
  | .error why => (.ended (.stopped why), [])
  | .ok st0 =>
      match evalClosedTerm M fnTable cr.procs source r [] cr.body []
          (Env.empty.extend cr.inputs heldIns) st0 limit with
      | .done (outVals, stFinal) _ rec =>
          match evalStackFinish M fnTable cr.finish stFinal with
          | .ok givesVals => (.ended (.returned (outVals, givesVals)), rec)
          | .error why => (.ended (.stopped why), rec)
      | .halt why rec => (.ended (.stopped why), rec)
      | .blocked at_ rec => (.ended (.blocked at_), rec)
      | .limit rec => (.limit, rec)

/-- Execute a specialized `ClosedRole` with `RV`-wrapped inputs/outputs matching `Core.execute`. -/
def runClosed {fns : List (FnHeader V)} {r : Role}
    {ins outs : List (LTy V)} {taken gives : List V.Ty}
    (fnTable : FnTable M fns) (cr : ClosedRole V fns r ins outs taken gives)
    (inputVals : HList (RV M r) ins) (takenVals : HList M.Val taken)
    (source : Source M) (limit : Nat) :
    Outcome (HList (RV M r) outs) (HList M.Val gives) × List (Happened M) :=
  let (out, rec) := runClosedHeld M fnTable cr (heldValues M r inputVals) takenVals source limit
  let out' := match out with
    | .ended (.returned (o, g)) => .ended (.returned (unheldValues M r o, g))
    | .ended (.stopped why) => .ended (.stopped why)
    | .ended (.blocked at_) => .ended (.blocked at_)
    | .limit => .limit
    | .failed msg => .failed msg
  (out', rec)

end ClosedExecutor

/-! ## Ergonomic scheme execution helpers -/

section Drivers
variable {V : Vocabulary} (M : Model V)

/-- Execute a deployed role via `Core.execute` (`d.run`). -/
def runDeployed (d : Deployed V) (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r))) (source : Source M) (limit : Nat) :
    Outcome (HList (RV M r) d.entry.outs) (HList M.Val (Stack.Gives (d.stack r))) ×
      List (Happened M) :=
  Core.execute d M r ins taken source limit

/-- Execute a deployed role via `Core.specialize` + `runClosed`. -/
def runDeployedClosed (d : Deployed V) (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r))) (source : Source M) (limit : Nat) :
    Outcome (HList (RV M r) d.entry.outs) (HList M.Val (Stack.Gives (d.stack r))) ×
      List (Happened M) :=
  runClosed M (Defs.fnTable M d.admitted.program.defs) (Core.specialize d r) ins taken source limit

/-- Run a two-party `.interactive` deployed scheme using `Core.runInteractive`. -/
def runInteractiveScheme (d : Deployed V) (r1 r2 : Role)
    (ins1 : HList (RV M r1) d.entry.ins) (ins2 : HList (RV M r2) d.entry.ins)
    (source : Source M) (limit : Nat) :
    Outcome (HList (RV M r1) d.entry.outs) Unit ×
      Outcome (HList (RV M r2) d.entry.outs) Unit ×
      List (Happened M) :=
  let p1 := roleMeaning M d.admitted.program d.callee r1 [] ins1
  let p2 := roleMeaning M d.admitted.program d.callee r2 [] ins2
  Core.runInteractive M source r1 r2 p1 p2 limit

end Drivers

end Zkc.Runtime
