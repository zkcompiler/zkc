import Zkc.Tools.Formal.DrawCharge
import Zkc.Tests.Formal.Reuse.Automatic

namespace ChargeConsumers
open Zkc.Core Zkc.Frontend Zkc.Tools.Formal Zkc.Tests.Formal
open Zkc.Formal.Interactive.Sumcheck ReductionRound Zkc.Formal.Written
open Zkc.Formal.FiniteService Zkc.Formal.ProbabilisticProcess OracleComp
open scoped ENNReal Zkc.Formal.Written.RoundCharge

private abbrev order := Zkc.Vocabulary.Field.bls12381Fr.order
private abbrev Fr := ZMod order
private abbrev standard := ArithmeticModel.model Fr Fr

private def fieldEvents (b : Emit.Bindings) : Events (SumcheckRows.sourceRows b).scalarTy :=
  ⟨.inl (.field .equal .bls12381Fr .all), rfl, .uniform (.nominal (.field .bls12381Fr)), ⟨_, rfl, rfl, rfl⟩⟩

-- Compute the expected total independently of the issuer's ceiling definition.
private noncomputable def amount (ch : Written.DrawCharge) : ℝ≥0∞ :=
  ch.draws.length * ((ch.numerator : ℝ≥0∞) / ch.denominator)

private abbrev Fee (ch : Written.DrawCharge) (count degree : Nat) :=
  ch.draws.length = count ∧ ch.numerator = degree ∧ ch.denominator = order

private theorem amount_eq {ch : Written.DrawCharge} {n d : Nat} (h : Fee ch n d) :
    amount ch = (n : ℝ≥0∞) * ((d : ℝ≥0∞) / order) := by
  rw [amount, h.1, h.2.1, h.2.2]

section Sumcheck
variable {c : Written.AdmittedRoot} (cert : ChargedSumcheck c 10 "challenge")
    (plain : c.emission.bindings = {}) (fee : Fee cert.issued.charge 10 1)
    {σ : Type} (advance : Occurrence → Fr → σ → σ)
    (other : Slots (RSig standard) σ) (path : List Zkc.Core.Frame) (s : σ) (table : Cube Fr 10) (claim : Fr)

private noncomputable def sumRun :
    ProbComp (Zkc.Formal.ProbabilisticProcess.Outcome Stop (HList (RV standard 1) []) × σ) :=
  let admitted := cast (congrArg (fun b : Emit.Bindings => Zkc.Core.Typed b.vocabulary) plain)
    c.evidence.admitted.program
  let verifier := (cert.standardVerifier (congrArg Emit.Bindings.rows plain)).1
  let root : Member admitted.headers.protocols
      (TableVerifier.header ArithmeticModel.scalarRows.scalarTy 10 ⟨c.id⟩ verifier.shape) := verifier.root
  let inputs := HList.cons (hide standard 1 (shared (TableHalves.table ArithmeticModel.scalarRows.scalarTy 10))
    (Cube.flatten 10 table)) (.cons (hide standard 1 (shared ArithmeticModel.scalarRows.scalarTy) claim) .nil)
  run (service (RoundService.withChallenge standard (fieldEvents {})
    (ZMod.finEquiv order) advance other)) (roleMeaning standard admitted root 1 path inputs) s

include fee in
private theorem sumBound (wrong : claim ≠ Cube.sum 10 table) :
    prEvent (observed (fun _ _ => true) <$> sumRun cert plain advance other path s table claim) ≤
      10 * (1 / (order : ℝ≥0∞)) := by
  let trial := sumRun cert plain advance other path s table claim
  let consume (proof : prEvent (observed (fun _ _ => true) <$> trial) ≤ amount cert.issued.charge) := proof
  fail_if_success with_reducible have := consume True.intro
  fail_if_success with_reducible
    have := fun (keep : σ → Bool) (weak : prEvent (observed (fun _ st => keep st) <$> trial) ≤
      amount cert.issued.charge) => consume weak
  let returnsAt (otherRoot : Written.AdmittedRoot) (otherCert : ChargedSumcheck otherRoot 10 "challenge")
      (otherPlain : otherRoot.emission.bindings = {}) :=
    prEvent (observed (fun _ _ => true) <$> sumRun otherCert otherPlain advance other path s table claim) ≤
      amount cert.issued.charge
  fail_if_success with_reducible
    have := fun r cert' plain' (h : returnsAt r cert' plain') => consume h
  have atPath (addr : List Zkc.Core.Frame) :
      prEvent (observed (fun _ _ => true) <$> sumRun cert plain advance other addr s table claim) ≤
        amount cert.issued.charge :=
    cert.primeBound (congrArg Emit.Bindings.rows plain) advance other addr s table claim wrong
  rw [show (10 : ℝ≥0∞) * (1 / order) = amount cert.issued.charge from (amount_eq fee).symm]
  fail_if_success with_reducible exact atPath (path ++ [.application ⟨1⟩])
  with_reducible exact consume (atPath path)
end Sumcheck

section Layer
-- These are the summand, reduction, site, operands and loop in examples/gkr_example.zkc.
private def summand : Emit.LocalApplication := ⟨34, [.binder 0, .binder 1, .bounded 4 6, .binder 4]⟩
variable {c : Written.AdmittedRoot} {hdr : ProtocolHeader c.emission.bindings.vocabulary}
    {root : Member c.evidence.admitted.program.headers.protocols hdr}
    {hidden residual : c.emission.bindings.vocabulary.Ty}
private abbrev rows (c : Written.AdmittedRoot) := SumcheckRows.sourceRows c.emission.bindings
variable (call : AtSite c.evidence.admitted.program root ⟨17⟩ ⟨11⟩ hidden (rows c).scalarTy residual 0 4 (fieldEvents c.emission.bindings)
    [15,16,9] (loopRoute 4 ⟨28⟩ 4 7))
    (cert : ChargedLayer call summand "challenge") (fee : Fee cert.issued.charge 4 2)
    (M : Model c.emission.bindings.vocabulary) [Field ((rows c).F M)] [DecidableEq ((rows c).F M)]
    (interpret : Emit.LocalApplication → Claims ((rows c).F M))
    {width : Nat} {σ : Type} (alphabet : Fin (width+1) → (rows c).F M)
    (advance : Occurrence → (rows c).F M → σ → σ) (other : Slots (RSig M) σ)
    (path : List Zkc.Core.Frame) (i : Fin 4) (s : σ) (hiddenInput : RV M 1 ⟨hidden,[0]⟩)
    (point : List ((rows c).F M)) (claim : (rows c).F M) (x : (interpret summand).State 4)

private noncomputable def layerRun :=
  let t := (rows c).scalarTy
  let application : RoleOp c.emission.bindings.vocabulary call.callerEntry.earlier 1
      (inputs hidden (.seq t (some 0)) t) (PointReturn.ports t residual 4) :=
    .apply call.linked.ref [0,1] (by decide) rfl _ (by
      change (_ = _ ∧ ∀ r, r ∈ [0] → r ∈ [0]) ∧ (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧
        (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧ True
      simp [t]
      exact ⟨rfl, rfl, rfl⟩)
  run (service (RoundService.withChallenge M (fieldEvents c.emission.bindings) alphabet advance other))
    (roleOp M 1 (Defs.fnTable M call.callerEntry.definitions) (Defs.rTable M call.callerEntry.definitions)
      ⟨11⟩ application (path ++ [.iteration ⟨28⟩ i.val])
      (.cons hiddenInput (.cons (hide M 1 (PointReturn.point (rows c).scalarTy 0) point)
        (.cons (hide M 1 (shared (rows c).scalarTy) claim) .nil)))) s

-- Read the returned point and scalar, drop the incoming prefix, and compare with the
-- value of the source-selected summand at that suffix. The prover owns the third port.
private def residualAgrees (q : Claims ((rows c).F M)) (subject : q.State 4) (prior : Nat) :
    HList (RV M 1) (PointReturn.ports (rows c).scalarTy residual 4) → Bool
  | .cons returnedPoint (.cons returnedClaim (.cons _ .nil)) =>
    decide (q.evaluate 4 subject
      ((reveal M (a := PointReturn.point (rows c).scalarTy 4) (by simp) returnedPoint).drop prior) =
      some (reveal M (a := shared (rows c).scalarTy) (by simp) returnedClaim))

include fee in
private theorem layerBound (math : (rows c).Arithmetic M)
    (model : Gate.Evaluation (rows c) (.inr (Emit.primitiveName ⟨"circuit.gate_evaluate",
      #[.type (StandardNames.fieldType .bls12381Fr)]⟩)) cert.gate.bound M)
    (equal : ScalarEquality.Law (rows c).scalarTy (fieldEvents c.emission.bindings).equal
      (fieldEvents c.emission.bindings).equalType M)
    (honest : ∀ d : Fin 4, (interpret summand).State (d.val+1) → Quadratic ((rows c).F M))
    (ends : ∀ d y, (interpret summand).value (d.val+1) y = (honest d y).boundary)
    (restricts : ∀ d y r, (interpret summand).value d.val ((interpret summand).restrict d.val y r) =
      (honest d y).eval r)
    (size : width+1 = order) (distinct : (List.ofFn alphabet).Nodup)
    (wrong : claim ≠ (interpret summand).value 4 x) :
    prEvent (observed (fun vs _ => residualAgrees M (interpret summand) x point.length vs) <$>
      layerRun call M alphabet advance other path i s hiddenInput point claim) ≤ 4 * (2 / (order : ℝ≥0∞)) := by
  let trial := layerRun call M alphabet advance other path i s hiddenInput point claim
  let agrees := residualAgrees (residual := residual) M (interpret summand) x point.length
  let consume (proof : prEvent (observed (fun vs _ => agrees vs) <$> trial) ≤ amount cert.issued.charge) := proof
  fail_if_success with_reducible have := consume True.intro
  fail_if_success with_reducible
    have := fun (keep : σ → Bool) (weak : prEvent (observed (fun vs st => agrees vs && keep st) <$> trial) ≤
      amount cert.issued.charge) => consume weak
  fail_if_success with_reducible
    have := fun h : prEvent (observed (fun _ _ => true) <$> trial) ≤ amount cert.issued.charge => consume h
  let swapped : Emit.LocalApplication := ⟨34, [.binder 1, .binder 0, .bounded 4 6, .binder 4]⟩
  let otherRelation (y : (interpret swapped).State 4) :=
    prEvent (observed (fun vs _ => residualAgrees M (interpret swapped) y point.length vs) <$> trial) ≤
      amount cert.issued.charge
  fail_if_success with_reducible have := fun y (h : otherRelation y) => consume h
  have sameEvent : agrees = correctReturn (k := 0) M (interpret summand) x point.length := by
    funext values
    match values with | .cons _ (.cons _ (.cons _ .nil)) => rfl
  have atLayer (iteration : Fin 4) :
      prEvent (observed (fun vs _ => agrees vs) <$>
        layerRun call M alphabet advance other path iteration s hiddenInput point claim) ≤ amount cert.issued.charge := by
    rw [sameEvent]
    exact cert.bound M math model equal iteration interpret honest ends restricts size alphabet distinct
      advance other path s hiddenInput point claim x wrong
  rw [show (4 : ℝ≥0∞) * (2 / order) = amount cert.issued.charge from (amount_eq fee).symm]
  fail_if_success with_reducible exact atLayer (i + 1)
  with_reducible exact consume (atLayer i)
end Layer

open Lean in
run_cmd
  let env ← getEnv
  for name in [``ChargedSumcheck.primeBound, ``ChargedLayer.bound] do
    unless (env.find? name).any (· matches .thmInfo _) &&
        env.getModuleIdxFor? name == env.getModuleIdx? `Zkc.Tools.Formal.DrawCharge do
      throwError "expected public theorem {name} in the audited charge issuer"

#eval show IO Unit from do
  let dir := (← IO.currentDir) / "../.."
  let admit (file : String) := do
    let entry ← SourcePairReadback.source .original (dir / "examples" / file)
    SourceProtocolRoots.admitRoot entry (SourcePairReadback.loadModule dir .original)
  let sum ← admit "sumcheck_example.zkc"
  let prime ← IO.ofExcept (chargeSumcheck sum 10 "challenge")
  if empty : sum.emission.bindings.rows = [] then
    have plain : sum.emission.bindings = {} := by
      generalize h : sum.emission.bindings = b at *
      cases b with | mk rows _ => cases empty; rfl
    if fee : Fee prime.issued.charge 10 1 then
      have _ := @sumBound sum prime plain fee
      pure ()
    else throw (IO.userError "expected ten charges of 1/Fr.order")
  else throw (IO.userError "Sumcheck needs the standard field model")
  let layer ← admit "gkr_example.zkc"
  let some component := Reuse.Automatic.gkr layer ⟨17⟩ ⟨11⟩ [15,16,9] ⟨28⟩
    | throw (IO.userError "missing verifier layer call")
  let gate ← IO.ofExcept (chargeLayer (c := layer) component.atCall summand "challenge")
  if fee : Fee gate.issued.charge 4 2 then
    have _ := @layerBound layer _ component.root _ _ component.atCall gate fee
    pure ()
  else throw (IO.userError "expected four charges of 2/Fr.order")
  IO.println "consumed Sumcheck root and GKR layer charge bounds"
end ChargeConsumers
