import Zkc.Tools.Formal.InstalledRound
import Zkc.Tools.Formal.DrawCharge
import Zkc.Frontend.Written.Claim
import Zkc.Formal.Written.SiteCaps

namespace Zkc.Tools.Formal
open Zkc.Core Zkc.Frontend Zkc.Frontend.Written Zkc.Formal.Interactive.Sumcheck
open Zkc.Formal.Written Zkc.Formal.FiniteService Zkc.Formal.ProbabilisticProcess OracleComp
open scoped NNRat NNReal ENNReal

/-- Check the single call and its draws in the shared table of uses, including a zero-round
callee whose list of draws is empty. -/
def paysSingleCall (caps : CapTable) (root site : Key) (charge : DrawCharge) : Bool := Id.run do
  let some caller := caps.uses.getLast? | return false
  let [call] := caller.calls | return false
  let some child := caps.uses[call.callee]? | return false
  return caller.definition == root && caller.draws.isEmpty && call.key == site && call.count == 1 &&
    child.definition == charge.owner && child.calls.isEmpty &&
    child.draws == charge.draws.map (fun (_, key) => ⟨key, charge.numerator, charge.denominator, 1⟩)

structure SingleRoundGoal (c : AdmittedRoot) (n : Nat) (name draw : String) (expression : LineExpression) where
  claims : GoalClaims
  fromSource : goalClaims c [name] = .ok claims
  goal : ClaimedGoal
  chosen : claims.goals = [goal]
  proves : goal.clause.kind = .proves
  relation : isTableSumRelation claims.state goal.relation = true
  operands : goal.statement = #[0,1] ∧ goal.witness = some #[]
  observer : claims.verifier = 1
  ceiling : goal.checkCeiling = .ok ()
  subject : ProofSubject
  checked : ChargedSumcheck c n draw expression.decode subject.specification
  atCall : (ProofSubject.mk c.id goal.specification).child c checked.keys.site = .ok subject
  callee : subject.protocol = checked.keys.reduction.number
  specification : RoundSpecification.ForExpression c.state checked.keys.reduction.number expression
  sites : paysSingleCall goal.caps ⟨c.id⟩ checked.keys.site checked.issued.charge = true
  budget : goal.caps.budget = ((checked.issued.charge.draws.length * checked.issued.charge.numerator : Nat) : ℚ≥0) /
    checked.issued.charge.denominator

def singleRoundGoal (c : AdmittedRoot) (n : Nat) (name draw : String) (expression : LineExpression)
    (companion : (Zkc.Formal.Written.SumcheckRows.sourceRows c.emission.bindings).Companion expression.decode) :
    Except String (SingleRoundGoal c n name draw expression) := do
  let ⟨claims,fromSource⟩ ← MonadAttach.attach (goalClaims c [name])
  match chosen : claims.goals with
  | [goal] =>
    let ⟨(),ceiling⟩ ← MonadAttach.attach goal.checkCeiling
    let ⟨proves⟩ ← goal.proving
    if suitable : isTableSumRelation claims.state goal.relation = true ∧
        (goal.statement = #[0,1] ∧ goal.witness = some #[]) ∧ claims.verifier = 1 then
      let some ⟨keys,located⟩ := (sumcheckCallKeys c.emission ⟨c.id⟩).attach | throw "expected a single reduction"
      let ⟨subject,atCall⟩ ← MonadAttach.attach ((ProofSubject.mk c.id goal.specification).child c keys.site)
      let specification ← RoundSpecification.readAs c.state keys.reduction.number expression
      let checked ← chargeSumcheckAt c n draw keys located (selectedMembers _ specification.selected companion)
        subject.specification
      have same := Option.some.inj (checked.located.symm.trans located)
      let charge := checked.issued.charge
      if ok : subject.protocol = keys.reduction.number ∧ paysSingleCall goal.caps ⟨c.id⟩ checked.keys.site charge = true ∧
          goal.caps.budget = ((charge.draws.length * charge.numerator : Nat) : ℚ≥0) / charge.denominator then
        return ⟨claims,fromSource,goal,chosen,proves,suitable.1,suitable.2.1,suitable.2.2,ceiling,
          subject,checked,same.symm ▸ atCall,same.symm ▸ ok.1,same.symm ▸ specification,ok.2.1,ok.2.2⟩
      else throw "the selected goal does not pay for the verifier at its checked call"
    else throw "expected the selected clause to prove the verifier's public table sum"
  | _ => throw "expected one written goal"

theorem SingleRoundGoal.total_eq {c : AdmittedRoot} {n : Nat} {name draw : String} {expression : LineExpression} (g : SingleRoundGoal c n name draw expression) :
    total g.checked.issued.charge = g.goal.caps.total := by
  unfold CapTable.total
  rw [g.budget, toProbability_natCast_div _ _ g.checked.issued.binding.2.2.2.1]
  simp [total, mul_div_assoc]

/-- The counted source budget is exactly one full-field challenge fee per executed round. -/
theorem SingleRoundGoal.degreeOneTotal {c : AdmittedRoot} {n : Nat} {name draw : String} {expression : LineExpression}
    (g : SingleRoundGoal c n name draw expression)
    (unitFee : g.checked.issued.charge.numerator = 1)
    (order : g.checked.issued.charge.denominator = Zkc.Vocabulary.Field.bls12381Fr.order) :
    g.goal.caps.total = (n : ℝ≥0∞) / Zkc.Vocabulary.Field.bls12381Fr.order := by
  have draws := g.checked.issued.binding.2.1
  rw [← g.total_eq]
  simp [total, draws, RoundCharge.locations, g.checked.verifier.linked.rounds.length_instances, unitFee, order, div_eq_mul_inv]

/-- Acceptance of the admitted source verifier on a false public sum, bounded by the
named goal's counted table, with uniform challenges from the source field. -/
theorem SingleRoundGoal.primeBound {c : AdmittedRoot} {n : Nat} {name draw : String} {expression : LineExpression}
    (g : SingleRoundGoal c n name draw expression) (plain : c.emission.bindings.rows = [])
    {σ : Type} (advance : Occurrence → Scalar → σ → σ) (other : Slots (RSig scalarModel) σ)
    (path : List Zkc.Core.Frame) (s : σ) (x : Cube Scalar n) (claim : Scalar) (wrong : claim ≠ Cube.sum n x) :
    let cert := (g.checked.standardVerifier plain).1
    let alphabet : Fin (Zkc.Vocabulary.Field.bls12381Fr.order - 1 + 1) → Scalar := ZMod.finEquiv _
    prEvent (observed (fun _ _ => true) <$> run
      (service (RoundService.withChallenge scalarModel ArithmeticModel.events alphabet advance other))
      (roleMeaning scalarModel _ cert.root 1 path (TableVerifier.args scalarModel (Cube.flatten n x) claim)) s) ≤
      g.goal.caps.total := by
  rw [← g.total_eq]
  exact g.checked.primeBound plain advance other path s x claim wrong

end Zkc.Tools.Formal
