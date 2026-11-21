import Zkc.Tools.Formal.InstalledRound
import Zkc.Tools.Formal.DrawCharge
import Zkc.Frontend.Written.Claim
import Zkc.Formal.Written.SiteCaps

namespace Zkc.Tools.Formal
open Zkc.Core Zkc.Frontend Zkc.Frontend.Written Zkc.Formal.Interactive.Sumcheck
open Zkc.Formal.Written Zkc.Formal.FiniteService Zkc.Formal.ProbabilisticProcess OracleComp
open scoped NNRat NNReal ENNReal

/-- Each paid occurrence must belong to the sole application under this verifier. -/
def applicationCharges (site : Key) (charge : DrawCharge) : List (Site × Nat × Nat × Nat) :=
  charge.draws.map fun (_,draw) => (⟨[site],draw⟩,charge.numerator,charge.denominator,1)

/-- A consumer of a single-call table verifier and the cap data of its named written goal. -/
structure SingleRoundGoal (c : AdmittedRoot) (n : Nat) (name draw : String) (expression : LineExpression) where
  checked : ChargedSumcheck c n draw
  selected : RoundSpecification.Selected
  source : RoundSpecification.read c.state checked.keys.reduction.number = .ok selected
  polynomial : selected.expression = expression
  claims : GoalClaims
  fromSource : goalClaims c [name] = .ok claims
  goal : ClaimedGoal
  chosen : claims.goals = [goal]
  relation : (claims.state.results.key? goal.relation).map (·.declaration) = some checked.relation
  operands : goal.statement = #[0,1]
  observer : claims.verifier = 1
  sites : goal.caps.sites = applicationCharges checked.keys.site checked.issued.charge
  denominator : 0 < checked.issued.charge.denominator
  budget : goal.caps.budget = ((checked.issued.charge.draws.length * checked.issued.charge.numerator : Nat) : ℚ≥0) /
    checked.issued.charge.denominator

def singleRoundGoal (c : AdmittedRoot) (n : Nat) (name draw : String) (expression : LineExpression)
    (companion : (Zkc.Formal.Written.SumcheckRows.sourceRows c.emission.bindings).Companion expression.decode) :
    Except String (SingleRoundGoal c n name draw expression) := do
  match located : sumcheckCallKeys c.emission ⟨c.id⟩ with
  | none => throw "expected a single reduction"
  | some keys =>
    match read : RoundSpecification.read c.state keys.reduction.number with
    | .error why => throw why
    | .ok selected =>
      if polynomial : selected.expression = expression then do
        let checked ← chargeSumcheckAt c n draw keys located (selectedMembers _ selected companion)
        have same := Option.some.inj (checked.located.symm.trans located)
        match fromSource : goalClaims c [name] with
        | .error why => throw why
        | .ok claims =>
          match chosen : claims.goals with
          | [goal] =>
            let charge := checked.issued.charge
            if ok : (claims.state.results.key? goal.relation).map (·.declaration) = some checked.relation ∧
                goal.statement = #[0,1] ∧ claims.verifier = 1 ∧
                goal.caps.sites = applicationCharges checked.keys.site charge ∧ 0 < charge.denominator ∧
                goal.caps.budget = ((charge.draws.length * charge.numerator : Nat) : ℚ≥0) / charge.denominator then
              return by
                obtain ⟨relation,operands,observer,sites,denominator,budget⟩ := ok
                exact ⟨checked,selected,same.symm ▸ read,polynomial,claims,fromSource,goal,chosen,
                  relation,operands,observer,sites,denominator,budget⟩
            else throw "the selected goal does not pay for the verifier at its checked call"
          | _ => throw "expected one written goal"
      else throw "the source polynomial differs from the companion"

theorem SingleRoundGoal.total_eq {c : AdmittedRoot} {n : Nat} {name draw : String} {expression : LineExpression} (g : SingleRoundGoal c n name draw expression) :
    total g.checked.issued.charge = g.goal.caps.total := by
  unfold CapTable.total
  rw [g.budget, toProbability_natCast_div _ _ g.denominator]
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
