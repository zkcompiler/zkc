import Zkc.Tools.Formal.DrawCharge

namespace Zkc.Tools.Formal
open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Formal.Interactive Zkc.Formal.Interactive.Sumcheck
open Zkc.Formal.Written Zkc.Formal.FiniteService
open scoped Zkc.Formal.Written.RoundCharge NNReal ENNReal

/-- Resolved inputs to the plain, fixed-statement, written soundness experiment. -/
structure SumcheckRequest where
  scheme : DeclarationId
  subject : ProofSubject
  rounds : Nat
  draw : String
  ceiling : Option Rat

/-- Read the request, parties, table dimension and charged draw from the selected source.
The shape and interpolation obligations are discharged by the admitted verifier checker. -/
def readSumcheckRequest (c : AdmittedRoot) (goal : String) : ExportM SumcheckRequest := do
  let (sel, _) ← selectNamedGoal c.state goal .soundness
  let scheme := sel.scheme
  unless scheme.protocol == c.id do refuse scheme.span "GL3" "goal selects a different root"
  let some key := c.state.results.key? c.id | throw "missing root instance"
  let clauses ← contractOf c.state key.declaration scheme.span
  unless (clauses.filter (fun cl => cl matches .proves .. | .reduces ..)).size == 1 do
    refuse scheme.span "GL3" "expected a single deciding clause"
  let some body := c.state.results.checked? c.id | throw "missing typed caller"
  let .protocol caller := body.definition.body | throw "expected a protocol"
  let #[values, _] := caller.ports | throw "expected two public Sumcheck ports"
  let .seq _ (some size) := values.binder.type | throw "expected a sized public table"
  let some rounds := Static.powerOfTwo size | throw "expected a Boolean cube"
  let some ⟨hdr, _⟩ := c.evidence.admitted.program.findProtocol ⟨c.id⟩ | throw "missing admitted root"
  let parties ← writtenParties scheme caller.roster
  unless onlineParties hdr [.online, .online] parties.interactive parties.declaredProver == some (0, 1) do
    refuse scheme.span "GL3" "the deciding role must be the verifier of this scheme"
  for line in scheme.lines do
    unless line matches .construction .. | .prover .. do
      refuse scheme.span "GL3" "unsupported scheme directive for written Sumcheck"
  let some keys := sumcheckCallKeys c.emission ⟨c.id⟩ | throw "missing Sumcheck application"
  let some reduction := c.state.results.key? keys.reduction.number | throw "missing reduction"
  let contract ← contractOf c.state reduction.declaration scheme.span
  let #[site] := contract.filterMap (fun | .charge _ site _ => some site | _ => none)
    | throw "expected one charged draw in the selected reduction"
  let #[draw] := site.names | throw "expected a direct draw"
  return ⟨scheme.declaration, ⟨c.id, sel.specification⟩, rounds, draw.text, sel.ceiling⟩

/-- Without a requested maximum, publish the accumulated written bound. -/
def SumcheckRequest.bound (request : SumcheckRequest) (fee : DrawCharge) : Nat × Nat :=
  match request.ceiling with
  | some q => (q.num.toNat, q.den)
  | none => (fee.draws.length * fee.numerator, fee.denominator)

structure CertifiedSumcheckGoal (c : AdmittedRoot) (goal : String) where
  request : SumcheckRequest
  selected : readSumcheckRequest c goal = .ok request
  checked : ChargedSumcheck c request.rounds request.draw request.subject.specification
  plain : c.emission.bindings.rows = []
  positive : 0 < (request.bound checked.issued.charge).2
  within : let fee := checked.issued.charge
    fee.draws.length * fee.numerator * (request.bound fee).2 ≤ (request.bound fee).1 * fee.denominator

def certifySumcheckGoal (c : AdmittedRoot) (goal : String) : ExportM (CertifiedSumcheckGoal c goal) := do
  match selected : readSumcheckRequest c goal with
  | .error why => throw why
  | .ok request =>
    let checked ← chargeSumcheck c request.rounds request.draw request.subject.specification
    let fee := checked.issued.charge
    let budget := request.bound fee
    if plain : c.emission.bindings.rows = [] then
      if positive : 0 < budget.2 then
        if within : fee.draws.length * fee.numerator * budget.2 ≤ budget.1 * fee.denominator then
          return ⟨request, selected, checked, plain, positive, within⟩
        else throw "GL4: the accumulated written charge exceeds the requested ceiling"
      else throw "GL4: zero denominator"
    else throw "GL3: unsupported arithmetic model"

/-- The named source request, its successful admission and the certificate on that root. -/
structure IssuedSumcheckGoal (assembly : Assembly) (goal : String) where
  root : AdmittedRoot
  admitted : admitSoundnessGoal assembly goal = .ok root
  certified : CertifiedSumcheckGoal root goal

def issueSumcheckGoal (assembly : Assembly) (goal : String) :
    ExportM (IssuedSumcheckGoal assembly goal) := do
  match admitted : admitSoundnessGoal assembly goal with
  | .error why => throw why
  | .ok c => return ⟨c, admitted, ← certifySumcheckGoal c goal⟩

private theorem total_le_bound (fee : DrawCharge) (num den : Nat)
    (hf : 0 < fee.denominator) (hd : 0 < den)
    (h : fee.draws.length * fee.numerator * den ≤ num * fee.denominator) :
    total fee ≤ (num : ℝ≥0∞) / den := by
  have le : (fee.draws.length : ℝ≥0) * (fee.numerator / (fee.denominator : ℝ≥0)) ≤ num / (den : ℝ≥0) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by exact_mod_cast hf) (by exact_mod_cast hd)]
    exact_mod_cast h
  have feeNonzero : (fee.denominator : ℝ≥0) ≠ 0 := by exact_mod_cast hf.ne'
  have denNonzero : (den : ℝ≥0) ≠ 0 := by exact_mod_cast hd.ne'
  have lifted := ENNReal.coe_le_coe.mpr le
  simpa only [total, ENNReal.coe_mul, ENNReal.coe_div feeNonzero,
    ENNReal.coe_div denNonzero, ENNReal.coe_natCast] using lifted

/-- On a false public cube sum, the admitted deciding role returns with probability at most
the bound of this named request under the source-field uniform challenge service. -/
theorem CertifiedSumcheckGoal.falseAcceptance {c : AdmittedRoot} {goal : String}
    (g : CertifiedSumcheckGoal c goal)
    {σ : Type} (advance : Occurrence → Scalar → σ → σ) (other : Slots (RSig scalarModel) σ)
    (path : List Zkc.Core.Frame) (s : σ) (x : Cube Scalar g.request.rounds) (claim : Scalar)
    (wrong : claim ≠ Cube.sum _ x) :
    let cert := (g.checked.standardVerifier g.plain).1
    let budget := g.request.bound g.checked.issued.charge
    prEvent (observed (fun _ _ => true) <$> Zkc.Formal.ProbabilisticProcess.run
      (service (RoundService.withChallenge scalarModel ArithmeticModel.events
        (ZMod.finEquiv Zkc.Vocabulary.Field.bls12381Fr.order) advance other))
      (roleMeaning scalarModel _ cert.root 1 path
        (TableVerifier.args scalarModel (Cube.flatten _ x) claim)) s) ≤
      (budget.1 : ℝ≥0∞) / budget.2 := by
  apply (g.checked.primeBound g.plain advance other path s x claim wrong).trans
  exact total_le_bound _ _ _ g.checked.issued.binding.2.2.2.1 g.positive g.within

end Zkc.Tools.Formal
