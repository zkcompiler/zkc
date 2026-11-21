import Zkc.Tools.Formal.RoundSpecification
import Zkc.Formal.Written.PolynomialBounds
import Zkc.Formal.Interactive.MappedReduction
import Zkc.Formal.Interactive.InstalledPair
import Zkc.Formal.Interactive.PairSequence
import Zkc.Formal.Written.SumcheckRows

namespace Zkc.Tools.Formal
open Zkc.Core Zkc.Frontend Zkc.Formal.Interactive.Sumcheck ReductionRound
open Zkc.Formal.Written.SumcheckRows

variable {c : Written.AdmittedRoot} {hdr : ProtocolHeader c.emission.bindings.vocabulary}
variable {root : Member c.evidence.admitted.program.headers.protocols hdr} {red site : Key}
variable {observer : Role} {roles : List Role}
variable {state residual : c.emission.bindings.vocabulary.Ty} {k n : Nat} {args : List Name} {route : List OperationSite.Move}
local notation "rows" => sourceRows c.emission.bindings

/-- A vacuous sequence needs no executable member. On a nonempty sequence certify the two
source-selected definitions once, then check the exact references in each occurrence. -/
def selectedMembers {V : Zkc.Core.Vocabulary} (scalar : ScalarRows V) (selected : RoundSpecification.Selected)
    {expression : LineExpression} (proof : scalar.Companion expression.decode) : SequenceInstaller scalar expression.decode :=
  fun {_} defs unique {_ _ _ _ _ _ count} rounds =>
    if empty : count = 0 then by
      subst count
      cases rounds
      exact some ⟨True.intro⟩
    else do
      let installed ← installPair scalar defs expression.decode ⟨selected.boundary⟩ ⟨selected.evaluate⟩ unique proof
      rounds.checkMembers _ (installed.atMembers unique)

/-- The named source laws, the selected line expression, and the two operations in every
executed round belong to the same admitted application. -/
structure InstalledRound (call : MappedReduction (p := c.evidence.admitted.program) root red site state (sourceRows c.emission.bindings).scalarTy residual
  k n (sourceEvents c.emission.bindings) observer roles args route) (expression : LineExpression) where
  selected : RoundSpecification.Selected
  source : RoundSpecification.read c.state red.number = .ok selected
  polynomial : selected.expression = expression
  members : call.linked.rounds.AllMembers (fun ops => PairLaws rows call.linked.entry.definitions ops expression.decode)

def installRound (call : MappedReduction (p := c.evidence.admitted.program) root red site state (sourceRows c.emission.bindings).scalarTy residual
  k n (sourceEvents c.emission.bindings) observer roles args route) (expression : LineExpression) (companion : (rows).Companion expression.decode) :
    Except String (InstalledRound call expression) := do
  match source : RoundSpecification.read c.state red.number with
  | .error why => throw why
  | .ok selected =>
    if polynomial : selected.expression = expression then
      let entry := call.linked.entry
      let unique := (List.nodup_append.mp entry.distinct).1
      let some ⟨members⟩ := selectedMembers rows selected companion entry.definitions unique call.linked.rounds
        | throw "an installed boundary or evaluation failed its source law"
      return ⟨selected,source,polynomial,members⟩
    else throw "the selected source polynomial differs from the companion"

open Zkc.Formal.Interactive

/-- Probability of the caller's observation at the certified application. The caller identifies
its actual entry operands and explains why its return observation implies a correct residual. -/
theorem InstalledRound.probabilityAt {expression : LineExpression}
    {call : MappedReduction (p := c.evidence.admitted.program) root red site state (rows).scalarTy
      residual k n (sourceEvents c.emission.bindings) observer roles args route}
    (installed : InstalledRound call expression) (M : Model c.emission.bindings.vocabulary)
    [Field ((rows).F M)] [DecidableEq ((rows).F M)] (math : (rows).Arithmetic M)
    (equalLaw : ScalarEquality.Law (rows).scalarTy (sourceEvents c.emission.bindings).equal
      (sourceEvents c.emission.bindings).equalType M)
    {σ : Type} (service : Experiment (RSig M) σ) (points : List ((rows).F M))
    (distinct : points.Nodup) (positive : 0 < points.length) (path : List Zkc.Core.Frame) (s : σ)
    (operands : HList (RV M observer) call.operands) (hidden : RV M 1 ⟨state,[0]⟩)
    (point : List ((rows).F M)) (claim : (rows).F M) (x : Cube ((rows).F M) n) (wrong : claim ≠ Cube.sum n x)
    (entered : (call.verifier ▸ enterAll M (RoleMap.ofList roles call.distinct) observer
      (fitAllRV M call.fits operands)) = publicArgs M hidden point claim)
    (post : HList (RV M observer) ((PointReturn.ports (rows).scalarTy residual (k+n)).map
      (LTy.map (RoleMap.ofList roles call.distinct).to)) → σ → Bool)
    (returned : ∀ out after, post (leaveAll M (RoleMap.ofList roles call.distinct) observer
      (call.verifier.symm ▸ out)) after = true → correctReturn M Cube.claims x point.length out = true)
    (fresh : call.linked.rounds.FreshFrom M (Defs.fnTable M call.linked.entry.definitions)
      (Defs.rTable M call.linked.entry.definitions) (service.renamePeers (RoleMap.ofList roles call.distinct).to)
      points positive (path ++ [.application site]) (initialEnv M hidden k point claim) s) :
    service.probability (roleOp M observer (Defs.fnTable M call.caller.definitions)
      (Defs.rTable M call.caller.definitions) site
      (.apply call.linked.ref roles call.distinct call.covers call.operands call.fits) path operands) s post ≤
      (n : Mass) * roundCost 1 points := by
  apply call.soundFrom M Cube.claims (roundCost 1 points) _ service path s operands hidden point claim x wrong entered post returned
  · exact call.linked.rounds.boundsFromMembers _ installed.members M _ _ Cube.claims points positive 1
      (fun _ law => (PairLaws.interpret rows law M math points distinct Zkc.Formal.Written.PolynomialBounds.pairs).reindex Fin.val)
      equalLaw _ _ _ s x fresh
  · exact Mass.mul_nonneg Mass.natCast_nonneg (Mass.le_of_lt (Mass.inv_pos.mpr (Mass.natCast_pos.mpr positive)))

end Zkc.Tools.Formal
