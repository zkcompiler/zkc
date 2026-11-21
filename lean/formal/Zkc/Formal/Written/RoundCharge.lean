module

public import Zkc.Formal.Written.Ceiling
public import Zkc.Formal.Written.RoundService
public import Zkc.Formal.Interactive.SourceSumcheck

@[expose] public section
namespace Zkc.Formal.Written.RoundCharge
open Core Interactive Sumcheck ReductionRound FiniteService ProbabilisticProcess OracleComp
open Frontend.Written (DrawCharge)
open scoped NNReal ENNReal

variable {V : Vocabulary} {p : Core.Typed V} {key : Key} {t state residual : V.Ty}
    {k n : Nat} {events : Events t}

def locations (linked : Linked p key state t residual k n events) :=
  linked.rounds.instances.map fun r => ([(r.block,r.iteration)], challengeSite r.checked.sites)

/-- Check the complete source operand against the very reduction used by the semantic
theorem. Multiplicity counts distinct dynamic block positions in execution order. -/
def Matches (charge : DrawCharge) (linked : Linked p key state t residual k n events)
    (degree order : Nat) : Prop :=
  charge.owner = key ∧ charge.draws = locations linked ∧ charge.draws.Nodup ∧ 0 < charge.denominator ∧
    (0 < n → degree * charge.denominator ≤ charge.numerator * order)

instance (charge : DrawCharge) (linked : Linked p key state t residual k n events)
    (degree order : Nat) : Decidable (Matches charge linked degree order) :=
  inferInstanceAs (Decidable (_ ∧ _))

export Zkc.Formal.Written (total)

/-- Transport the family theorem and its exact finite experiment to the external service.
Only the caller chooses the event. Both interpreters observe the same reply and next state. -/
theorem probability_le {S : Sig} {σ H A F : Type} {charge : DrawCharge}
    {linked : Linked p key state t residual k n events} {degree : Nat}
    (service : Slots S σ) (proc : Process S H A) (s : σ) (event : A → σ → Bool)
    (points : List F) (positive : 0 < points.length)
    (matches_ : Matches charge linked degree points.length)
    (bounded : (finite service).probability proc s event ≤ (n : Mass) * roundCost degree points) :
    prEvent (observed event <$> run (FiniteService.service service) proc s) ≤ total charge := by
  obtain ⟨_,draws,_,denPositive,covers⟩ := matches_
  exact writtenCeiling service proc s event charge n degree points.length positive
    (by simp [draws, locations, linked.rounds.length_instances]) denPositive covers bounded

variable {rows : ScalarRows V} {vectors : (d : Nat) → TableRestriction.Rows rows.scalarTy d}
    {root red eval : Key} {ev : Events rows.scalarTy} {width : Nat} {σ : Type}

/-- Written bound for acceptance by the admitted Sumcheck verifier on a false public sum. -/
theorem sumcheck {decode : ScalarRows.PairEncoding} (cert : TableVerifier.Certified rows vectors p root red eval n ev decode)
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (vectorMath : ∀ d, d < n → TableRestriction.Arithmetic (vectors d) M)
    (equality : ScalarEquality.Law rows.scalarTy ev.equal ev.equalType M)
    (alphabet : Fin (width+1) → rows.F M) (distinct : (List.ofFn alphabet).Nodup)
    (advance : Occurrence → rows.F M → σ → σ) (other : Slots (RSig M) σ)
    (charge : DrawCharge) (binding : Matches charge cert.linked 1 (width+1))
    (path : List Frame) (s : σ) (x : Cube (rows.F M) n) (claim : rows.F M) (wrong : claim ≠ Cube.sum n x)
    (collisions : CollisionBound (fun a : rows.F M × rows.F M => a.1 + a.2) line 1 := lineCollisions) :
    prEvent (observed (fun _ _ => true) <$> run
      (service (RoundService.withChallenge M ev alphabet advance other))
      (roleMeaning M p cert.root 1 path (TableVerifier.args M (Cube.flatten n x) claim)) s) ≤ total charge := by
  apply probability_le _ _ _ _ (List.ofFn alphabet) (by simp) (by simpa using binding)
  exact cert.soundFrom rows vectors M math vectorMath equality _ _ distinct _ path s x claim wrong
    (cert.linked.rounds.freshFromService _ _ _ _ _ _ (RoundService.fresh M ev alphabet advance other) _ _ _) collisions

/-- Written degree-two bound at a reached GKR layer call. Its public relation and honest
quadratic still belong to the layer. The observed event is a correct residual of a false claim. -/
theorem gate {hdr : ProtocolHeader V} {member : Member p.headers.protocols hdr}
    {site loopKey : Key} {args : List Name} {before layers inside : Nat}
    (atCall : AtSite p member key site state rows.scalarTy residual k n ev args (loopRoute before loopKey layers inside))
    {primitive : V.RowKey} {sig : V.row primitive = some (Gate.signature rows)}
    (checked : atCall.linked.rounds.AllMembers (fun ops => Gate.Laws rows primitive sig atCall.linked.entry.definitions ops))
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (model : Gate.Evaluation rows primitive sig M) (equality : ScalarEquality.Law rows.scalarTy ev.equal ev.equalType M)
    (i : Fin layers) (q : Claims (rows.F M)) (honest : ∀ d : Fin n, q.State (d.val+1) → Quadratic (rows.F M))
    (sum : ∀ d x, q.value (d.val+1) x = (honest d x).boundary)
    (restricted : ∀ d x r, q.value d.val (q.restrict d.val x r) = (honest d x).eval r)
    (alphabet : Fin (width+1) → rows.F M) (distinct : (List.ofFn alphabet).Nodup)
    (advance : Occurrence → rows.F M → σ → σ) (other : Slots (RSig M) σ)
    (charge : DrawCharge) (binding : Matches charge atCall.linked 2 (width+1))
    (path : List Frame) (s : σ) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (rows.F M)) (claim : rows.F M)
    (x : q.State n) (wrong : claim ≠ q.value n x)
    (collisions : CollisionBound (Quadratic.boundary (F := rows.F M)) Quadratic.eval 2 := Quadratic.collisions) :
    prEvent (observed (fun vs _ => correctReturn M q x point.length vs) <$> run
      (service (RoundService.withChallenge M ev alphabet advance other))
      (roleOp M 1 (Defs.fnTable M atCall.callerEntry.definitions) (Defs.rTable M atCall.callerEntry.definitions)
        site atCall.linked.application (path ++ [.iteration loopKey i.val]) (publicArgs M hidden point claim)) s) ≤ total charge := by
  apply probability_le _ _ _ _ (List.ofFn alphabet) (by simp) (by simpa using binding)
  exact atCall.gate_soundFrom rows checked M math model equality i q honest sum restricted _ _ distinct _
    path s hidden point claim x wrong
    (atCall.linked.rounds.freshFromService _ _ _ _ _ _ (RoundService.fresh M ev alphabet advance other) _ _ _) collisions

end Zkc.Formal.Written.RoundCharge
