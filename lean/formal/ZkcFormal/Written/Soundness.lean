module

public import Zkc.Subject.WrittenGoal
public import ZkcFormal.Written.Goal.Inputs
public import ZkcFormal.Written.FunctionMeaning
public import ZkcFormal.Written.LawSamplers

@[expose] public section
set_option autoImplicit false

/-! The return probability of a written verifier at a short application of a relation.
The same bound applies to every deployed path, valid verifier input and conforming service.
A separate receipt states that the rejection premise is met at a valid input.

A statement of soundness reads a short application (`Zkc.Subject.ShortApplication`): the
relation, its arity, its Boolean result and the statement operands. The place of a clause in its
contract and its witness operands are of the decision (`Zkc.Subject.Decision`) and are not read
here. -/

namespace ZkcFormal.Written.Soundness

open Zkc.Core Zkc.Subject ProbabilisticProcess
open scoped ENNReal

variable {V : Vocabulary} (M : Model V)

open Goal.Internal

variable {pkg : Package V} {scheme : WrittenRoot pkg} (app : ShortApplication scheme)

/-- The rejection expression at a short application, elaborated where it is used: here and
at a goal's short application in `ZkcFormal.Written.Goal`. -/
scoped macro "rejectionAt%(" M:term ", " app:term ", " p:term ", " relation:term ", " xs:term ")" : term =>
  `(let statement := ($app).statement.map (G := ($M).Val) fun t port ↦
      reveal $M (a := ⟨t, port.holders⟩) port.heldByVerifier (valueAt port.member $xs)
    witnesses $M (($app).relation.header.ins.drop ($app).arity) fun ws ↦
      validWitnesses $M ws <|
        functionResult (M := $M) (t := .bool) (($app).boolean ▸ fnMeaning $M $p $relation
          (arguments _ ($app).arity statement ws)) ≠ some true)

/-- No valid witness makes the selected relation return true on these statement operands: the
statement is outside the relation's language. A witness at which the relation stops does not
make the statement accepted. The witness mapping records source positions. The universal
quantifiers use the function types. -/
def Rejected (p : Typed V) (relation : Member p.headers.fns app.relation.header)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins) : Prop :=
  rejectionAt%(M, app, p, relation, xs)

/-- **What a rejected statement is, pointwise**: at the statement's operands, every list of
valid witnesses gives the relation a result other than `some true`. -/
theorem rejected_iff (p : Typed V) (relation : Member p.headers.fns app.relation.header)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins) :
    Rejected M app p relation xs ↔
      ∀ ws : HList M.Val (app.relation.header.ins.drop app.arity), ws.All M.Valid →
        functionResult (M := M) (t := .bool) (app.boolean ▸ fnMeaning M p relation
          (arguments _ app.arity (app.statement.map (G := M.Val) fun t port ↦
            reveal M (a := ⟨t, port.holders⟩) port.heldByVerifier (valueAt port.member xs)) ws)) ≠
          some true := by
  unfold Rejected
  dsimp only
  rw [witnesses_iff]
  exact forall_congr' fun ws ↦ validWitnesses_iff M ws _

variable (draws : LawDraws M)

/-- At the given members, returning on a rejected statement has probability at most `b`. -/
def BoundOf (b : ℝ≥0∞) (p : Typed V) (root : Member p.headers.protocols scheme.entry.header)
    (relation : Member p.headers.fns app.relation.header) : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Rejected M app p relation xs →
      ReturnsWithin (roleMeaning M p root scheme.verifier path xs)
        (lawSamplers M draws) (Permitted M) (fun _ ↦ True) b

/-- The bound at the selected members of the installation. -/
def Installed (b : ℝ≥0∞) : Prop :=
  BoundOf M app draws b pkg.installed scheme.entry.member app.relation.member

/-- Look up both named entries in the same admitted program before applying its claim. -/
def admission (stored : NamedProgram V) (association : Association)
    (rootHeader : ProtocolHeader V) (rootKey : Key) (relationHeader : FnHeader V) (relationKey : Key)
    (claim : (p : Typed V) → Member p.headers.protocols rootHeader →
      Member p.headers.fns relationHeader → Prop) : Prop :=
  ∀ {a : Admitted V}, admit stored association = .ok a →
    ∃ root : Member a.program.headers.protocols rootHeader,
      a.program.findProtocol rootKey = some ⟨rootHeader, root⟩ ∧
      ∃ relation : Member a.program.headers.fns relationHeader,
        a.program.find relationKey = some (.fn relation) ∧ claim a.program root relation

/-- At the selected root and relation, properties of the installed members hold at precisely
the members found by admission. Both lookups are deterministic, and the package admits. -/
theorem installed_iff_admission (P : (p : Typed V) → Member p.headers.protocols scheme.entry.header →
    Member p.headers.fns app.relation.header → Prop) :
    P pkg.installed scheme.entry.member app.relation.member ↔
      admission pkg.stored pkg.association scheme.entry.header scheme.entry.header.key
        app.relation.header app.relation.header.key P := by
  constructor
  · intro holds a ok
    exact pkg.atProtocolAndFunction ok _ _ scheme.entry.found _ _ app.relation.found P holds
  · intro admitted
    obtain ⟨a, ok⟩ := pkg.admitted_exists
    have selected := admitted ok
    rw [pkg.readback ok] at selected
    obtain ⟨root, hr, relation, hf, holds⟩ := selected
    have root_eq : scheme.entry.member = root :=
      eq_of_heq (Sigma.mk.inj (Option.some.inj (scheme.entry.found.symm.trans hr))).2
    have fn_eq : app.relation.member = relation :=
      eq_of_heq (Ref.fn.inj (Option.some.inj (app.relation.found.symm.trans hf))).2
    subst root
    subst relation
    exact holds

/-- The bound at the members obtained by looking up the selected keys after admission. -/
def AdmittedBound (b : ℝ≥0∞) : Prop :=
  admission pkg.stored pkg.association scheme.entry.header scheme.entry.header.key
    app.relation.header app.relation.header.key (BoundOf M app draws b)

theorem installed_iff_admitted (b : ℝ≥0∞) : Installed M app draws b ↔ AdmittedBound M app draws b :=
  installed_iff_admission app (BoundOf M app draws b)

/-- Interpretation covers the selected source, and its admitted verifier has the stated bound. -/
def Result (covers : NamedProgram V → Key → Key → Bool) (b : ℝ≥0∞) : Prop :=
  covers pkg.stored scheme.entry.header.key app.relation.header.key = true ∧ AdmittedBound M app draws b

/-- Rejection by all valid witnesses and a served model hold together at one valid input. -/
def Witnessed : Prop :=
  inputs M scheme.verifier true scheme.entry.header.ins fun xs ↦
    Served (lawSamplers M draws) (Permitted M) ∧
      Rejected M app pkg.installed app.relation.member xs

theorem boundOf_mono {b larger : ℝ≥0∞} (le : b ≤ larger) {p : Typed V}
    {root : Member p.headers.protocols scheme.entry.header} {relation : Member p.headers.fns app.relation.header}
    (holds : BoundOf M app draws b p root relation) : BoundOf M app draws larger p root relation :=
  fun path ↦ mapInputs M _ _ _ _ (fun _ h rejected ↦ (h rejected).mono le) (holds path)

theorem installed_mono {b larger : ℝ≥0∞} (le : b ≤ larger) (holds : Installed M app draws b) :
    Installed M app draws larger :=
  boundOf_mono M app draws le holds

theorem admitted_mono {b larger : ℝ≥0∞} (le : b ≤ larger) (holds : AdmittedBound M app draws b) :
    AdmittedBound M app draws larger :=
  (installed_iff_admitted M app draws larger).mp <|
    installed_mono M app draws le ((installed_iff_admitted M app draws b).mpr holds)

/-- Each choice of valid visible inputs can introduce the matching existential telescope. -/
private theorem introInputs (r : Role) :
    ∀ (ports : List (LTy V)) (P : HList (RV M r) ports → Prop) (R : Prop),
      (inputs M r true ports P → R) → inputs M r false ports (fun xs ↦ P xs → R)
  | [], _, _, finish => finish
  | port :: rest, _, _, finish => by
    by_cases h : r ∈ port.holders
    · simp only [inputs, h, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte] at finish ⊢
      exact fun x hx ↦ introInputs r rest _ _ (fun hrest ↦ finish ⟨x, hx, hrest⟩)
    · simp only [inputs, h, ↓reduceDIte] at finish ⊢
      exact introInputs r rest _ _ finish

/-- Valid verifier inputs and installed rejection meet the hypotheses with the given service. -/
theorem witnessed_of (served : Served (lawSamplers M draws) (Permitted M)) :
    inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
      Rejected M app pkg.installed app.relation.member xs → Witnessed M app draws :=
  mapInputs M _ _ _ _ (fun _ h rejected ↦ h ⟨served, rejected⟩)
    (introInputs M _ _ _ _ (fun h ↦ h))

end ZkcFormal.Written.Soundness
