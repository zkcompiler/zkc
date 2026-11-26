module

public import Zkc.Subject.WrittenGoal
public import ZkcFormal.Written.FunctionMeaning
public import ZkcFormal.Written.LawSamplers

@[expose] public section
set_option autoImplicit false

/-! The return probability of a written verifier at a selected deciding clause.
The same bound applies to every deployed path, valid verifier input and conforming service.
A separate receipt states that the rejection premise is met at a valid input. -/

namespace ZkcFormal.Written.Soundness

open Zkc.Core Zkc.Subject ProbabilisticProcess
open scoped ENNReal

variable {V : Vocabulary} (M : Model V)

namespace Internal

/-- Bind each visible value next to its validity, building every position in the deployed header. -/
def inputs (r : Role) (existential : Bool) :
    (ports : List (LTy V)) → (HList (RV M r) ports → Prop) → Prop
  | [], k => k .nil
  | port :: rest, k =>
    if h : r ∈ port.holders then
      let more := fun (x : M.Val port.ty) ↦
        inputs r existential rest fun xs ↦ k (.cons (hide M r port x) xs)
      if existential then ∃ x, M.Valid port.ty x ∧ more x else ∀ x, M.Valid port.ty x → more x
    else
      inputs r existential rest fun xs ↦ k (.cons (nothing M h) xs)

/-- Read a heterogeneous value at its typed position. -/
def valueAt {α : Type} {F : α → Type} :
    {ts : List α} → {t : α} → Member ts t → HList F ts → F t
  | _, _, .head, .cons x _ => x
  | _, _, .tail i, .cons _ xs => valueAt i xs

/-- Assemble the two sides of the actual signature. Recursing on the signature makes the
argument spine compute even when the selected values are free variables. -/
def arguments {α : Type} {F : α → Type} :
    (ts : List α) → (n : Nat) → HList F (ts.take n) → HList F (ts.drop n) → HList F ts
  | [], _, _, _ => .nil
  | _ :: _, 0, _, ws => ws
  | _ :: ts, n + 1, .cons x xs, ws => .cons x (arguments ts n xs ws)

/-- Bind all witness values before entering the validity assumptions. -/
def witnesses :
    (ts : List V.Ty) → (HList M.Val ts → Prop) → Prop
  | [], k => k .nil
  | t :: ts, k => ∀ x : M.Val t, witnesses ts fun xs ↦ k (.cons x xs)

/-- Imply the body from each witness validity in parameter order. -/
def validWitnesses : {ts : List V.Ty} → HList M.Val ts → Prop → Prop
  | [], .nil, q => q
  | t :: _, .cons x xs, q => M.Valid t x → validWitnesses xs q

/-- Apply a pointwise implication under the universal deployed-input telescope. -/
theorem mapInputs (r : Role) :
    ∀ (ports : List (LTy V)) (P Q : HList (RV M r) ports → Prop),
      (∀ xs, P xs → Q xs) → inputs M r false ports P → inputs M r false ports Q
  | [], _, _, f, hp => f .nil hp
  | port :: rest, _, _, f, hp => by
    by_cases h : r ∈ port.holders
    · simp only [inputs, h, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact fun x hx ↦ mapInputs r rest _ _ (fun xs ↦ f (.cons (hide M r port x) xs)) (hp x hx)
    · simp only [inputs, h, ↓reduceDIte] at hp ⊢
      exact mapInputs r rest _ _ (fun xs ↦ f (.cons (nothing M h) xs)) hp

end Internal

open Internal

variable {pkg : Package V} {scheme : WrittenRoot pkg} (d : Decision scheme)

/-- Every valid witness makes the selected relation return false on these statement operands.
The witness mapping records source positions. The universal quantifiers use the function types. -/
def Rejected (p : Typed V) (relation : Member p.headers.fns d.relation.header)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins) : Prop :=
  let statement := d.statement.map (G := M.Val) fun t port ↦
    reveal M (a := ⟨t, port.holders⟩) port.heldByVerifier (valueAt port.member xs)
  witnesses M (d.relation.header.ins.drop d.arity) fun ws ↦
    validWitnesses M ws <|
      functionResult (M := M) (t := .bool) (d.boolean ▸ fnMeaning M p relation
        (arguments _ d.arity statement ws)) = some false

variable (draws : LawDraws M)

/-- At the given members, returning on a rejected statement has probability at most `b`. -/
def BoundOf (b : ℝ≥0∞) (p : Typed V) (root : Member p.headers.protocols scheme.entry.header)
    (relation : Member p.headers.fns d.relation.header) : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Rejected M d p relation xs →
      ReturnsWithin (roleMeaning M p root scheme.verifier path xs)
        (lawSamplers M draws) (Permitted M) (fun _ ↦ True) b

/-- The bound at the selected members of the installation. -/
def Installed (b : ℝ≥0∞) : Prop :=
  BoundOf M d draws b pkg.installed scheme.entry.member d.relation.member

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
    Member p.headers.fns d.relation.header → Prop) :
    P pkg.installed scheme.entry.member d.relation.member ↔
      admission pkg.stored pkg.association scheme.entry.header scheme.entry.header.key
        d.relation.header d.relation.header.key P := by
  constructor
  · intro holds a ok
    exact pkg.atProtocolAndFunction ok _ _ scheme.entry.found _ _ d.relation.found P holds
  · intro admitted
    obtain ⟨a, ok⟩ := pkg.admitted_exists
    have selected := admitted ok
    rw [pkg.readback ok] at selected
    obtain ⟨root, hr, relation, hf, holds⟩ := selected
    have root_eq : scheme.entry.member = root :=
      eq_of_heq (Sigma.mk.inj (Option.some.inj (scheme.entry.found.symm.trans hr))).2
    have fn_eq : d.relation.member = relation :=
      eq_of_heq (Ref.fn.inj (Option.some.inj (d.relation.found.symm.trans hf))).2
    subst root
    subst relation
    exact holds

/-- The bound at the members obtained by looking up the selected keys after admission. -/
def AdmittedBound (b : ℝ≥0∞) : Prop :=
  admission pkg.stored pkg.association scheme.entry.header scheme.entry.header.key
    d.relation.header d.relation.header.key (BoundOf M d draws b)

theorem installed_iff_admitted (b : ℝ≥0∞) : Installed M d draws b ↔ AdmittedBound M d draws b :=
  installed_iff_admission d (BoundOf M d draws b)

/-- Interpretation covers the selected source, and its admitted verifier has the stated bound. -/
def Result (covers : NamedProgram V → Key → Key → Bool) (b : ℝ≥0∞) : Prop :=
  covers pkg.stored scheme.entry.header.key d.relation.header.key = true ∧ AdmittedBound M d draws b

/-- Rejection by all valid witnesses and a served model hold together at one valid input. -/
def Witnessed : Prop :=
  inputs M scheme.verifier true scheme.entry.header.ins fun xs ↦
    Served (lawSamplers M draws) (Permitted M) ∧
      Rejected M d pkg.installed d.relation.member xs

theorem boundOf_mono {b larger : ℝ≥0∞} (le : b ≤ larger) {p : Typed V}
    {root : Member p.headers.protocols scheme.entry.header} {relation : Member p.headers.fns d.relation.header}
    (holds : BoundOf M d draws b p root relation) : BoundOf M d draws larger p root relation :=
  fun path ↦ mapInputs M _ _ _ _ (fun _ h rejected ↦ (h rejected).mono le) (holds path)

theorem installed_mono {b larger : ℝ≥0∞} (le : b ≤ larger) (holds : Installed M d draws b) :
    Installed M d draws larger :=
  boundOf_mono M d draws le holds

theorem admitted_mono {b larger : ℝ≥0∞} (le : b ≤ larger) (holds : AdmittedBound M d draws b) :
    AdmittedBound M d draws larger :=
  (installed_iff_admitted M d draws larger).mp <|
    installed_mono M d draws le ((installed_iff_admitted M d draws b).mpr holds)

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
      Rejected M d pkg.installed d.relation.member xs → Witnessed M d draws :=
  mapInputs M _ _ _ _ (fun _ h rejected ↦ h ⟨served, rejected⟩)
    (introInputs M _ _ _ _ (fun h ↦ h))

end ZkcFormal.Written.Soundness
