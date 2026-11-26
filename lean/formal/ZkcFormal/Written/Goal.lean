module

public import Zkc.Subject.WrittenGoal
public import ZkcFormal.Written.FunctionMeaning
public import ZkcFormal.Written.LawSamplers
public import ZkcFormal.Written.SiteCaps

@[expose] public section

/-!
A written goal selects a protocol, a deciding function and a table of caps. The verifier runs
on the full vector of role inputs. The decision selects statement operands from this same vector,
and rejection ranges over all valid witnesses of the deciding function.
-/

namespace ZkcFormal.Written.Goal

open Zkc.Core Zkc.Subject ProbabilisticProcess

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

end Internal

open Internal

variable {pkg : Package V} {scheme : WrittenRoot pkg} (g : WrittenGoal scheme)

/-- Every valid witness makes the selected relation return false on these statement operands.
The witness mapping records source positions. The universal quantifiers use the function types. -/
def Rejected (p : Typed V) (relation : Member p.headers.fns g.decision.relation.header)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins) : Prop :=
  let statement := g.decision.statement.map (G := M.Val) fun t port ↦
    reveal M (a := ⟨t, port.holders⟩) port.heldByVerifier (valueAt port.member xs)
  witnesses M (g.decision.relation.header.ins.drop g.decision.arity) fun ws ↦
    validWitnesses M ws <|
      functionResult (M := M) (t := .bool) (g.decision.boolean ▸ fnMeaning M p relation
        (arguments _ g.decision.arity statement ws)) = some false

variable (draws : LawDraws M)

/-- On valid inputs rejected by the deciding relation, the verifier returns with probability
at most the goal's cap total against the services of this model and its law draws. -/
def ClaimOf (p : Typed V) (root : Member p.headers.protocols scheme.entry.header)
    (relation : Member p.headers.fns g.decision.relation.header) : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Rejected M g p relation xs →
      ReturnsWithin (roleMeaning M p root scheme.verifier path xs)
        (lawSamplers M draws) (Permitted M) (fun _ ↦ True) g.fields.caps.total

/-- The claim at the two members in the installation. -/
def Claim : Prop :=
  ClaimOf M g draws pkg.installed scheme.entry.member g.decision.relation.member

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

/-- Admission at the headers and keys selected by this decision. -/
def admittedAt (claim : (p : Typed V) → Member p.headers.protocols scheme.entry.header →
    Member p.headers.fns g.decision.relation.header → Prop) : Prop :=
  admission pkg.stored pkg.association scheme.entry.header scheme.entry.header.key
    g.decision.relation.header g.decision.relation.header.key claim

set_option linter.dupNamespace false in
/-- The written claim at the entries found by admission. -/
def Goal : Prop := admittedAt g (ClaimOf M g draws)

/-- Coverage and the cap count on the stored program accompany the supplied goal. -/
def countedResult (stored : NamedProgram V) (rootKey relationKey : Key) (caps : CapTable)
    (covers : NamedProgram V → Key → Key → Bool) (goal : Prop) : Prop :=
  covers stored rootKey relationKey = true ∧ caps.counted stored rootKey = true ∧ goal

/-- The result at the keys and caps selected by this goal. -/
def resultOf (covers : NamedProgram V → Key → Key → Bool) (goal : Prop) : Prop :=
  countedResult pkg.stored scheme.entry.header.key g.decision.relation.header.key g.fields.caps
    covers goal

/-- Coverage, cap counts, and the written goal. -/
def Result (covers : NamedProgram V → Key → Key → Bool) : Prop :=
  resultOf g covers (Goal M g draws)

/-- The hypotheses are met together at one vector of valid verifier inputs. -/
def Witnessed : Prop :=
  inputs M scheme.verifier true scheme.entry.header.ins fun xs ↦
    Served (lawSamplers M draws) (Permitted M) ∧
      Rejected M g pkg.installed g.decision.relation.member xs

/-- The installed verifier is judged never to return, with each fee paid at its site within
the goal's budget. -/
def Judged : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Rejected M g pkg.installed g.decision.relation.member xs →
      (roleMeaning M pkg.installed scheme.entry.member scheme.verifier path xs).interpret
        (.charged (Permitted M) (paysWithin (lawSamplers M draws) (g.fields.caps.allowance M path)))
        (fun _ _ ↦ False) (fun _ _ ↦ True) g.fields.caps.budget

private theorem mapInputs (r : Role) :
    ∀ (ports : List (LTy V)) (P Q : HList (RV M r) ports → Prop),
      (∀ xs, P xs → Q xs) → inputs M r false ports P → inputs M r false ports Q
  | [], _, _, f, hp => f .nil hp
  | port :: rest, _, _, f, hp => by
    by_cases h : r ∈ port.holders
    · simp only [inputs, h, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact fun x hx ↦ mapInputs r rest _ _ (fun xs ↦ f (.cons (hide M r port x) xs)) (hp x hx)
    · simp only [inputs, h, ↓reduceDIte] at hp ⊢
      exact mapInputs r rest _ _ (fun xs ↦ f (.cons (nothing M h) xs)) hp

/-- A judgment with fees gives the installed probability bound. -/
theorem claim_of_judged (judged : Judged M g draws) : Claim M g draws :=
  fun path ↦ mapInputs M _ _ _ _ (fun _ h rejected ↦
    returnsWithin_of_never _ _ _ _ _ (h rejected)) (judged path)

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
      Rejected M g pkg.installed g.decision.relation.member xs → Witnessed M g draws :=
  mapInputs M _ _ _ _ (fun _ h rejected ↦ h ⟨served, rejected⟩)
    (introInputs M _ _ _ _ (fun h ↦ h))

end ZkcFormal.Written.Goal
