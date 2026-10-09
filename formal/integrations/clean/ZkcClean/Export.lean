import ZkcClean.Flatten
import Clean.Air.FlatComponent

/-! Export of a Clean flat AIR component into a serialized arithmetic artifact.

The admitted fragment is channel-free and lookup-free *anywhere* in the
flattened operations, including nested subcircuits: every component's body is
itself a nested subcircuit of `Component.operations`. Witness operations are
skipped because witness generation does not restrict the accepted witnesses.
Each assertion is exported in order. Constants use Clean's canonical embedding
`FiniteField.val`; a variable at or beyond the declared width is refused,
because `Environment.fromArray` would silently read zero there.
-/

set_option autoImplicit false

namespace ZkcClean

/-- A serialized ring expression over one trace row. -/
inductive Term where
  | constant (value : Nat)
  | column (index : Nat)
  | add (left right : Term)
  | mul (left right : Term)
  deriving DecidableEq, Repr

/-- The exported relation: field size of the canonical constant presentation,
row width and every assertion. Equality is the artifact's identity. -/
structure Artifact where
  fieldSize : Nat
  width : Nat
  assertions : List Term
  deriving DecidableEq, Repr

inductive Refusal where
  | lookup
  | interaction
  | variableOutOfRange (index : Nat)
  deriving DecidableEq, Repr

/-- Export results are compared exactly, including the refusal reason. -/
instance : DecidableEq (Except Refusal Artifact)
  | .ok a, .ok b =>
      if h : a = b then .isTrue (h ▸ rfl) else .isFalse (by intro e; cases e; exact h rfl)
  | .error a, .error b =>
      if h : a = b then .isTrue (h ▸ rfl) else .isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => .isFalse (by intro e; cases e)
  | .error _, .ok _ => .isFalse (by intro e; cases e)

variable {F : Type} [FiniteField F]

/-- Every variable of the expression is below `width`. -/
def Bounded (width : Nat) : Expression F → Prop
  | .var v => v.index < width
  | .const _ => True
  | .add left right | .mul left right => Bounded width left ∧ Bounded width right

/-- The total serialization of an expression. -/
def encode : Expression F → Term
  | .var v => .column v.index
  | .const c => .constant (FiniteField.val c)
  | .add left right => .add (encode left) (encode right)
  | .mul left right => .mul (encode left) (encode right)

def exportExpression (width : Nat) : Expression F → Except Refusal Term
  | .var v => if v.index < width then .ok (.column v.index) else .error (.variableOutOfRange v.index)
  | .const c => .ok (.constant (FiniteField.val c))
  | .add left right =>
      match exportExpression width left, exportExpression width right with
      | .ok l, .ok r => .ok (.add l r)
      | .error e, _ => .error e
      | .ok _, .error e => .error e
  | .mul left right =>
      match exportExpression width left, exportExpression width right with
      | .ok l, .ok r => .ok (.mul l r)
      | .error e, _ => .error e
      | .ok _, .error e => .error e

def exportFlat (width : Nat) : List (FlatOperation F) → Except Refusal (List Term)
  | [] => .ok []
  | .witness _ _ :: rest => exportFlat width rest
  | .assert e :: rest =>
      match exportExpression width e, exportFlat width rest with
      | .ok t, .ok ts => .ok (t :: ts)
      | .error r, _ => .error r
      | .ok _, .error r => .error r
  | .lookup _ :: _ => .error .lookup
  | .interact _ :: _ => .error .interaction

def exportOperations (width : Nat) (operations : Operations F) : Except Refusal Artifact :=
  match exportFlat width (flatten operations) with
  | .ok assertions => .ok { fieldSize := FiniteField.size F, width, assertions }
  | .error r => .error r

/-- The component's row width is Clean's `Component.width`, the number of
variables its instantiated circuit allocates. -/
def exportComponent (component : Air.Flat.Component F) : Except Refusal Artifact :=
  exportOperations component.width component.operations

theorem exportExpression_ok {width : Nat} :
    ∀ {e : Expression F} {t : Term}, exportExpression width e = .ok t →
      Bounded width e ∧ t = encode e
  | .var v, t, h => by
      unfold exportExpression at h
      split at h
      · cases h; exact ⟨by assumption, rfl⟩
      · cases h
  | .const c, t, h => by
      cases h; exact ⟨trivial, rfl⟩
  | .add left right, t, h => by
      unfold exportExpression at h
      split at h
      · rename_i l r hl hr
        cases h
        obtain ⟨bl, rfl⟩ := exportExpression_ok hl
        obtain ⟨br, rfl⟩ := exportExpression_ok hr
        exact ⟨⟨bl, br⟩, rfl⟩
      · cases h
      · cases h
  | .mul left right, t, h => by
      unfold exportExpression at h
      split at h
      · rename_i l r hl hr
        cases h
        obtain ⟨bl, rfl⟩ := exportExpression_ok hl
        obtain ⟨br, rfl⟩ := exportExpression_ok hr
        exact ⟨⟨bl, br⟩, rfl⟩
      · cases h
      · cases h

theorem exportExpression_of_bounded {width : Nat} :
    ∀ {e : Expression F}, Bounded width e → exportExpression width e = .ok (encode e)
  | .var v, h => by simp only [exportExpression, encode, if_pos (show v.index < width from h)]
  | .const c, _ => rfl
  | .add left right, h => by
      simp only [exportExpression, exportExpression_of_bounded h.1,
        exportExpression_of_bounded h.2, encode]
  | .mul left right, h => by
      simp only [exportExpression, exportExpression_of_bounded h.1,
        exportExpression_of_bounded h.2, encode]

/-- What a successful flat export establishes about the upstream lists. -/
theorem exportFlat_ok {width : Nat} :
    ∀ {operations : List (FlatOperation F)} {terms : List Term},
      exportFlat width operations = .ok terms →
      FlatOperation.lookups operations = [] ∧
      FlatOperation.interactions operations = [] ∧
      (∀ e ∈ FlatOperation.constraints operations, Bounded width e) ∧
      terms = (FlatOperation.constraints operations).map encode
  | [], terms, h => by
      cases h
      exact ⟨rfl, rfl, by simp [FlatOperation.constraints], rfl⟩
  | .witness m compute :: rest, terms, h => by
      have := exportFlat_ok (operations := rest) h
      simpa [FlatOperation.lookups, FlatOperation.interactions,
        FlatOperation.constraints] using this
  | .assert e :: rest, terms, h => by
      unfold exportFlat at h
      split at h
      · rename_i t ts he hrest
        cases h
        obtain ⟨bounded, rfl⟩ := exportExpression_ok he
        obtain ⟨hl, hi, hb, rfl⟩ := exportFlat_ok hrest
        refine ⟨by simpa [FlatOperation.lookups] using hl,
          by simpa [FlatOperation.interactions] using hi, ?_, by simp [FlatOperation.constraints]⟩
        intro e' he'
        simp only [FlatOperation.constraints, List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact bounded
        · exact hb e' he'
      · cases h
      · cases h
  | .lookup _ :: _, terms, h => by cases h
  | .interact _ :: _, terms, h => by cases h

/-- Conversely, every admitted list exports exactly its encoded assertions. -/
theorem exportFlat_of_admitted {width : Nat} :
    ∀ {operations : List (FlatOperation F)},
      FlatOperation.lookups operations = [] →
      FlatOperation.interactions operations = [] →
      (∀ e ∈ FlatOperation.constraints operations, Bounded width e) →
      exportFlat width operations = .ok ((FlatOperation.constraints operations).map encode)
  | [], _, _, _ => rfl
  | .witness m compute :: rest, hl, hi, hb => by
      simp only [exportFlat, FlatOperation.constraints]
      exact exportFlat_of_admitted (by simpa [FlatOperation.lookups] using hl)
        (by simpa [FlatOperation.interactions] using hi)
        (by simpa [FlatOperation.constraints] using hb)
  | .assert e :: rest, hl, hi, hb => by
      have he : Bounded width e := hb e (by simp [FlatOperation.constraints])
      have hrest := exportFlat_of_admitted (operations := rest)
        (by simpa [FlatOperation.lookups] using hl)
        (by simpa [FlatOperation.interactions] using hi)
        (fun e' h' => hb e' (by simp [FlatOperation.constraints, h']))
      simp only [exportFlat, exportExpression_of_bounded he, hrest, FlatOperation.constraints,
        List.map_cons]
  | .lookup _ :: _, hl, _, _ => by simp [FlatOperation.lookups] at hl
  | .interact _ :: _, _, hi, _ => by simp [FlatOperation.interactions] at hi

/-- The facts carried by an admitted export of `operations` at `width`. -/
structure Admitted (width : Nat) (operations : Operations F) (artifact : Artifact) : Prop where
  fieldSize_eq : artifact.fieldSize = FiniteField.size F
  width_eq : artifact.width = width
  noLookups : operations.lookups = []
  noInteractions : operations.interactions = []
  bounded : ∀ e ∈ operations.constraints, Bounded width e
  assertions : artifact.assertions = operations.constraints.map encode

theorem exportOperations_ok {width : Nat} {operations : Operations F} {artifact : Artifact}
    (h : exportOperations width operations = .ok artifact) : Admitted width operations artifact := by
  unfold exportOperations at h
  split at h
  · rename_i terms hterms
    cases h
    obtain ⟨hl, hi, hb, rfl⟩ := exportFlat_ok hterms
    rw [lookups_flatten] at hl
    rw [interactions_flatten] at hi
    rw [constraints_flatten] at hb
    exact ⟨rfl, rfl, hl, hi, hb, by rw [constraints_flatten]⟩
  · cases h

/-- The export succeeds exactly on the admitted fragment, and then its artifact
is determined by the upstream constraint list. -/
theorem exportOperations_eq_ok {width : Nat} {operations : Operations F}
    (noLookups : operations.lookups = []) (noInteractions : operations.interactions = [])
    (bounded : ∀ e ∈ operations.constraints, Bounded width e) :
    exportOperations width operations =
      .ok { fieldSize := FiniteField.size F, width,
            assertions := operations.constraints.map encode } := by
  unfold exportOperations
  rw [exportFlat_of_admitted (by rwa [lookups_flatten]) (by rwa [interactions_flatten])
    (by rwa [constraints_flatten]), constraints_flatten]

/-- A refusal is issued only outside the admitted fragment. -/
theorem exportOperations_refused {width : Nat} {operations : Operations F} {refusal : Refusal}
    (h : exportOperations width operations = .error refusal) :
    operations.lookups ≠ [] ∨ operations.interactions ≠ [] ∨
      ∃ e ∈ operations.constraints, ¬ Bounded width e := by
  by_contra admitted
  simp only [not_or, not_not, not_exists, not_and] at admitted
  obtain ⟨noLookups, noInteractions, bounded⟩ := admitted
  rw [exportOperations_eq_ok noLookups noInteractions bounded] at h
  cases h

theorem exportComponent_ok {component : Air.Flat.Component F} {artifact : Artifact}
    (h : exportComponent component = .ok artifact) :
    Admitted component.width component.operations artifact :=
  exportOperations_ok h

end ZkcClean
