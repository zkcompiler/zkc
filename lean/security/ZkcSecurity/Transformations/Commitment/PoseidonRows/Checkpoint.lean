module

public import ZkcSecurity.Transformations.Commitment.PoseidonRows.RecordStability
public import ZkcSecurity.Transformations.Commitment.TableLog

@[expose] public section

/-! # Extraction before first transcript allocation

Primitive calls use key `none`; a transcript allocation uses `some key` and its registered roots.
This log represents the physical allocation boundary, which may be an off-path constituent of
a grouped query. Connecting that boundary to a selected source execution remains the producer's
obligation. The unconditional freeze law and conditional future agreement are separate theorems.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {Key F : Type} {rate : ℕ} [DecidableEq Key] [Zero F] [DecidableEq F]

abbrev HistoryData (F : Type) (rate : ℕ) := Exposure F rate ⊕ List (Digest F rate)
abbrev History (Key F : Type) (rate : ℕ) :=
  List ((_key : Option Key) × HistoryData F rate)

def primitive (e : Exposure F rate) : (_key : Option Key) × HistoryData F rate :=
  ⟨none, .inl e⟩

def allocation (key : Key) (roots : List (Digest F rate)) :
    (_key : Option Key) × HistoryData F rate := ⟨some key, .inr roots⟩

def calls (history : History Key F rate) : List (Exposure F rate) :=
  history.filterMap fun entry ↦ match entry.2 with | .inl e => some e | .inr _ => none

omit [DecidableEq Key] [Zero F] [DecidableEq F] in
theorem calls_append (a b : History Key F rate) : calls (a ++ b) = calls a ++ calls b := by
  simp [calls]

/-- Fresh coordinate flags at every actual allocation marker. The event does not mention
extraction, decoded rows, successful openings, or stability. Repeated pairs retain birth order. -/
def GoodHistory (history : History Key F rate) : Prop :=
  Good (normalize (calls history)) ∧
    ∀ (prior : History Key F rate) (key : Key) (roots : List (Digest F rate))
      (later : History Key F rate), history = prior ++ allocation key roots :: later →
      ∀ fresh, normalize (calls history) = normalize (calls prior) ++ fresh →
        ∀ e ∈ fresh, e.forward = true → ∀ root ∈ roots, e.output.1 ≠ root

def checkpoint (request : Request rate) (key : Key) (history : History Key F rate)
    (root : Digest F rate) : Table (List F) :=
  extract request (normalize (calls (beforeFirst (some key) history))) root

/-- Structural freezing uses the existing generic first-allocation prefix law. -/
theorem checkpoint_frozen (request : Request rate) (key : Key) (history later : History Key F rate)
    (root : Digest F rate) (queried : ∃ entry ∈ history, entry.1 = some key) :
    checkpoint request key (history ++ later) root = checkpoint request key history root := by
  unfold checkpoint
  rw [beforeFirst_append_of_mem (some key) later history queried]

/-- The prior table is independent of the answer at the same allocation key. -/
theorem checkpoint_update {α : Type} (request : Request rate) (key : Key)
    (root : Digest F rate) (oa : OracleComp (OracleSpec.ofFn
      (fun _ : Option Key ↦ HistoryData F rate)) α)
    (table : Option Key → HistoryData F rate) (answer : HistoryData F rate) :
    checkpoint request key (OracleComp.tableQueryLog oa (Function.update table (some key) answer))
      root = checkpoint request key (OracleComp.tableQueryLog oa table) root := by
  unfold checkpoint
  rw [beforeFirst_update]

/-- Future agreement is proved from primitive bad-flag absence, rather than placed in `Good`.
The marker premise identifies the first allocation and its exact registered roots. -/
theorem checkpoint_agrees {request : Request rate} {key : Key} {history : History Key F rate}
    {root : Digest F rate} (good : GoodHistory history) {roots : List (Digest F rate)}
    {later : History Key F rate}
    (marker : history = beforeFirst (some key) history ++ allocation key roots :: later)
    (registered : root ∈ roots) :
    checkpoint request key history root = extract request (normalize (calls history)) root := by
  have cutPrefix : normalize (calls (beforeFirst (some key) history)) <+:
      normalize (calls history) := by
    have eqCalls : calls history = calls (beforeFirst (some key) history) ++ calls later := by
      conv_lhs => rw [marker, calls_append]
      simp [calls, allocation]
    rw [eqCalls]
    exact normalize_prefix _ _
  obtain ⟨fresh, extension⟩ := cutPrefix
  have safe := good.2 (beforeFirst (some key) history) key roots later marker fresh extension.symm
  have flags : ∀ e ∈ fresh, e.forward = true → e.output.1 ≠ root :=
    fun e em ef ↦ safe e em ef root registered
  unfold checkpoint
  rw [← extension]
  exact (extract_stable (by simpa [extension] using good.1) flags).symm

end ZkcSecurity.Commitment.PoseidonRows
