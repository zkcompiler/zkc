module

public import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.RecordedCalls

@[expose] public section

/-! # Direct fixed-request implementation

This implementation follows the first forward-born rate match before attempting reconstruction.
It does not skip a failed first endpoint to search for a later successful leaf. Its equality to
the derived-macro presentation is proved on good records, including absent entries.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {F : Type} {rate : ℕ} [Zero F] [DecidableEq F]

def descend (log : List (Exposure F rate)) : ℕ → Digest F rate → ℕ → Option (Digest F rate)
  | 0, label, _ => some label
  | depth + 1, label, index =>
      (findRate log label).bind fun e ↦
        if index < 2 ^ depth then descend log depth e.input.1 index
        else descend log depth e.input.2 (index - 2 ^ depth)

/-- Executable request-fixed extraction using only primitive forward-born pairs. -/
def directExtract (request : Request rate) (log : List (Exposure F rate))
    (root : Digest F rate) : Table (List F) := fun index ↦
  if index < request.height then
    (descend log request.depth root index).bind fun label ↦
      (findRate log label).bind (recover log request.width.full request.width.tail)
  else none

def directComplete (request : Request rate) (log : List (Exposure F rate)) (root : Digest F rate)
    (index : ℕ) : List F :=
  (directExtract request log root index).getD (List.replicate request.width.length 0)

theorem directComplete_present {request : Request rate} {log : List (Exposure F rate)}
    {root : Digest F rate} {index : ℕ} {row : List F}
    (present : directExtract request log root index = some row) :
    directComplete request log root index = row := by simp [directComplete, present]

theorem directComplete_absent {request : Request rate} {log : List (Exposure F rate)}
    {root : Digest F rate} {index : ℕ} (absent : directExtract request log root index = none) :
    directComplete request log root index = List.replicate request.width.length 0 := by
  simp [directComplete, absent]

omit [Zero F] in
theorem rate_found {log : List (Exposure F rate)} {label : Digest F rate}
    {e : Exposure F rate} (found : findRate log label = some e) :
    e ∈ log ∧ e.forward = true ∧ e.output.1 = label := by
  have flags := List.find?_some found
  simp only [Bool.and_eq_true, decide_eq_true_eq] at flags
  exact ⟨List.mem_of_find?_eq_some found, flags⟩

omit [Zero F] in
theorem rate_absent {log : List (Exposure F rate)} {label : Digest F rate}
    (absent : findRate log label = none) {e : Exposure F rate}
    (member : e ∈ log) (forward : e.forward = true) : e.output.1 ≠ label := by
  have miss := List.find?_eq_none.mp absent e member
  simpa [forward] using miss

theorem macro_find_absent {Value : Type} (decode : MacroQuery F rate → Option Value)
    {log : List (Exposure F rate)} (width : Width rate) {label : Digest F rate}
    (absent : findRate log label = none) :
    (macroLog log width).find?
      (fun entry ↦ (decode entry.1).isSome && entry.2 == label) = none := by
  apply List.find?_eq_none.mpr
  intro entry member hit
  obtain ⟨e, em, ef, answer, _⟩ := macro_source member
  have flags : (decode entry.1).isSome = true ∧ entry.2 = label := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using hit
  exact rate_absent absent em ef (answer.symm.trans flags.2)

theorem children_lookup {log : List (Exposure F rate)} (good : Good log)
    (width : Width rate) (label : Digest F rate) :
    hashing.findChildren (macroLog log width) label = (findRate log label).map Exposure.input := by
  cases found : findRate log label with
  | none =>
      simp only [LeafHashing.findChildren, macro_find_absent _ width found, Option.bind_none,
        Option.map_none]
  | some e =>
      obtain ⟨em, ef, answer⟩ := rate_found found
      rw [← answer]
      exact hashing.findChildren_of_mem_of_decoderConsistent (decoder_consistent good width).1
        (node_mem em ef) rfl

theorem row_lookup {log : List (Exposure F rate)} (good : Good log)
    (width : Width rate) (label : Digest F rate) :
    hashing.findRow (macroLog log width) label =
      (findRate log label).bind (recover log width.full width.tail) := by
  cases found : findRate log label with
  | none =>
      simp only [LeafHashing.findRow, macro_find_absent _ width found, Option.bind_none]
  | some e =>
      obtain ⟨em, ef, answer⟩ := rate_found found
      cases recovered : recover log width.full width.tail e with
      | some row =>
          have member : (⟨.leaf row, e.output.1⟩ :
              (_ : MacroQuery F rate) × Digest F rate) ∈ macroLog log width :=
            List.mem_flatMap.mpr ⟨e, em,
              mem_macrosAt.mpr ⟨ef, rfl, Or.inr ⟨row, recovered, rfl⟩⟩⟩
          simpa only [Option.bind_some, recovered, answer] using
            hashing.findRow_of_mem_of_decoderConsistent (decoder_consistent good width).2 member rfl
      | none =>
          have noLeaf : (macroLog log width).find?
              (fun entry ↦ (hashing.leafRow entry.1).isSome && entry.2 == label) = none := by
            apply List.find?_eq_none.mpr
            intro entry member hit
            obtain ⟨other, om, ofwd, oy, query⟩ := macro_source member
            have flags : (hashing.leafRow entry.1).isSome = true ∧ entry.2 = label := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hit
            have equal := flags.2
            have same := good.rate_unique om em ofwd ef (oy.symm.trans (equal.trans answer.symm))
            subst other
            rcases query with node | ⟨row, decoded, _⟩
            · simp [node, hashing] at hit
            · rw [recovered] at decoded
              contradiction
          simp only [LeafHashing.findRow, noLeaf, Option.bind_none, Option.bind_some, recovered]

theorem descend_eq {log : List (Exposure F rate)} (good : Good log) (width : Width rate) :
    ∀ depth root index, descend log depth root index =
      hashing.extractLabel (macroLog log width) depth root index
  | 0, _, _ => rfl
  | depth + 1, root, index => by
      simp only [descend, LeafHashing.extractLabel, children_lookup good width]
      cases found : findRate log root with
      | none => rfl
      | some e =>
          simp only [Option.bind_some, Option.map_some]
          split <;> apply descend_eq good width

/-- Equality to the reusable Merkle presentation, proved even when a link or endpoint is absent. -/
theorem directExtract_eq {request : Request rate} {log : List (Exposure F rate)}
    (good : Good log) (root : Digest F rate) :
    directExtract request log root = extract request log root := by
  funext index
  unfold directExtract extract
  split
  · rename_i range
    have bound : index < 2 ^ request.depth := Nat.lt_of_lt_of_le range request.heightBound
    simp only [LeafHashing.extract, bound, ↓reduceIte,
      descend_eq good request.width, row_lookup good request.width]
  · rfl

def directCheckpoint {Key : Type} [DecidableEq Key] (request : Request rate) (key : Key)
    (history : History Key F rate) (root : Digest F rate) : Table (List F) :=
  directExtract request (normalize (calls (beforeFirst (some key) history))) root

theorem directCheckpoint_frozen {Key : Type} [DecidableEq Key] (request : Request rate)
    (key : Key) (history later : History Key F rate) (root : Digest F rate)
    (queried : ∃ entry ∈ history, entry.1 = some key) :
    directCheckpoint request key (history ++ later) root =
      directCheckpoint request key history root := by
  unfold directCheckpoint
  rw [beforeFirst_append_of_mem (some key) later history queried]

theorem directCheckpoint_update {Key α : Type} [DecidableEq Key] (request : Request rate)
    (key : Key) (root : Digest F rate) (oa : OracleComp (OracleSpec.ofFn
      (fun _ : Option Key ↦ HistoryData F rate)) α)
    (table : Option Key → HistoryData F rate) (answer : HistoryData F rate) :
    directCheckpoint request key
      (OracleComp.tableQueryLog oa (Function.update table (some key) answer)) root =
        directCheckpoint request key (OracleComp.tableQueryLog oa table) root := by
  unfold directCheckpoint
  rw [beforeFirst_update]

theorem cut_good {Key : Type} [DecidableEq Key] {key : Key} {history : History Key F rate}
    (good : Good (normalize (calls history))) :
    Good (normalize (calls (beforeFirst (some key) history))) := by
  obtain ⟨later, extension⟩ := beforeFirst_prefix (some key) history
  have covered := normalize_prefix (calls (beforeFirst (some key) history)) (calls later)
  rw [← calls_append, extension] at covered
  obtain ⟨fresh, equal⟩ := covered
  apply Good.prefix (b := fresh)
  simpa [equal] using good

/-- Main deterministic endpoint: the *direct*, pre-first-allocation extractor agrees with any
later recorded positive-width opening outside the specified chronological primitive flags. -/
theorem direct_checkpoint_opening_agrees {Key : Type} [DecidableEq Key]
    {request : Request rate} {key : Key} {history : History Key F rate} {root : Digest F rate}
    (good : GoodHistory history) {roots : List (Digest F rate)} {later : History Key F rate}
    (marker : history = beforeFirst (some key) history ++ allocation key roots :: later)
    (registered : root ∈ roots) {e : Exposure F rate} {row : List F} {index : ℕ}
    {siblings : List (Digest F rate)}
    (trace : SpongeTrace (calls history) request.width.full request.width.tail e row)
    (climb : NodeClimb (calls history) index siblings e root)
    (length : siblings.length = request.depth) (range : index < request.height) :
    directCheckpoint request key history root index = some row := by
  unfold directCheckpoint
  rw [directExtract_eq (cut_good (key := key) good.1)]
  exact checkpoint_opening_agrees good marker registered trace climb length range

theorem direct_checkpoint_agrees {Key : Type} [DecidableEq Key]
    {request : Request rate} {key : Key} {history : History Key F rate} {root : Digest F rate}
    (good : GoodHistory history) {roots : List (Digest F rate)} {later : History Key F rate}
    (marker : history = beforeFirst (some key) history ++ allocation key roots :: later)
    (registered : root ∈ roots) :
    directCheckpoint request key history root =
      directExtract request (normalize (calls history)) root := by
  unfold directCheckpoint
  rw [directExtract_eq (cut_good (key := key) good.1), directExtract_eq good.1]
  exact checkpoint_agrees good marker registered

end ZkcSecurity.Commitment.PoseidonRows
