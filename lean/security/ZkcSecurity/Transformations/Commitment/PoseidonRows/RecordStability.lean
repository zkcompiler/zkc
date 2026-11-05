module

public import ZkcSecurity.Transformations.Commitment.PoseidonRows.MerkleExtraction

@[expose] public section

/-! # Primitive append and protected-root stability

Capacity targets prevent a late predecessor from completing an old endpoint. Rate targets protect
roots and earlier child labels. Both are coordinate conditions on fresh chronological exposures;
neither is an extraction-success or extraction-stability assumption.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {F : Type} {rate : ℕ} [Zero F] [DecidableEq F]

theorem macrosAt_append {log : List (Exposure F rate)} {fresh : Exposure F rate}
    (safe : CapacitySafe log fresh) (width : Width rate) {old : Exposure F rate}
    (member : old ∈ log) : macrosAt (log ++ [fresh]) width old = macrosAt log width old := by
  unfold macrosAt
  rw [recover_append safe _ _ _ member]

/-- Exact prefix append, including old failed decodings and their absent leaf macros. -/
theorem macroLog_append {log : List (Exposure F rate)} {fresh : Exposure F rate}
    (safe : CapacitySafe log fresh) (width : Width rate) :
    macroLog (log ++ [fresh]) width =
      macroLog log width ++ macrosAt (log ++ [fresh]) width fresh := by
  simp only [macroLog, List.flatMap_append, List.flatMap_singleton]
  congr 1
  apply List.flatMap_congr
  intro old member
  exact macrosAt_append safe width member

theorem inputs_macrosAt {log : List (Exposure F rate)} {width : Width rate}
    {e : Exposure F rate} {entry : (_ : MacroQuery F rate) × Digest F rate}
    (member : entry ∈ macrosAt log width e) {label : Digest F rate}
    (input : label ∈ hashing.inputs entry.1) : label = e.input.1 ∨ label = e.input.2 := by
  obtain ⟨_, _, query⟩ := mem_macrosAt.mp member
  rcases query with query | ⟨row, _, query⟩
  · simpa [query, LeafHashing.inputs, hashing] using input
  · simp [query, LeafHashing.inputs, hashing] at input

theorem inputs_macroLog {log : List (Exposure F rate)} {width : Width rate}
    {entry : (_ : MacroQuery F rate) × Digest F rate} (member : entry ∈ macroLog log width)
    {label : Digest F rate} (input : label ∈ hashing.inputs entry.1) :
    ∃ e ∈ log, label = e.input.1 ∨ label = e.input.2 := by
  obtain ⟨e, em, atEndpoint⟩ := List.mem_flatMap.mp member
  exact ⟨e, em, inputs_macrosAt atEndpoint input⟩

omit [Zero F] in
/-- Reuse the generic extractor's append law for any finite group of equal-answer macros. -/
theorem extract_macros_stable (label root : Digest F rate) (missRoot : label ≠ root)
    (base extra : HashLog (MacroQuery F rate) (Digest F rate)) (depth : ℕ)
    (answers : ∀ entry ∈ extra, entry.2 = label)
    (missInputs : ∀ entry ∈ base ++ extra, label ∉ hashing.inputs entry.1) :
    hashing.extract (base ++ extra) depth root = hashing.extract base depth root := by
  induction extra generalizing base with
  | nil => simp
  | cons entry rest ih =>
      have one : hashing.extract (base ++ [entry]) depth root =
          hashing.extract base depth root := by
        by_contra changed
        obtain ⟨_, hit⟩ := hashing.extract_append_changed base entry depth root changed
        rw [answers entry List.mem_cons_self] at hit
        rcases hit with hit | ⟨old, om, hit⟩
        · exact missRoot hit
        · exact missInputs old (List.mem_append_left _ om) hit
      have restAnswers : ∀ e ∈ rest, e.2 = label := fun e em ↦
        answers e (List.mem_cons_of_mem _ em)
      have restMiss : ∀ e ∈ (base ++ [entry]) ++ rest, label ∉ hashing.inputs e.1 := by
        intro e em
        apply missInputs e
        simpa [List.append_assoc] using em
      calc
        hashing.extract (base ++ entry :: rest) depth root =
            hashing.extract ((base ++ [entry]) ++ rest) depth root := by simp
        _ = hashing.extract (base ++ [entry]) depth root := ih _ restAnswers restMiss
        _ = hashing.extract base depth root := one

/-- One fresh good exposure cannot change a protected root; inverse births emit nothing. -/
theorem extract_append {request : Request rate} {log : List (Exposure F rate)}
    {fresh : Exposure F rate} {root : Digest F rate} (good : Good (log ++ [fresh]))
    (rootMisses : fresh.forward = true → fresh.output.1 ≠ root) :
    extract request (log ++ [fresh]) root = extract request log root := by
  have appended := macroLog_append (capacitySafe_of_good good) request.width
  cases forward : fresh.forward with
  | false =>
      funext i
      unfold extract
      rw [appended]
      simp [macrosAt, forward]
  | true =>
      have own := good.2 fresh (List.mem_append_right _ (by simp))
      simp only [LocalGood, forward, ↓reduceIte] at own
      have missInputs : ∀ entry ∈ macroLog log request.width ++
          macrosAt (log ++ [fresh]) request.width fresh,
          fresh.output.1 ∉ hashing.inputs entry.1 := by
        intro entry member input
        rcases List.mem_append.mp member with old | newest
        · obtain ⟨e, em, coordinate⟩ := inputs_macroLog old input
          have flags := (List.pairwise_append.mp good.1).2.2 e em fresh (by simp)
          simp only [OrderedGood, forward, ↓reduceIte] at flags
          exact coordinate.elim flags.2.1 flags.2.2.1
        · exact (inputs_macrosAt newest input).elim own.1 own.2.1
      have stable := extract_macros_stable fresh.output.1 root (rootMisses forward)
        (macroLog log request.width) (macrosAt (log ++ [fresh]) request.width fresh)
        request.depth (fun _ member ↦ (mem_macrosAt.mp member).2.1) missInputs
      funext i
      simp only [extract, appended, stable]

/-- Simultaneous stability over a finite extension, with coordinate-only registered-root flags. -/
theorem extract_stable {request : Request rate} {prior later : List (Exposure F rate)}
    {root : Digest F rate} (good : Good (prior ++ later))
    (rootMisses : ∀ e ∈ later, e.forward = true → e.output.1 ≠ root) :
    extract request (prior ++ later) root = extract request prior root := by
  induction later using List.reverseRecOn with
  | nil => simp
  | append_singleton earlier fresh ih =>
      have prefixGood : Good (prior ++ earlier) := by
        apply Good.prefix (b := [fresh])
        simpa [List.append_assoc] using good
      have prefixProtected : ∀ e ∈ earlier, e.forward = true → e.output.1 ≠ root :=
        fun e em ↦ rootMisses e (List.mem_append_left _ em)
      have step := extract_append (request := request)
        (log := prior ++ earlier) (fresh := fresh) (root := root)
        (by simpa [List.append_assoc] using good) (rootMisses fresh (by simp))
      simpa [List.append_assoc] using step.trans (ih prefixGood prefixProtected)

end ZkcSecurity.Commitment.PoseidonRows
