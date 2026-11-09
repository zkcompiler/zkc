module

public import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.PrimitiveRecord

@[expose] public section

/-! # Fixed-width overwrite sponge reconstruction

These are the equations of `p3-symmetric` 0.8.0 `sponge.rs:195-231`: overwrite the consumed
rate coordinates, retain the rate suffix and capacity, then permute. There is one call per nonempty
block, including the last partial block, with no additional call at an exact boundary.
The equations describe a generic permutation; no Rust refinement or Poseidon security is claimed.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {F : Type} {rate : ℕ}

/-- The number of complete blocks preceding the nonempty final block is fixed by the request. -/
structure Width (rate : ℕ) where
  full : ℕ
  tail : ℕ
  positive : 0 < tail
  bounded : tail ≤ rate

def Width.length (w : Width rate) : ℕ := w.full * rate + w.tail

def Width.ofLength (positiveRate : 0 < rate) (length : ℕ) (_positive : 0 < length) :
    Width rate where
  full := (length - 1) / rate
  tail := (length - 1) % rate + 1
  positive := by omega
  bounded := by have := Nat.mod_lt (length - 1) positiveRate; omega

theorem Width.ofLength_length (positiveRate : 0 < rate) (length : ℕ)
    (positive : 0 < length) : (Width.ofLength positiveRate length positive).length = length := by
  have := Nat.mod_add_div (length - 1) rate
  simp only [Width.ofLength, Width.length]
  rw [Nat.mul_comm] at this
  omega

/-- Overwrite exactly `count` rate coordinates. Capacity and the other rate coordinates remain. -/
def overwrite (state : State F rate) (count : ℕ) (block : Digest F rate) : State F rate :=
  (fun i ↦ if i.val < count then block i else state.1 i, state.2)

@[simp] theorem overwrite_capacity (state : State F rate) (count : ℕ)
    (block : Digest F rate) : (overwrite state count block).2 = state.2 := rfl

theorem overwrite_full (state : State F rate) (block : Digest F rate) :
    overwrite state rate block = (block, state.2) := by
  apply Prod.ext
  · funext i
    simp [overwrite]
  · rfl

/-- Ascending base coordinates. Extension rows must first use their registered basis order. -/
def coordinates (count : ℕ) (block : Digest F rate) : List F :=
  (List.ofFn block).take count

theorem coordinates_overwrite (state : State F rate) {count : ℕ} (_bound : count ≤ rate)
    (block : Digest F rate) :
    coordinates count (overwrite state count block).1 = coordinates count block := by
  apply List.ext_getElem
  · simp [coordinates]
  · intro i hi hj
    have below : i < count := (by simpa [coordinates] using hi : i < count ∧ i < rate).1
    simp [coordinates, overwrite, below]

variable [Zero F] [DecidableEq F]

/-- Find a forward-born predecessor by output capacity, without any supplied decoder. -/
def findCapacity (log : List (Exposure F rate)) (capacity : Digest F rate) :
    Option (Exposure F rate) :=
  log.find? (fun e ↦ e.forward && decide (e.output.2 = capacity))

/-- Find a forward-born endpoint by output rate. -/
def findRate (log : List (Exposure F rate)) (label : Digest F rate) :
    Option (Exposure F rate) :=
  log.find? (fun e ↦ e.forward && decide (e.output.1 = label))

theorem findCapacity_of_mem {log : List (Exposure F rate)} (good : Good log)
    {e : Exposure F rate} (member : e ∈ log) (forward : e.forward = true) :
    findCapacity log e.output.2 = some e := by
  cases found : findCapacity log e.output.2 with
  | none =>
      have absent := List.find?_eq_none.mp found e member
      simp [forward] at absent
  | some other =>
      have om := List.mem_of_find?_eq_some found
      have flags := List.find?_some found
      simp only [Bool.and_eq_true, decide_eq_true_eq] at flags
      exact congrArg some (good.capacity_unique om member flags.1 forward flags.2)

theorem findRate_of_mem {log : List (Exposure F rate)} (good : Good log)
    {e : Exposure F rate} (member : e ∈ log) (forward : e.forward = true) :
    findRate log e.output.1 = some e := by
  cases found : findRate log e.output.1 with
  | none =>
      have absent := List.find?_eq_none.mp found e member
      simp [forward] at absent
  | some other =>
      have om := List.mem_of_find?_eq_some found
      have flags := List.find?_some found
      simp only [Bool.and_eq_true, decide_eq_true_eq] at flags
      exact congrArg some (good.rate_unique om member flags.1 forward flags.2)

/-- A fixed-length backward algorithm. Full intermediate blocks have no rate-tail constraint.
Only the final partial block retains its predecessor's suffix (or the zero initial suffix). -/
def recover (log : List (Exposure F rate)) : ℕ → ℕ → Exposure F rate → Option (List F)
  | 0, tail, e =>
      if e.input.2 = 0 ∧ (∀ i : Fin rate, tail ≤ i.val → e.input.1 i = 0) then
        some (coordinates tail e.input.1)
      else none
  | full + 1, tail, e =>
      (findCapacity log e.input.2).bind fun previous ↦
        (recover log full rate previous).bind fun accumulated ↦
          if ∀ i : Fin rate, tail ≤ i.val → e.input.1 i = previous.output.1 i then
            some (accumulated ++ coordinates tail e.input.1)
          else none

/-- Exact equations of recorded sponge calls. The constructors supply primitive input/output
data and overwrite equations, never successful extraction or a macro-oracle answer. -/
inductive SpongeTrace (log : List (Exposure F rate)) :
    ℕ → ℕ → Exposure F rate → List F → Prop
  | single {tail : ℕ} {e : Exposure F rate} (block : Digest F rate)
      (member : e ∈ log) (input : e.input = overwrite (0, 0) tail block) :
      SpongeTrace log 0 tail e (coordinates tail block)
  | next {full tail : ℕ} {previous e : Exposure F rate} {accumulated : List F}
      (block : Digest F rate) (prior : SpongeTrace log full rate previous accumulated)
      (member : e ∈ log) (input : e.input = overwrite previous.output tail block) :
      SpongeTrace log (full + 1) tail e (accumulated ++ coordinates tail block)

omit [DecidableEq F] in
theorem SpongeTrace.member {log : List (Exposure F rate)} {full tail : ℕ}
    {e : Exposure F rate} {row : List F} (trace : SpongeTrace log full tail e row) : e ∈ log := by
  cases trace <;> assumption

omit [DecidableEq F] in
theorem SpongeTrace.forward {log : List (Exposure F rate)} (good : Good log)
    {full tail : ℕ} {e : Exposure F rate} {row : List F}
    (trace : SpongeTrace log full tail e row) : e.forward = true := by
  induction trace with
  | single block member input =>
      exact good.initial_forward member (by simp [input])
  | next block prior member input ih =>
      exact good.capacity_forward prior.member member ih (by simp [input])

/-- Recovery is derived from chronological flags and actual overwrite equations. -/
theorem SpongeTrace.recover {log : List (Exposure F rate)} (good : Good log)
    {full tail : ℕ} {e : Exposure F rate} {row : List F} (bound : tail ≤ rate)
    (trace : SpongeTrace log full tail e row) : recover log full tail e = some row := by
  induction trace with
  | @single tail e block member input =>
      have capacity : e.input.2 = 0 := by simp [input]
      have suffix : ∀ i : Fin rate, tail ≤ i.val → e.input.1 i = 0 := by
        intro i hi
        simp [input, overwrite, Nat.not_lt.mpr hi]
      rw [PoseidonRows.recover, ite_eq_left ⟨capacity, suffix⟩]
      rw [input, coordinates_overwrite _ bound]
  | @next full tail previous e accumulated block prior member input ih =>
      have capacity : e.input.2 = previous.output.2 := by simp [input]
      have suffix : ∀ i : Fin rate, tail ≤ i.val → e.input.1 i = previous.output.1 i := by
        intro i hi
        simp [input, overwrite, Nat.not_lt.mpr hi]
      rw [PoseidonRows.recover, capacity,
        findCapacity_of_mem good prior.member (prior.forward good)]
      simp only [Option.bind_some, ih (Nat.le_refl rate)]
      rw [ite_eq_left suffix]
      rw [input, coordinates_overwrite _ bound]

/-- Successful recovery always has the request-fixed number of coordinates. -/
theorem recover_length {log : List (Exposure F rate)} :
    ∀ (full tail : ℕ) (e : Exposure F rate) (row : List F), tail ≤ rate →
      recover log full tail e = some row → row.length = full * rate + tail
  | 0, tail, e, row, bound, found => by
      simp only [recover] at found
      split at found
      · cases found
        simp [coordinates, Nat.min_eq_left bound]
      · contradiction
  | full + 1, tail, e, row, bound, found => by
      simp only [recover] at found
      cases pred : findCapacity log e.input.2 with
      | none => simp [pred] at found
      | some previous =>
          simp only [pred, Option.bind_some] at found
          cases recovered : recover log full rate previous with
          | none => simp [recovered] at found
          | some accumulated =>
              simp only [recovered, Option.bind_some] at found
              split at found
              · cases found
                have length :=
                  recover_length full rate previous accumulated (Nat.le_refl _) recovered
                simp [List.length_append, length, coordinates, Nat.min_eq_left bound, Nat.add_mul]
              · contradiction

/-- Every successful decoding gives actual recorded overwrite calls, with no good-event premise.
If the record is consistent with a selected permutation, these same calls evaluate that sponge. -/
theorem recover_sound {log : List (Exposure F rate)} :
    ∀ full tail e row, e ∈ log → recover log full tail e = some row →
      SpongeTrace log full tail e row
  | 0, tail, e, row, member, found => by
      simp only [recover] at found
      split at found
      · rename_i checks
        cases found
        apply SpongeTrace.single e.input.1 member
        apply Prod.ext
        · funext i
          dsimp [overwrite]
          split
          · rfl
          · exact checks.2 i (by omega)
        · exact checks.1
      · contradiction
  | full + 1, tail, e, row, member, found => by
      simp only [recover] at found
      cases pred : findCapacity log e.input.2 with
      | none => simp [pred] at found
      | some previous =>
          simp only [pred, Option.bind_some] at found
          cases recovered : recover log full rate previous with
          | none => simp [recovered] at found
          | some accumulated =>
              simp only [recovered, Option.bind_some] at found
              split at found
              · rename_i suffix
                cases found
                have pm := List.mem_of_find?_eq_some pred
                have flags := List.find?_some pred
                simp only [Bool.and_eq_true, decide_eq_true_eq] at flags
                apply SpongeTrace.next e.input.1
                  (recover_sound full rate previous accumulated pm recovered) member
                apply Prod.ext
                · funext i
                  dsimp [overwrite]
                  split
                  · rfl
                  · exact suffix i (by omega)
                · exact flags.2.symm
              · contradiction

/-- A selected permutation's consistency is a separate finite-record equation. -/
def Consistent (permutation : State F rate → State F rate) (log : List (Exposure F rate)) : Prop :=
  ∀ e ∈ log, e.output = permutation e.input

/-- Exact primitive evaluation of the ordered blocks, without padding or an extra final call. -/
def evaluateBlocks (permutation : State F rate → State F rate)
    (blocks : List (ℕ × Digest F rate)) : State F rate :=
  blocks.foldl (fun state block ↦ permutation (overwrite state block.1 block.2)) (0, 0)

omit [DecidableEq F] in
/-- A recorded sponge trace agrees with the exact overwrite evaluator. The witness lists the
actual absorbed blocks; it is used only in the proof and is not an input to extraction. -/
theorem SpongeTrace.evaluates {log : List (Exposure F rate)}
    {permutation : State F rate → State F rate} (consistent : Consistent permutation log)
    {full tail : ℕ} {e : Exposure F rate} {row : List F}
    (trace : SpongeTrace log full tail e row) :
    ∃ blocks : List (ℕ × Digest F rate),
      blocks.map Prod.fst = List.replicate full rate ++ [tail] ∧
      blocks.flatMap (fun block ↦ coordinates block.1 block.2) = row ∧
      evaluateBlocks permutation blocks = e.output := by
  induction trace with
  | @single tail e block member input =>
      refine ⟨[(tail, block)], rfl, by simp, ?_⟩
      simpa [evaluateBlocks, input] using (consistent e member).symm
  | @next full tail previous e accumulated block prior member input ih =>
      obtain ⟨blocks, widths, data, evaluated⟩ := ih
      refine ⟨blocks ++ [(tail, block)], ?_, ?_, ?_⟩
      · rw [List.map_append, widths]
        simp [List.replicate_succ', List.append_assoc]
      · simp [data]
      · have equation := (consistent e member).symm
        rw [input] at equation
        simpa [evaluateBlocks, List.foldl_append, ← evaluated] using equation

/-- Late capacity completion is exactly the obstruction absent from rate-only append laws. -/
def CapacitySafe (log : List (Exposure F rate)) (fresh : Exposure F rate) : Prop :=
  fresh.forward = true → ∀ e ∈ log, fresh.output.2 ≠ e.input.2

instance (log : List (Exposure F rate)) (fresh : Exposure F rate) :
    Decidable (CapacitySafe log fresh) := by
  unfold CapacitySafe
  infer_instance

omit [DecidableEq F] in
theorem capacitySafe_of_good {log : List (Exposure F rate)} {fresh : Exposure F rate}
    (good : Good (log ++ [fresh])) : CapacitySafe log fresh := by
  intro forward e member
  have flags := (List.pairwise_append.mp good.1).2.2 e member fresh (by simp)
  simp only [OrderedGood, forward, ↓reduceIte] at flags
  exact flags.2.2.2.2

omit [Zero F] in
theorem findCapacity_append {log : List (Exposure F rate)} {fresh e : Exposure F rate}
    (safe : CapacitySafe log fresh) (member : e ∈ log) :
    findCapacity (log ++ [fresh]) e.input.2 = findCapacity log e.input.2 := by
  unfold findCapacity
  rw [List.find?_append]
  cases found : log.find? (fun a ↦ a.forward && decide (a.output.2 = e.input.2)) with
  | some _ => rfl
  | none =>
      have miss : (fresh.forward && decide (fresh.output.2 = e.input.2)) = false := by
        cases forward : fresh.forward
        · rfl
        · simp [safe forward e member]
      simp [miss]

/-- An old endpoint's entire successful or failed decoding is stable, including missing links. -/
theorem recover_append {log : List (Exposure F rate)} {fresh : Exposure F rate}
    (safe : CapacitySafe log fresh) :
    ∀ full tail e, e ∈ log → recover (log ++ [fresh]) full tail e = recover log full tail e
  | 0, _, _, _ => rfl
  | full + 1, tail, e, member => by
      simp only [recover, findCapacity_append safe member]
      cases pred : findCapacity log e.input.2 with
      | none => rfl
      | some previous =>
          have pm := List.mem_of_find?_eq_some pred
          simp only [Option.bind_some, recover_append safe full rate previous pm]

end ZkcSecurity.Commitment.PoseidonRows
