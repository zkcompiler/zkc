module

public import ZkcSecurity.Commitment.Extractable

@[expose] public section

/-! # Merkle trees with hashed leaves

A table of `2 ^ depth` rows is committed by the root of a perfect binary tree whose leaves are the
hashes of the rows and whose internal nodes hash their two children (`LeafHashing`: the leaf and
node hash calls of one hash family, which need not be domain-separated by position). Row `i` is
reached from the root by the bits of `i`, most significant first; an opening climbs from the leaf
hash with the siblings, least significant bit first (`climb`), as deployed Merkle verifiers do.

The extractor reads the record of hash calls straight-line: from a label it follows the first
recorded node call answered by that label down to the leaf level (`extractLabel`), and reads the
row of the first recorded leaf call answered by the leaf label (`extractRow`). `scheme` proves the
two laws of `Extractable`:

* `extractLabel_of_climbs`: an accepted climb recorded in a record without two calls answered
  alike leads the extractor to the climb's leaf label, so the opened row is the extracted row;
* `extract_append_changed`: recording one more call changes an extraction only when the call is
  new and is answered by the root or by a label an earlier call took as input.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec

variable {Row Query Y : Type}

/-- The leaf and node calls of a hash family over rows `Row` and labels `Y`. -/
structure LeafHashing (Row Query Y : Type) where
  leaf : Row → Query
  node : Y → Y → Query
  /-- The row a call hashes, when it is a leaf call. -/
  leafRow : Query → Option Row
  /-- The children a call hashes, when it is a node call. -/
  children : Query → Option (Y × Y)
  leafRow_leaf : ∀ row, leafRow (leaf row) = some row
  children_node : ∀ left right, children (node left right) = some (left, right)

namespace LeafHashing

variable (model : LeafHashing Row Query Y)

/-- The node call one level up a climb: at an even index the current label is the left child. -/
def parent (index : ℕ) (current sibling : Y) : Query :=
  if index % 2 = 0 then model.node current sibling else model.node sibling current

/-- Climb from a label along siblings, least significant bit of the index first, through hash
calls. -/
def climb : ℕ → List Y → Y → OracleComp (Query →ₒ Y) Y
  | _, [], current => pure current
  | index, sibling :: rest, current => do
      let up ← (liftM ((Query →ₒ Y).query (model.parent index current sibling)) :
        OracleComp (Query →ₒ Y) Y)
      climb (index / 2) rest up

/-- A climb recorded in a log: every node call of the climb is in the log with its answer. -/
def Climbs (log : HashLog Query Y) : ℕ → List Y → Y → Y → Prop
  | _, [], current, top => current = top
  | index, sibling :: rest, current, top =>
      ∃ up, (⟨model.parent index current sibling, up⟩ : (_ : Query) × Y) ∈ log ∧
        Climbs log (index / 2) rest up top

/-! ### Climbs -/

theorem climbs_mono {log larger : HashLog Query Y} (included : ∀ entry ∈ log, entry ∈ larger) :
    ∀ (index : ℕ) (path : List Y) (current top : Y),
      Climbs model log index path current top → Climbs model larger index path current top
  | _, [], _, _, climbs => climbs
  | index, _ :: rest, _, top, ⟨up, member, climbs⟩ =>
      ⟨up, included _ member, climbs_mono included (index / 2) rest up top climbs⟩

/-- A climb evaluated against a complete answer table is recorded in its own table log. -/
theorem climbs_table (answer : Query → Y) :
    ∀ (index : ℕ) (path : List Y) (current : Y),
      Climbs model (tableQueryLog (model.climb index path current) answer) index path current
        (evalWithAnswerFn (QueryImpl.ofFn answer) (model.climb index path current))
  | _, [], _ => rfl
  | index, sibling :: rest, current => by
      have later := climbs_table answer (index / 2) rest (answer (model.parent index current sibling))
      simp only [climb, tableQueryLog_query_bind, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ⟨_, List.mem_cons_self, climbs_mono model (fun entry member =>
        List.mem_cons_of_mem _ member) _ _ _ _ later⟩

theorem climbs_append (log : HashLog Query Y) (index : ℕ) (sibling : Y) :
    ∀ (path : List Y) (current top : Y),
      Climbs model log index (path ++ [sibling]) current top →
        ∃ middle, Climbs model log index path current middle ∧
          (⟨model.parent (index / 2 ^ path.length) middle sibling, top⟩ : (_ : Query) × Y) ∈ log
  | [], current, top, climbs => by
      obtain ⟨up, member, rest⟩ := climbs
      simp only [Climbs] at rest
      subst rest
      exact ⟨current, rfl, by simpa using member⟩
  | first :: rest, current, top, ⟨up, member, climbs⟩ => by
      obtain ⟨middle, below, last⟩ := climbs_append log (index / 2) sibling rest up top climbs
      refine ⟨middle, ⟨up, member, below⟩, ?_⟩
      rwa [List.length_cons, pow_succ', ← Nat.div_div_eq_div_mul] at *

/-- A climb reads only as many low bits of the index as it has levels. -/
theorem climbs_mod (log : HashLog Query Y) :
    ∀ (index : ℕ) (path : List Y) (current top : Y),
      Climbs model log index path current top ↔
        Climbs model log (index % 2 ^ path.length) path current top
  | _, [], _, _ => by simp [Climbs]
  | index, sibling :: rest, current, top => by
      have low : index % 2 ^ (rest.length + 1) % 2 = index % 2 := by
        rw [pow_succ, Nat.mod_mul_left_mod]
      have high : index % 2 ^ (rest.length + 1) / 2 % 2 ^ rest.length =
          index / 2 % 2 ^ rest.length := by
        rw [pow_succ, Nat.mod_mul_left_div_self, Nat.mod_mod]
      have sameParent : model.parent (index % 2 ^ (rest.length + 1)) current sibling =
          model.parent index current sibling := by
        unfold parent
        rw [low]
      simp only [Climbs, List.length_cons, sameParent]
      constructor
      · rintro ⟨up, member, climbs⟩
        refine ⟨up, member, ?_⟩
        rw [climbs_mod log (index % 2 ^ (rest.length + 1) / 2), high, ← climbs_mod log]
        exact climbs
      · rintro ⟨up, member, climbs⟩
        refine ⟨up, member, ?_⟩
        rw [climbs_mod log (index / 2), ← high, ← climbs_mod log]
        exact climbs

variable [DecidableEq Y]

/-- The children of the first recorded node call answered by `label`. -/
def findChildren (log : HashLog Query Y) (label : Y) : Option (Y × Y) :=
  (log.find? fun entry => (model.children entry.1).isSome && entry.2 == label).bind
    fun entry => model.children entry.1

/-- The row of the first recorded leaf call answered by `label`. -/
def findRow (log : HashLog Query Y) (label : Y) : Option Row :=
  (log.find? fun entry => (model.leafRow entry.1).isSome && entry.2 == label).bind
    fun entry => model.leafRow entry.1

/-- The leaf label reached from `label` at `index`, most significant bit first. -/
def extractLabel (log : HashLog Query Y) : ℕ → Y → ℕ → Option Y
  | 0, label, _ => some label
  | depth + 1, label, index =>
      match findChildren model log label with
      | none => none
      | some (left, right) =>
          if index < 2 ^ depth then extractLabel log depth left index
          else extractLabel log depth right (index - 2 ^ depth)

/-- The table of rows extracted for a root of a tree of the given depth. -/
def extract (log : HashLog Query Y) (depth : ℕ) (root : Y) : Table Row := fun index =>
  if index < 2 ^ depth then (extractLabel model log depth root index).bind (findRow model log)
  else none

/-- Authenticate an opening of row `index` of a tree of depth `depth`: hash the row, climb with
the path, and compare with the root. Positions outside the table and paths of the wrong length
reject. -/
def authenticate (depth : ℕ) (root : Y) (index : ℕ) (opening : Opening Row Y) :
    OracleComp (Query →ₒ Y) Bool :=
  if index < 2 ^ depth ∧ opening.path.length = depth then do
    let leafLabel ← (liftM ((Query →ₒ Y).query (model.leaf opening.value)) :
      OracleComp (Query →ₒ Y) Y)
    let top ← model.climb index opening.path leafLabel
    pure (top == root)
  else pure false

/-- The labels a call takes as input: the children of a node call. -/
def inputs (query : Query) : List Y :=
  match model.children query with
  | some (left, right) => [left, right]
  | none => []

/-! ### Extraction along a recorded climb -/

theorem findChildren_of_mem {log : HashLog Query Y}
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log) {query : Query} {label left right : Y}
    (member : (⟨query, label⟩ : (_ : Query) × Y) ∈ log)
    (children : model.children query = some (left, right)) :
    findChildren model log label = some (left, right) := by
  unfold findChildren
  cases found : log.find? (fun entry => (model.children entry.1).isSome && entry.2 == label) with
  | none =>
      have := List.find?_eq_none.mp found _ member
      simp [children] at this
  | some entry =>
      have holds := List.find?_some found
      have entryMember := List.mem_of_find?_eq_some found
      simp only [Bool.and_eq_true, beq_iff_eq] at holds
      have same : entry.1 = query := injective entry entryMember _ member holds.2
      simp [same, children]

theorem findRow_of_mem {log : HashLog Query Y}
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log) {query : Query} {label : Y}
    {row : Row} (member : (⟨query, label⟩ : (_ : Query) × Y) ∈ log)
    (leafRow : model.leafRow query = some row) :
    findRow model log label = some row := by
  unfold findRow
  cases found : log.find? (fun entry => (model.leafRow entry.1).isSome && entry.2 == label) with
  | none =>
      have := List.find?_eq_none.mp found _ member
      simp [leafRow] at this
  | some entry =>
      have holds := List.find?_some found
      have entryMember := List.mem_of_find?_eq_some found
      simp only [Bool.and_eq_true, beq_iff_eq] at holds
      have same : entry.1 = query := injective entry entryMember _ member holds.2
      simp [same, leafRow]

/-- A recorded climb leads the extractor from its top to its bottom label, in a record without
two calls answered alike. -/
theorem extractLabel_of_climbs {log : HashLog Query Y}
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log) :
    ∀ (depth index : ℕ) (path : List Y) (current top : Y), path.length = depth →
      index < 2 ^ depth → Climbs model log index path current top →
      extractLabel model log depth top index = some current
  | 0, _, path, current, top, length, _, climbs => by
      rw [List.length_eq_zero_iff.mp length] at climbs
      simp only [Climbs] at climbs
      subst climbs
      rfl
  | depth + 1, index, path, current, top, length, below, climbs => by
      obtain ⟨lower, sibling, rfl⟩ : ∃ lower sibling, path = lower ++ [sibling] := by
        rcases List.eq_nil_or_concat path with empty | ⟨lower, sibling, concat⟩
        · simp [empty] at length
        · exact ⟨lower, sibling, concat.trans List.concat_eq_append⟩
      have lowerLength : lower.length = depth := by simpa using length
      obtain ⟨middle, belowClimb, top⟩ := climbs_append model log index sibling lower current top climbs
      rw [lowerLength] at top
      rw [climbs_mod, lowerLength] at belowClimb
      simp only [extractLabel]
      by_cases inLeft : index < 2 ^ depth
      · have bit : index / 2 ^ depth = 0 := Nat.div_eq_of_lt inLeft
        rw [bit] at top
        rw [findChildren_of_mem model injective (left := middle) (right := sibling) top
          (by simp [parent, model.children_node])]
        simp only [inLeft, ↓reduceIte]
        rw [Nat.mod_eq_of_lt inLeft] at belowClimb
        exact extractLabel_of_climbs injective depth index lower current middle lowerLength inLeft
          belowClimb
      · have upper : index - 2 ^ depth < 2 ^ depth := by rw [pow_succ] at below; omega
        have bit : index / 2 ^ depth = 1 := by
          rw [Nat.div_eq_iff (Nat.two_pow_pos depth)]
          constructor <;> rw [pow_succ] at below <;> omega
        have low : index % 2 ^ depth = index - 2 ^ depth := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt upper]
        rw [bit] at top
        rw [findChildren_of_mem model injective (left := sibling) (right := middle) top
          (by simp [parent, model.children_node])]
        simp only [inLeft, ↓reduceIte]
        rw [low] at belowClimb
        exact extractLabel_of_climbs injective depth (index - 2 ^ depth) lower current middle
          lowerLength upper belowClimb

theorem opening_agrees (answer : Query → Y) (log : HashLog Query Y) (depth : ℕ) (root : Y)
    (index : ℕ) (opening : Opening Row Y)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log)
    (recorded : ∀ entry ∈ tableQueryLog (model.authenticate depth root index opening) answer,
      entry ∈ log)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (model.authenticate depth root index opening) = true) :
    model.extract log depth root index = some opening.value := by
  unfold authenticate at recorded accepted
  split at accepted
  · rename_i valid
    simp only [valid, and_self, ↓reduceIte, tableQueryLog_bind, tableQueryLog_query,
      tableQueryLog_pure, List.append_nil, List.singleton_append, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      QueryImpl.ofFn_apply, evalWithAnswerFn_pure, beq_iff_eq] at recorded accepted
    have leafMember := recorded _ List.mem_cons_self
    have climbs := climbs_table model answer index opening.path (answer (model.leaf opening.value))
    rw [accepted] at climbs
    have label := extractLabel_of_climbs model injective depth index opening.path _ root valid.2
      valid.1 (climbs_mono model (fun entry member => recorded entry
        (List.mem_cons_of_mem _ member)) _ _ _ _ climbs)
    simp only [extract, valid.1, ↓reduceIte, label, Option.bind_some]
    exact findRow_of_mem model injective leafMember (model.leafRow_leaf _)
  · simp at accepted

/-! ### Extraction changes only at fresh hits -/

omit [DecidableEq Y] in
theorem find?_append_singleton_of_mem {α : Type} (p : α → Bool) (log : List α) (entry : α)
    (member : entry ∈ log) : (log ++ [entry]).find? p = log.find? p := by
  rw [List.find?_append]
  cases found : log.find? p with
  | some _ => rfl
  | none =>
      have := List.find?_eq_none.mp found entry member
      simp [this]

theorem findChildren_append (log : HashLog Query Y) (entry : (_ : Query) × Y) (label : Y)
    (changed : findChildren model (log ++ [entry]) label ≠ findChildren model log label) :
    entry ∉ log ∧ entry.2 = label := by
  refine ⟨fun member => changed (by unfold findChildren; rw [find?_append_singleton_of_mem _ _ _
    member]), ?_⟩
  unfold findChildren at changed
  rw [List.find?_append] at changed
  cases found : log.find? (fun entry => (model.children entry.1).isSome && entry.2 == label) with
  | some _ => simp [found] at changed
  | none =>
      simp only [found, Option.none_or] at changed
      by_cases hit : ((model.children entry.1).isSome && entry.2 == label) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hit
        exact hit.2
      · simp [hit] at changed

theorem findRow_append (log : HashLog Query Y) (entry : (_ : Query) × Y) (label : Y)
    (changed : findRow model (log ++ [entry]) label ≠ findRow model log label) :
    entry ∉ log ∧ entry.2 = label := by
  refine ⟨fun member => changed (by unfold findRow; rw [find?_append_singleton_of_mem _ _ _
    member]), ?_⟩
  unfold findRow at changed
  rw [List.find?_append] at changed
  cases found : log.find? (fun entry => (model.leafRow entry.1).isSome && entry.2 == label) with
  | some _ => simp [found] at changed
  | none =>
      simp only [found, Option.none_or] at changed
      by_cases hit : ((model.leafRow entry.1).isSome && entry.2 == label) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hit
        exact hit.2
      · simp [hit] at changed

/-- The children found for a label are the inputs of a recorded call. -/
theorem inputs_of_findChildren {log : HashLog Query Y} {label left right : Y}
    (found : findChildren model log label = some (left, right)) :
    ∃ recorded ∈ log, left ∈ model.inputs recorded.1 ∧ right ∈ model.inputs recorded.1 := by
  unfold findChildren at found
  cases entryFound : log.find? (fun entry => (model.children entry.1).isSome && entry.2 == label)
    with
  | none => simp [entryFound] at found
  | some entry =>
      simp only [entryFound, Option.bind_some] at found
      refine ⟨entry, List.mem_of_find?_eq_some entryFound, ?_, ?_⟩ <;>
        simp [inputs, found]

/-- A label extracted below a root is the root or an input of a recorded call. -/
theorem extractLabel_input {log : HashLog Query Y} :
    ∀ (depth : ℕ) (root : Y) (index : ℕ) {label : Y},
      extractLabel model log depth root index = some label →
        label = root ∨ ∃ recorded ∈ log, label ∈ model.inputs recorded.1
  | 0, root, _, label, found => by
      simp only [extractLabel, Option.some.injEq] at found
      exact Or.inl found.symm
  | depth + 1, root, index, label, found => by
      simp only [extractLabel] at found
      cases children : findChildren model log root with
      | none => simp [children] at found
      | some pair =>
          obtain ⟨left, right⟩ := pair
          obtain ⟨recorded, member, leftInput, rightInput⟩ := inputs_of_findChildren model children
          simp only [children] at found
          split at found
          · rcases extractLabel_input depth left index found with rfl | deeper
            · exact Or.inr ⟨recorded, member, leftInput⟩
            · exact Or.inr deeper
          · rcases extractLabel_input depth right (index - 2 ^ depth) found with rfl | deeper
            · exact Or.inr ⟨recorded, member, rightInput⟩
            · exact Or.inr deeper

theorem extractLabel_append (log : HashLog Query Y) (entry : (_ : Query) × Y) :
    ∀ (depth : ℕ) (root : Y) (index : ℕ),
      extractLabel model (log ++ [entry]) depth root index ≠ extractLabel model log depth root index →
        entry ∉ log ∧ (entry.2 = root ∨ ∃ recorded ∈ log, entry.2 ∈ model.inputs recorded.1)
  | 0, _, _, changed => absurd rfl changed
  | depth + 1, root, index, changed => by
      simp only [extractLabel] at changed
      by_cases same : findChildren model (log ++ [entry]) root = findChildren model log root
      · rw [same] at changed
        cases children : findChildren model log root with
        | none => simp [children] at changed
        | some pair =>
            obtain ⟨left, right⟩ := pair
            obtain ⟨recorded, member, leftInput, rightInput⟩ :=
              inputs_of_findChildren model children
            simp only [children] at changed
            split at changed
            · obtain ⟨absent, hit⟩ := extractLabel_append log entry depth left index changed
              refine ⟨absent, Or.inr ?_⟩
              rcases hit with rfl | deeper
              · exact ⟨recorded, member, leftInput⟩
              · exact deeper
            · obtain ⟨absent, hit⟩ :=
                extractLabel_append log entry depth right (index - 2 ^ depth) changed
              refine ⟨absent, Or.inr ?_⟩
              rcases hit with rfl | deeper
              · exact ⟨recorded, member, rightInput⟩
              · exact deeper
      · obtain ⟨absent, hit⟩ := findChildren_append model log entry root same
        exact ⟨absent, Or.inl hit⟩

theorem extract_append_changed (log : HashLog Query Y) (entry : (_ : Query) × Y) (depth : ℕ)
    (root : Y) (changed : model.extract (log ++ [entry]) depth root ≠ model.extract log depth root) :
    entry ∉ log ∧ (entry.2 = root ∨ ∃ recorded ∈ log, entry.2 ∈ model.inputs recorded.1) := by
  by_contra unchanged
  apply changed
  funext index
  unfold extract
  split
  · by_cases labelSame : extractLabel model (log ++ [entry]) depth root index =
        extractLabel model log depth root index
    · rw [labelSame]
      cases found : extractLabel model log depth root index with
      | none => rfl
      | some label =>
          simp only [Option.bind_some]
          by_contra rowChanged
          obtain ⟨absent, hit⟩ := findRow_append model log entry label rowChanged
          apply unchanged
          refine ⟨absent, ?_⟩
          rw [hit]
          exact extractLabel_input model depth root index found
    · exact absurd (extractLabel_append model log entry depth root index labelSame) unchanged
  · rfl

/-- Merkle trees with hashed leaves as an extractable table commitment; a commitment's shape is
its depth. -/
def scheme : Extractable ℕ Row Query Y where
  authenticate := model.authenticate
  extract := model.extract
  inputs := model.inputs
  opening_agrees := model.opening_agrees
  extract_append := model.extract_append_changed

omit [DecidableEq Y] in
theorem inputs_length (query : Query) : (model.inputs query).length ≤ 2 := by
  unfold inputs
  split <;> simp

end LeafHashing

end ZkcSecurity.Commitment
