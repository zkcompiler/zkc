module

public import Zkc.Core.Elaborate

public section

/-! Callee references across a step that changes protocol headers.

A step that rewrites protocols builds a new list of protocol headers. An `apply` of the
old program names a callee by a reference into the old list; the rewritten `apply`
needs a reference into the new list, at the callee's new header. One old definition may
have several rewritten ones (a definition reached under two assignments of the
transcript roles is specialized once per assignment), so the image is chosen by a key.

`CalleeTable F old new` records, for every old protocol, the levels of its rewritten
protocols in the new list, each with its key. `F key header` is the header of the
protocol rewritten for `key`; the table's invariant says that the new list has that
header at the recorded level. `CalleeTable.find` returns the reference
`Var new (F key header)` for an old reference `Var old header`, or nothing when the
definition was not rewritten for the key.

Levels do not change when the new list grows, so the table is extended in constant
time per rewritten protocol. `CalleeTable.find_eq_some_iff` says that the table names an
image exactly when it records a level for it (`CalleeTable.level?`); after one more
rewritten protocol it names the same image one binding later (`find_weaken`), and after
one more old protocol it names, for that protocol, an image at a level of the list it was
extended with (`find_extend_here`) and, for an earlier protocol, the image it named before
(`find_extend_there`).

The second half is a compiled sketch of a step that uses the table: every protocol is
copied once per key, and an `apply` in the copy for a key names the callee's copy for
the same key. The header function is the identity, so the sketch shows the re-typing
of protocol terms over the new list and the mapping of callees, and nothing else. A
step whose header function changes signatures (Fiat–Shamir across `apply`) uses the
same table with its own rewriting of the operands and results.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The most recent entry is at the level of the old depth. -/
theorem atLevel?_newest {β : Type} (Δ : List β) (head : β) :
    atLevel? (head :: Δ) (Δ.length + 1) Δ.length = some head := by
  have position : Δ.length + 1 - 1 - Δ.length = 0 := by omega
  simp only [atLevel?, Nat.lt_succ_self, ↓reduceIte, position]
  rfl

/-- For every old protocol, the rewritten protocols that stand for it, by key. -/
structure CalleeTable {K : Type} (F : K → ProtocolHeader → ProtocolHeader)
    (old new : List ProtocolHeader) where
  /-- For each old protocol, the most recent first: its keys with the levels of the
  rewritten protocols. -/
  images : Sequence (List (K × Nat))
  depth : Nat
  counted : depth = new.length
  sound : ∀ (index : Nat) (header : ProtocolHeader), old[index]? = some header →
    ∃ list, images.toList[index]? = some list ∧
      ∀ pair ∈ list, atLevel? new depth pair.2 = some (F pair.1 header)

namespace CalleeTable

variable {K : Type} {F : K → ProtocolHeader → ProtocolHeader} {old new : List ProtocolHeader}

/-- The table of a program without protocols. -/
@[expose] def empty : CalleeTable F [] ([] : List ProtocolHeader) :=
  ⟨.empty, 0, rfl, fun _ _ found => nomatch found⟩

/-- The same table after one more rewritten protocol. -/
@[expose] def weaken (table : CalleeTable F old new) (added : ProtocolHeader) :
    CalleeTable F old (added :: new) :=
  ⟨table.images, table.depth + 1, by rw [table.counted, List.length_cons],
    fun index header found => by
      obtain ⟨list, at_, valid⟩ := table.sound index header found
      exact ⟨list, at_, fun pair member => atLevel?_cons new added (valid pair member)⟩⟩

/-- One more old protocol with the levels of its rewritten protocols. -/
@[expose] def extend (table : CalleeTable F old new) (header : ProtocolHeader) (list : List (K × Nat))
    (valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (F pair.1 header)) :
    CalleeTable F (header :: old) new :=
  ⟨table.images.push list, table.depth, table.counted, fun index found at_ => by
    rw [Sequence.toList_push]
    cases index with
    | zero =>
        have same : header = found := Option.some.inj at_
        subst same
        exact ⟨list, rfl, valid⟩
    | succ index => exact table.sound index found at_⟩

/-- The level recorded for a key. -/
@[expose] def levelOf [DecidableEq K] (key : K) :
    (list : List (K × Nat)) → Option { level : Nat // (key, level) ∈ list }
  | [] => none
  | (other, level) :: rest =>
      if same : other = key then some ⟨level, by subst same; exact List.mem_cons_self⟩
      else
        match levelOf key rest with
        | some ⟨found, member⟩ => some ⟨found, List.mem_cons_of_mem _ member⟩
        | none => none

/-- The rewritten callee for a key. -/
@[expose] def find [DecidableEq K] (table : CalleeTable F old new) {header : ProtocolHeader}
    (callee : Var old header) (key : K) : Option (Var new (F key header)) :=
  match found : table.images.get? callee.index with
  | none => none
  | some list =>
      match levelOf key list with
      | none => none
      | some ⟨level, member⟩ =>
          some ⟨table.depth - 1 - level, by
            obtain ⟨recorded, at_, valid⟩ := table.sound callee.index header callee.valid
            rw [Sequence.get?_eq, at_] at found
            have same : recorded = list := Option.some.inj found
            subst same
            have image := valid (key, level) member
            unfold atLevel? at image
            split at image
            · exact image
            · cases image⟩

/-! ### The image of a callee, by the level the table records -/

/-- The level that the table records for a key of the old protocol at a position. -/
@[expose] def level? [DecidableEq K] (table : CalleeTable F old new) (index : Nat) (key : K) :
    Option Nat :=
  match table.images.get? index with
  | some list => (levelOf key list).map Subtype.val
  | none => none

/-- A level found for a key is recorded with the key. -/
theorem levelOf_member [DecidableEq K] {key : K} {list : List (K × Nat)} {level : Nat}
    (found : (levelOf key list).map Subtype.val = some level) : (key, level) ∈ list := by
  cases recorded : levelOf key list with
  | none => rw [recorded] at found; cases found
  | some entry =>
      rw [recorded] at found
      have same : entry.val = level := Option.some.inj found
      exact same ▸ entry.property

/-- The new list has the header of the image at a level that the table records. -/
theorem level?_valid [DecidableEq K] (table : CalleeTable F old new) {header : ProtocolHeader}
    (callee : Var old header) {key : K} {level : Nat}
    (found : table.level? callee.index key = some level) :
    atLevel? new table.depth level = some (F key header) := by
  obtain ⟨recorded, at_, valid⟩ := table.sound callee.index header callee.valid
  unfold level? at found
  rw [Sequence.get?_eq, at_] at found
  exact valid (key, level) (levelOf_member found)

/-- A recorded level is below the depth of the new list. -/
theorem level?_lt [DecidableEq K] (table : CalleeTable F old new) {header : ProtocolHeader}
    (callee : Var old header) {key : K} {level : Nat}
    (found : table.level? callee.index key = some level) : level < table.depth := by
  have image := table.level?_valid callee found
  unfold atLevel? at image
  split at image
  · assumption
  · cases image

/-- The table names an image exactly when it records a level for it. -/
theorem find_eq_some_iff [DecidableEq K] (table : CalleeTable F old new) {header : ProtocolHeader}
    (callee : Var old header) (key : K) (image : Var new (F key header)) :
    table.find callee key = some image ↔
      ∃ level, table.level? callee.index key = some level ∧
        image.index = table.depth - 1 - level := by
  have atPosition : ∀ entry, table.images.get? callee.index = entry →
      table.level? callee.index key =
        match entry with
        | some list => (levelOf key list).map Subtype.val
        | none => none := by
    intro entry same
    subst same
    rfl
  unfold find
  split
  · rename_i missing
    rw [atPosition none missing]
    constructor
    · intro found; cases found
    · rintro ⟨level, found, _⟩; cases found
  · rename_i list found
    rw [atPosition (some list) found]
    split
    · rename_i missing
      show _ ↔ ∃ level, (levelOf key list).map Subtype.val = some level ∧ _
      rw [missing]
      constructor
      · intro found; cases found
      · rintro ⟨level, found, _⟩; cases found
    · rename_i level member recorded
      show _ ↔ ∃ other, (levelOf key list).map Subtype.val = some other ∧ _
      rw [recorded]
      constructor
      · intro same
        exact ⟨level, rfl, by rw [← Option.some.inj same]⟩
      · rintro ⟨other, at_, index⟩
        have same : level = other := Option.some.inj at_
        subst same
        exact congrArg some (Var.ext index.symm)

/-- The table names no image exactly when it records no level. -/
theorem find_eq_none_iff [DecidableEq K] (table : CalleeTable F old new) {header : ProtocolHeader}
    (callee : Var old header) (key : K) :
    table.find callee key = none ↔ table.level? callee.index key = none := by
  constructor
  · intro missing
    cases recorded : table.level? callee.index key with
    | none => rfl
    | some level =>
        have valid := table.level?_valid callee recorded
        have below := table.level?_lt callee recorded
        have position : new[table.depth - 1 - level]? = some (F key header) := by
          unfold atLevel? at valid
          simpa only [below, ↓reduceIte] using valid
        have named := (table.find_eq_some_iff callee key ⟨_, position⟩).mpr ⟨level, recorded, rfl⟩
        rw [missing] at named
        cases named
  · intro missing
    cases named : table.find callee key with
    | none => rfl
    | some image =>
        obtain ⟨level, recorded, _⟩ := (table.find_eq_some_iff callee key image).mp named
        rw [missing] at recorded
        cases recorded

theorem level?_weaken [DecidableEq K] (table : CalleeTable F old new) (added : ProtocolHeader)
    (index : Nat) (key : K) : (table.weaken added).level? index key = table.level? index key :=
  rfl

theorem level?_extend_zero [DecidableEq K] (table : CalleeTable F old new)
    (header : ProtocolHeader) (list : List (K × Nat))
    (valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (F pair.1 header)) (key : K) :
    (table.extend header list valid).level? 0 key = (levelOf key list).map Subtype.val := by
  unfold level? extend
  simp only [Sequence.get?_eq, Sequence.toList_push, List.getElem?_cons_zero]

theorem level?_extend_succ [DecidableEq K] (table : CalleeTable F old new)
    (header : ProtocolHeader) (list : List (K × Nat))
    (valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (F pair.1 header))
    (index : Nat) (key : K) :
    (table.extend header list valid).level? (index + 1) key = table.level? index key := by
  unfold level? extend
  simp only [Sequence.get?_eq, Sequence.toList_push, List.getElem?_cons_succ]

/-- After one more rewritten protocol the table names the same image, one binding later. -/
theorem find_weaken [DecidableEq K] (table : CalleeTable F old new) (added : ProtocolHeader)
    {header : ProtocolHeader} (callee : Var old header) (key : K) :
    (table.weaken added).find callee key = (table.find callee key).map Var.there := by
  cases named : table.find callee key with
  | none =>
      exact ((table.weaken added).find_eq_none_iff callee key).mpr
        ((table.find_eq_none_iff callee key).mp named)
  | some image =>
      obtain ⟨level, recorded, index⟩ := (table.find_eq_some_iff callee key image).mp named
      have below := table.level?_lt callee recorded
      refine ((table.weaken added).find_eq_some_iff callee key image.there).mpr
        ⟨level, recorded, ?_⟩
      show image.index + 1 = table.depth + 1 - 1 - level
      omega

/-- The image of the newest old protocol is at a level of the list it was extended with. -/
theorem find_extend_here [DecidableEq K] (table : CalleeTable F old new)
    (header : ProtocolHeader) (list : List (K × Nat))
    (valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (F pair.1 header)) (key : K)
    (image : Var new (F key header))
    (named : (table.extend header list valid).find .here key = some image) :
    ∃ level, (key, level) ∈ list ∧ image.index = table.depth - 1 - level := by
  obtain ⟨level, recorded, index⟩ :=
    ((table.extend header list valid).find_eq_some_iff .here key image).mp named
  rw [Var.index_here, level?_extend_zero] at recorded
  exact ⟨level, levelOf_member recorded, index⟩

/-- The image of an earlier old protocol is the one the earlier table names. -/
theorem find_extend_there [DecidableEq K] (table : CalleeTable F old new)
    (header : ProtocolHeader) (list : List (K × Nat))
    (valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (F pair.1 header))
    {other : ProtocolHeader} (callee : Var old other) (key : K) :
    (table.extend header list valid).find callee.there key = table.find callee key := by
  cases named : table.find callee key with
  | none =>
      refine ((table.extend header list valid).find_eq_none_iff callee.there key).mpr ?_
      rw [Var.index_there, level?_extend_succ]
      exact (table.find_eq_none_iff callee key).mp named
  | some image =>
      obtain ⟨level, recorded, index⟩ := (table.find_eq_some_iff callee key image).mp named
      refine ((table.extend header list valid).find_eq_some_iff callee.there key image).mpr
        ⟨level, ?_, index⟩
      rw [Var.index_there, level?_extend_succ]
      exact recorded

end CalleeTable

/-! ## A step that copies every protocol once per key -/

inductive RetargetRefusal where
  /-- An applied protocol has no copy for the key. -/
  | missing
  /-- A rewritten definition violates a residual condition. -/
  | residual (violation : Violation)
  deriving Repr

section Retarget

variable {K : Type} [DecidableEq K] {operations : List OperationSignature}
  {functions : List FunctionHeader} {old new : List ProtocolHeader} {deployed : Bool}

mutual
  /-- A region over the old protocol headers as a region over the new ones. Every
  operation but `apply` is rebuilt from its own parts; a local operation with its nested
  regions is the old term. An `apply` names the callee's copy for the key. -/
  def retargetRegion (table : CalleeTable (fun (_ : K) header => header) old new) (key : K)
      {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out →
        Except RetargetRefusal (Region (ProtocolDialect operations functions new deployed) Γ out)
    | .ret values => .ok (.ret values)
    | .stop reason => .ok (.stop reason)
    | .bind body rest =>
        match retargetRegion table key body, retargetRegion table key rest with
        | .ok body, .ok rest => .ok (.bind body rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.at role op bodies) arguments _ rest =>
        match retargetRegion table key rest with
        | .ok rest => .ok (.letOp (.at role op bodies) arguments .nil rest)
        | .error refusal => .error refusal
    | .letOp (.exchange sender receiver site type) arguments _ rest =>
        match retargetRegion table key rest with
        | .ok rest => .ok (.letOp (.exchange sender receiver site type) arguments .nil rest)
        | .error refusal => .error refusal
    | .letOp (.draw owner receivers site law populated) arguments _ rest =>
        match retargetRegion table key rest with
        | .ok rest => .ok (.letOp (.draw owner receivers site law populated) arguments .nil rest)
        | .error refusal => .error refusal
    | .letOp (.sample owner site law populated) arguments _ rest =>
        match retargetRegion table key rest with
        | .ok rest => .ok (.letOp (.sample owner site law populated) arguments .nil rest)
        | .error refusal => .error refusal
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest =>
        match retargetRegions table key bodies, retargetRegion table key rest with
        | .ok bodies, .ok rest =>
            .ok (.letOp (.repeat participants count carried collected captures covered) arguments
              bodies rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest =>
        match retargetRegions table key bodies, retargetRegion table key rest with
        | .ok bodies, .ok rest =>
            .ok (.letOp (.choose participants tag captures outputs covered) arguments bodies rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.apply callee roleMap site permitted) arguments _ rest =>
        match table.find callee key, retargetRegion table key rest with
        | some image, .ok rest => .ok (.letOp (.apply image roleMap site permitted) arguments .nil rest)
        | none, _ => .error .missing
        | _, .error refusal => .error refusal

  def retargetRegions (table : CalleeTable (fun (_ : K) header => header) old new) (key : K)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures →
        Except RetargetRefusal
          (Regions (ProtocolDialect operations functions new deployed) signatures)
    | .nil => .ok .nil
    | .cons body tail =>
        match retargetRegion table key body, retargetRegions table key tail with
        | .ok body, .ok tail => .ok (.cons body tail)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
end

/-- The copies made so far of one protocol, over the new headers so far. -/
structure Copies (K : Type) (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (old : List ProtocolHeader) (header : ProtocolHeader) where
  new : List ProtocolHeader
  protocols : Protocols typeTable operations functions new
  table : CalleeTable (fun (_ : K) header => header) old new
  list : List (K × Nat)
  valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some header

/-- One copy of a protocol per key. Each copy is typed over the new headers before it
and is checked for residual violations. -/
def copyProtocol {typeTable : TypeTable} {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions old header) :
    List K → Copies K typeTable operations functions old header →
      Except RetargetRefusal (Copies K typeTable operations functions old header)
  | [], copies => .ok copies
  | key :: keys, ⟨new, protocols, table, list, valid⟩ =>
      match retargetRegion table key definition.body with
      | .ok body =>
          match wellFormed : (ProtocolDefinition.mk (protocols := new) (header := header) body).violation
              typeTable with
          | none =>
              copyProtocol definition keys
                ⟨header :: new, .snoc protocols ⟨body⟩ wellFormed, table.weaken header,
                  (key, table.depth) :: list, fun pair member => by
                    rcases List.mem_cons.mp member with rfl | earlier
                    · show atLevel? (header :: new) (table.depth + 1) table.depth = some header
                      rw [table.counted]
                      exact atLevel?_newest new header
                    · exact atLevel?_cons new header (valid pair earlier)⟩
          | some violation => .error (.residual violation)
      | .error refusal => .error refusal

/-- The copied protocols of a program, with the table from the old protocols. -/
structure Retargeted (K : Type) (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (old : List ProtocolHeader) where
  new : List ProtocolHeader
  protocols : Protocols typeTable operations functions new
  table : CalleeTable (fun (_ : K) header => header) old new

/-- Every protocol of a program, copied once per key. The functions are not touched. -/
def copyProtocols {typeTable : TypeTable} (keys : List K) :
    {old : List ProtocolHeader} → Protocols typeTable operations functions old →
      Except RetargetRefusal (Retargeted K typeTable operations functions old)
  | _, .nil => .ok ⟨[], .nil, .empty⟩
  | _, .snoc (header := header) earlier definition _ =>
      match copyProtocols keys earlier with
      | .ok ⟨new, protocols, table⟩ =>
          match copyProtocol definition keys ⟨new, protocols, table, [], fun _ member => nomatch member⟩ with
          | .ok ⟨new, protocols, table, list, valid⟩ =>
              .ok ⟨new, protocols, table.extend header list valid⟩
          | .error refusal => .error refusal
      | .error refusal => .error refusal

end Retarget

end Zkc.Core
