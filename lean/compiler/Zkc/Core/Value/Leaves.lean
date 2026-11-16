module

public import Zkc.Core.Value.Skeleton
public import Zkc.Core.Value.Valuation

@[expose] public section

/-!
The leaves of a skeleton, whatever the run.

The leaves of a skeleton are apart from the table (`Skel.Apart`): no leaf is a result of an
entry. They are below the next identifier (`Skel.Below`), and made in order from a number on
(`Skel.Fresh`), so that setting one never changes a value that a name in scope reads. Each of
these is kept as the table grows above the leaves. An application is placed on the operands
written, in the order that `ValueRules.order` gives, which are the same identifiers
(`ValueRules.mem_order`). Nothing here reads a semantics: these are the facts about identifiers
that the meaning of a skeleton (`Value/Runs.lean`) and the walk that builds and follows skeletons
(`Facts/Growth.lean`) rest on.
-/

namespace Zkc.Core

open FactCheck (Table St share fresh idsOf bindIds)

/-! ## Leaves apart from the table -/

section
variable {D : Dialect} {Raw : Type} (table : Table Raw)

/-- No identifier from `lo` to `lo + count - 1` is a result of an entry of the table. -/
def LeavesApart (lo count : Nat) : Prop :=
  ∀ e, e ∈ table → ∀ j, j < e.count → ∀ i, i < count → e.lo + j ≠ lo + i

mutual
  /-- The leaves of a skeleton are no results of entries of the table. -/
  def Skel.Apart : {outs : List D.Ty} → Skel D outs → Prop
    | _, .ret _ => True
    | _, .effect (res := res) _ _ _ results rest =>
        LeavesApart table results res.length ∧ rest.Apart
    | _, .guard _ _ _ _ _ rest => rest.Apart
    | _, .choose (mid := mid) _ _ _ _ onTrue onFalse results rest =>
        onTrue.Apart ∧ onFalse.Apart ∧ LeavesApart table results mid.length ∧ rest.Apart
    | _, .cases (mid := mid) _ _ _ _ arms results rest =>
        arms.Apart ∧ LeavesApart table results mid.length ∧ rest.Apart
    | _, .loop (carried := carried) (each := each) _ _ _ _ inputs body results rest =>
        LeavesApart table inputs (carried.length + 1) ∧ body.Apart ∧
          LeavesApart table results (carried.length + each.length) ∧ rest.Apart
    | _, .block (mid := mid) _ _ body results rest =>
        body.Apart ∧ LeavesApart table results mid.length ∧ rest.Apart
    | _, .attempt (mid := mid) _ _ input body results rest =>
        LeavesApart table input 1 ∧ body.Apart ∧ LeavesApart table results mid.length ∧
          rest.Apart
  /-- The leaves of the arms of a skeleton are no results of entries of the table. -/
  def SkelArms.Apart : {mid payloads : List D.Ty} → SkelArms D mid payloads → Prop
    | _, _, .nil => True
    | _, _, .cons input arm rest => LeavesApart table input 1 ∧ arm.Apart ∧ rest.Apart
end

mutual
  /-- Every leaf of a skeleton is below a number. -/
  def Skel.Below {outs : List D.Ty} (skel : Skel D outs) (next : Nat) : Prop :=
    match skel with
    | .ret _ => True
    | .effect (res := res) _ _ _ results rest => results + res.length ≤ next ∧ rest.Below next
    | .guard _ _ _ _ _ rest => rest.Below next
    | .choose (mid := mid) _ _ _ _ onTrue onFalse results rest =>
        onTrue.Below next ∧ onFalse.Below next ∧ results + mid.length ≤ next ∧ rest.Below next
    | .cases (mid := mid) _ _ _ _ arms results rest =>
        arms.Below next ∧ results + mid.length ≤ next ∧ rest.Below next
    | .loop (carried := carried) (each := each) _ _ _ _ inputs body results rest =>
        inputs + (carried.length + 1) ≤ next ∧ body.Below next ∧
          results + (carried.length + each.length) ≤ next ∧ rest.Below next
    | .block (mid := mid) _ _ body results rest =>
        body.Below next ∧ results + mid.length ≤ next ∧ rest.Below next
    | .attempt (mid := mid) _ _ input body results rest =>
        input + 1 ≤ next ∧ body.Below next ∧ results + mid.length ≤ next ∧ rest.Below next
  /-- Every leaf of the arms of a skeleton is below a number. -/
  def SkelArms.Below {mid payloads : List D.Ty} (arms : SkelArms D mid payloads) (next : Nat) :
      Prop :=
    match arms with
    | .nil => True
    | .cons input arm rest => input + 1 ≤ next ∧ arm.Below next ∧ rest.Below next
end

mutual
  /-- The leaves of a skeleton are made in order from a number on, so that setting one never
  changes a value that a name in scope reads: the leaves of an entry are at or above the number,
  and what follows the entry has its leaves above them; a region has its leaves from the number
  on, or above its inputs when it has some. Following a skeleton relies on it, from a number
  above every value that the run already has (`Analysis.ValueSide.walk_runs_followed`). -/
  def Skel.Fresh {outs : List D.Ty} (skel : Skel D outs) (lo : Nat) : Prop :=
    match skel with
    | .ret _ => True
    | .effect (res := res) _ _ _ results rest => lo ≤ results ∧ rest.Fresh (results + res.length)
    | .guard _ _ _ _ _ rest => rest.Fresh lo
    | .choose (mid := mid) _ _ _ _ onTrue onFalse results rest =>
        onTrue.Fresh lo ∧ onFalse.Fresh lo ∧ lo ≤ results ∧ rest.Fresh (results + mid.length)
    | .cases (mid := mid) _ _ _ _ arms results rest =>
        arms.Fresh lo ∧ lo ≤ results ∧ rest.Fresh (results + mid.length)
    | .loop (carried := carried) (each := each) _ _ _ _ inputs body results rest =>
        lo ≤ inputs ∧ body.Fresh (inputs + (carried.length + 1)) ∧ lo ≤ results ∧
          rest.Fresh (results + (carried.length + each.length))
    | .block (mid := mid) _ _ body results rest =>
        body.Fresh lo ∧ lo ≤ results ∧ rest.Fresh (results + mid.length)
    | .attempt (mid := mid) _ _ input body results rest =>
        lo ≤ input ∧ body.Fresh (input + 1) ∧ lo ≤ results ∧ rest.Fresh (results + mid.length)
  /-- The leaves of the arms of a skeleton are made in order from a number on: each arm's above
  its input, so that setting them never changes a value that a name in scope reads. -/
  def SkelArms.Fresh {mid payloads : List D.Ty} (arms : SkelArms D mid payloads) (lo : Nat) :
      Prop :=
    match arms with
    | .nil => True
    | .cons input arm rest => lo ≤ input ∧ arm.Fresh (input + 1) ∧ rest.Fresh lo
end

end

/-! ### Leaves and entries as the table grows -/

section
variable {D : Dialect} {Raw : Type}

/-- A state that grew from another has the other's entries. -/
theorem FactCheck.St.Grows.sub {T : Type} {st st' : St T Raw} (grows : FactCheck.St.Grows st st') :
    ∀ e, e ∈ st.table → e ∈ st'.table := fun e known => by
  obtain ⟨_, new, entries, _⟩ := grows
  show e ∈ st'.table.entries
  rw [entries]
  exact List.mem_append_right _ known

/-- Identifiers apart from a table are apart from every table that grows from it by entries
above them. -/
theorem LeavesApart.grows {T : Type} {st st' : St T Raw} {lo count : Nat}
    (apart : LeavesApart st.table lo count) (below : lo + count ≤ st.next)
    (grows : FactCheck.St.Grows st st') : LeavesApart st'.table lo count := by
  obtain ⟨_, new, entries, above⟩ := grows
  intro e known j position i lt same
  have known' : e ∈ new ++ st.table.entries := by rw [← entries]; exact known
  rcases List.mem_append.mp known' with made | old
  · have := above e made
    omega
  · exact apart e old j position i lt same

/-- Identifiers made fresh are apart from every table that grows from the state that made
them. -/
theorem LeavesApart.of_fresh {T : Type} {st st' : St T Raw} (count : Nat)
    (wf : Table.WF st.next st.table) (grows : FactCheck.St.Grows (fresh count st).2 st') :
    LeavesApart st'.table st.next count := by
  obtain ⟨_, new, entries, above⟩ := grows
  intro e known j position i lt same
  have known' : e ∈ new ++ (fresh count st).2.table.entries := by rw [← entries]; exact known
  rcases List.mem_append.mp known' with made | old
  · have := above e made
    simp only [fresh] at this
    omega
  · have := (wf.mem (show e ∈ st.table from old)).2
    omega

mutual
  /-- Leaves below a number are below every larger number. -/
  theorem Skel.Below.mono :
      ∀ {outs : List D.Ty} {skel : Skel D outs} {next next' : Nat}, skel.Below next →
        next ≤ next' → skel.Below next'
    | _, .ret _, _, _, _, _ => trivial
    | _, .effect _ _ _ _ rest, _, _, below, le =>
        ⟨Nat.le_trans below.1 le, Skel.Below.mono (skel := rest) below.2 le⟩
    | _, .guard _ _ _ _ _ rest, _, _, below, le => Skel.Below.mono (skel := rest) below le
    | _, .choose _ _ _ _ onTrue onFalse _ rest, _, _, below, le =>
        ⟨Skel.Below.mono (skel := onTrue) below.1 le, Skel.Below.mono (skel := onFalse) below.2.1
          le, Nat.le_trans below.2.2.1 le, Skel.Below.mono (skel := rest) below.2.2.2 le⟩
    | _, .cases _ _ _ _ arms _ rest, _, _, below, le =>
        ⟨SkelArms.Below.mono (arms := arms) below.1 le, Nat.le_trans below.2.1 le,
          Skel.Below.mono (skel := rest) below.2.2 le⟩
    | _, .loop _ _ _ _ _ body _ rest, _, _, below, le =>
        ⟨Nat.le_trans below.1 le, Skel.Below.mono (skel := body) below.2.1 le,
          Nat.le_trans below.2.2.1 le, Skel.Below.mono (skel := rest) below.2.2.2 le⟩
    | _, .block _ _ body _ rest, _, _, below, le =>
        ⟨Skel.Below.mono (skel := body) below.1 le, Nat.le_trans below.2.1 le,
          Skel.Below.mono (skel := rest) below.2.2 le⟩
    | _, .attempt _ _ _ body _ rest, _, _, below, le =>
        ⟨Nat.le_trans below.1 le, Skel.Below.mono (skel := body) below.2.1 le,
          Nat.le_trans below.2.2.1 le, Skel.Below.mono (skel := rest) below.2.2.2 le⟩
  /-- Leaves of arms below a number are below every larger number. -/
  theorem SkelArms.Below.mono :
      ∀ {mid payloads : List D.Ty} {arms : SkelArms D mid payloads} {next next' : Nat},
        arms.Below next → next ≤ next' → arms.Below next'
    | _, _, .nil, _, _, _, _ => trivial
    | _, _, .cons _ arm rest, _, _, below, le =>
        ⟨Nat.le_trans below.1 le, Skel.Below.mono (skel := arm) below.2.1 le,
          SkelArms.Below.mono (arms := rest) below.2.2 le⟩
end

mutual
  /-- Leaves made in order from a number on are made in order from every smaller number on. -/
  theorem Skel.Fresh.mono :
      ∀ {outs : List D.Ty} {skel : Skel D outs} {lo lo' : Nat}, skel.Fresh lo → lo' ≤ lo →
        skel.Fresh lo'
    | _, .ret _, _, _, _, _ => trivial
    | _, .effect _ _ _ _ _, _, _, fresh, le => ⟨Nat.le_trans le fresh.1, fresh.2⟩
    | _, .guard _ _ _ _ _ rest, _, _, fresh, le => Skel.Fresh.mono (skel := rest) fresh le
    | _, .choose _ _ _ _ onTrue onFalse _ _, _, _, fresh, le =>
        ⟨Skel.Fresh.mono (skel := onTrue) fresh.1 le, Skel.Fresh.mono (skel := onFalse) fresh.2.1
          le, Nat.le_trans le fresh.2.2.1, fresh.2.2.2⟩
    | _, .cases _ _ _ _ arms _ _, _, _, fresh, le =>
        ⟨SkelArms.Fresh.mono (arms := arms) fresh.1 le, Nat.le_trans le fresh.2.1, fresh.2.2⟩
    | _, .loop _ _ _ _ _ _ _ _, _, _, fresh, le =>
        ⟨Nat.le_trans le fresh.1, fresh.2.1, Nat.le_trans le fresh.2.2.1, fresh.2.2.2⟩
    | _, .block _ _ body _ _, _, _, fresh, le =>
        ⟨Skel.Fresh.mono (skel := body) fresh.1 le, Nat.le_trans le fresh.2.1, fresh.2.2⟩
    | _, .attempt _ _ _ _ _ _, _, _, fresh, le =>
        ⟨Nat.le_trans le fresh.1, fresh.2.1, Nat.le_trans le fresh.2.2.1, fresh.2.2.2⟩
  /-- Leaves of arms made in order from a number on are made in order from every smaller number
  on. -/
  theorem SkelArms.Fresh.mono :
      ∀ {mid payloads : List D.Ty} {arms : SkelArms D mid payloads} {lo lo' : Nat},
        arms.Fresh lo → lo' ≤ lo → arms.Fresh lo'
    | _, _, .nil, _, _, _, _ => trivial
    | _, _, .cons _ _ rest, _, _, fresh, le =>
        ⟨Nat.le_trans le fresh.1, fresh.2.1, SkelArms.Fresh.mono (arms := rest) fresh.2.2 le⟩
end

mutual
  /-- Leaves apart from a table and below its next identifier are apart from every table that
  grows from it. -/
  theorem Skel.Apart.grows {T : Type} {st st' : St T Raw} (grows : FactCheck.St.Grows st st') :
      ∀ {outs : List D.Ty} (skel : Skel D outs), skel.Apart st.table → skel.Below st.next →
        skel.Apart st'.table
    | _, .ret _, _, _ => trivial
    | _, .effect _ _ _ _ rest, apart, below =>
        ⟨apart.1.grows below.1 grows, Skel.Apart.grows grows rest apart.2 below.2⟩
    | _, .guard _ _ _ _ _ rest, apart, below => Skel.Apart.grows grows rest apart below
    | _, .choose _ _ _ _ onTrue onFalse _ rest, apart, below =>
        ⟨Skel.Apart.grows grows onTrue apart.1 below.1,
          Skel.Apart.grows grows onFalse apart.2.1 below.2.1,
          apart.2.2.1.grows below.2.2.1 grows, Skel.Apart.grows grows rest apart.2.2.2 below.2.2.2⟩
    | _, .cases _ _ _ _ arms _ rest, apart, below =>
        ⟨SkelArms.Apart.grows grows arms apart.1 below.1, apart.2.1.grows below.2.1 grows,
          Skel.Apart.grows grows rest apart.2.2 below.2.2⟩
    | _, .loop _ _ _ _ _ body _ rest, apart, below =>
        ⟨apart.1.grows below.1 grows, Skel.Apart.grows grows body apart.2.1 below.2.1,
          apart.2.2.1.grows below.2.2.1 grows, Skel.Apart.grows grows rest apart.2.2.2 below.2.2.2⟩
    | _, .block _ _ body _ rest, apart, below =>
        ⟨Skel.Apart.grows grows body apart.1 below.1, apart.2.1.grows below.2.1 grows,
          Skel.Apart.grows grows rest apart.2.2 below.2.2⟩
    | _, .attempt _ _ _ body _ rest, apart, below =>
        ⟨apart.1.grows below.1 grows, Skel.Apart.grows grows body apart.2.1 below.2.1,
          apart.2.2.1.grows below.2.2.1 grows, Skel.Apart.grows grows rest apart.2.2.2 below.2.2.2⟩
  /-- Leaves of arms apart from a table and below its next identifier are apart from every
  table that grows from it. -/
  theorem SkelArms.Apart.grows {T : Type} {st st' : St T Raw} (grows : FactCheck.St.Grows st st') :
      ∀ {mid payloads : List D.Ty} (arms : SkelArms D mid payloads), arms.Apart st.table →
        arms.Below st.next → arms.Apart st'.table
    | _, _, .nil, _, _ => trivial
    | _, _, .cons _ arm rest, apart, below =>
        ⟨apart.1.grows below.1 grows, Skel.Apart.grows grows arm apart.2.1 below.2.1,
          SkelArms.Apart.grows grows rest apart.2.2 below.2.2⟩
end

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : ValueRules D Raw)

/-! ### Sharing and the order of operands -/

/-- Sharing gives as many identifiers as asked for. -/
theorem FactCheck.share_length {T : Type} (written : Raw) (args : List Nat) (count : Nat)
    (st : St T Raw) : (share written args count st).1.length = count := by
  simp only [share]
  split <;> simp

omit [DecidableEq Raw] in
/-- The operands in the order in which the table places an application are the operands
written. -/
theorem ValueRules.mem_order (raw : Raw) :
    ∀ {ids : List Nat} {id : Nat}, id ∈ rules.order raw ids → id ∈ ids
  | [], _, m => m
  | [_], _, m => m
  | [first, second], id, m => by
      simp only [ValueRules.order] at m
      split at m
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at m ⊢
        exact m.symm
      · exact m
  | _ :: _ :: _ :: _, _, m => m

omit [DecidableEq Raw] in
/-- Operands below a bound are below it in the order in which the table places an
application. -/
theorem ValueRules.order_lt {raw : Raw} {ids : List Nat} {next : Nat}
    (below : ∀ id, id ∈ ids → id < next) : ∀ id, id ∈ rules.order raw ids → id < next :=
  fun id m => below id (rules.mem_order raw m)

end

end Zkc.Core
