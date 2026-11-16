module

public import Zkc.Core.Value.Follows
public import Zkc.Core.Facts.Growth

@[expose] public section

/-!
What building a skeleton and following one do to the state, whatever the run.

The leaves of a skeleton are apart from the table (`Skel.Apart`): no leaf is a result of an
entry. They are below the next identifier (`Skel.Below`), and made in order from a number on
(`Skel.Fresh`), so that setting one never changes a value that a name in scope reads. Each of
these is kept as the table grows above the leaves.

The skeleton of a term is built above its state: the table stays well formed and grows, and
the skeleton's leaves are below the next identifier, apart from the table, and made in order
from the state's next identifier on (`Term.skeleton_state`). Following a skeleton builds above
the state in the same way and keeps its leaves apart (`Term.follows_state`). Nothing here reads
a semantics: these are the facts about identifiers that the meaning of a skeleton
(`Value/Runs.lean`) and its proofs (`Value/Soundness.lean`) rest on.
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
  above every value that the run already has (`Term.follows_runs`). -/
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

/-! ### The state that the skeleton of a term builds -/

/-- Sharing gives as many identifiers as asked for. -/
theorem FactCheck.share_length {T : Type} (written : Raw) (args : List Nat) (count : Nat)
    (st : St T Raw) : (share written args count st).1.length = count := by
  simp only [share]
  split <;> simp

mutual
  /-- The skeleton of a term is built above the state: the table stays well formed and grows,
  and the leaves are below the next identifier, apart from the table and made in order from the
  state's next identifier on. -/
  theorem Term.skeleton_state :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (st : St D.Ty Raw),
        FactCheck.InScope Γ ids st.next → Table.WF st.next st.table →
        Table.WF (t.skeleton rules ids st).2.next (t.skeleton rules ids st).2.table ∧
          FactCheck.St.Grows st (t.skeleton rules ids st).2 ∧
          (t.skeleton rules ids st).1.Below (t.skeleton rules ids st).2.next ∧
          (t.skeleton rules ids st).1.Apart (t.skeleton rules ids st).2.table ∧
          (t.skeleton rules ids st).1.Fresh st.next
    | _, _, .ret _, _, st, _, wf => ⟨wf, .refl st, trivial, trivial, trivial⟩
    | _, _, .op (res := res) _ o operands results rest, ids, st, scope, wf => by
        cases written : rules.written o with
        | some raw =>
            simp only [Term.skeleton, written]
            obtain ⟨wf', grows, made⟩ :=
              FactCheck.share_grows raw (idsOf ids operands) res.length st wf
                (FactCheck.idsOf_lt scope operands)
            obtain ⟨wf'', grows', below, apart, inOrder⟩ := Term.skeleton_state rest _ _
              (FactCheck.InScope.bind results _ (scope.mono grows.next)
                (by rw [FactCheck.share_length]) made) wf'
            exact ⟨wf'', grows.trans grows', below, apart, inOrder.mono grows.next⟩
        | none =>
            simp only [Term.skeleton, written]
            obtain ⟨wf', grows, made⟩ := FactCheck.fresh_grows res.length st wf
            obtain ⟨wf'', grows', below, apart, inOrder⟩ := Term.skeleton_state rest _ _
              (FactCheck.InScope.bind results _ (scope.mono grows.next) (by simp [fresh]) made) wf'
            exact ⟨wf'', grows.trans grows', ⟨grows'.next, below⟩,
              ⟨LeavesApart.of_fresh res.length wf grows', apart⟩, ⟨Nat.le_refl _, inOrder⟩⟩
    | _, _, .guard _ _ _ _ _ rest, ids, st, scope, wf => by
        simp only [Term.skeleton]
        exact Term.skeleton_state rest ids st scope wf
    | _, _, .choose (mid := mid) _ _ _ _ _ onTrue onFalse results rest, ids, st, scope, wf => by
        simp only [Term.skeleton]
        obtain ⟨wf1, grows1, below1, apart1, inOrder1⟩ := Term.skeleton_state onTrue ids st scope wf
        obtain ⟨wf2, grows2, below2, apart2, inOrder2⟩ :=
          Term.skeleton_state onFalse ids _ (scope.mono grows1.next) wf1
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf2
        obtain ⟨wf4, grows4, below4, apart4, inOrder4⟩ := Term.skeleton_state rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows1.trans (grows2.trans grows3)).next)
            (by simp [fresh]) made) wf3
        have after1 := grows2.trans (grows3.trans grows4)
        have after2 := grows3.trans grows4
        exact ⟨wf4, grows1.trans after1,
          ⟨below1.mono after1.next, below2.mono after2.next, grows4.next, below4⟩,
          ⟨Skel.Apart.grows after1 _ apart1 below1, Skel.Apart.grows after2 _ apart2 below2,
            LeavesApart.of_fresh mid.length wf2 grows4, apart4⟩,
          ⟨inOrder1, inOrder2.mono grows1.next, (grows1.trans grows2).next, inOrder4⟩⟩
    | _, _, .cases (mid := mid) _ _ _ _ _ arms results rest, ids, st, scope, wf => by
        simp only [Term.skeleton]
        obtain ⟨wf1, grows1, below1, apart1, inOrder1⟩ := Arms.skeleton_state arms ids st scope wf
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf1
        obtain ⟨wf4, grows4, below4, apart4, inOrder4⟩ := Term.skeleton_state rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows1.trans grows3).next)
            (by simp [fresh]) made) wf3
        have after1 := grows3.trans grows4
        exact ⟨wf4, grows1.trans after1, ⟨below1.mono after1.next, grows4.next, below4⟩,
          ⟨SkelArms.Apart.grows after1 _ apart1 below1, LeavesApart.of_fresh mid.length wf1 grows4,
            apart4⟩,
          ⟨inOrder1, grows1.next, inOrder4⟩⟩
    | _, _, .loop (carried := carried) (each := each) _ _ _ _ _ inputs body results rest, ids, st,
        scope, wf => by
        simp only [Term.skeleton]
        obtain ⟨wf0, grows0, made0⟩ := FactCheck.fresh_grows (carried.length + 1) st wf
        obtain ⟨wf1, grows1, below1, apart1, inOrder1⟩ := Term.skeleton_state body _ _
          (FactCheck.InScope.bind inputs _ (scope.mono grows0.next) (by simp [fresh]) made0) wf0
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows (carried.length + each.length) _ wf1
        obtain ⟨wf4, grows4, below4, apart4, inOrder4⟩ := Term.skeleton_state rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows0.trans (grows1.trans grows3)).next)
            (by simp [fresh]) made) wf3
        have after1 := grows3.trans grows4
        exact ⟨wf4, grows0.trans (grows1.trans after1),
          ⟨(grows1.trans after1).next, below1.mono after1.next, grows4.next, below4⟩,
          ⟨LeavesApart.of_fresh _ wf (grows1.trans after1), Skel.Apart.grows after1 _ apart1 below1,
            LeavesApart.of_fresh _ wf1 grows4, apart4⟩,
          ⟨Nat.le_refl _, inOrder1, (grows0.trans grows1).next, inOrder4⟩⟩
    | _, _, .block (mid := mid) _ _ body results rest, ids, st, scope, wf => by
        simp only [Term.skeleton]
        obtain ⟨wf1, grows1, below1, apart1, inOrder1⟩ := Term.skeleton_state body ids st scope wf
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf1
        obtain ⟨wf4, grows4, below4, apart4, inOrder4⟩ := Term.skeleton_state rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows1.trans grows3).next)
            (by simp [fresh]) made) wf3
        have after1 := grows3.trans grows4
        exact ⟨wf4, grows1.trans after1, ⟨below1.mono after1.next, grows4.next, below4⟩,
          ⟨Skel.Apart.grows after1 _ apart1 below1, LeavesApart.of_fresh mid.length wf1 grows4,
            apart4⟩,
          ⟨inOrder1, grows1.next, inOrder4⟩⟩
    | _, _, .attempt (mid := mid) _ _ _ inputs body results rest, ids, st, scope, wf => by
        simp only [Term.skeleton]
        obtain ⟨wf0, grows0, made0⟩ := FactCheck.fresh_grows 1 st wf
        obtain ⟨wf1, grows1, below1, apart1, inOrder1⟩ := Term.skeleton_state body _ _
          (FactCheck.InScope.bind inputs _ (scope.mono grows0.next) (by simp [fresh]) made0) wf0
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf1
        obtain ⟨wf4, grows4, below4, apart4, inOrder4⟩ := Term.skeleton_state rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows0.trans (grows1.trans grows3)).next)
            (by simp [fresh]) made) wf3
        have after1 := grows3.trans grows4
        exact ⟨wf4, grows0.trans (grows1.trans after1),
          ⟨(grows1.trans after1).next, below1.mono after1.next, grows4.next, below4⟩,
          ⟨LeavesApart.of_fresh 1 wf (grows1.trans after1), Skel.Apart.grows after1 _ apart1 below1,
            LeavesApart.of_fresh mid.length wf1 grows4, apart4⟩,
          ⟨Nat.le_refl _, inOrder1, (grows0.trans grows1).next, inOrder4⟩⟩
  /-- The skeletons of arms are built above the state, as those of terms. -/
  theorem Arms.skeleton_state :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) (ids : Ctx Nat)
        (st : St D.Ty Raw),
        FactCheck.InScope Γ ids st.next → Table.WF st.next st.table →
        Table.WF (arms.skeleton rules ids st).2.next (arms.skeleton rules ids st).2.table ∧
          FactCheck.St.Grows st (arms.skeleton rules ids st).2 ∧
          (arms.skeleton rules ids st).1.Below (arms.skeleton rules ids st).2.next ∧
          (arms.skeleton rules ids st).1.Apart (arms.skeleton rules ids st).2.table ∧
          (arms.skeleton rules ids st).1.Fresh st.next
    | _, _, _, .nil, _, st, _, wf => ⟨wf, .refl st, trivial, trivial, trivial⟩
    | _, _, _, .cons inputs arm rest, ids, st, scope, wf => by
        simp only [Arms.skeleton]
        obtain ⟨wf0, grows0, made0⟩ := FactCheck.fresh_grows 1 st wf
        obtain ⟨wf1, grows1, below1, apart1, inOrder1⟩ := Term.skeleton_state arm _ _
          (FactCheck.InScope.bind inputs _ (scope.mono grows0.next) (by simp [fresh]) made0) wf0
        obtain ⟨wf2, grows2, below2, apart2, inOrder2⟩ := Arms.skeleton_state rest ids _
          (scope.mono (grows0.trans grows1).next) wf1
        exact ⟨wf2, grows0.trans (grows1.trans grows2),
          ⟨(grows1.trans grows2).next, below1.mono grows2.next, below2⟩,
          ⟨LeavesApart.of_fresh 1 wf (grows1.trans grows2), Skel.Apart.grows grows2 _ apart1 below1,
            apart2⟩,
          ⟨Nat.le_refl _, inOrder1, inOrder2.mono (grows0.trans grows1).next⟩⟩
end

/-- A count that a loop's count follows is the loop's count on the identifiers. -/
theorem Times.follows_eq (checks : SkelRules D) {w : D.Who} {Γ : Ctx D.Ty} (ids : Ctx Nat) :
    ∀ (times : Times D w Γ) (count : Count D w), times.follows checks ids count = true →
      count = times.count ids
  | .fixed n, .fixed n', same => by
      simp only [Times.follows, decide_eq_true_eq] at same
      subst same
      rfl
  | .value (t := t) c ok, .value (t := t') id ok', same => by
      simp only [Times.follows] at same
      split at same
      · next sameType _ =>
          subst sameType
          simp only [decide_eq_true_eq] at same
          subst same
          rfl
      · cases same
  | .fixed _, .value .., same => by cases same
  | .value .., .fixed _, same => by cases same

/-! ### The state that following builds -/

mutual
  /-- Following a skeleton builds above the state: the table stays well formed and grows, and the
  skeleton's leaves, below the state's next identifier, stay apart from it. -/
  theorem Term.follows_state (checks : SkelRules D) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (skel : Skel D outs) (ids : Ctx Nat)
        (st st' : St D.Ty Raw), t.follows rules checks skel ids st = some st' →
        FactCheck.InScope Γ ids st.next → Table.WF st.next st.table → skel.Below st.next →
        skel.Apart st.table →
        Table.WF st'.next st'.table ∧ FactCheck.St.Grows st st' ∧ skel.Apart st'.table
    | _, _, .ret _, skel, _, st, st', followed, _, wf, _, apart => by
        cases skel
        case ret =>
          simp only [Term.follows] at followed
          split at followed
          · cases followed
            exact ⟨wf, .refl st, apart⟩
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .op (res := res) _ o operands results rest, skel, ids, st, st', followed, scope, wf,
        below, apart => by
        cases written : rules.written o with
        | some raw =>
            simp only [Term.follows, written] at followed
            obtain ⟨wf', grows, made⟩ :=
              FactCheck.share_grows raw (idsOf ids operands) res.length st wf
                (FactCheck.idsOf_lt scope operands)
            obtain ⟨wf'', grows', apart'⟩ := Term.follows_state checks rest skel _ _ st'
              followed
              (FactCheck.InScope.bind results _ (scope.mono grows.next)
                (by rw [FactCheck.share_length]) made)
              wf' (below.mono grows.next) (Skel.Apart.grows grows skel apart below)
            exact ⟨wf'', grows.trans grows', apart'⟩
        | none =>
            cases skel
            case effect ins' res' key' o' operands' results' rest' =>
              simp only [Term.follows, written] at followed
              split at followed
              · next sameIns sameRes _ _ =>
                  split at followed
                  · subst sameIns sameRes
                    obtain ⟨wf', grows, apart'⟩ := Term.follows_state checks rest rest' _ st st'
                      followed
                      (FactCheck.InScope.bind results _ scope (by simp) fun i m => by
                        have := mem_range'_bounds m
                        have := below.1
                        omega)
                      wf below.2 apart.2
                    exact ⟨wf', grows, ⟨apart.1.grows below.1 grows, apart'⟩⟩
                  · cases followed
              · cases followed
            all_goals simp [Term.follows, written] at followed
    | _, _, .guard _ _ _ _ _ rest, skel, ids, st, st', followed, scope, wf, below, apart => by
        cases skel
        case guard t' key' w' condition ok' why' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · split at followed
            · exact Term.follows_state checks rest rest' ids st st' followed scope wf below
                apart
            · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .choose _ _ _ _ _ onTrue onFalse results rest, skel, ids, st, st', followed, scope, wf,
        below, apart => by
        cases skel
        case choose mid' t' key' w' condition ok' onTrue' onFalse' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameTy sameMid _ _ _ =>
              split at followed
              · subst sameMid
                simp only [cast_eq] at followed
                obtain ⟨afterTrue, followedTrue, followedAfter⟩ :=
                  Option.bind_eq_some_iff.mp followed
                obtain ⟨afterFalse, followedFalse, followedRest⟩ :=
                  Option.bind_eq_some_iff.mp followedAfter
                obtain ⟨wf1, grows1, apart1⟩ := Term.follows_state checks onTrue onTrue' ids
                  st afterTrue followedTrue scope wf below.1 apart.1
                obtain ⟨wf2, grows2, apart2⟩ := Term.follows_state checks onFalse onFalse'
                  ids afterTrue afterFalse followedFalse (scope.mono grows1.next) wf1
                  (below.2.1.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.1 below.2.1)
                obtain ⟨wf3, grows3, apart3⟩ := Term.follows_state checks rest rest' _
                  afterFalse st' followedRest
                  (FactCheck.InScope.bind results _ (scope.mono (grows1.trans grows2).next)
                    (by simp) fun i m => by
                      have := mem_range'_bounds m
                      have := below.2.2.1
                      have := (grows1.trans grows2).next
                      omega)
                  wf2 (below.2.2.2.mono (grows1.trans grows2).next)
                  (Skel.Apart.grows (grows1.trans grows2) _ apart.2.2.2 below.2.2.2)
                exact ⟨wf3, grows1.trans (grows2.trans grows3),
                  ⟨Skel.Apart.grows (grows2.trans grows3) _ apart1 (below.1.mono grows1.next),
                    Skel.Apart.grows grows3 _ apart2 (below.2.1.mono (grows1.trans grows2).next),
                    apart.2.2.1.grows below.2.2.1 (grows1.trans (grows2.trans grows3)), apart3⟩⟩
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .cases _ _ _ _ _ arms results rest, skel, ids, st, st', followed, scope, wf, below,
        apart => by
        cases skel
        case cases mid' t' payloads' key' w' subject ok' arms' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameTy sameMid samePayloads _ _ _ _ =>
              split at followed
              · subst sameMid samePayloads
                simp only [cast_eq] at followed
                obtain ⟨afterArms, followedArms, followedRest⟩ :=
                  Option.bind_eq_some_iff.mp followed
                obtain ⟨wf1, grows1, apart1⟩ := Arms.follows_state checks arms arms' ids st
                  afterArms followedArms scope wf below.1 apart.1
                obtain ⟨wf3, grows3, apart3⟩ := Term.follows_state checks rest rest' _
                  afterArms st' followedRest
                  (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp) fun i m => by
                    have := mem_range'_bounds m
                    have := below.2.1
                    have := grows1.next
                    omega)
                  wf1 (below.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2 below.2.2)
                exact ⟨wf3, grows1.trans grows3,
                  ⟨SkelArms.Apart.grows grows3 _ apart1 (below.1.mono grows1.next),
                    apart.2.1.grows below.2.1 (grows1.trans grows3), apart3⟩⟩
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .loop _ _ _ _ _ inputs body results rest, skel, ids, st, st', followed, scope, wf,
        below, apart => by
        cases skel
        case loop carried' each' key' w' times' initial' inputs' body' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameCarried sameEach _ _ _ =>
              split at followed
              · subst sameWho sameCarried sameEach
                simp only [cast_eq] at followed
                obtain ⟨afterBody, followedBody, followedRest⟩ :=
                  Option.bind_eq_some_iff.mp followed
                obtain ⟨wf1, grows1, apart1⟩ := Term.follows_state checks body body' _ st
                  afterBody followedBody
                  (FactCheck.InScope.bind inputs _ scope (by simp) fun i m => by
                    have := mem_range'_bounds m
                    have := below.1
                    omega)
                  wf below.2.1 apart.2.1
                obtain ⟨wf3, grows3, apart3⟩ := Term.follows_state checks rest rest' _
                  afterBody st' followedRest
                  (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp) fun i m => by
                    have := mem_range'_bounds m
                    have := below.2.2.1
                    have := grows1.next
                    omega)
                  wf1 (below.2.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2.2
                      below.2.2.2)
                exact ⟨wf3, grows1.trans grows3,
                  ⟨apart.1.grows below.1 (grows1.trans grows3),
                    Skel.Apart.grows grows3 _ apart1 (below.2.1.mono grows1.next),
                    apart.2.2.1.grows below.2.2.1 (grows1.trans grows3), apart3⟩⟩
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .block _ _ body results rest, skel, ids, st, st', followed, scope, wf, below, apart =>
        by
        cases skel
        case block mid' key' number' body' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameMid _ =>
              split at followed
              · subst sameMid
                simp only [cast_eq] at followed
                obtain ⟨afterBody, followedBody, followedRest⟩ :=
                  Option.bind_eq_some_iff.mp followed
                obtain ⟨wf1, grows1, apart1⟩ := Term.follows_state checks body body' ids st
                  afterBody followedBody scope wf below.1 apart.1
                obtain ⟨wf3, grows3, apart3⟩ := Term.follows_state checks rest rest' _
                  afterBody st' followedRest
                  (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp) fun i m => by
                    have := mem_range'_bounds m
                    have := below.2.1
                    have := grows1.next
                    omega)
                  wf1 (below.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2 below.2.2)
                exact ⟨wf3, grows1.trans grows3,
                  ⟨Skel.Apart.grows grows3 _ apart1 (below.1.mono grows1.next),
                    apart.2.1.grows below.2.1 (grows1.trans grows3), apart3⟩⟩
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .attempt _ _ _ inputs body results rest, skel, ids, st, st', followed, scope, wf, below,
        apart => by
        cases skel
        case attempt mid' key' w' input' body' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameMid _ _ =>
              split at followed
              · subst sameMid
                simp only [cast_eq] at followed
                obtain ⟨afterBody, followedBody, followedRest⟩ :=
                  Option.bind_eq_some_iff.mp followed
                obtain ⟨wf1, grows1, apart1⟩ := Term.follows_state checks body body' _ st
                  afterBody followedBody
                  (FactCheck.InScope.bind inputs _ scope (by simp) fun i m => by
                    have := mem_range'_bounds m
                    have := below.1
                    omega)
                  wf below.2.1 apart.2.1
                obtain ⟨wf3, grows3, apart3⟩ := Term.follows_state checks rest rest' _
                  afterBody st' followedRest
                  (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp) fun i m => by
                    have := mem_range'_bounds m
                    have := below.2.2.1
                    have := grows1.next
                    omega)
                  wf1 (below.2.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2.2
                      below.2.2.2)
                exact ⟨wf3, grows1.trans grows3,
                  ⟨apart.1.grows below.1 (grows1.trans grows3),
                    Skel.Apart.grows grows3 _ apart1 (below.2.1.mono grows1.next),
                    apart.2.2.1.grows below.2.2.1 (grows1.trans grows3), apart3⟩⟩
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
  /-- Following the arms of a skeleton builds above the state, as following a skeleton. -/
  theorem Arms.follows_state (checks : SkelRules D) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (skel : SkelArms D mid payloads) (ids : Ctx Nat) (st st' : St D.Ty Raw),
        arms.follows rules checks skel ids st = some st' →
        FactCheck.InScope Γ ids st.next → Table.WF st.next st.table → skel.Below st.next →
        skel.Apart st.table →
        Table.WF st'.next st'.table ∧ FactCheck.St.Grows st st' ∧ skel.Apart st'.table
    | _, _, _, .nil, .nil, _, st, st', followed, _, wf, _, _ => by
        simp only [Arms.follows] at followed
        cases followed
        exact ⟨wf, .refl st, trivial⟩
    | _, _, _, .cons inputs arm rest, .cons input' arm' rest', ids, st, st', followed, scope, wf,
        below, apart => by
        simp only [Arms.follows] at followed
        obtain ⟨afterArm, followedArm, followed⟩ := Option.bind_eq_some_iff.mp followed
        obtain ⟨wf1, grows1, apart1⟩ := Term.follows_state checks arm arm' _ st afterArm
          followedArm
          (FactCheck.InScope.bind inputs _ scope (by simp) fun i m => by
            have := mem_range'_bounds m
            have := below.1
            omega)
          wf below.2.1 apart.2.1
        obtain ⟨wf2, grows2, apart2⟩ := Arms.follows_state checks rest rest' ids afterArm st'
          followed (scope.mono grows1.next) wf1 (below.2.2.mono grows1.next)
          (SkelArms.Apart.grows grows1 _ apart.2.2 below.2.2)
        exact ⟨wf2, grows1.trans grows2,
          ⟨apart.1.grows below.1 (grows1.trans grows2),
            Skel.Apart.grows grows2 _ apart1 (below.2.1.mono grows1.next), apart2⟩⟩
end

end

end Zkc.Core
