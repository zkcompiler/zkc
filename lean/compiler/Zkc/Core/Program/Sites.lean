module

public import Zkc.Core.Program.Identity

@[expose] public section

/-!
The site of an occurrence in a run that starts somewhere.

An occurrence is a path of frames and a key; a site is the keys of the applications on the way
and the key, and stands for every occurrence under the iterations and attempts between. A run
of a definition starts at a path that its caller chose. What a table of a root says of a site
is said of the occurrences below the start of the root's run: `Occurrence.siteBelow start` is
the site of an occurrence among those, the applications entered after `start` and the key, and
nothing for an occurrence that is not below `start`.
-/

namespace Zkc.Core

/-- What is left of a path after a prefix, when it has the prefix. -/
def Frame.after : List Frame → List Frame → Option (List Frame)
  | [], rest => some rest
  | frame :: start, next :: path => if frame = next then Frame.after start path else none
  | _ :: _, [] => none

/-- What is left after a prefix of a path that is written as the prefix and a rest is the
rest. -/
theorem Frame.after_append : ∀ (start rest : List Frame),
    Frame.after start (start ++ rest) = some rest
  | [], _ => rfl
  | frame :: start, rest => by
    simp only [List.cons_append, Frame.after, ite_true]
    exact Frame.after_append start rest

/-- A path with something left after a prefix is the prefix and what is left. -/
theorem Frame.eq_of_after : ∀ {start path rest : List Frame},
    Frame.after start path = some rest → path = start ++ rest
  | [], _, _, left => by
    simp only [Frame.after, Option.some.injEq] at left
    simp [left]
  | _ :: _, [], _, left => by simp [Frame.after] at left
  | frame :: start, next :: path, rest, left => by
    simp only [Frame.after] at left
    split at left
    · rename_i same
      subst same
      simp [Frame.eq_of_after left]
    · simp at left

/-- The applications of a path in two parts are those of the first, then those of the
second. -/
theorem Frame.applications_append : ∀ (first second : List Frame),
    Frame.applications (first ++ second) = Frame.applications first ++ Frame.applications second
  | [], _ => rfl
  | .application _ :: rest, second => by
    simp [Frame.applications, Frame.applications_append rest second]
  | .iteration _ _ :: rest, second => by
    simp [Frame.applications, Frame.applications_append rest second]
  | .attempt _ _ :: rest, second => by
    simp [Frame.applications, Frame.applications_append rest second]

/-- The site of an occurrence in a run that starts at `start`: the applications entered after
`start`, and the key. None for an occurrence that is not below `start`. -/
def Occurrence.siteBelow (start : List Frame) (at_ : Occurrence) : Option Site :=
  (Frame.after start at_.path).map fun rest => ⟨Frame.applications rest, at_.key⟩

/-- **The site below a start.** An occurrence at the start's path and a rest has, below the
start, the applications of the rest and its key: at the root's own instructions no application,
under iterations and attempts no application either, and under an application its key in
front. -/
theorem Occurrence.siteBelow_append (start rest : List Frame) (key : Key) :
    Occurrence.siteBelow start ⟨start ++ rest, key⟩ = some ⟨Frame.applications rest, key⟩ := by
  simp [Occurrence.siteBelow, Frame.after_append]

/-- An occurrence below an application of `key` at `start` has, below `start`, the site with
`key` in front: the table of a caller, read at the key of an application, is a table of the
callee's sites. -/
theorem Occurrence.siteBelow_application {start : List Frame} {key : Key} {at_ : Occurrence}
    {site : Site} (below : Occurrence.siteBelow (start ++ [.application key]) at_ = some site) :
    Occurrence.siteBelow start at_ = some ⟨key :: site.through, site.key⟩ := by
  unfold Occurrence.siteBelow at below ⊢
  obtain ⟨rest, left, rfl⟩ := Option.map_eq_some_iff.mp below
  rw [Frame.eq_of_after left, List.append_assoc, Frame.after_append]
  simp [Frame.applications]

end Zkc.Core
