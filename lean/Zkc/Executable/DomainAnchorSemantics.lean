module

public import Zkc.Executable.DomainTermSemantics
public import Zkc.Executable.DomainMotion

@[expose] public section

/-! Locality of actual canonical anchors. Failed metadata and helper invocation
remain failures, and all effects stay in order. -/
set_option autoImplicit false
namespace Zkc.Executable.CanonicalNormalization
open Zkc.Construction Zkc.Source
variable {F G : Type}
theorem read_range' (env : List (Value F G)) :
    ∀ (values : List (Value F G)),
      (List.range' env.length values.length).mapM (fun reference => (env ++ values)[reference]?) =
        some values
  | [] => rfl
  | value :: values => by
      simp only [List.length_cons, List.range'_succ, List.mapM_cons]
      have tail := read_range' (env ++ [value]) values
      simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.singleton_append] at tail
      rw [tail]
      simp

theorem value_at {env : List (Value F G)} {references : List Nat} {values : List (Value F G)}
    (found : references.mapM (fun reference => env[reference]?) = some values)
    {position reference : Nat} (entry : references[position]? = some reference) :
    values[position]? = env[reference]? := by
  induction references generalizing values position with
  | nil => simp at entry
  | cons head tail ih =>
      simp only [List.mapM_cons] at found
      cases first : env[head]? with
      | none => simp [first] at found
      | some value =>
          cases others : tail.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              cases position with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at entry
                  subst entry
                  simp [first]
              | succ position =>
                  simp only [List.getElem?_cons_succ] at entry ⊢
                  exact ih others entry

theorem length_of_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.length = ys.length
  | [], ys, found => by
      change some [] = some ys at found
      cases found
      rfl
  | x :: xs, ys, found => by
      simp only [List.mapM_cons] at found
      cases first : f x with
      | none => simp [first] at found
      | some y =>
          cases others : xs.mapM f with
          | none => simp [first, others] at found
          | some zs =>
              simp [first, others] at found
              subst found
              simp [length_of_mapM_some others]


theorem read_positions (arguments : List (Value F G)) :
    Domain.read arguments (List.range' 0 arguments.length) = some arguments := by
  simpa [Domain.read] using read_range' ([] : List (Value F G)) arguments

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem step_local (program : Structured.Program) (context : Context)
    {R : Type} {operation : Operation} {operands : List Nat} {results : List ValueSort}
    {env arguments : List (Value F G)}
    (next : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R)
    (notLoop : ∀ site maximum yielded, operation ≠ .loop site maximum yielded)
    (notLocal : ∀ port request template coordinates,
      operation ≠ .localService port request template coordinates)
    (found : Domain.read env operands = some arguments) :
    (Domain.step (Structured.ringModel F G) program context ⟨operation, operands, results, []⟩ env).bind next =
      (Domain.step (Structured.ringModel F G) program context
        ⟨operation, List.range' 0 arguments.length, results, []⟩ arguments).bind
        (fun final => next (env ++ final.drop arguments.length)) := by
  have lengths : operands.length = arguments.length := length_of_mapM_some found
  have values : ∀ position reference, operands[position]? = some reference →
      env[reference]? = arguments[position]? := fun position reference entry =>
    (value_at found entry).symm
  cases operation with
  | loop site maximum yielded => exact absurd rfl (notLoop site maximum yielded)
  | localService port request template coordinates => exact absurd rfl (notLocal port request template coordinates)
  | calculate calculation =>
      simp only [Domain.step, found, read_positions]
      repeat' first
        | (solve | simp_all [PIR.Process.bind])
        | (split <;> try simp_all)
  | call name =>
      simp only [Domain.step, found, read_positions]
      repeat' first
        | (solve | simp_all [PIR.Process.bind])
        | (split <;> try simp_all)
  | _ =>
      rcases operands with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        rcases arguments with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, more⟩⟩⟩⟩ <;>
        (try simp at lengths)
      all_goals try have va : env[a]? = some x := by simpa using values 0 a rfl
      all_goals try have vb : env[b]? = some y := by simpa using values 1 b rfl
      all_goals try have vc : env[c]? = some z := by simpa using values 2 c rfl
      all_goals
        simp only [Domain.step, List.length_nil, List.length_cons, List.range'_succ, List.range'_zero,
          Nat.zero_add, Nat.reduceAdd, List.getElem?_cons_zero, List.getElem?_cons_succ]
      all_goals try rw [va]
      all_goals try rw [vb]
      all_goals try rw [vc]
      all_goals
        repeat' first
          | (solve | rfl | simp_all)
          | (split <;> try simp_all [PIR.Process.bind])
          | (funext reply)


end Zkc.Executable.CanonicalNormalization
