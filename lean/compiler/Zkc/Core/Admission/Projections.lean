module

public import Zkc.Core.Facts.Body.RoleChecking
public import Zkc.Core.Facts.Body.BoundsOwnership

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts
variable {V : Vocabulary} {hs : Headers V} (catalog : FunctionContracts hs.fns)
variable (hdr : ProtocolHeader V) {inputs : Names hdr.ins} (body : Prot V hs hdr inputs)

/-- Report a role failure at its original place, including the projected operation
and the precise contract clause whose proof failed. -/
def projectionRefusals (key : Key) (role : Role) :
    FactCheckError (RoleRaw V) → List (AdmissionRefusal V)
  | .definition reason =>
    let rule := match reason with
      | .contract => Rule.summary
      | .registry | .annotations => Rule.annotation
    [.projection ⟨rule, ⟨key, [], none, some role⟩, .nothing⟩]
  | .refused refusals => refusals.map fun f => .projection <| match f.concern with
    | .requirement op =>
      match ((contract catalog op).preconditions)[f.index]? with
      | some clause => ⟨.domain, f.place, .unjustifiedAssertion op clause⟩
      | none => ⟨.domain, f.place, .operation op⟩
    | .guarantee => ⟨.guarantee, f.place, .nothing⟩
    | .premise site _ => ⟨.lemmaPremise, f.place, .premise site f.index⟩
    | .invariant site _ kept => ⟨.loopInvariant, f.place, .invariant site f.index kept⟩

/-- The collected loop bounds and their origin in each checked role body. -/
structure CheckedProjections (parts : List Role) where
  bounds : List (Place × Nat)
  owned : ∀ q ∈ bounds, q.1.definition = hdr.key ∧ ∃ r ∈ parts, q.1.role = some r
  atRole : ∀ r ∈ parts, ∃ mine, checkRole catalog r hdr (project r body) = .ok mine ∧
    ∀ q ∈ bounds, q.1.role = some r → q ∈ mine

/-- Check every listed projection, retaining all role-specific errors in participant order. -/
def checkProjections : ∀ (parts : List Role), parts.Nodup →
    Except (List (Role × FactCheckError (RoleRaw V))) (CheckedProjections catalog hdr body parts)
  | [], _ => .ok ⟨[], by simp, by simp⟩
  | r :: rs, unique =>
    match current : checkRole catalog r hdr (project r body),
        checkProjections rs (List.nodup_cons.mp unique).2 with
    | .error err, .error errs => .error ((r,err) :: errs)
    | .error err, .ok _ => .error [(r,err)]
    | .ok _, .error errs => .error errs
    | .ok mine, .ok others => .ok {
        bounds := mine ++ others.bounds
        owned := by
          intro q member
          rcases List.mem_append.mp member with m | m
          · obtain ⟨d, role⟩ := checkFacts_places (config catalog r hdr.key []) [] ⟨[],[]⟩
              inputs (project r body) current q m
            exact ⟨d, r, List.mem_cons_self, role⟩
          · obtain ⟨d, j, inRest, role⟩ := others.owned q m
            exact ⟨d, j, List.mem_cons_of_mem _ inRest, role⟩
        atRole := by
          intro j member
          rcases List.mem_cons.mp member with eq | earlier
          · subst j
            refine ⟨mine, current, ?_⟩
            intro q m role
            rcases List.mem_append.mp m with belongs | belongs
            · exact belongs
            · obtain ⟨_, j, found, other⟩ := others.owned q belongs
              have same := Option.some.inj (role.symm.trans other)
              exact False.elim ((List.nodup_cons.mp unique).1 (same ▸ found))
          · obtain ⟨bs, checked, covers⟩ := others.atRole j earlier
            refine ⟨bs, checked, ?_⟩
            intro q m role
            rcases List.mem_append.mp m with belongs | belongs
            · have atHead := (checkFacts_places (config catalog r hdr.key []) [] ⟨[],[]⟩
                inputs (project r body) current q belongs).2
              have same : r = j := Option.some.inj (atHead.symm.trans role)
              exact False.elim ((List.nodup_cons.mp unique).1 (same ▸ earlier))
            · exact covers q belongs role }

theorem distinctParticipants : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨distinctParticipants n, by simp, ?_⟩
    intro i earlier j last same
    have jn := List.mem_singleton.mp last
    exact (Nat.ne_of_lt (List.mem_range.mp earlier)) (same.trans jn)

/-- The executable check covers exactly the participant numbers declared by the header. -/
def checkDeclared := checkProjections catalog hdr body (List.range hdr.roles) (distinctParticipants hdr.roles)

end Zkc.Core.BodyAnalysis.RoleContracts
