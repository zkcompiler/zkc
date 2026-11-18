module

public import Zkc.Core.Program.Project

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : Headers V} (r : Role) (blocks : List (Key × Nat))

private theorem projectOp_addresses {Γ : Ctx (LTy V)} {ins mid outs : List (LTy V)}
    (key : Key) (op : ProtocolOp V hs ins mid) (args : HList (Var Γ) ins) (names : Names mid)
    (rest : Term (roleDialect V hs r) (Γ.extend names) outs) :
    (op.project r key args names rest).addresses blocks = (blocks,key) :: rest.addresses blocks := by
  cases op <;> simp only [ProtocolOp.project] <;> repeat' split
  all_goals rfl

private theorem projectLoop_addresses {Γ : Ctx (LTy V)} {outs carried each : List (LTy V)}
    (key : Key) (who : Holders) (here : r ∈ who) (times : Times (protocolDialect V hs) who Γ)
    (init : HList (Var Γ) carried) (names : Names (LTy.index who :: carried))
    (body : Term (roleDialect V hs r) (Γ.extend names) (carried ++ each))
    (results : Names (carried ++ each.map (LTy.collected times.size)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs) :
    (projectLoop r key who here times init names body results rest).addresses blocks =
      (blocks,key) :: (body.addresses blocks ++ rest.addresses blocks) := by
  cases times <;> rfl

mutual
  /-- A role visits a subsequence of the protocol's static addresses, in the same block scopes. -/
  theorem projectedAddresses (blocks : List (Key × Nat)) : ∀ {Γ outs} (body : Term (protocolDialect V hs) Γ outs),
      ((project r body).addresses blocks).Sublist (body.addresses blocks)
    | _, _, .ret _ => .slnil
    | _, _, .op _ _ _ _ rest => by
      rw [project, projectOp_addresses, Term.addresses]
      exact (projectedAddresses blocks rest).cons_cons _
    | _, _, .guard _ _ _ _ _ rest => by
      rw [project]
      split
      · exact (projectedAddresses blocks rest).cons_cons _
      · exact (projectedAddresses blocks rest).cons _
    | _, _, .choose _ _ _ _ _ first second _ rest => by
      rw [project, Term.addresses]
      split
      · exact (((projectedAddresses blocks first).append (projectedAddresses blocks second)).append
          (projectedAddresses blocks rest)).cons_cons _
      · exact (List.sublist_append_of_sublist_right (projectedAddresses blocks rest)).cons_cons _
    | _, _, .cases _ _ _ _ _ arms _ rest => by
      rw [project, Term.addresses]
      split
      · exact ((projectedArmAddresses blocks arms).append (projectedAddresses blocks rest)).cons_cons _
      · exact (List.sublist_append_of_sublist_right (projectedAddresses blocks rest)).cons_cons _
    | _, _, .loop _ _ _ _ _ _ body _ rest => by
      rw [project, Term.addresses]
      split
      · rw [projectLoop_addresses]
        exact ((projectedAddresses blocks body).append (projectedAddresses blocks rest)).cons_cons _
      · exact (List.sublist_append_of_sublist_right (projectedAddresses blocks rest)).cons_cons _
    | _, _, .block key n body _ rest =>
      (projectedAddresses (blocks ++ [(key,n)]) body).append (projectedAddresses blocks rest)
    | _, _, .attempt _ _ _ _ body _ rest =>
      ((projectedAddresses blocks body).append (projectedAddresses blocks rest)).cons_cons _
  theorem projectedArmAddresses (blocks : List (Key × Nat)) : ∀ {Γ outs payloads} (arms : Arms (protocolDialect V hs) Γ outs payloads),
      ((projectArms r arms).addresses blocks).Sublist (arms.addresses blocks)
    | _, _, _, .nil => .slnil
    | _, _, _, .cons _ arm rest => (projectedAddresses blocks arm).append (projectedArmAddresses blocks rest)
end

/-- The protocol elaborator's uniqueness check supplies the address hypothesis for every role. -/
theorem projectedAddresses_nodup {Γ outs} (body : Term (protocolDialect V hs) Γ outs)
    (ok : body.Distinct) : ((project r body).addresses []).Nodup := by
  simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact (projectedAddresses r [] body).nodup ok.1

#print axioms projectedAddresses_nodup
end Zkc.Core.BodyAnalysis
