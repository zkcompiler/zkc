module

public import Zkc.Core.Facts.Body.Roles
public import Zkc.Core.Facts.Knowledge.Inference
public import Zkc.Core.Facts.Body.Skeleton
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Meaning.Role

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {V : Vocabulary}

theorem localKnowledgeTypes_lawful (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns) :
    (localKnowledgeTypes V).Lawful (localReading M) (TypedValue (localSem M fns table) (ValidDyn M)) where
  range := by
    intro t value range typed found
    obtain ⟨u, v⟩ := value
    obtain ⟨valid, rfl⟩ := typed
    exact FactCheck.localRange_has (M := M) found v valid
  inhabited := by
    intro t value typed
    obtain ⟨u, v⟩ := value
    obtain ⟨valid, rfl⟩ := typed
    exact Ty.noValue_of_valid u v valid

/-- Expose a local reading exactly where the role can reveal the value. -/
def heldValue (M : Model V) (r : Role) (v : (a : LTy V) × RV M r a) :
    Option ((t : V.Ty) × M.Val t) :=
  if held : r ∈ v.1.holders then some ⟨v.1.ty, reveal M held v.2⟩ else none

def roleReading (M : Model V) (r : Role) : Reading ((a : LTy V) × RV M r a) where
  nat v := (heldValue M r v).bind (localReading M).nat
  bool v := (heldValue M r v).bind (localReading M).bool

abbrev RoleValueValid (M : Model V) (r : Role) (v : (a : LTy V) × RV M r a) : Prop :=
  RV.Valid M r v.1 v.2

theorem roleKnowledgeTypes_lawful (M : Model V) (r : Role) {hs : Headers V}
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) :
    (roleKnowledgeTypes V r).Lawful (roleReading M r)
      (TypedValue (roleSem M r fns roles) (RoleValueValid M r)) where
  range := by
    intro t value range typed found
    obtain ⟨u, v⟩ := value
    obtain ⟨valid, rfl⟩ := typed
    by_cases held : r ∈ u.holders
    · have h : localRange u.ty = some range := by simpa [roleKnowledgeTypes, held] using found
      obtain ⟨n, val, fit⟩ := FactCheck.localRange_has (M := M) h (reveal M held v) (valid held)
      exact ⟨n, by simpa [roleReading, heldValue, held] using val, fit⟩
    · simp [roleKnowledgeTypes, held] at found
  inhabited := by
    intro t value typed
    obtain ⟨u, v⟩ := value
    obtain ⟨valid, rfl⟩ := typed
    by_cases held : r ∈ u.holders
    · simp [roleKnowledgeTypes, held, Ty.noValue_of_valid u.ty (reveal M held v) (valid held)]
    · simp [roleKnowledgeTypes, held]

/-- The role evaluator and selection reads agree at all legal conditions, including invalid inputs. -/
theorem roleConditionsRead (M : Model V) (r : Role) {hs : Headers V} (fns : FnTable M hs.fns)
    (roles : RTable M hs.protocols) : ConditionsRead (roleSem M r fns roles) (roleReading M r) := by
  intro w t ok v
  obtain ⟨ty, holders⟩ := t
  obtain ⟨eq, held, _⟩ := ok
  cases eq
  simp [roleReading, heldValue, held, localReading, asBool, roleSem]

example : (roleKnowledgeTypes V 0).empty ⟨.fin 0, [1]⟩ = false := rfl
example : (roleKnowledgeTypes V 0).empty ⟨.fin 0, [0]⟩ = true := rfl
example : (roleKnowledgeTypes V 0).range ⟨.nat, [1]⟩ = none := rfl

#print axioms roleKnowledgeTypes_lawful
#print axioms roleConditionsRead
end Zkc.Core.BodyAnalysis
