module

public import Zkc.Core.Facts.Knowledge.Carried
public import Zkc.Core.Facts.Knowledge.Decisions
public import Zkc.Core.Facts.Domains.Product

@[expose] public section

namespace Zkc.Core.BodyAnalysis.Knowledge

/-- Every operation of the executable knowledge domain respects the same fact interpretation. -/
def lawful {T Raw Val : Type} {types : KnowledgeTypes T} {ops : KnowledgeOperations Raw}
    {Run : Raw → List Val → List Val → Prop} {R : Reading Val} {Typed : Val → T → Prop}
    (observations : ops.Lawful R Run) (typing : types.Lawful R Typed) :
    (domain types ops).Lawful Run R Typed where
  Means := Means Run R
  mono := mono
  init _ _ := empty
  dead killed h := by
    obtain ⟨_, _, facts⟩ := h
    exact Bool.noConfusion (facts.alive.symm.trans killed)
  answers := answers_sound
  leaves slots h reads := leaves_sound typing observations.functional slots _ h reads
  transfer slots peer h := transfer_sound observations slots h peer
  observe slots peer h src dst same := by
    have ranged := addRange_sound observations.functional slots h dst (fun r found => by
      rw [← same.number]
      exact rangeFor_sound observations.functional slots peer h src found)
    simp only [observe]
    split
    · rename_i b found
      exact assume_sound observations.functional slots peer ranged dst
        (same.truth ▸ decideTruth_sound observations slots peer h src found)
    · exact ranged
  assume slots peer h read val := learnTruth_sound observations slots peer _ h read val
  truth slots peer h read found := decideTruth_sound observations slots peer h read found
  after slots prior member last peer result := by
    obtain ⟨_, out, made⟩ := result
    exact after_sound observations.functional slots prior member last peer out made
  enter slots := enter_sound observations.functional slots typing
  afterLoop slots := afterLoop_sound observations slots

#print axioms lawful
end Zkc.Core.BodyAnalysis.Knowledge
