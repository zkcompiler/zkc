import Zkc.Core.Facts.Knowledge.Functions

namespace Zkc.Core.BodyAnalysis.Knowledge
open FactCheck (Known)
variable {V : Vocabulary}

private abbrev localDomain (V : Vocabulary) := domain (localKnowledgeTypes V) (KnowledgeOperations.ofFacts (localOpFacts (V := V) []))
private def table (V : Vocabulary) : Table (LocalRaw V) := Table.empty (fun _ => 0)
private def loop (V : Vocabulary) (count : Nat ⊕ Ident) (numbered := true) : Loop V.Ty where
  count := count
  numbered := numbered
  index := .leaf 1
  indexType := .nat
  initial := [.leaf 0]
  carried := [.leaf 2]
  types := [.nat]
private def entry (args : List Ident) : Entry (LocalRaw V) := ⟨.app (.owned .natAdd [] []) args, 3, 1⟩
private def knownAt (id : Ident) (n : Nat) := Known.empty.addRange id.key (Range.point n)

example : ((localDomain V).transfer .nobody (table V) Known.empty
    ⟨.app (.literal .nat [11]) [], 3, 0⟩).rangeOf (Ident.val 3).key = none := by rfl'

example : ((localDomain V).answers ((localDomain V).transfer .nobody (table V) Known.empty
    ⟨.app (.literal .nat [11]) [], 3, 1⟩)).exact (.val 3) = some 11 := by rfl'

example : (after Known.empty [(.nobody, knownAt (.leaf 4) 7, [.leaf 4]),
    (.nobody, knownAt (.leaf 5) 2, [.leaf 5])] [.val 0]).rangeOf (Ident.val 0).key =
    some ⟨2, some 7⟩ := by rfl'

example : (after Known.empty [(.nobody, knownAt (.leaf 4) 7, [.leaf 4]),
    (.nobody, Known.empty, [.leaf 5])] [.val 0]).rangeOf (Ident.val 0).key = none := by rfl'

example : (after Known.empty [] []).dead = true := by rfl'

example : ((localDomain V).enter .nobody (table V) Known.empty (loop V (.inl 0))).dead = true := by rfl'

example : ((localDomain V).enter .nobody (table V) Known.empty (loop V (.inl 3))).rangeOf
    (Ident.leaf 1).key = some ⟨0, some 2⟩ := by rfl'

example : ((localDomain V).enter .nobody (table V) Known.empty (loop V (.inl 3) false)).rangeOf
    (Ident.leaf 1).key = some ⟨0, none⟩ := by rfl'

/-- Transfer intersects the full source interval with the destination type range.
The second domain also sees the upper bound supplied by its peer. -/
example :
    let d := localDomain V
    let src := Ident.val 0
    let dst := Ident.leaf 0
    let left := (Known.empty.addRange src.key ⟨2, some 7⟩).addRange dst.key ⟨0, some 5⟩
    let pair := (d.prod d).observe .nobody (table V) (left, Known.empty) src dst
    (pair.1.rangeOf dst.key, pair.2.rangeOf dst.key, pair.1.rangeOf src.key) =
      (some ⟨2, some 5⟩, some ⟨0, some 7⟩, some ⟨2, some 7⟩) := by rfl'

example :
    let d := localDomain V
    let src := Ident.leaf 3
    let dst := Ident.leaf 4
    let pair := (d.prod d).observe .nobody (table V)
      (Known.empty, Known.empty.addTruth src.key false) src dst
    ((d.answers pair.1).truth dst, (d.answers pair.2).truth dst) = (some false, some false) := by
  rfl'

private def loopRange (V : Vocabulary) (count : Nat ⊕ Ident) (args : List Ident) (out : Known) :=
  ((localDomain V).afterLoop .nobody .nobody ((table V).add (entry args))
    (knownAt (.leaf 0) 2) (loop V count) out [.val 3] [.leaf 7]).rangeOf (Ident.leaf 7).key

example : loopRange V (.inl 3) [.leaf 2, .leaf 4] (knownAt (.leaf 4) 5) =
    some ⟨2, some 17⟩ := by rfl'
example : loopRange V (.inl 3) [.leaf 4, .leaf 2] (knownAt (.leaf 4) 5) =
    some ⟨2, some 17⟩ := by rfl'
example : loopRange V (.inl 3) [.leaf 5, .leaf 4] (knownAt (.leaf 4) 5) = none := by rfl'
example : loopRange V (.inl 0) [] Known.empty = some (Range.point 2) := by rfl'
example : loopRange V (.inr (.leaf 8)) [] Known.empty.kill = some (Range.point 2) := by rfl'

private def decisionTable (V : Vocabulary) :=
  let t := (table V).add ⟨.app (.owned .natLess [] []) [.leaf 0, .leaf 1], 0, 1⟩
  let t := t.add ⟨.app (.literal .bool [0]) [], 1, 1⟩
  let t := t.add ⟨.select (.leaf 3) (.val 0) (.val 1), 2, 1⟩
  let t := t.add ⟨.app (.owned .boolNot [] []) [.val 0], 3, 1⟩
  let t := t.add ⟨.app (.owned .boolOr [] []) [.val 0, .leaf 4], 4, 1⟩
  let t := t.add ⟨.app (.owned .boolAnd [] []) [.val 3, .leaf 5], 5, 1⟩
  t.add ⟨.app (.owned .natEqual [] []) [.leaf 0, .leaf 1], 6, 1⟩

private def chosen (V : Vocabulary) := (localDomain V).assume .nobody (decisionTable V)
  (knownAt (.leaf 1) 4) (.val 2) true

-- A true lazy conjunction selects its first arm and establishes its inner comparison.
example : ((localDomain V).answers (chosen V)).truth (.leaf 3) = some true := by rfl'
example : (chosen V).rangeOf (Ident.leaf 0).key = some ⟨0, some 3⟩ := by rfl'
-- A false result can come from either arm, so it does not determine the condition.
example : ((localDomain V).answers ((localDomain V).assume .nobody (decisionTable V)
    Known.empty (.val 2) false)).truth (.leaf 3) = none := by rfl'
-- A false disjunction pushes back into both operands, including the reversed non-strict order.
example : ((localDomain V).assume .nobody (decisionTable V) (knownAt (.leaf 0) 2)
    (.val 4) false).rangeOf (Ident.leaf 1).key = some ⟨0, some 2⟩ := by rfl'

private def numerals := (knownAt (.leaf 0) 2).addRange (Ident.leaf 1).key (Range.point 4)
example : (localDomain V).truth .nobody (decisionTable V) numerals (.val 0) = some true := by rfl'
example : (localDomain V).truth .nobody (decisionTable V) numerals (.val 3) = some false := by rfl'
example : (localDomain V).truth .nobody (decisionTable V) numerals (.val 4) = some true := by rfl'
example : (localDomain V).truth .nobody (decisionTable V) numerals (.val 5) = some false := by rfl'
example : (localDomain V).truth .nobody (decisionTable V) numerals (.val 6) = some false := by rfl'
example : (localDomain V).truth .nobody (decisionTable V)
    ((knownAt (.leaf 0) 4).addRange (Ident.leaf 1).key (Range.point 4)) (.val 6) = some true := by rfl'
example : (localDomain V).truth .nobody (decisionTable V) Known.empty (.val 3) = none := by rfl'
example : (localDomain V).truth .nobody (decisionTable V)
    (Known.empty.addTruth (Ident.leaf 3).key false) (.val 2) = some false := by rfl'
example : (localDomain V).truth { Asks.nobody with exact := fun _ => some 1 }
    (decisionTable V) Known.empty (.val 6) = some true := by rfl'

private def offsetTable (V : Vocabulary) :=
  let t := (table V).add ⟨.app (.owned .natSub [] []) [.leaf 8, .leaf 1], 0, 1⟩
  let t := t.add ⟨.app (.owned .natAdd [] []) [.leaf 1, .leaf 2], 1, 1⟩
  let t := t.add ⟨.app (.owned .natLess [] []) [.val 1, .leaf 8], 2, 1⟩
  let t := t.add ⟨.app (.owned .natLess [] []) [.val 0, .leaf 8], 3, 1⟩
  let t := t.add ⟨.app (.owned .natLess [] []) [.leaf 2, .val 1], 4, 1⟩
  let t := t.add ⟨.app (.owned .natAdd [] []) [.leaf 7, .leaf 2], 5, 1⟩
  t.add ⟨.app (.owned .natEqual [] []) [.val 1, .val 5], 6, 1⟩

private def offsetState (byLoop : Bool) := (knownAt (.leaf 8) 12).addOrder
  (Ident.leaf 2).key (Ident.val 0).key true byLoop

-- The loop tag distinguishes a ranged index from a fact learned by an ordinary branch.
example : (localDomain V).truth .nobody (offsetTable V) (offsetState true) (.val 2) = some true := by rfl'
example : (localDomain V).truth .nobody (offsetTable V) (offsetState false) (.val 2) = none := by rfl'
example : ((localDomain V).transfer .nobody (offsetTable V) (offsetState true)
    ⟨.app (.owned .natAdd [] []) [.leaf 1, .leaf 2], 1, 1⟩).rangeOf (Ident.val 1).key =
    some ⟨0, some 11⟩ := by rfl'
example : ((localDomain V).transfer .nobody (offsetTable V) (offsetState false)
    ⟨.app (.owned .natAdd [] []) [.leaf 1, .leaf 2], 1, 1⟩).rangeOf (Ident.val 1).key = none := by rfl'

example : (localDomain V).truth .nobody (offsetTable V) (knownAt (.leaf 1) 3) (.val 3) = some true := by rfl'
example : (localDomain V).truth .nobody (offsetTable V) (knownAt (.leaf 1) 3) (.val 4) = some true := by rfl'
example : (localDomain V).truth .nobody (offsetTable V) Known.empty (.val 3) = none := by rfl'
example : (localDomain V).truth .nobody (offsetTable V)
    ((knownAt (.leaf 1) 3).addRange (Ident.leaf 7).key (Range.point 3)) (.val 6) = some true := by rfl'
example : (localDomain V).truth .nobody (offsetTable V) (knownAt (.leaf 1) 3) (.val 6) = none := by rfl'

end Zkc.Core.BodyAnalysis.Knowledge
