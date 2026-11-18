module

public import Zkc.Frontend.Semantics.VocabularyTable

@[expose] public section

namespace Zkc.Frontend.StandardNames

open Zkc.Vocabulary (Field CurveGroup TypeKey)

def fieldOf? : ClosedType → Option Field
  | .nominal row #[] => fields.find? (fun f => fieldName f == row)
  | _ => none

def groupOf? : ClosedType → Option CurveGroup
  | .nominal row #[] => groups.find? (fun g => groupName g == row)
  | _ => none

/-- The project-independent types that the standard vocabulary can supply directly. -/
partial def typeOf? : ClosedType → Option Zkc.Vocabulary.Ty
  | .bool => some .bool
  | .nat => some .nat
  | .index bound => some (.fin bound)
  | .nonzero t => (fieldOf? t).map (·.units)
  | .seq t size => return .seq (← typeOf? t) size
  | .tuple ts _ => return .tuple ((← ts.toList.mapM typeOf?).foldr .cons .nil)
  | t => (fieldOf? t).map (·.ty) <|> (groupOf? t).map (·.ty)

mutual
  /-- Read a signature built entirely from standard types. A project must resolve the
  keys of records and variants in its own declaration table. -/
  def closed? : Zkc.Vocabulary.Ty → Option ClosedType
    | .bool => some .bool
    | .nat => some .nat
    | .fin n => some (.index n)
    | .seq t n => return .seq (← closed? t) n
    | .tuple ts => do
      let fields := (← closedFields? ts).toArray
      return .tuple fields (fields.map fun _ => none)
    | .record .. | .variant .. => none
    | .nominal (.field f) => some (fieldType f)
    | .nominal (.nonzero f) => some (.nonzero (fieldType f))
    | .nominal (.group g) => some (groupType g)
  def closedFields? : Core.Tys TypeKey → Option (List ClosedType)
    | .nil => some []
    | .cons t ts => return (← closed? t) :: (← closedFields? ts)
end

end Zkc.Frontend.StandardNames
