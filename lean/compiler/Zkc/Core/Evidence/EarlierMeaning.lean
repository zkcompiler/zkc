module

public import Zkc.Core.Evidence.ProtocolReadback
public import Zkc.Core.Evidence.FunctionEntry

@[expose] public section

/-!
A definition has one meaning, whichever definition applies it.

The meaning of a definition is read over the tables of the definitions before it
(`ProtocolEntry`, `FunctionEntry`), so a protocol that two others apply is named by them in two
lists of earlier definitions. A definition among those before an entry is a definition of the
whole program (`Defs.protocolBefore`, `Defs.functionBefore`, `Defs.functionBeforeFunction`), and
its process in the earlier tables is its process in the whole program's
(`Defs.rTable_protocolBefore`, `Defs.fnTable_functionBefore`,
`Defs.fnTable_functionBeforeFunction`). So a statement about a callee is made once, about the
program's own member, and is used wherever the callee is applied.
-/

namespace Zkc.Core
variable {V : Vocabulary}

/-- A protocol among the definitions before a protocol, as a protocol of the whole. -/
def Defs.protocolBefore : {hs : Headers V} → (defs : Defs V hs) → (distinct : hs.keys.Nodup) →
    {h : ProtocolHeader V} → (ref : Member hs.protocols h) → {callee : ProtocolHeader V} →
    Member (defs.protocolEntry distinct ref).earlier.protocols callee → Member hs.protocols callee
  | _, .nil, _, _, ref, _, _ => nomatch ref
  | _, .fn _ _ _ _ ds _, distinct, _, ref, _, m =>
    ds.protocolBefore (List.nodup_cons.mp distinct).2 ref m
  | _, .protocol _ _ _ _ _, _, _, .head, _, m => .tail m
  | _, .protocol _ _ _ _ ds, distinct, _, .tail ref, _, m =>
    .tail (ds.protocolBefore (Headers.earlierProtocolKeys distinct) ref m)

/-- A function among the definitions before a protocol, as a function of the whole. -/
def Defs.functionBefore : {hs : Headers V} → (defs : Defs V hs) → (distinct : hs.keys.Nodup) →
    {h : ProtocolHeader V} → (ref : Member hs.protocols h) → {callee : FnHeader V} →
    Member (defs.protocolEntry distinct ref).earlier.fns callee → Member hs.fns callee
  | _, .nil, _, _, ref, _, _ => nomatch ref
  | _, .fn _ _ _ _ ds _, distinct, _, ref, _, m =>
    .tail (ds.functionBefore (List.nodup_cons.mp distinct).2 ref m)
  | _, .protocol _ _ _ _ _, _, _, .head, _, m => m
  | _, .protocol _ _ _ _ ds, distinct, _, .tail ref, _, m =>
    ds.functionBefore (Headers.earlierProtocolKeys distinct) ref m

/-- A function among the definitions before a function, as a function of the whole. -/
def Defs.functionBeforeFunction : {hs : Headers V} → (defs : Defs V hs) →
    (unique : (hs.fns.map (·.key)).Nodup) → {h : FnHeader V} → (ref : Member hs.fns h) →
    {callee : FnHeader V} →
    Member (defs.functionEntry unique ref).earlier.fns callee → Member hs.fns callee
  | _, .nil, _, _, ref, _, _ => nomatch ref
  | _, .protocol _ _ _ _ ds, unique, _, ref, _, m => ds.functionBeforeFunction unique ref m
  | _, .fn _ _ _ _ _ _, _, _, .head, _, m => .tail m
  | _, .fn _ _ _ _ ds _, unique, _, .tail ref, _, m =>
    .tail (ds.functionBeforeFunction (List.nodup_cons.mp unique).2 ref m)

variable (M : Model V)

/-- **A protocol that a protocol applies has its process in the whole program.** -/
theorem Defs.rTable_protocolBefore : {hs : Headers V} → (defs : Defs V hs) →
    (distinct : hs.keys.Nodup) → {h : ProtocolHeader V} → (ref : Member hs.protocols h) →
    {callee : ProtocolHeader V} →
    (m : Member (defs.protocolEntry distinct ref).earlier.protocols callee) →
    Defs.rTable M defs _ (defs.protocolBefore distinct ref m) =
      Defs.rTable M (defs.protocolEntry distinct ref).definitions _ m
  | _, .nil, _, _, ref, _, _ => nomatch ref
  | _, .fn _ _ _ _ ds _, distinct, _, ref, _, m =>
    ds.rTable_protocolBefore (List.nodup_cons.mp distinct).2 ref m
  | _, .protocol _ _ _ _ _, _, _, .head, _, _ => rfl
  | _, .protocol _ _ _ _ ds, distinct, _, .tail ref, _, m =>
    ds.rTable_protocolBefore (Headers.earlierProtocolKeys distinct) ref m

/-- **A function that a protocol calls has its process in the whole program.** -/
theorem Defs.fnTable_functionBefore : {hs : Headers V} → (defs : Defs V hs) →
    (distinct : hs.keys.Nodup) → {h : ProtocolHeader V} → (ref : Member hs.protocols h) →
    {callee : FnHeader V} → (m : Member (defs.protocolEntry distinct ref).earlier.fns callee) →
    Defs.fnTable M defs _ (defs.functionBefore distinct ref m) =
      Defs.fnTable M (defs.protocolEntry distinct ref).definitions _ m
  | _, .nil, _, _, ref, _, _ => nomatch ref
  | _, .fn _ _ _ _ ds _, distinct, _, ref, _, m =>
    ds.fnTable_functionBefore (List.nodup_cons.mp distinct).2 ref m
  | _, .protocol _ _ _ _ _, _, _, .head, _, _ => rfl
  | _, .protocol _ _ _ _ ds, distinct, _, .tail ref, _, m =>
    ds.fnTable_functionBefore (Headers.earlierProtocolKeys distinct) ref m

/-- **A function that a function calls has its process in the whole program.** -/
theorem Defs.fnTable_functionBeforeFunction : {hs : Headers V} → (defs : Defs V hs) →
    (unique : (hs.fns.map (·.key)).Nodup) → {h : FnHeader V} → (ref : Member hs.fns h) →
    {callee : FnHeader V} → (m : Member (defs.functionEntry unique ref).earlier.fns callee) →
    Defs.fnTable M defs _ (defs.functionBeforeFunction unique ref m) =
      Defs.fnTable M (defs.functionEntry unique ref).definitions _ m
  | _, .nil, _, _, ref, _, _ => nomatch ref
  | _, .protocol _ _ _ _ ds, unique, _, ref, _, m => ds.fnTable_functionBeforeFunction unique ref m
  | _, .fn _ _ _ _ _ _, _, _, .head, _, _ => rfl
  | _, .fn _ _ _ _ ds _, unique, _, .tail ref, _, m =>
    ds.fnTable_functionBeforeFunction (List.nodup_cons.mp unique).2 ref m

end Zkc.Core
