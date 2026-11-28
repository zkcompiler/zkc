import ZkcFormal.Written.Views

/-!
A check's entry to the naming of views on a proposition that `publish_views` does not state: an
author's own lemma, a wrapper of the caller's, a telescope with another continuation. The
library declares views only by `publish_views`; these elaborators call the same functions
(`ZkcFormal.Written.Views.viewOf`, and `namedOf`, naming without presenting).

* `view% S P`: the view of `P` over the subject `S`, named and presented;
* `named_view% S P`: `P` named after the origins of `S`, not presented;
* `declare_view S b : P`: `def b.view : Prop := view% S P` and `theorem b.view_iff`, through
  Lean's own elaboration of a definition (which moves a proof inside the value into an auxiliary
  constant).
-/

open Lean Meta Elab Term Command

namespace ZkcFormalTests.ViewEntry

/-- The view of a proposition over a subject, named and presented. -/
elab "view% " s:ident t:term:max : term => do
  let subject ← realizeGlobalConstNoOverloadWithInfo s
  let e ← elabTermEnsuringType t (some (.sort .zero))
  synthesizeSyntheticMVarsNoPostponing
  ZkcFormal.Written.Views.viewOf subject (← instantiateMVars e)

/-- A proposition named after the origins of a subject, not presented. -/
elab "named_view% " s:ident t:term:max : term => do
  let subject ← realizeGlobalConstNoOverloadWithInfo s
  let e ← elabTermEnsuringType t (some (.sort .zero))
  synthesizeSyntheticMVarsNoPostponing
  ZkcFormal.Written.Views.namedOf subject (← instantiateMVars e)

/-- `declare_view S b : P` declares `b.view` and `b.view_iff : b.view ↔ P`. -/
macro "declare_view " s:ident b:ident " : " t:term : command => do
  let view := mkIdentFrom b (b.getId ++ `view)
  let iff := mkIdentFrom b (b.getId ++ `view_iff)
  `(def $view : Prop := view% $s ($t)
    theorem $iff : $view ↔ $t := Iff.rfl)

end ZkcFormalTests.ViewEntry
