import Tools.Artifact.Identity
import Tools.Interactive.TypedLocal

/-! Conditional laws, not an adequacy theorem for JSON normalization. The
representation law is used by ordinary-operation normalization. The occurrence
laws concern the existing origin encoding. The typed law explicitly assumes a
common resolved language, common interpretation and corresponding environments.
It makes no assertion about Inputs.prepare under whole-library restriction. -/

set_option autoImplicit false

namespace Tools.Artifact.Identity
open Lean (Json)
open Tools.Interactive

/-- With the rest of the occurrence fixed, distinct resolved operation sites
remain distinct transcript origins, regardless of equal operation contracts. -/
theorem challenge_site_separation (location : Location) (left right : Name) :
    ({ location with operation := left } : Location).challenge =
      ({ location with operation := right } : Location).challenge ↔ left = right := by
  simp [Location.challenge, Location.origin]

/-- Dynamic call/iteration ancestry is retained independently of local sites. -/
theorem origin_path_separation (location : Location) (left right : List PathElement) (event : Json) :
    ({ location with path := left } : Location).origin event =
      ({ location with path := right } : Location).origin event ↔
      left.map PathElement.json = right.map PathElement.json := by
  simp [Location.origin]

open Zkc.Source

/-- Once both sides use the same resolved operation language and meaning,
typed SSA renaming preserves full execution under the stated environment
correspondence. This includes stopping states and event prefixes. In particular,
this theorem supplies no premise relating raw normalization to typed regions. -/
theorem run_resolved_rename {interface : PIR.Signature}
    (meaning : Interpretation TypedLocal.language interface)
    {Γ Δ : List TypedLocal.language.Ty} {ty : TypedLocal.language.Ty}
    (body : Region TypedLocal.language Γ ty) (rename : Renaming Γ Δ)
    (sourceEnvironment : Zkc.Source.Environment meaning.Value Γ)
    (resolvedEnvironment : Zkc.Source.Environment meaning.Value Δ)
    (environmentCorrespondence : ∀ {t} (value : Var Γ t),
      resolvedEnvironment (rename value) = sourceEnvironment value)
    {S E : Type} (handler : PIR.Handler interface S E) (state : S) :
    ((body.rename rename).denote meaning resolvedEnvironment).run handler state =
      (body.denote meaning sourceEnvironment).run handler state := by
  rw [Region.denote_rename]
  have same : (fun {t} (value : Var Γ t) => resolvedEnvironment (rename value)) =
      @sourceEnvironment := by
    funext t value
    exact environmentCorrespondence value
  rw [same]

end Tools.Artifact.Identity
