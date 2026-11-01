module

public import Zkc.Source.Structured.UnitViews

@[expose] public section

/-! Exact syntax selection for generated callback bindings. This traverses the
retained typed Region, not an execution model or a second representation. -/

namespace Zkc.Source.Structured.Bindings

/-- The complete local repeat node. The first operand is the runtime count,
followed by ordered state and captures. The continuation retains every return
and stop; scopes, roles and the static maximum belong to `spec`. -/
structure RepeatSite where
  context : List Ty
  outputs : List Ty
  spec : RepeatSpec
  site : String
  operands : Operands context (.index :: (spec.state ++ spec.captures))
  body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state
  next : Region protocolDialect (spec.state ++ context) outputs

def RepeatSite.region (selected : RepeatSite) :
    Region protocolDialect selected.context selected.outputs :=
  .letOp (.repeat selected.spec selected.site) selected.operands (.cons selected.body .nil) selected.next

/-- Structural association with the actual typed source. An enclosing repeat
retains its own operands, scopes, captures and continuation. This is lexical
evidence only: a zero count or an earlier stop may prevent execution. -/
inductive RepeatAt (selected : RepeatSite) :
    {inputs outputs : List Ty} → Region protocolDialect inputs outputs → Type where
  | here : RepeatAt selected selected.region
  | next {inputs outputs} (op : ProtocolOp) (args : Operands inputs op.arguments)
      (bodies : Regions protocolDialect op.regions)
      (tail : Region protocolDialect (op.results ++ inputs) outputs) :
      RepeatAt selected tail → RepeatAt selected (.letOp op args bodies tail)
  | bindBody {inputs mid outputs} (body : Region protocolDialect inputs mid)
      (next : Region protocolDialect (mid ++ inputs) outputs) :
      RepeatAt selected body → RepeatAt selected (.bind body next)
  | bindNext {inputs mid outputs} (body : Region protocolDialect inputs mid)
      (next : Region protocolDialect (mid ++ inputs) outputs) :
      RepeatAt selected next → RepeatAt selected (.bind body next)
  | repeatBody {inputs outputs} (spec : RepeatSpec) (site : String)
      (args : Operands inputs (.index :: (spec.state ++ spec.captures)))
      (body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
      (next : Region protocolDialect (spec.state ++ inputs) outputs) :
      RepeatAt selected body →
      RepeatAt selected (.letOp (.repeat spec site) args (.cons body .nil) next)

namespace RepeatAt
variable {selected : RepeatSite}

/-- Child zero is a bind body or repeat callback; child one is a suffix. -/
def position : {inputs outputs : List Ty} → {body : Region protocolDialect inputs outputs} →
    RepeatAt selected body → List Nat
  | _, _, _, .here => []
  | _, _, _, .next _ _ _ _ occurrence => 1 :: occurrence.position
  | _, _, _, .bindBody _ _ occurrence => 0 :: occurrence.position
  | _, _, _, .bindNext _ _ occurrence => 1 :: occurrence.position
  | _, _, _, .repeatBody _ _ _ _ _ occurrence => 0 :: occurrence.position

/-- Exact enclosing repeat nodes, outermost first, with root-relative paths.
Their lexical presence does not assert a reached runtime iteration. -/
def enclosing : {inputs outputs : List Ty} → {body : Region protocolDialect inputs outputs} →
    RepeatAt selected body → List (List Nat × RepeatSite)
  | _, _, _, .here => []
  | _, _, _, .next _ _ _ _ occurrence => occurrence.enclosing.map fun (path, site) => (1 :: path, site)
  | _, _, _, .bindBody _ _ occurrence => occurrence.enclosing.map fun (path, site) => (0 :: path, site)
  | _, _, _, .bindNext _ _ occurrence => occurrence.enclosing.map fun (path, site) => (1 :: path, site)
  | _, _, _, .repeatBody spec site args body suffix occurrence =>
      ([], ⟨_, _, spec, site, args, body, suffix⟩) ::
        occurrence.enclosing.map (fun (path, site) => (0 :: path, site))

end RepeatAt

structure RepeatOccurrence {inputs outputs : List Ty} (body : Region protocolDialect inputs outputs) where
  repeatSite : RepeatSite
  occurrence : RepeatAt repeatSite body

namespace RepeatOccurrence

def position {inputs outputs} {body : Region protocolDialect inputs outputs}
    (selected : RepeatOccurrence body) : List Nat := selected.occurrence.position

def here {inputs outputs} (spec : RepeatSpec) (site : String)
    (args : Operands inputs (.index :: (spec.state ++ spec.captures)))
    (body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
    (next : Region protocolDialect (spec.state ++ inputs) outputs) :
    RepeatOccurrence (.letOp (.repeat spec site) args (.cons body .nil) next) :=
  ⟨⟨_, _, spec, site, args, body, next⟩, .here⟩

def next {inputs outputs} (op : ProtocolOp) (args : Operands inputs op.arguments)
    (bodies : Regions protocolDialect op.regions)
    (tail : Region protocolDialect (op.results ++ inputs) outputs) (selected : RepeatOccurrence tail) :
    RepeatOccurrence (.letOp op args bodies tail) :=
  ⟨selected.repeatSite, .next op args bodies tail selected.occurrence⟩

def bindBody {inputs mid outputs} (body : Region protocolDialect inputs mid)
    (next : Region protocolDialect (mid ++ inputs) outputs) (selected : RepeatOccurrence body) :
    RepeatOccurrence (.bind body next) :=
  ⟨selected.repeatSite, .bindBody body next selected.occurrence⟩

def bindNext {inputs mid outputs} (body : Region protocolDialect inputs mid)
    (next : Region protocolDialect (mid ++ inputs) outputs) (selected : RepeatOccurrence next) :
    RepeatOccurrence (.bind body next) :=
  ⟨selected.repeatSite, .bindNext body next selected.occurrence⟩

def repeatBody {inputs outputs} (spec : RepeatSpec) (site : String)
    (args : Operands inputs (.index :: (spec.state ++ spec.captures)))
    (body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
    (next : Region protocolDialect (spec.state ++ inputs) outputs) (selected : RepeatOccurrence body) :
    RepeatOccurrence (.letOp (.repeat spec site) args (.cons body .nil) next) :=
  ⟨selected.repeatSite, .repeatBody spec site args body next selected.occurrence⟩

end RepeatOccurrence

/-- One preorder traversal: a repeat, its nested callbacks, then its suffix.
Both bind children are retained, even when a prefix stops. Equal labels do not
coalesce occurrences. This is the order used by generated callbacks. -/
def repeatInventory {inputs outputs} (body : Region protocolDialect inputs outputs) :
    List (RepeatOccurrence body) :=
  match body with
  | .ret _ | .stop _ => []
  | .bind body next => (repeatInventory body).map (RepeatOccurrence.bindBody body next) ++
      (repeatInventory next).map (RepeatOccurrence.bindNext body next)
  | .letOp op args bodies next =>
      (match op, args, bodies, next with
       | .repeat spec site, args, .cons body tail, next =>
           match tail with
           | .nil => RepeatOccurrence.here spec site args body next ::
               (repeatInventory body).map (RepeatOccurrence.repeatBody spec site args body next)
       | _, _, _, _ => []) ++
      (repeatInventory next).map (RepeatOccurrence.next op args bodies next)

/-- Every independently constructed structural witness is enumerated. -/
theorem repeatInventory_complete {inputs outputs} {body : Region protocolDialect inputs outputs}
    (selected : RepeatOccurrence body) : selected ∈ repeatInventory body := by
  rcases selected with ⟨site, occurrence⟩
  induction occurrence with
  | here =>
    rcases site with ⟨context, result, spec, label, args, callback, suffix⟩
    exact List.mem_append_left _ (List.mem_cons_self)
  | next op args bodies tail occurrence ih =>
    unfold repeatInventory
    split
    all_goals exact List.mem_append_right _ (List.mem_map.mpr ⟨RepeatOccurrence.mk site occurrence, ih, rfl⟩)
  | bindBody body next occurrence ih =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨⟨site, occurrence⟩, ih, rfl⟩)
  | bindNext body next occurrence ih =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨site, occurrence⟩, ih, rfl⟩)
  | repeatBody spec label args body next occurrence ih =>
    exact List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨⟨site, occurrence⟩, ih, rfl⟩))

/-- Ordinals locate candidates; full typed equality establishes association. -/
def selectRepeat {inputs outputs} (ordinal : Nat) (body : Region protocolDialect inputs outputs) :
    Option (RepeatOccurrence body) := (repeatInventory body)[ordinal]?

/-- Project a complete occurrence from a checked locator without copying its
callback or suffix into generated syntax. The inventory remains the authority. -/
def checkedRepeat {inputs outputs} (ordinal : Nat) (body : Region protocolDialect inputs outputs)
    (present : (selectRepeat ordinal body).isSome = true) : RepeatOccurrence body :=
  (selectRepeat ordinal body).get present

theorem checkedRepeat_selected {inputs outputs} (ordinal : Nat)
    (body : Region protocolDialect inputs outputs)
    (present : (selectRepeat ordinal body).isSome = true) :
    (selectRepeat ordinal body).map (·.repeatSite) = some (checkedRepeat ordinal body present).repeatSite := by
  exact (congrArg (Option.map (·.repeatSite)) (Option.some_get present)).symm

/-- Recover usable structural evidence from a checked complete descriptor.
There is no assumed reachability or successful callback result. -/
def selectedRepeat {inputs outputs} {ordinal : Nat} {body : Region protocolDialect inputs outputs}
    {site : RepeatSite}
    (exactSite : (selectRepeat ordinal body).map (·.repeatSite) = some site) : RepeatAt site body := by
  cases found : selectRepeat ordinal body with
  | none => simp [found] at exactSite
  | some selected =>
    have same : selected.repeatSite = site := Option.some.inj (by simpa [found] using exactSite)
    exact same ▸ selected.occurrence

def repeatSites {inputs outputs} (body : Region protocolDialect inputs outputs) : List RepeatSite :=
  (repeatInventory body).map (·.repeatSite)

/-- Erasing the proof retains exactly, and only, structurally witnessed nodes. -/
theorem mem_repeatSites_iff {inputs outputs} {body : Region protocolDialect inputs outputs}
    (site : RepeatSite) : site ∈ repeatSites body ↔ Nonempty (RepeatAt site body) := by
  simp only [repeatSites, List.mem_map]
  constructor
  · rintro ⟨selected, _, same⟩
    exact ⟨same ▸ selected.occurrence⟩
  · rintro ⟨occurrence⟩
    exact ⟨⟨site, occurrence⟩, repeatInventory_complete _, rfl⟩

end Zkc.Source.Structured.Bindings
