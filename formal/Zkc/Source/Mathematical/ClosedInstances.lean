import Zkc.Source.Mathematical.DefinitionCalls

/-! Closed source-instance discovery with exact call provenance.

Keys retain the authored definition index and concrete static, role and root
tuples. Discovery follows source preorder, including the body of every repeat
without iterating its count. A second bounded pass certifies every edge against
the final unique key table. This graph is an input to typed closed assembly;
discovery alone does not discharge body typing or registered root requirements.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.ClosedInstances

structure Key where
  definition : Nat
  statics : List Nat
  roles : List Nat
  roots : List Nat
  deriving DecidableEq, Repr

def Key.cost (key : Key) : Nat := 1 + key.statics.length + key.roles.length + key.roots.length

def entryKey (source : Raw.Subject) : Key :=
  ⟨source.module.entry.definition.index, source.module.entry.statics,
    source.module.entry.roles.map (·.index), source.module.entry.capabilities.map (·.index)⟩

/-- Maximum native closure depth is 256, with the entry at depth zero. -/
def depthFuel : Nat := 257

inductive Error where
  | resource | depth | staticArity | staticBound | roleArity | roleScope | roleAlias
  | rootArity | rootScope | forward | missing | duplicate | order
  | selection (reason : SignatureAdmission.Error)
  | static (reason : Static.ResolutionError)
  | roles (reason : String)
  deriving Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

structure Instance (source : Raw.Subject) (key : Key) where
  declaration : SignatureAdmission.Selected source.module.definitions key.definition
  staticArity : key.statics.length = declaration.value.statics
  staticBounds : ∀ value ∈ key.statics, value < Static.limit
  roleArity : key.roles.length = declaration.value.roles
  roleBounds : ∀ role ∈ key.roles, role < source.module.roles.length
  roleInjective : key.roles.Nodup
  rootArity : key.roots.length = declaration.value.capabilities.length
  rootBounds : ∀ root ∈ key.roots, root < source.module.roots.length

def Instance.parameters {source key} (checked : Instance source key) :
    Fin checked.declaration.value.statics → Static.Expression 0 := fun index =>
  let bound : index.val < key.statics.length := by rw [checked.staticArity]; exact index.isLt
  .literal ⟨key.statics[index.val], checked.staticBounds _ (List.getElem_mem bound)⟩

def Instance.binding {source key} (checked : Instance source key) : RoleResolution.Binding :=
  ⟨key.roles, checked.roleInjective⟩

def admit (source : Raw.Subject) (key : Key) : Admission (Instance source key) := do
  consume (key.cost + key.roles.length ^ 2)
  let declaration ← fun remaining =>
    (SignatureAdmission.select source.module.definitions key.definition remaining).mapError Error.selection
  if staticArity : key.statics.length = declaration.value.statics then
    if staticBounds : ∀ value ∈ key.statics, value < Static.limit then
      if roleArity : key.roles.length = declaration.value.roles then
        if roleBounds : ∀ role ∈ key.roles, role < source.module.roles.length then
          if roleInjective : key.roles.Nodup then
            if rootArity : key.roots.length = declaration.value.capabilities.length then
              if rootBounds : ∀ root ∈ key.roots, root < source.module.roots.length then
                return ⟨declaration, staticArity, staticBounds, roleArity, roleBounds, roleInjective, rootArity, rootBounds⟩
              else throw .rootScope
            else throw .rootArity
          else throw .roleAlias
        else throw .roleScope
      else throw .roleArity
    else throw .staticBound
  else throw .staticArity

structure CallSite where
  site : Nat
  use : ProtocolResolution.CallUse
  deriving DecidableEq

mutual
  inductive StepCalls : Raw.Step → List CallSite → Prop where
    | pure (region) : StepCalls (.pure region) []
    | local (site owner op statics attributes caps args) : StepCalls (.local site owner op statics attributes caps args) []
    | query (site owner cap args) : StepCalls (.query site owner cap args) []
    | guard (site owner value) : StepCalls (.guard site owner value) []
    | message (site wire statics sender receiver value) : StepCalls (.message site wire statics sender receiver value) []
    | invoke (site definition statics roles caps args) :
        StepCalls (.invoke site definition statics roles caps args) [⟨site, ⟨definition, statics, roles, caps⟩⟩]
    | repeat (site count carried initial captures) {body calls} (nested : BodyCalls body calls) :
        StepCalls (.repeat site count carried initial captures body) calls
  inductive StepsCalls : List Raw.Step → List CallSite → Prop where
    | nil : StepsCalls [] []
    | cons {step steps first rest} (head : StepCalls step first) (tail : StepsCalls steps rest) :
        StepsCalls (step :: steps) (first ++ rest)
  inductive BodyCalls : Raw.Body → List CallSite → Prop where
    | mk {steps calls} (terminal) (checked : StepsCalls steps calls) : BodyCalls (.mk steps terminal) calls
end

mutual
  def collectStep (fuel : Nat) (step : Raw.Step) : Admission { calls : List CallSite // StepCalls step calls } := do
    consume
    match hstep : step with
    | .pure region => return ⟨[], by rw [hstep]; exact .pure region⟩
    | .local site owner op statics attributes caps args => return ⟨[], by rw [hstep]; exact .local site owner op statics attributes caps args⟩
    | .query site owner cap args => return ⟨[], by rw [hstep]; exact .query site owner cap args⟩
    | .guard site owner value => return ⟨[], by rw [hstep]; exact .guard site owner value⟩
    | .message site wire statics sender receiver value => return ⟨[], by rw [hstep]; exact .message site wire statics sender receiver value⟩
    | .invoke site definition statics roles caps args =>
        return ⟨[⟨site, ⟨definition, statics, roles, caps⟩⟩], by rw [hstep]; exact .invoke site definition statics roles caps args⟩
    | .repeat site count carried initial captures body =>
        let nested ← collectBody (fuel - 2) body
        return ⟨nested.val, by rw [hstep]; exact .repeat site count carried initial captures nested.property⟩
  termination_by sizeOf step
  def collectSteps (fuel : Nat) : (steps : List Raw.Step) → Admission { calls : List CallSite // StepsCalls steps calls }
    | [] => return ⟨[], .nil⟩
    | first :: rest => do
        let first ← collectStep fuel first
        let rest ← collectSteps fuel rest
        consume first.val.length
        return ⟨first.val ++ rest.val, .cons first.property rest.property⟩
  termination_by steps => sizeOf steps
  def collectBody : Nat → (body : Raw.Body) → Admission { calls : List CallSite // BodyCalls body calls }
    | 0, _ => throw .depth
    | fuel + 1, .mk steps terminal => do
        consume
        let checked ← collectSteps (fuel + 1) steps
        return ⟨checked.val, .mk terminal checked.property⟩
  termination_by _ body => sizeOf body
end

/-- Root substitution follows caller port positions and preserves aliases. -/
inductive Roots (available : List Nat) : List (Raw.Reference .capabilityPort) → List Nat → Prop where
  | nil : Roots available [] []
  | cons {reference references root roots} (selected : available[reference.index]? = some root)
      (rest : Roots available references roots) : Roots available (reference :: references) (root :: roots)

def roots (available : List Nat) : (references : List (Raw.Reference .capabilityPort)) →
    Admission { result : List Nat // Roots available references result }
  | [] => return ⟨[], .nil⟩
  | first :: rest => do
      consume (1 + min first.index available.length)
      match selected : available[first.index]? with
      | none => throw .rootScope
      | some root =>
          let rest ← roots available rest
          return ⟨root :: rest.val, .cons selected rest.property⟩

structure Call {source key} (parent : Instance source key) (site : CallSite) where
  earlier : site.use.definition.index < key.definition
  declaration : SignatureAdmission.Selected source.module.definitions site.use.definition.index
  statics : Static.Tuple parent.parameters declaration.value.statics site.use.statics
  roles : RoleResolution.Composed parent.binding declaration.value.roles site.use.roles
  roots : List Nat
  rootSelection : Roots key.roots site.use.capabilities roots
  target : Key
  exactDefinition : target.definition = site.use.definition.index
  exactStatics : target.statics = statics.values.map (·.eval Fin.elim0)
  exactRoles : target.roles = roles.binding.roles
  exactRoots : target.roots = roots

def call {source key} (parent : Instance source key) (site : CallSite) : Admission (Call parent site) := do
  consume
  if earlier : site.use.definition.index < key.definition then
    let declaration ← fun remaining =>
      (SignatureAdmission.select source.module.definitions site.use.definition.index remaining).mapError Error.selection
    let statics ← fun remaining =>
      (Static.tuple parent.parameters declaration.value.statics site.use.statics remaining).mapError Error.static
    let roles ← fun remaining =>
      (RoleResolution.compose parent.binding declaration.value.roles site.use.roles remaining).mapError Error.roles
    let selected ← roots key.roots site.use.capabilities
    let target : Key := ⟨site.use.definition.index, statics.values.map (·.eval Fin.elim0), roles.binding.roles, selected.val⟩
    return ⟨earlier, declaration, statics, roles, selected.val, selected.property, target, rfl, rfl, rfl, rfl⟩
  else throw .forward

def calls {source key} (parent : Instance source key) : (sites : List CallSite) → Admission (Values (Call parent) sites)
  | [] => return .nil
  | first :: rest => do
      let first ← call parent first
      let rest ← calls parent rest
      return .cons first rest

def targets {source key parent} : {sites : List CallSite} → Values (Call (source := source) (key := key) parent) sites → List Key
  | _, .nil => []
  | _, .cons first rest => first.target :: targets rest

structure Node (source : Raw.Subject) (key : Key) where
  checked : Instance source key
  sites : List CallSite
  coverage : BodyCalls checked.declaration.value.body sites
  children : Values (Call checked) sites

def node (source : Raw.Subject) (key : Key) : Admission (Node source key) := do
  let checked ← admit source key
  let sites ← collectBody (FormationLimits.bodyDepth + 1) checked.declaration.value.body
  let children ← calls checked sites.val
  return ⟨checked, sites.val, sites.property, children⟩

abbrev Packed (source : Raw.Subject) := (key : Key) × Node source key

def keys {source} (nodes : List (Packed source)) : List Key := nodes.map (·.1)

abbrev Reference (keys : List Key) (key : Key) := { index : Nat // keys[index]? = some key }

theorem Reference.bound {keys key} (reference : Reference keys key) : reference.val < keys.length :=
  (List.getElem?_eq_some_iff.mp reference.property).1

def referenceAt {keys : List Key} : {sources : List Key} → Values (Reference keys) sources →
    (index : Fin sources.length) → Reference keys sources[index.val]
  | _, .nil, index => Fin.elim0 index
  | _, .cons first _, ⟨0, _⟩ => first
  | _, .cons _ rest, ⟨index + 1, bound⟩ => referenceAt rest ⟨index, Nat.lt_of_succ_lt_succ bound⟩

def indexMap {keys sources : List Key} (references : Values (Reference keys) sources)
    (index : Fin sources.length) : Fin keys.length :=
  let selected := referenceAt references index
  ⟨selected.val, selected.bound⟩

theorem indexMap_key {keys sources : List Key} (references : Values (Reference keys) sources)
    (index : Fin sources.length) : keys[(indexMap references index).val]? = sources[index.val]? := by
  rw [List.getElem?_eq_getElem index.isLt]
  exact (referenceAt references index).property

theorem indexMap_inverse {keys sources : List Key} (unique : sources.Nodup)
    (forward : Values (Reference keys) sources) (backward : Values (Reference sources) keys)
    (index : Fin sources.length) : indexMap backward (indexMap forward index) = index := by
  apply Fin.ext
  apply (List.getElem?_inj (indexMap backward (indexMap forward index)).isLt unique).mp
  rw [indexMap_key backward, indexMap_key forward]

def find (key : Key) : (keys : List Key) → Admission (Option (Reference keys key))
  | [] => return none
  | first :: rest => do
      consume (key.cost + first.cost)
      if same : first = key then return some ⟨0, by simp [same]⟩
      else
        match ← find key rest with
        | none => return none
        | some selected => return some ⟨selected.val + 1, by simpa using selected.property⟩

private abbrev Discovery (source : Raw.Subject) := StateT (List (Packed source)) Admission

private def liftAdmission {source α} (action : Admission α) : Discovery source α :=
  fun nodes => do return (← action, nodes)

def visit (source : Raw.Subject) : Nat → Key → Discovery source Unit
  | 0, _ => throw .resource
  | fuel + 1, key => do
      let existing ← get
      liftAdmission (consume existing.length)
      let previous ← liftAdmission (find key (keys existing))
      if previous.isSome then return
      let checked ← liftAdmission (node source key)
      liftAdmission (consume (existing.length + 1))
      set (existing ++ [⟨key, checked⟩])
      for child in targets checked.children do
        visit source fuel child

def references (keys : List Key) : (targets : List Key) → Admission (Values (Reference keys) targets)
  | [] => return .nil
  | first :: rest => do
      let some first ← find first keys | throw .missing
      let rest ← references keys rest
      return .cons first rest

def edges {source} (keys : List Key) : (nodes : List (Packed source)) →
    Admission (Values (fun node => Values (Reference keys) (targets node.2.children)) nodes)
  | [] => return .nil
  | first :: rest => do
      let first ← references keys (targets first.2.children)
      let rest ← edges keys rest
      return .cons first rest

/-- Canonical DFS trace over already certified nodes. The caller charges its
finite table/edge comparison bound before evaluating this independent check. -/
def trace {source} (nodes : List (Packed source)) : Nat → Key → List Key → Option (List Key)
  | 0, _, _ => none
  | fuel + 1, key, visited => do
      if key ∈ visited then return visited
      let node ← nodes.find? (fun node => node.1 == key)
      (targets node.2.children).foldlM (fun visited child => trace nodes fuel child visited) (visited ++ [key])

def canonical {source} (nodes : List (Packed source)) : Option (List Key) :=
  trace nodes depthFuel (entryKey source) []

private def traceCost {source} (nodes : List (Packed source)) : Nat :=
  let nodeCost := nodes.foldl (fun total node => total + node.1.cost) 1
  let edgeCost := nodes.foldl (fun total node => total +
    (targets node.2.children).foldl (fun total key => total + key.cost) 0) 1
  -- Every edge can scan the node/visited table once. Copying a new visited
  -- prefix occurs at most once per node. Key sizes include all tuple entries.
  4 * (nodeCost + 1) * (edgeCost + nodeCost + 1)

structure Graph (source : Raw.Subject) where
  nodes : List (Packed source)
  unique : (keys nodes).Nodup
  entry : Reference (keys nodes) (entryKey source)
  edges : Values (fun node => Values (Reference (keys nodes)) (targets node.2.children)) nodes
  preorder : canonical nodes = some (keys nodes)

/-- Certifies exact identity, edge coverage and native preorder independently
of construction. Extra unreachable nodes, reordered IDs and incomplete tables
cannot obtain this certificate by supplying compatible signatures. -/
def certify (source : Raw.Subject) (nodes : List (Packed source)) : Admission (Graph source) := do
  let allKeys := keys nodes
  consume ((allKeys.foldl (fun total key => total + key.cost) 1) * (allKeys.length + 1))
  if unique : allKeys.Nodup then
    let some entry ← find (entryKey source) allKeys | throw .missing
    let edges ← edges allKeys nodes
    consume (traceCost nodes)
    if preorder : canonical nodes = some allKeys then
      return ⟨nodes, unique, entry, edges, preorder⟩
    else throw .order
  else throw .duplicate

def discover (source : Raw.Subject) : Admission (Graph source) := do
  let (_, nodes) ← (visit source depthFuel (entryKey source)).run []
  certify source nodes

end Zkc.Source.Mathematical.ClosedInstances
