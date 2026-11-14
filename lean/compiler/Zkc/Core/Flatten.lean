module

public import Zkc.Core.Region

public section

/-! Flattening nested blocks, for any dialect.

`Region.bind body rest` is a nested block over the whole surrounding context. The
exchange form has no such operation: every region of the dialect is closed. `flatten`
removes the blocks of a closed region: the operations of a block come in place of the
block, and the values the block returns stand for its results in what follows. Nested
closed regions are flattened in place.

The function is `spliceInto`, a structural recursion on the region. It carries a renaming
of the region's context into the context built so far, which is data, and a continuation
that receives the returned values. A continuation is a closure only at a block; within a
block the growth of the context is recorded as data (`Extension`), so the number of
closures does not grow with the length of a body.

`flatten_denote`: flattening keeps the denotation, for every meaning of the dialect.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {Ty : Type}

/-! ## A context that extends another -/

/-- The larger context has every value of the smaller one at the same level. -/
structure Extension (Δ Δ' : List Ty) where
  base : Nat
  depth : Nat
  based : base = Δ.length
  counted : depth = Δ'.length
  preserved : ∀ (level : Nat) (entry : Ty), atLevel? Δ base level = some entry →
    atLevel? Δ' depth level = some entry

namespace Extension

variable {Δ Δ' Δ'' : List Ty}

/-- A context extends itself. -/
def refl (depth : Nat) (counted : depth = Δ.length) : Extension Δ Δ :=
  ⟨depth, depth, counted, counted, fun _ _ found => found⟩

/-- More values in the larger context. -/
def bind (extension : Extension Δ Δ') (added : List Ty) : Extension Δ (bindAll Δ' added) :=
  ⟨extension.base, extension.depth + added.length, extension.based,
    by rw [length_bindAll, extension.counted],
    fun level entry found => atLevel?_bindAll added Δ' (extension.preserved level entry found)⟩

def trans (first : Extension Δ Δ') (second : Extension Δ' Δ'') : Extension Δ Δ'' :=
  ⟨first.base, second.depth, first.based, second.counted, fun level entry found =>
    second.preserved level entry (by
      rw [second.based, ← first.counted]
      exact first.preserved level entry found)⟩

theorem level_valid (extension : Extension Δ Δ') {ty : Ty} (reference : Var Δ ty) :
    atLevel? Δ' extension.depth (extension.base - 1 - reference.index) = some ty := by
  apply extension.preserved
  rw [extension.based]
  exact atLevel?_index reference

theorem level_lt (extension : Extension Δ Δ') {ty : Ty} (reference : Var Δ ty) :
    extension.base - 1 - reference.index < extension.depth := by
  have valid := extension.level_valid reference
  unfold atLevel? at valid
  split at valid
  · assumption
  · cases valid

/-- A value of the smaller context, in the larger one. -/
def var (extension : Extension Δ Δ') {ty : Ty} (reference : Var Δ ty) : Var Δ' ty :=
  ⟨extension.depth - 1 - (extension.base - 1 - reference.index), by
    have valid := extension.level_valid reference
    unfold atLevel? at valid
    split at valid
    · exact valid
    · cases valid⟩

theorem var_refl (depth : Nat) (counted : depth = Δ.length) {ty : Ty} (reference : Var Δ ty) :
    (refl depth counted).var reference = reference := by
  apply Var.ext
  have bound := reference.index_lt
  show depth - 1 - (depth - 1 - reference.index) = reference.index
  omega

theorem var_bind (extension : Extension Δ Δ') (added : List Ty) {ty : Ty} (reference : Var Δ ty) :
    (extension.bind added).var reference = (extension.var reference).weaken added := by
  apply Var.ext
  have below := extension.level_lt reference
  show extension.depth + added.length - 1 - (extension.base - 1 - reference.index) =
    extension.depth - 1 - (extension.base - 1 - reference.index) + added.length
  omega

theorem var_trans (first : Extension Δ Δ') (second : Extension Δ' Δ'') {ty : Ty}
    (reference : Var Δ ty) :
    (first.trans second).var reference = second.var (first.var reference) := by
  apply Var.ext
  have below := first.level_lt reference
  have same : second.base = first.depth := second.based.trans first.counted.symm
  show second.depth - 1 - (first.base - 1 - reference.index) =
    second.depth - 1 - (second.base - 1 - (first.depth - 1 - (first.base - 1 - reference.index)))
  omega

end Extension

/-- A map into a context is a map into a context that extends it. -/
def Mapping.extendTo {α β : Type} {R : α → β → Prop} {Γ : List α} {Δ Δ' : List β}
    (map : Mapping R Γ Δ) (extension : Extension Δ Δ') : Mapping R Γ Δ' :=
  ⟨map.levels, extension.depth, extension.counted, fun index source found => by
    obtain ⟨level, at_, image⟩ := map.sound index source found
    exact ⟨level, at_, fun target related =>
      extension.preserved level target (by
        rw [extension.based, ← map.counted]
        exact image target related)⟩⟩

theorem Mapping.apply_extendTo {α β : Type} {R : α → β → Prop} {Γ : List α} {Δ Δ' : List β}
    (map : Mapping R Γ Δ) (extension : Extension Δ Δ') {source : α} {target : β}
    (reference : Var Γ source) (related : R source target) :
    (map.extendTo extension).apply reference related =
      extension.var (map.apply reference related) := by
  apply Var.ext
  have found := map.level_sound reference related
  have same : extension.base = map.depth := extension.based.trans map.counted.symm
  unfold atLevel? at found
  split at found
  · rename_i below
    show extension.depth - 1 - map.level reference.index =
      extension.depth - 1 - (extension.base - 1 - (map.depth - 1 - map.level reference.index))
    omega
  · cases found

/-- More old values, renamed to given values of the new context. -/
def Renaming.bindOperands {Δ : List Ty} : {Γ : List Ty} → Renaming Γ Δ → (added : List Ty) →
    Operands Δ added → Renaming (bindAll Γ added) Δ
  | _, map, [], _ => map
  | _, map, _ :: rest, .cons reference operands => bindOperands (map.to reference) rest operands

/-! ## Environments under a renaming -/

/-- The new environment holds, at the image of every old value, that value. -/
structure Renaming.Holds {Value : Ty → Type} {Γ Δ : List Ty} (map : Renaming Γ Δ)
    (env : Environment Value Γ) (image : Environment Value Δ) : Prop where
  value : ∀ {ty : Ty} (reference : Var Γ ty), image (map.rename reference) = env reference

namespace Renaming.Holds

variable {Value : Ty → Type} {Γ Δ : List Ty} {map : Renaming Γ Δ} {env : Environment Value Γ}
  {image : Environment Value Δ}

theorem keep (holds : map.Holds env image) (ty : Ty) (value : Value ty) :
    Renaming.Holds (map.keep ty ty fun _ same => same.symm) (env.push value) (image.push value) := by
  refine ⟨fun {other} reference => ?_⟩
  cases reference with
  | here => exact congrArg (image.push value) (Mapping.apply_keep_here ..)
  | there reference =>
      exact (congrArg (image.push value) (Mapping.apply_keep_there ..)).trans (holds.value reference)

theorem keepAll :
    ∀ (added : List Ty) {Γ Δ : List Ty} {map : Renaming Γ Δ} {env : Environment Value Γ}
      {image : Environment Value Δ}, map.Holds env image → ∀ (values : Values Value added),
        Renaming.Holds (map.keepAll added) (Environment.bindAll env values)
          (Environment.bindAll image values)
  | [], _, _, _, _, _, holds, .nil => holds
  | ty :: rest, _, _, _, _, _, holds, .cons value values => keepAll rest (holds.keep ty value) values

theorem to (holds : map.Holds env image) {ty : Ty} (reference : Var Δ ty) :
    Renaming.Holds (map.to reference) (env.push (image reference)) image := by
  refine ⟨fun {other} position => ?_⟩
  cases position with
  | here => exact congrArg image (Mapping.apply_bind_here ..)
  | there position =>
      exact (congrArg image (Mapping.apply_bind_there ..)).trans (holds.value position)

theorem bindOperands {image : Environment Value Δ} :
    ∀ (added : List Ty) {Γ : List Ty} {map : Renaming Γ Δ} {env : Environment Value Γ},
      map.Holds env image → ∀ (operands : Operands Δ added),
        Renaming.Holds (map.bindOperands added operands)
          (Environment.bindAll env (Operands.eval image operands)) image
  | [], _, _, _, holds, .nil => holds
  | _ :: rest, _, _, _, holds, .cons reference operands =>
      bindOperands rest (holds.to reference) operands

theorem extendTo {Δ' : List Ty} (holds : map.Holds env image) (extension : Extension Δ Δ')
    (larger : Environment Value Δ')
    (extends_ : ∀ {ty : Ty} (reference : Var Δ ty), larger (extension.var reference) = image reference) :
    Renaming.Holds (map.extendTo extension) env larger :=
  ⟨fun reference =>
    (congrArg larger (Mapping.apply_extendTo map extension reference rfl)).trans
      ((extends_ _).trans (holds.value reference))⟩

/-- The renamed operands hold the values of the operands. -/
theorem eval (holds : map.Holds env image) :
    ∀ {types : List Ty} (operands : Operands Γ types),
      Operands.eval image (map.operands operands) = Operands.eval env operands
  | _, .nil => rfl
  | _, .cons reference rest =>
      congr (congrArg Values.cons (holds.value reference)) (eval holds rest)

end Renaming.Holds

/-! ## Flattening -/

mutual
  /-- The operations of a region and of its blocks, in order, in a context that renames
  the region's, followed by the continuation on the returned values. `extension` is from
  the context in which the continuation was fixed. -/
  def Region.spliceInto {dialect : Dialect} {Γ mid : List dialect.Ty} :
      Region dialect Γ mid → {base Δ : List dialect.Ty} → Renaming Γ Δ → Extension base Δ →
        {out : List dialect.Ty} →
        ({Δ' : List dialect.Ty} → Extension base Δ' → Operands Δ' mid → Region dialect Δ' out) →
          Region dialect Δ out
    | .ret values, _, _, map, extension, _, continue_ => continue_ extension (map.operands values)
    | .stop reason, _, _, _, _, _, _ => .stop reason
    | .letOp op arguments bodies rest, _, _, map, extension, _, continue_ =>
        .letOp op (map.operands arguments) (Regions.flatten bodies)
          (Region.spliceInto rest (map.keepAll (dialect.results op))
            (extension.bind (dialect.results op)) continue_)
    | .bind (mid := inner) body rest, _, _, map, extension, _, continue_ =>
        Region.spliceInto body map (Extension.refl map.depth map.counted) fun later operands =>
          Region.spliceInto rest (Renaming.bindOperands (map.extendTo later) inner operands)
            (extension.trans later) continue_

  /-- Closed regions without blocks. -/
  def Regions.flatten {dialect : Dialect} {signatures : List (List dialect.Ty × List dialect.Ty)} :
      Regions dialect signatures → Regions dialect signatures
    | .nil => .nil
    | .cons (inputs := inputs) body tail =>
        .cons
          (Region.spliceInto body (Renaming.keepAll (Mapping.start (Δ := ([] : List dialect.Ty)) 0 rfl) inputs)
            (Extension.refl inputs.length (by rw [length_bindAll]; simp))
            fun _ operands => .ret operands)
          (Regions.flatten tail)
end

/-- A closed region without blocks. -/
def Region.flatten {dialect : Dialect} {inputs out : List dialect.Ty}
    (region : Region dialect (bindAll [] inputs) out) : Region dialect (bindAll [] inputs) out :=
  Region.spliceInto region (Renaming.keepAll (Mapping.start (Δ := ([] : List dialect.Ty)) 0 rfl) inputs)
    (Extension.refl inputs.length (by rw [length_bindAll]; simp)) fun _ operands => .ret operands

section Denote

variable {dialect : Dialect} {interface : PIR.Signature} (meaning : RegionMeaning dialect interface)

mutual
  theorem Region.spliceInto_denote {Γ mid : List dialect.Ty} :
      ∀ (region : Region dialect Γ mid) {base Δ : List dialect.Ty} (map : Renaming Γ Δ)
        (extension : Extension base Δ) {out : List dialect.Ty}
        (continue_ : {Δ' : List dialect.Ty} → Extension base Δ' → Operands Δ' mid →
          Region dialect Δ' out)
        (env : Environment meaning.Value Γ) (image : Environment meaning.Value Δ)
        (outer : Environment meaning.Value base)
        (after : Values meaning.Value mid → PIR.Process interface (Values meaning.Value out)),
        map.Holds env image →
        (∀ {ty : dialect.Ty} (reference : Var base ty), image (extension.var reference) = outer reference) →
        (∀ {Δ' : List dialect.Ty} (later : Extension base Δ') (operands : Operands Δ' mid)
          (larger : Environment meaning.Value Δ'),
          (∀ {ty : dialect.Ty} (reference : Var base ty), larger (later.var reference) = outer reference) →
            (continue_ later operands).denote meaning larger = after (Operands.eval larger operands)) →
        (Region.spliceInto region map extension continue_).denote meaning image =
          (region.denote meaning env).bind after
    | .ret values, _, _, map, extension, _, continue_, env, image, outer, after, holds, extends_,
        continues => by
        show (continue_ extension (map.operands values)).denote meaning image = after _
        rw [continues extension _ image extends_, holds.eval]
    | .stop reason, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
    | .letOp op arguments bodies rest, _, _, map, extension, _, continue_, env, image, outer, after,
        holds, extends_, continues => by
        show (meaning.operation op (Operands.eval image (map.operands arguments))
            ((Regions.flatten bodies).denote meaning)).bind _ =
          ((meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind _).bind _
        rw [holds.eval, Regions.flatten_denote bodies, PIR.Process.bind_assoc]
        congr 1
        funext results
        refine Region.spliceInto_denote rest _ _ continue_ _ _ outer after
          (Renaming.Holds.keepAll _ holds results) ?_ continues
        intro ty reference
        rw [Extension.var_bind, Environment.bindAll_weaken]
        exact extends_ reference
    | .bind (mid := inner) body rest, _, _, map, extension, _, continue_, env, image, outer, after,
        holds, extends_, continues => by
        show (Region.spliceInto body map (Extension.refl map.depth map.counted) _).denote meaning image =
          ((body.denote meaning env).bind _).bind after
        rw [PIR.Process.bind_assoc]
        refine Region.spliceInto_denote body map _ _ env image image _ holds
          (fun reference => congrArg image (Extension.var_refl ..)) ?_
        intro _ later operands larger larger_extends
        refine Region.spliceInto_denote rest _ _ continue_ _ larger outer after
          (Renaming.Holds.bindOperands inner (holds.extendTo later larger larger_extends) operands) ?_
          continues
        intro ty reference
        rw [Extension.var_trans, larger_extends]
        exact extends_ reference

  theorem Regions.flatten_denote {signatures : List (List dialect.Ty × List dialect.Ty)} :
      ∀ (regions : Regions dialect signatures),
        (Regions.flatten regions).denote meaning = regions.denote meaning
    | .nil => rfl
    | .cons (inputs := inputs) body tail => by
        show Values.cons _ _ = Values.cons _ _
        rw [Regions.flatten_denote tail]
        congr 1
        funext values
        refine (Region.spliceInto_denote body _ _ _ (Environment.ofValues values)
          (Environment.ofValues values) (Environment.ofValues values) .done
          (Renaming.Holds.keepAll inputs ⟨fun reference => reference.elimNil⟩ values)
          (fun reference => congrArg _ (Extension.var_refl ..)) ?_).trans (PIR.Process.bind_done _)
        intro _ _ _ _ _
        rfl
end

/-- Flattening a closed region keeps its denotation. -/
theorem Region.flatten_denote {inputs out : List dialect.Ty}
    (region : Region dialect (bindAll [] inputs) out) (values : Values meaning.Value inputs) :
    region.flatten.denote meaning (Environment.ofValues values) =
      region.denote meaning (Environment.ofValues values) := by
  refine (Region.spliceInto_denote meaning region _ _ _ (Environment.ofValues values)
    (Environment.ofValues values) (Environment.ofValues values) .done
    (Renaming.Holds.keepAll inputs ⟨fun reference => reference.elimNil⟩ values)
    (fun reference => congrArg _ (Extension.var_refl ..)) ?_).trans (PIR.Process.bind_done _)
  intro _ _ _ _ _
  rfl

end Denote

end Zkc.Source
