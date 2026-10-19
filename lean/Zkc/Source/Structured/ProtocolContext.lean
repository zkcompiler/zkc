module

public import Zkc.Source.Structured.ProtocolSignature
public import Init.Data.Nat.ToString

@[expose] public section

namespace Zkc.Source.Structured

/-- Definition-local coordinates mapped into the immutable selected-root roster. -/
structure ProtocolContext where
  applicationPrefix : Option String := none
  roles : Nat → Nat := id

/-- Decimal digits used by protocol labels have a public kernel reduction. -/
def protocolSiteDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- Structural recursion bounds the number of divisions; callers supply `n + 1`.
Only the decimal expansion is constructed, not a list proportional to the fuel. -/
def protocolSiteDigits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n < 10 then [protocolSiteDigit n]
    else protocolSiteDigits fuel (n / 10) ++ [protocolSiteDigit (n % 10)]

/-- Project-owned decimal rendering shared by process and metadata labels. -/
def protocolSiteDecimal (n : Nat) : String :=
  String.ofList (protocolSiteDigits (n + 1) n)

theorem protocolSiteDigit_eq (n : Nat) (bound : n < 10) :
    protocolSiteDigit n = Nat.digitChar n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => simp [protocolSiteDigit]
  | _ + 10 => omega

theorem protocolSiteDigits_eq (fuel n : Nat) (enough : n < fuel) :
    protocolSiteDigits fuel n = Nat.toDigits 10 n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    rw [protocolSiteDigits, Nat.toDigits_eq_ite (by decide : 1 < 10)]
    split
    · rw [protocolSiteDigit_eq _ ‹_›]
    · have smaller := Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 10)
      rw [ih _ (by omega), protocolSiteDigit_eq _ (Nat.mod_lt _ (by decide))]

/-- Agreement with ordinary natural-number decimal spelling, for every length. -/
theorem protocolSiteDecimal_eq_toString (n : Nat) :
    protocolSiteDecimal n = toString n := by
  rw [protocolSiteDecimal, protocolSiteDigits_eq _ _ (Nat.lt_succ_self n),
    Nat.toString_eq_ofList_toDigits]

/-- The empty synthetic mark remains empty; nesting uses the rendered parent. -/
def qualifyProtocolSite : Option String → String → String
  | none, site => site
  | some captured, site =>
    if site = "" then "" else
      "apply_" ++ protocolSiteDecimal captured.utf8ByteSize ++ "_" ++ captured ++ "_" ++ site

def roleSubstitution (indices : List Nat) : Nat → Nat :=
  fun role => indices[role]?.getD 0

def ProtocolContext.enter (context : ProtocolContext)
    (site : String) (indices : List Nat) : ProtocolContext :=
  ⟨some (qualifyProtocolSite context.applicationPrefix site),
    context.roles ∘ roleSubstitution indices⟩

def ProtocolContext.mapScopes (context : ProtocolContext)
    (scopes : List (List Nat)) : List (List Nat) :=
  scopes.map (List.map context.roles)

def ProtocolContext.contains (context : ProtocolContext)
    (signature : ProtocolSignature) (self : Nat) : Bool :=
  (List.range signature.roles.length).any (fun role => context.roles role == self)

/-- Only the finite local roster has bounded, injective coordinates. -/
def ProtocolContext.Valid (rootRoles localRoles : List String)
    (context : ProtocolContext) : Prop :=
  (∀ role, role < localRoles.length → context.roles role < rootRoles.length) ∧
  ∀ left, left < localRoles.length → ∀ right, right < localRoles.length →
    context.roles left = context.roles right → left = right

def ValidSubstitution (callerRoles : List String) (signature : ProtocolSignature)
    (indices : List Nat) : Prop :=
  indices.length = signature.roles.length ∧
    (∀ role ∈ indices, role < callerRoles.length) ∧ indices.Nodup

@[simp] theorem qualify_root (site : String) : qualifyProtocolSite none site = site := rfl

@[simp] theorem qualify_empty (parent : Option String) : qualifyProtocolSite parent "" = "" := by
  cases parent <;> simp [qualifyProtocolSite]

theorem qualify_prefix (captured site : String) (nonempty : site ≠ "") :
    qualifyProtocolSite (some captured) site =
      "apply_" ++ toString captured.utf8ByteSize ++ "_" ++ captured ++ "_" ++ site := by
  simp [qualifyProtocolSite, nonempty, protocolSiteDecimal_eq_toString]

/-- Size of the prefix before constructing the qualified label. -/
def protocolSiteOverhead : Option String → Nat
  | none => 0
  | some captured => 8 + (protocolSiteDecimal captured.utf8ByteSize).utf8ByteSize +
      captured.utf8ByteSize

/-- Empty synthetic marks allocate no label; other sites include the exact prefix. -/
def protocolSiteSize (parent : Option String) (site : String) : Nat :=
  if site = "" then 0 else protocolSiteOverhead parent + site.utf8ByteSize

theorem qualifyProtocolSite_utf8ByteSize (parent : Option String) (site : String) :
    (qualifyProtocolSite parent site).utf8ByteSize = protocolSiteSize parent site := by
  cases parent with
  | none => by_cases empty : site = "" <;> simp [qualifyProtocolSite, protocolSiteSize,
      protocolSiteOverhead, empty]
  | some captured =>
    by_cases empty : site = ""
    · simp [qualifyProtocolSite, protocolSiteSize, empty]
    · simp only [qualifyProtocolSite, protocolSiteSize, empty, ↓reduceIte,
        String.utf8ByteSize_append, protocolSiteOverhead]
      change 6 + _ + 1 + _ + 1 + _ = 8 + _ + _ + _
      omega

/-- Nested labels use the complete rendered parent, with its UTF-8 byte length. -/
theorem qualify_nested (parent callSite leaf : String)
    (callNonempty : callSite ≠ "") (leafNonempty : leaf ≠ "") :
    qualifyProtocolSite (some (qualifyProtocolSite (some parent) callSite)) leaf =
      let rendered := "apply_" ++ toString parent.utf8ByteSize ++ "_" ++ parent ++ "_" ++ callSite
      "apply_" ++ toString rendered.utf8ByteSize ++ "_" ++ rendered ++ "_" ++ leaf := by
  rw [qualify_prefix parent callSite callNonempty, qualify_prefix _ leaf leafNonempty]

/-- Entry stores the qualified header, so the next leaf nests on the left. -/
theorem qualify_enter (context : ProtocolContext) (site leaf : String) (indices : List Nat) :
    qualifyProtocolSite (context.enter site indices).applicationPrefix leaf =
      qualifyProtocolSite (some (qualifyProtocolSite context.applicationPrefix site)) leaf := rfl

@[simp] theorem ProtocolContext.mapScopes_root (scopes : List (List Nat)) :
    ({} : ProtocolContext).mapScopes scopes = scopes := by
  simp [mapScopes]

@[simp] theorem ProtocolContext.map_roles_root (roles : List Nat) :
    roles.map ({} : ProtocolContext).roles = roles := by
  simp

theorem ProtocolContext.mapScopes_enter (context : ProtocolContext)
    (site : String) (indices : List Nat) (scopes : List (List Nat)) :
    (context.enter site indices).mapScopes scopes =
      context.mapScopes (scopes.map (List.map (roleSubstitution indices))) := by
  simp [mapScopes, enter, List.map_map, Function.comp_def]

theorem ProtocolContext.mem_mapped_scope (context : ProtocolContext)
    (scope : List Nat) (self : Nat) :
    self ∈ scope.map context.roles ↔ ∃ role ∈ scope, context.roles role = self :=
  List.mem_map

theorem ProtocolContext.contains_iff (context : ProtocolContext)
    (signature : ProtocolSignature) (self : Nat) :
    context.contains signature self = true ↔
      ∃ role, role < signature.roles.length ∧ context.roles role = self := by
  simp [contains]

theorem roleSubstitution_get (indices : List Nat) (role : Nat) (bound : role < indices.length) :
    roleSubstitution indices role = indices[role] := by
  simp [roleSubstitution, bound]

theorem ProtocolContext.valid_root (roles : List String) : Valid roles roles {} :=
  ⟨fun _ bound => bound, fun _ _ _ _ same => same⟩

theorem ProtocolContext.Valid.enter {rootRoles callerRoles : List String}
    {context : ProtocolContext} (valid : Valid rootRoles callerRoles context)
    {signature : ProtocolSignature} {indices : List Nat}
    (substitution : ValidSubstitution callerRoles signature indices) (site : String) :
    Valid rootRoles signature.roles (context.enter site indices) := by
  rcases substitution with ⟨length, bounded, distinct⟩
  have indexBound : ∀ role, role < signature.roles.length → role < indices.length := by
    intro role bound
    simpa [length] using bound
  have mappedBound : ∀ role, role < signature.roles.length →
      roleSubstitution indices role < callerRoles.length := by
    intro role bound
    rw [roleSubstitution_get indices role (indexBound role bound)]
    exact bounded _ (List.getElem_mem _)
  constructor
  · intro role bound
    exact valid.1 _ (mappedBound role bound)
  · intro left leftBound right rightBound same
    have equal := valid.2 _ (mappedBound left leftBound) _ (mappedBound right rightBound) same
    rw [roleSubstitution_get indices left (indexBound left leftBound),
      roleSubstitution_get indices right (indexBound right rightBound)] at equal
    exact (List.Nodup.getElem_inj distinct).mp equal

end Zkc.Source.Structured
