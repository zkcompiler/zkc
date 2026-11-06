module

public import ZkcSecurity.Transformations.FiatShamir.QueryTree
public import ZkcSecurity.Transformations.FiatShamir.QueryTreeSimulation
public import Zkc.Construction.OccurrenceResolution

@[expose] public section

/-! Authenticated scalar-tree keys in the existing typed transcript domain.
The root is the entire segment-entry history. A node records every earlier delivered scalar,
including duplicates. Occurrences use the existing coordinate constructor; nothing is inferred
from a service label. Source ancestry admission remains with OccurrenceResolution.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource
open Zkc.Source Zkc.Construction QueryTree

def decimalValue (digits : List Char) : Nat :=
  digits.foldl (fun value digit ↦ value * 10 + (digit.toNat - 48)) 0

private theorem decimalValue_digits (n : Nat) : decimalValue (Nat.toDigits 10 n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Nat.toDigits_eq_ite (by decide : 1 < 10)]
    split
    · rename_i small
      simp [decimalValue, Nat.toNat_digitChar_sub_48_of_lt_ten small]
    · rename_i large
      simp only [decimalValue, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show (Nat.toDigits 10 (n / 10)).foldl
        (fun value digit ↦ value * 10 + (digit.toNat - 48)) 0 = n / 10 from
          ih (n / 10) (Nat.div_lt_self (by omega) (by decide)),
        Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt _ (by decide))]
      omega

/-- The actual decimal coordinate spelling is injective, at every natural coordinate. -/
theorem coordinateString_injective : Function.Injective (toString : Nat → String) := by
  intro a b same
  have decoded := congrArg (fun text : String ↦ decimalValue text.toList) same
  simpa only [Nat.toString_eq_ofList_toDigits, String.toList_ofList,
    decimalValue_digits] using decoded

/-- Appending the varying innermost coordinate preserves every fixed outer coordinate. -/
theorem coordinateOrigin_injective (base : Origin) (outer : List Nat) :
    Function.Injective (fun ordinal ↦ Domain.atCoordinates base (outer ++ [ordinal])) := by
  intro a b same
  have fields := congrArg Origin.event same
  have nonempty (n : Nat) : (outer ++ [n]).isEmpty = false := by simp
  simp only [Domain.atCoordinates, nonempty, Bool.false_eq_true, ↓reduceIte,
    List.map_append, List.map_cons, List.map_nil] at fields
  have strings := List.append_cancel_left fields
  have last := List.append_cancel_left (List.cons.inj strings).2
  exact coordinateString_injective (List.singleton_inj.mp last)

/-- A local recipe for one scalar segment. These are exact source origins, not source laws.
The bound, nominal service/owner and sites are already inside the complete query origin.
`outer` is the reached enclosing coordinate vector; source routing separately authenticates it. -/
structure Segment where
  query : Origin
  delivery : Origin
  outer : List Nat

namespace Segment

def queryAt (segment : Segment) (ordinal : Nat) : Origin :=
  Domain.atCoordinates segment.query (segment.outer ++ [ordinal])

def deliveryAt (segment : Segment) (ordinal : Nat) : Origin :=
  Domain.atCoordinates segment.delivery (segment.outer ++ [ordinal])

theorem queryAt_injective (segment : Segment) : Function.Injective segment.queryAt :=
  coordinateOrigin_injective segment.query segment.outer

@[simp] theorem queryAt_request (segment : Segment) (ordinal : Nat) :
    (segment.queryAt ordinal).request = segment.query.request :=
  OccurrenceResolution.atCoordinates_request _ _

end Segment

/-- The complete response prefix of a finite node in the existing simulator. -/
def nodePrefix {Step : Type} : {height : Nat} → Node Step height → List Step
  | _ + 1, .inl _ => []
  | _ + 1, .inr (step, rest) => step :: nodePrefix rest

theorem prefix_injective {Step : Type} (height : Nat) :
    Function.Injective (@nodePrefix Step height) := by
  induction height with
  | zero => intro node; exact node.elim
  | succ height ih =>
    intro first second same
    cases first with
    | inl marker =>
      cases marker
      cases second with
      | inl marker => cases marker; rfl
      | inr pair => simp [nodePrefix] at same
    | inr pair =>
      rcases pair with ⟨step, rest⟩
      cases second with
      | inl marker => simp [nodePrefix] at same
      | inr pair =>
        rcases pair with ⟨other, tail⟩
        simp only [nodePrefix, List.cons.injEq] at same
        exact congrArg Sum.inr (Prod.ext same.1 (ih same.2))

/-- Only the finite scalar reply is a branch observation in this source recipe. The source
sends that exact value; any intervening additional observation requires a different recipe. -/
def events {carriers : Structured.Carriers} {bound : Nat} (segment : Segment) :
    Nat → List (Fin bound) → Domain.History carriers
  | _, [] => []
  | ordinal, position :: rest =>
      .challenge (segment.queryAt ordinal) ::
        .message (segment.deliveryAt ordinal) (.index position.val) ::
          events segment (ordinal + 1) rest

@[simp] theorem events_length {carriers : Structured.Carriers} {bound : Nat}
    (segment : Segment) (ordinal : Nat) (positions : List (Fin bound)) :
    (events (carriers := carriers) segment ordinal positions).length = 2 * positions.length := by
  induction positions generalizing ordinal with
  | nil => rfl
  | cons position rest ih => simp [events, ih]; omega

theorem events_injective {carriers : Structured.Carriers} {bound : Nat}
    (segment : Segment) (ordinal : Nat) :
    Function.Injective (events (carriers := carriers) (bound := bound) segment ordinal) := by
  intro first
  induction first generalizing ordinal with
  | nil => intro second same; cases second <;> simp_all [events]
  | cons position rest ih =>
    intro second same
    cases second with
    | nil => simp [events] at same
    | cons other tail =>
      have pair := (List.cons.inj (List.cons.inj same).2)
      have payload := (Domain.Event.message.inj pair.1).2
      have value := (Domain.Payload.mk_inj.mp payload)
      exact congrArg₂ List.cons (Fin.ext value) (ih _ pair.2)

/-- The kernel's actual key is the preceding history together with its full query origin. -/
abbrev Key (carriers : Structured.Carriers) := Domain.History carriers × Origin

/-- Every successor-key-relevant observation is retained in order. -/
def encode {carriers : Structured.Carriers} {bound height : Nat} (segment : Segment)
    (pair : Domain.History carriers × Node (Fin bound) height) : Key carriers :=
  (pair.1 ++ events segment 0 (nodePrefix pair.2), segment.queryAt (nodePrefix pair.2).length)

theorem encode_injective {carriers : Structured.Carriers} {bound height : Nat}
    (segment : Segment) : Function.Injective (@encode carriers bound height segment) := by
  intro first second same
  have depth := segment.queryAt_injective (congrArg Prod.snd same)
  have histories := congrArg Prod.fst same
  obtain ⟨root, suffix⟩ := List.append_inj' histories (by simp only [events_length, depth])
  exact Prod.ext root (prefix_injective height (events_injective segment 0 suffix))

private theorem prefix_lt {Step : Type} {height : Nat} (node : Node Step height) :
    (nodePrefix node).length < height := by
  induction height with
  | zero => exact node.elim
  | succ n ih =>
    cases node with
    | inl marker => simp [nodePrefix]
    | inr pair =>
      rcases pair with ⟨step, tail⟩
      exact Nat.succ_lt_succ (ih tail)

/-- Read exactly the two source observations made by one scalar delivery. -/
def readStep {carriers : Structured.Carriers} {bound : Nat} (segment : Segment)
    (ordinal : Nat) : Domain.Event carriers → Domain.Event carriers → Option (Fin bound)
  | .challenge query, .message delivery data =>
    if query = segment.queryAt ordinal ∧ delivery = segment.deliveryAt ordinal then do
      let n ← data.value .index
      if h : n < bound then some ⟨n, h⟩ else none
    else none
  | _, _ => none

private theorem readStep_iff {carriers : Structured.Carriers} {bound : Nat} (segment : Segment)
    (ordinal : Nat) (q m : Domain.Event carriers) (pos : Fin bound) :
    readStep segment ordinal q m = some pos ↔
      q = .challenge (segment.queryAt ordinal) ∧
      m = .message (segment.deliveryAt ordinal) (.index pos.val) := by
  constructor
  · intro ok
    cases q <;> cases m <;> simp only [readStep] at ok
    all_goals try cases ok
    split at ok
    · rename_i origins
      obtain ⟨n, data, decoded⟩ := Option.bind_eq_some_iff.mp ok
      split at decoded
      · cases Option.some.inj decoded
        rw [← Option.some.inj (Domain.Payload.ofValue_value data)]
        simp [origins.1, origins.2]
      · cases decoded
    · cases ok
  · rintro ⟨rfl, rfl⟩
    simp [readStep, Domain.Payload.value, pos.isLt]

def readNode {carriers : Structured.Carriers} {bound : Nat} (segment : Segment) :
    (height ordinal : Nat) → Domain.History carriers → Option (Node (Fin bound) height)
  | 0, _, _ => none
  | _ + 1, _, [] => some (.inl ())
  | _ + 1, _, [_] => none
  | h + 1, ordinal, q :: m :: tail => do
    let pos ← readStep segment ordinal q m
    let node ← readNode segment h (ordinal + 1) tail
    pure (.inr (pos, node))

private theorem readNode_iff {carriers : Structured.Carriers} {bound height : Nat}
    (segment : Segment) (ordinal : Nat) (history : Domain.History carriers)
    (node : Node (Fin bound) height) :
    readNode segment height ordinal history = some node ↔
      history = events segment ordinal (nodePrefix node) := by
  induction height generalizing history ordinal with
  | zero => exact node.elim
  | succ h ih =>
    cases node with
    | inl marker =>
      cases marker
      cases history with
      | nil => constructor <;> intro _ <;> rfl
      | cons q tail =>
        cases tail with
        | nil => simp [readNode, nodePrefix, events]
        | cons m rest =>
          constructor
          · intro ok
            obtain ⟨_, _, ok⟩ := Option.bind_eq_some_iff.mp ok
            obtain ⟨_, _, diff⟩ := Option.bind_eq_some_iff.mp ok
            cases diff
          · intro diff; cases diff
    | inr pair =>
      rcases pair with ⟨pos, tail⟩
      cases history with
      | nil => constructor <;> intro diff <;> cases diff
      | cons q rest =>
        cases rest with
        | nil => constructor <;> intro diff <;> cases diff
        | cons m rest =>
          constructor
          · intro ok
            obtain ⟨p, edge, ok⟩ := Option.bind_eq_some_iff.mp ok
            obtain ⟨t, decoded, eq⟩ := Option.bind_eq_some_iff.mp ok
            cases eq
            obtain ⟨rfl, rfl⟩ := (readStep_iff ..).mp edge
            rw [(ih _ _ _).mp decoded]
            rfl
          · intro eq
            rcases List.cons.inj eq with ⟨head, tailEq⟩
            rcases List.cons.inj tailEq with ⟨delivered, suffix⟩
            subst q; subst m; subst rest
            have edge := (readStep_iff (carriers := carriers) segment ordinal _ _ pos).mpr ⟨rfl, rfl⟩
            simp [readNode, edge, (ih _ _ tail).mpr rfl]


def depthOf (segment : Segment) (height : Nat) (origin : Origin) : Option Nat :=
  (List.range height).find? fun d => decide (segment.queryAt d = origin)

private theorem depthOf_at (segment : Segment) {d height : Nat} (lt : d < height) :
    depthOf segment height (segment.queryAt d) = some d := by
  have existsDepth : (depthOf segment height (segment.queryAt d)).isSome := by
    rw [depthOf, List.find?_isSome]
    exact ⟨d, List.mem_range.mpr lt, by simp⟩
  obtain ⟨actual, found⟩ := Option.isSome_iff_exists.mp existsDepth
  have accepted : decide (segment.queryAt actual = segment.queryAt d) = true :=
    List.find?_some (p := fun i => decide (segment.queryAt i = segment.queryAt d)) found
  have eq := segment.queryAt_injective (of_decide_eq_true accepted)
  simpa [eq] using found

/-- Decode the addressed depth and read only its delivered suffix. The arbitrary root is
retained opaquely, including nominal payloads. Work depends on the history and height,
independently of the number of nodes in the complete answer tree. -/
def parse {carriers : Structured.Carriers} {bound height : Nat} (segment : Segment)
    (key : Key carriers) : Option (Domain.History carriers × Node (Fin bound) height) := do
  let depth ← depthOf segment height key.2
  let cut := key.1.length - 2 * depth
  let node ← readNode segment height 0 (key.1.drop cut)
  if (nodePrefix node).length = depth then some (key.1.take cut, node) else none

theorem encode_parse {carriers : Structured.Carriers} {bound height : Nat}
    (segment : Segment) (key : Key carriers)
    (pair : Domain.History carriers × Node (Fin bound) height)
    (parsed : parse segment key = some pair) : encode segment pair = key := by
  obtain ⟨d, found, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨node, read, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed
  · rename_i depth
    cases Option.some.inj parsed
    apply Prod.ext
    · exact (congrArg (key.1.take (key.1.length - 2 * d) ++ ·)
        ((readNode_iff segment 0 _ node).mp read).symm).trans (List.take_append_drop ..)
    · have accepted : decide (segment.queryAt d = key.2) = true :=
        List.find?_some (p := fun i => decide (segment.queryAt i = key.2)) found
      exact (congrArg segment.queryAt depth).trans (of_decide_eq_true accepted)
  · cases parsed

theorem parse_encode {carriers : Structured.Carriers} {bound height : Nat}
    (segment : Segment) (pair : Domain.History carriers × Node (Fin bound) height) :
    parse segment (encode segment pair) = some pair := by
  rcases pair with ⟨root, node⟩
  have read := (readNode_iff (carriers := carriers) segment 0
    (events segment 0 (nodePrefix node)) node).mpr rfl
  simp [parse, encode, depthOf_at segment (prefix_lt node), events_length, read]

/-- Both directions are proved for the actual semantic key, not postulated in a profile. -/
def encoding {carriers : Structured.Carriers} (segment : Segment)
    (bound height : Nat) :
    KeyEncoding (Key carriers) (Domain.History carriers) (Node (Fin bound) height) :=
  ⟨encode segment, parse segment, parse_encode segment, encode_parse segment⟩

/-- The keyed FS oracle uses the history ending in the challenge occurrence. -/
def oracleKey {carriers : Structured.Carriers} (key : Key carriers) : Domain.History carriers :=
  key.1 ++ [.challenge key.2]

theorem oracleKey_injective {carriers : Structured.Carriers} :
    Function.Injective (@oracleKey carriers) := by
  intro first second same
  obtain ⟨history, event⟩ := List.append_inj' same rfl
  exact Prod.ext history (Domain.Event.challenge.inj (List.singleton_inj.mp event))

end ZkcSecurity.FiatShamir.QueryTreeSource
