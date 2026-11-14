module

public import Std.Data.HashMap
public import Zkc.Frontend.Syntax.UnicodeData

@[expose] public section

set_option autoImplicit false

/-!
# Unicode properties for the lexer

XID_Start and XID_Continue decide identifiers (LX6); the blocks of mathematical symbols are never
identifier characters (LX6, LX10); and a text must be in Normalization Form C (LX1). The data
are the generated tables of `UnicodeData`, read once.
-/

namespace Zkc.Frontend.Syntax.Unicode

open UnicodeData

def hexValue (text : String) : UInt32 :=
  text.foldl (fun acc c =>
    let digit :=
      if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
      else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else c.toNat - 'a'.toNat + 10
    acc * 16 + digit.toUInt32) 0

def words (text : String) : List String :=
  (text.splitOn " ").filter (· ≠ "")

/-- Parses `A-B` or `A` into a range. -/
def parseRange (word : String) : UInt32 × UInt32 :=
  match word.splitOn "-" with
  | [a, b] => (hexValue a, hexValue b)
  | _ => (hexValue word, hexValue word)

def parseRanges (text : String) : Array (UInt32 × UInt32) :=
  (words text).toArray.map parseRange

/-- Whether `code` is in one of the sorted, disjoint `ranges`. -/
def inRanges (ranges : Array (UInt32 × UInt32)) (code : UInt32) : Bool := Id.run do
  let mut low := 0
  let mut high := ranges.size
  while low < high do
    let middle := (low + high) / 2
    let (first, last) := ranges[middle]!
    if code < first then high := middle
    else if last < code then low := middle + 1
    else return true
  return false

def xidStartRanges : Array (UInt32 × UInt32) := parseRanges xidStart
def xidContinueRanges : Array (UInt32 × UInt32) := parseRanges xidContinue
def notInNfcRanges : Array (UInt32 × UInt32) := parseRanges notInNfc

/-- Combining classes: the ranges, and the class of each. -/
def combiningClassTable : Array (UInt32 × UInt32 × UInt8) :=
  (words combiningClasses).toArray.map fun word =>
    match word.splitOn ":" with
    | [range, value] =>
      let (first, last) := parseRange range
      (first, last, value.toNat!.toUInt8)
    | _ => (0, 0, 0)

def decompositionTable : Std.HashMap UInt32 (Array UInt32) :=
  (words decompositions).foldl (init := {}) fun table word =>
    match word.splitOn ">" with
    | [code, parts] => table.insert (hexValue code) ((parts.splitOn ".").toArray.map hexValue)
    | _ => table

def compositionTable : Std.HashMap (UInt32 × UInt32) UInt32 :=
  (words compositions).foldl (init := {}) fun table word =>
    match word.splitOn ">" with
    | [pair, composite] =>
      match pair.splitOn "." with
      | [first, second] => table.insert (hexValue first, hexValue second) (hexValue composite)
      | _ => table
    | _ => table

/-- The second characters of the primary compositions: a text holding one needs the full test
(the property NFC_Quick_Check = Maybe). -/
def composingSeconds : Std.HashMap UInt32 Unit :=
  compositionTable.fold (init := {}) fun set (_, second) _ => set.insert second ()

/-- Whether a character can compose with what precedes it (NFC_Quick_Check = Maybe): the second
character of a primary composition, or a Hangul vowel or trailing consonant. -/
def mayCompose (code : UInt32) : Bool :=
  (0x1161 ≤ code ∧ code ≤ 0x1175) ∨ (0x11A8 ≤ code ∧ code ≤ 0x11C2) ∨ composingSeconds.contains code

def isXidStart (code : UInt32) : Bool :=
  if code < 0x80 then
    (0x41 ≤ code ∧ code ≤ 0x5A) ∨ (0x61 ≤ code ∧ code ≤ 0x7A)
  else inRanges xidStartRanges code

def isXidContinue (code : UInt32) : Bool :=
  if code < 0x80 then
    (0x41 ≤ code ∧ code ≤ 0x5A) ∨ (0x61 ≤ code ∧ code ≤ 0x7A) ∨ (0x30 ≤ code ∧ code ≤ 0x39)
      ∨ code = 0x5F
  else inRanges xidContinueRanges code

/-- The blocks Mathematical Operators, Supplemental Mathematical Operators, and Miscellaneous
Mathematical Symbols A and B (LX6). -/
def isMathematicalSymbol (code : UInt32) : Bool :=
  (0x2200 ≤ code ∧ code ≤ 0x22FF) ∨ (0x2A00 ≤ code ∧ code ≤ 0x2AFF)
    ∨ (0x27C0 ≤ code ∧ code ≤ 0x27EF) ∨ (0x2980 ≤ code ∧ code ≤ 0x29FF)

def combiningClass (code : UInt32) : UInt8 := Id.run do
  if code < 0x300 then return 0
  let table := combiningClassTable
  let mut low := 0
  let mut high := table.size
  while low < high do
    let middle := (low + high) / 2
    let (first, last, value) := table[middle]!
    if code < first then high := middle
    else if last < code then low := middle + 1
    else return value
  return 0

def hangulFirst : UInt32 := 0xAC00
def leadFirst : UInt32 := 0x1100
def vowelFirst : UInt32 := 0x1161
def trailFirst : UInt32 := 0x11A7
def vowelCount : UInt32 := 21
def trailCount : UInt32 := 28
def syllableCount : UInt32 := 11172

/-- The full canonical decomposition of one character. -/
def decompose (code : UInt32) : Array UInt32 :=
  if hangulFirst ≤ code ∧ code < hangulFirst + syllableCount then
    let index := code - hangulFirst
    let lead := leadFirst + index / (vowelCount * trailCount)
    let vowel := vowelFirst + (index % (vowelCount * trailCount)) / trailCount
    let trail := trailFirst + index % trailCount
    if trail == trailFirst then #[lead, vowel] else #[lead, vowel, trail]
  else
    match decompositionTable[code]? with
    | some parts => parts
    | none => #[code]

/-- Sorts each run of non-starters by combining class, keeping the order of equal classes. -/
def canonicalOrder (codes : Array UInt32) : Array UInt32 := Id.run do
  let mut out := codes
  -- insertion sort within runs; runs are short
  for i in [1:out.size] do
    let mut j := i
    while 0 < j do
      let current := combiningClass out[j]!
      let previous := combiningClass out[j - 1]!
      if current != 0 ∧ previous > current then
        out := out.swapIfInBounds j (j - 1)
        j := j - 1
      else
        j := 0
  return out

def composePair (first second : UInt32) : Option UInt32 :=
  if leadFirst ≤ first ∧ first < leadFirst + 19 ∧ vowelFirst ≤ second ∧ second < vowelFirst + vowelCount then
    some (hangulFirst + ((first - leadFirst) * vowelCount + (second - vowelFirst)) * trailCount)
  else if hangulFirst ≤ first ∧ first < hangulFirst + syllableCount ∧ (first - hangulFirst) % trailCount == 0
      ∧ trailFirst < second ∧ second < trailFirst + trailCount then
    some (first + (second - trailFirst))
  else compositionTable[(first, second)]?

/-- Canonical composition of a canonically ordered decomposition (UAX #15). -/
def compose (codes : Array UInt32) : Array UInt32 := Id.run do
  if codes.isEmpty then return codes
  let mut out : Array UInt32 := #[]
  -- the position of the last starter, and the class of the last character kept after it
  let mut starter : Option Nat := none
  let mut lastClass : Option UInt8 := none
  for code in codes do
    let cls := combiningClass code
    let composite := match starter with
      | some index =>
        let blocked : Bool := match lastClass with
          | some previous => decide (previous ≥ cls)
          | none => false
        if blocked then none else (composePair out[index]! code).map (index, ·)
      | none => none
    match composite with
    | some (index, value) => out := out.set! index value
    | none =>
      if cls == 0 then
        starter := some out.size
        lastClass := none
      else
        lastClass := some cls
      out := out.push code
  return out

/-- Whether a text, given as its code points, is in Normalization Form C. A text in which every
character may occur in NFC, no character can compose with what precedes it, and the combining
classes are in order is in NFC; any other text is normalized and compared. -/
def isNfc (codes : Array UInt32) : Bool := Id.run do
  let mut needsFullTest := false
  let mut lastClass : UInt8 := 0
  for code in codes do
    if code < 0x300 then
      lastClass := 0
    else
      if inRanges notInNfcRanges code then return false
      let cls := combiningClass code
      if cls != 0 ∧ lastClass > cls then needsFullTest := true
      if mayCompose code then needsFullTest := true
      lastClass := cls
  if !needsFullTest then return true
  let decomposed := codes.foldl (fun acc code => acc ++ decompose code) #[]
  return compose (canonicalOrder decomposed) == codes

end Zkc.Frontend.Syntax.Unicode
