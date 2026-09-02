import M0.Encode

/-!
# The strict decoder

`docs-next/foundation/executable-foundations.md` Section 2.1: "A decoder
consumes exactly one value and requires byte-for-byte re-encoding equality.
Unknown tags, trailing bytes, invalid symbols, duplicate or unsorted fields,
overlong magnitudes, and length disagreement are malformed." The parser below
consumes exactly one value and returns the remainder; `decode` additionally
refuses a nonempty remainder, an input above the byte limit, and a value that
crosses any of the other three constitutional limits.

The parser is structurally recursive on a fuel argument that bounds the
nesting depth it will follow. `decode` supplies the constitutional root-zero
depth bound plus one, so fuel exhaustion and the depth limit coincide.
`M0.Theorems` proves that decoding inverts encoding on every well-formed
value within the limits; it does not prove the converse (that every accepted
input re-encodes to itself), which remains a stated next increment.
-/

namespace M0

/-- Take exactly `k` octets or refuse (truncation). -/
def readOctets (k : Nat) (bs : List Octet) : Option (List Octet × List Octet) :=
  if k ≤ bs.length then some (bs.take k, bs.drop k) else none

/-- Read one `u64`. -/
def readU64 (bs : List Octet) : Option (Nat × List Octet) :=
  match readOctets 8 bs with
  | some (ds, rest) => some (fromBE ds, rest)
  | none => none

/-- Read one framed body `F(x)`; length disagreement is truncation. -/
def readFrame (bs : List Octet) : Option (List Octet × List Octet) :=
  match readU64 bs with
  | some (n, rest) => readOctets n rest
  | none => none

/-- A minimal magnitude: nonempty, and without a leading zero octet unless it
is the single octet zero. -/
def minimalMagnitude : List Octet → Bool
  | [] => false
  | [_] => true
  | d :: _ :: _ => d != 0

/-- The value of a framed magnitude, refusing an overlong one. -/
def magnitudeValue (ds : List Octet) : Option Nat :=
  if minimalMagnitude ds then some (fromBE ds) else none

/-- A valid symbol body: nonempty printable ASCII. -/
def validSymbol (s : List Octet) : Bool := !s.isEmpty && s.all symbolOctet

/-- Parse `k` framed children with the child parser `p`, requiring each frame
to be consumed exactly. -/
def parseFramed (p : List Octet → Option (Datum × List Octet)) :
    Nat → List Octet → Option (List Datum × List Octet)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    match readFrame bs with
    | none => none
    | some (body, rest) =>
      match p body with
      | none => none
      | some (x, tail) =>
        if tail.isEmpty then
          match parseFramed p k rest with
          | none => none
          | some (xs, rest) => some (x :: xs, rest)
        else none

/-- Parse `k` record fields, each `u64(ordinal) || F(M(value))`, requiring
strictly increasing ordinals after `previous`. -/
def parseFields (p : List Octet → Option (Datum × List Octet)) :
    Nat → Option Nat → List Octet → Option (List (Nat × Datum) × List Octet)
  | 0, _, bs => some ([], bs)
  | k + 1, previous, bs =>
    match readU64 bs with
    | none => none
    | some (o, rest) =>
      if previous.all (· < o) then
        match readFrame rest with
        | none => none
        | some (body, rest) =>
          match p body with
          | none => none
          | some (x, tail) =>
            if tail.isEmpty then
              match parseFields p k (some o) rest with
              | none => none
              | some (fs, rest) => some ((o, x) :: fs, rest)
            else none
      else none

/-- Parse one value, returning the remainder. -/
def parse : Nat → List Octet → Option (Datum × List Octet)
  | 0, _ => none
  | fuel + 1, bs =>
    match bs with
    | 0x00 :: rest => some (.unit, rest)
    | 0x01 :: rest => some (.bool false, rest)
    | 0x02 :: rest => some (.bool true, rest)
    | 0x03 :: rest =>
      match readFrame rest with
      | none => none
      | some (m, rest) =>
        match magnitudeValue m with
        | none => none
        | some n => some (.nat n, rest)
    | 0x04 :: s :: rest =>
      match readFrame rest with
      | none => none
      | some (m, rest) =>
        match magnitudeValue m with
        | none => none
        | some n =>
          if s = 0 then some (.int n, rest)
          else if s = 1 then (if n = 0 then none else some (.int (-n), rest))
          else none
    | 0x05 :: rest =>
      match readFrame rest with
      | none => none
      | some (b, rest) => some (.bytes b, rest)
    | 0x06 :: rest =>
      match readFrame rest with
      | none => none
      | some (s, rest) => if validSymbol s then some (.symbol s, rest) else none
    | 0x07 :: rest =>
      match readU64 rest with
      | none => none
      | some (k, rest) =>
        match parseFramed (parse fuel) k rest with
        | none => none
        | some (xs, rest) => some (.seq xs, rest)
    | 0x08 :: rest =>
      match readU64 rest with
      | none => none
      | some (k, rest) =>
        match parseFields (parse fuel) k none rest with
        | none => none
        | some (fs, rest) => some (.record fs, rest)
    | 0x09 :: rest =>
      match readU64 rest with
      | none => none
      | some (c, rest) =>
        match readFrame rest with
        | none => none
        | some (body, rest) =>
          match parse fuel body with
          | none => none
          | some (p, tail) => if tail.isEmpty then some (.variant c p, rest) else none
    | _ => none

/-- The strict decoder: exactly one value, no trailing octets, within the
constitutional limits. The fuel is the depth limit plus one, so a value deeper
than `maxRootZeroDepth` is refused by fuel exhaustion. -/
def decode (bs : List Octet) : Option Datum :=
  if bs.length ≤ maxCanonicalBytes then
    match parse (maxRootZeroDepth + 1) bs with
    | none => none
    | some (d, rest) => if rest.isEmpty && withinLimits d then some d else none
  else none

end M0
