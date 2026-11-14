import Zkc.Frontend

/-!
# `zkc-syntax bench`

Time and peak memory of reading, lexing, parsing and formatting one file. Each phase runs once
cold, in the order of the pipeline, then `repetitions` more times warm; the times reported are the
cold one and the minimum and median of the warm ones. The peak resident memory of a phase is
read from `/proc/self/status` (`VmHWM`) after the peak was reset to the current resident size
through `/proc/self/clear_refs`, on the cold run; it includes what the earlier phases left
resident, which is reported beside it.
-/

namespace Zkc.Tools.Frontend.Bench

open Zkc.Frontend.Syntax

inductive Phase where
  | lex
  | parse
  | all
  deriving BEq

/-- A field of `/proc/self/status`, in kibibytes; 0 where the file is not available. -/
def statusField (field : String) : IO Nat := do
  try
    let text ← IO.FS.readFile "/proc/self/status"
    for line in text.splitOn "\n" do
      if line.startsWith (field ++ ":") then
        let digits := (line.toList.drop (field.length + 1)).filter Char.isDigit
        return (String.ofList digits).toNat!
    return 0
  catch _ => return 0

def resetPeak : IO Unit := do
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()

def trimSpaces (text : String) : String :=
  let isSpace (c : Char) := c == ' ' || c == '\t'
  String.ofList ((text.toList.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- The model of the processor and the number of logical processors, from `/proc/cpuinfo`. -/
def machine : IO String := do
  try
    let text ← IO.FS.readFile "/proc/cpuinfo"
    let lines := text.splitOn "\n"
    let models := lines.filter (·.startsWith "model name")
    let model := match models.head? with
      | some line => trimSpaces (((line.splitOn ":").drop 1).foldl (· ++ ·) "")
      | none => "unknown processor"
    let memory ← try
        let info ← IO.FS.readFile "/proc/meminfo"
        let total := (info.splitOn "\n").find? (·.startsWith "MemTotal:")
        pure (match total with
          | some line =>
            let kib := (String.ofList ((line.toList.filter Char.isDigit))).toNat!
            s!", {kib / 1048576} GiB of memory"
          | none => "")
      catch _ => pure ""
    return s!"{model}, {models.length} logical processors{memory}"
  catch _ => return "unknown machine"

def milliseconds (nanos : Nat) : String :=
  let hundredths := nanos / 10000
  s!"{hundredths / 100}.{if hundredths % 100 < 10 then "0" else ""}{hundredths % 100}"

def mebibytes (kib : Nat) : String :=
  let tenths := kib * 10 / 1024
  s!"{tenths / 10}.{tenths % 10}"

def median (values : Array Nat) : Nat :=
  let sorted := values.qsort (· < ·)
  if sorted.isEmpty then 0 else sorted[sorted.size / 2]!

structure Measure where
  cold : Nat
  warm : Array Nat
  startKiB : Nat
  peakKiB : Nat

/-- Runs `action` once cold, measuring its peak, then `repetitions` times warm. -/
def measure {α : Type} (repetitions : Nat) (action : Nat → IO α) (use : α → IO Unit) :
    IO (α × Measure) := do
  let startKiB ← statusField "VmRSS"
  resetPeak
  let begin ← IO.monoNanosNow
  let result ← action 0
  let cold := (← IO.monoNanosNow) - begin
  use result
  let peakKiB ← statusField "VmHWM"
  let mut warm := #[]
  for i in [0:repetitions] do
    let begin ← IO.monoNanosNow
    let again ← action (i + 1)
    warm := warm.push ((← IO.monoNanosNow) - begin)
    use again
  return (result, { cold, warm, startKiB, peakKiB })

def report (name : String) (m : Measure) : String :=
  let warm := if m.warm.isEmpty then "-" else
    s!"{milliseconds (m.warm.foldl min m.warm[0]!)} / {milliseconds (median m.warm)}"
  s!"{name}: cold {milliseconds m.cold} ms, warm min / median {warm} ms, peak resident {mebibytes m.peakKiB} MiB (resident at start {mebibytes m.startKiB} MiB)"

def countLines (source : ByteArray) : Nat :=
  source.foldl (fun count b => if b == 10 then count + 1 else count) 0

def run (path : String) (phase : Phase) (repetitions : Nat) : IO UInt32 := do
  IO.println s!"machine: {← machine}"
  IO.println s!"toolchain: Lean {Lean.versionString}"
  let (source, readMeasure) ← measure repetitions (fun _ => IO.FS.readBinFile path)
    (fun _ => pure ())
  IO.println s!"file: {path}, {source.size} bytes, {countLines source} lines"
  IO.println s!"runs: one cold run, then {repetitions} warm runs of each phase"
  IO.println (report "read" readMeasure)
  -- the file name differs between runs so that no run reuses another's result
  let (lexed, lexMeasure) ← measure repetitions (fun i => pure (lex s!"{path}#{i}" source))
    (fun result => match result with
      | .ok value => if value.tokens.size == 0 then IO.println "no tokens" else pure ()
      | .error _ => pure ())
  match lexed with
  | .error error =>
    IO.eprintln s!"{path}: {error.render}"
    return 1
  | .ok tokens =>
    IO.println s!"tokens: {tokens.tokens.size}, comments: {tokens.comments.size}"
    IO.println (report "lex" lexMeasure)
    if phase == .lex then
      IO.println s!"process peak resident {mebibytes (← statusField "VmHWM")} MiB"
      return 0
    let (parsed, parseMeasure) ← measure repetitions (fun i => pure (parseLexed s!"{path}#{i}" tokens))
      (fun result => match result with
        | .ok value => if value.tree.items.size == 0 then IO.println "no items" else pure ()
        | .error _ => pure ())
    match parsed with
    | .error error =>
      IO.eprintln s!"{path}: {error.render}"
      return 1
    | .ok tree =>
      IO.println s!"items: {tree.tree.items.size}"
      IO.println (report "parse" parseMeasure)
      if phase == .parse then
        IO.println s!"process peak resident {mebibytes (← statusField "VmHWM")} MiB"
        return 0
      -- the input depends on the run, so that no run reuses another's result
      let (text, formatMeasure) ← measure repetitions
        (fun i => pure (formatSourceFile (if i == 999999999 then default else tree)))
        (fun text => if text.isEmpty then IO.println "empty" else pure ())
      IO.println s!"canonical text: {text.utf8ByteSize} bytes"
      IO.println (report "format" formatMeasure)
      IO.println s!"process peak resident {mebibytes (← statusField "VmHWM")} MiB"
      return 0

end Zkc.Tools.Frontend.Bench
