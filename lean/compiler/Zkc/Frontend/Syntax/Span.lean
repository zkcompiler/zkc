module

@[expose] public section

set_option autoImplicit false

namespace Zkc.Frontend.Syntax

/-- A place in a source file. Lines and columns count from 1; a column counts characters
(Unicode scalar values), not bytes. The byte offset counts from 0. -/
structure Position where
  line : Nat
  column : Nat
  byte : Nat
  deriving Inhabited, BEq, Repr

/-- The extent of a node or token: the file, and the first position and the position just after
the last character. Stored flat, with 32-bit fields, so that a span is one small object. -/
structure Span where
  file : String
  startLine : UInt32
  startColumn : UInt32
  startByte : UInt32
  stopLine : UInt32
  stopColumn : UInt32
  stopByte : UInt32
  deriving Inhabited

namespace Span

def make (file : String) (start stop : Position) : Span :=
  { file
    startLine := start.line.toUInt32, startColumn := start.column.toUInt32
    startByte := start.byte.toUInt32
    stopLine := stop.line.toUInt32, stopColumn := stop.column.toUInt32
    stopByte := stop.byte.toUInt32 }

def start (span : Span) : Position :=
  { line := span.startLine.toNat, column := span.startColumn.toNat, byte := span.startByte.toNat }

def stop (span : Span) : Position :=
  { line := span.stopLine.toNat, column := span.stopColumn.toNat, byte := span.stopByte.toNat }

/-- The span from the start of `first` to the end of `last`. -/
def join (first last : Span) : Span :=
  { first with
    stopLine := last.stopLine, stopColumn := last.stopColumn, stopByte := last.stopByte }

/-- `line:column-line:column`, the form used by the tree dump. -/
def render (span : Span) : String :=
  s!"{span.startLine}:{span.startColumn}-{span.stopLine}:{span.stopColumn}"

end Span

end Zkc.Frontend.Syntax
