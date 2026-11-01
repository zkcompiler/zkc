import Tests.RepeatOccurrences

/-! Executable driver for the generated repeat-occurrence controls. Keeping the
entry outside the imported fixture prevents global `main` declaration collisions. -/
def main (args : List String) : IO Unit :=
  Tests.RepeatOccurrences.checkGenerated args
