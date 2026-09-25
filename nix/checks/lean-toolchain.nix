{ runCommand, lean }:
runCommand "zkc-lean-toolchain-check" { nativeBuildInputs = [ lean ]; } ''
  cat > lakefile.toml <<'EOF'
  name = "native_probe"
  defaultTargets = ["native_probe"]
  [[lean_exe]]
  name = "native_probe"
  root = "Main"
  EOF
  cat > Main.lean <<'EOF'
  import Std
  def main : IO Unit := IO.println (toString (([1, 2, 3] : List Nat).foldl (· + ·) 0))
  EOF
  lake --no-cache build
  test "$(.lake/build/bin/native_probe)" = 6
  mkdir -p "$out"
  lean --version > "$out/version"
''
