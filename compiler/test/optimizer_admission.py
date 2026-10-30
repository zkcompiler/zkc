"""Admission precedes generic transforms and replayed MLIR reproducer passes."""
from cases import case, counted
from commands import Commands
from tools import optimizer

commands = Commands()
source = r'''module @unit attributes {exec.computation} {
  func.func @main(%x: i1) -> i1 { return %x : i1 }
  func.func private @unused(%x: i1) -> i1 {
    %unused = builtin.unrealized_conversion_cast %x : i1 to i1
    return %x : i1
  }
}'''
resource = r'''
{-#
  external_resources: {
    mlir_reproducer: {
      pipeline: "builtin.module(symbol-dce)",
      disable_threading: true,
      verify_each: false
    }
  }
#-}
'''
with case("admission precedes symbol elimination with structural verification disabled"):
    commands.run([optimizer, "--verify-each=false", "--symbol-dce"],
                 stdin=source, refuses="mathematical-formation")
with case("admission precedes the upstream reproducer pipeline"):
    commands.run([optimizer, "--run-reproducer"], stdin=source + resource,
                 refuses="mathematical-formation")
with case("valid reproducer still executes the recorded passes"):
    valid = source.replace("    %unused = builtin.unrealized_conversion_cast %x : i1 to i1\n", "")
    output = commands.run([optimizer, "--run-reproducer"], stdin=valid + resource)
    assert "@main" in output and "@unused" not in output, output
counted()
