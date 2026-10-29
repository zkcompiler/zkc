#include <zkc/Syntax/Syntax.h>

int main() {
  auto source = zkc::source::Revision(
      {"m", "module m\ndef id(x:F)->F:\n    x\n", "consumer"});
  auto headers = zkc::syntax::parseHeaders(source);
  auto syntax = zkc::syntax::parseBodies(headers);
  auto formatted = zkc::syntax::format(syntax);
  return syntax.status() == zkc::syntax::Status::Complete && formatted.complete
             ? 0
             : 1;
}
