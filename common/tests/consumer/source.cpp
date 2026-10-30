#include <zkc/Source/Names.h>
#include <zkc/Source/Source.h>

int main() {
  zkc::source::Revision source({"m", "α😀\r\nx", "consumer"});
  auto offset = source.offset({0, 3}, zkc::source::PositionEncoding::UTF16);
  return offset && *offset == 6 && zkc::source::isSourceIdentifier("α") ? 0 : 1;
}
