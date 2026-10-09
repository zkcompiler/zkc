#include "../Support/Input.h"
#include "Language.h"
#include "zkc/Compiler/AssetSharing.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
int zkc::runAssetSharing(int argc, char **argv) {
  auto refuse = [](Error failure) {
    errs() << toString(std::move(failure)) << '\n';
    return 1;
  };
  if (argc != 4)
    return refuse(
        error("asset-sharing-command", "expected asset-share FORMAT FILE"));
  StringRef format(argv[2]);
  if (format != "ring-json" && format != "relation-bundle-json")
    return refuse(error("asset-sharing-kind"));
  auto bytes = readInput(argv[3], ring::Limits::bytes);
  if (!bytes)
    return refuse(bytes.takeError());
  auto asset = language::Asset::read({"input", format.str(), *bytes, argv[3]});
  if (!asset)
    return refuse(asset.takeError());
  auto shared = language::shareAsset(*asset);
  if (!shared)
    return refuse(shared.takeError());
  outs() << printJson(shared->asset.encode());
  return 0;
}
