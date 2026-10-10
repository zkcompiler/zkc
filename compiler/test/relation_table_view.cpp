// Derived facts, exact layout and preflight of one bundle table viewed
// through the installed relation.table_rows kernel, and the static premises
// of the polynomial table kernels. The actual recurrence bundle fixture and
// separately authored finite and cyclic bundles are exercised; evaluation
// itself belongs to the native runtime and backend.
#include "support/NativeCases.h"
#include "zkc/Relation/BundlePolynomial.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include <string>

using namespace llvm;
using namespace zkc::relation;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;

namespace {
const std::string KB = "koala-bear", EXT = "koala-bear.ext8-binomial3";
std::string fixtureDirectory;

std::string read(StringRef name) {
  auto buffer = MemoryBuffer::getFile(fixtureDirectory + "/" + name.str());
  require(bool(buffer), "fixture " + name + " is unreadable");
  return (*buffer)->getBuffer().str();
}
Bundle bundle(StringRef text) { return take(readBundleText(text)); }
json::Value carrier(StringRef text) { return take(readBundleDataJson(text)); }
Expected<bool> accepted(Error error) {
  if (error)
    return std::move(error);
  return true;
}

/// One finite table with a public slot and a two-column witness: first,
/// last, interior, interval and all scopes, and a product with zero over a
/// next-row read whose window is undefined on short tables.
std::string finite() {
  return R"(["zkc.relation-bundle/0",[["p","koala-bear"]],[],
    [["t","required",["instance",1,8,false],"finite",
      [["w","witness","koala-bear",2]],
      ["zkc.ring/0",["koala-bear","koala-bear","koala-bear","koala-bear"],
       [["input",0],["input",1],["neg",0],["add",1,2],["input",3],["neg",4],
        ["add",0,5],["input",2],["mul",7,7],["neg",7],["add",8,9],
        ["constant","koala-bear","0"],["mul",11,1]],
       [3,6,10,12,6]],
      [["read",0,"0",0],["read",0,"1",0],["read",0,"0",1],["public",0]],
      [[0,["interior",0,1]],[1,["first"]],[2,["all"]],[3,["interval",0,2]],
       [4,["last"]]],
      []]]])";
}
/// One cyclic fixed-height table with configuration, witness and public
/// groups, a wrapping next-row read and a negative-offset public read.
std::string cyclic(StringRef slotField = "",
                   StringRef groupField = "koala-bear") {
  std::string publics =
      slotField.empty() ? "[]" : "[[\"s\",\"" + slotField.str() + "\"]]";
  std::string arenaInputs = "[\"" + groupField.str() + "\",\"" +
                            groupField.str() + "\",\"" + groupField.str() +
                            "\",\"" + groupField.str() + "\"]";
  return "[\"zkc.relation-bundle/0\"," + publics + ",[]," +
         "[[\"c\",\"required\",[\"fixed\",4],\"cyclic\","
         "[[\"k\",\"config\",\"" +
         groupField.str() + "\",1],[\"x\",\"witness\",\"" + groupField.str() +
         "\",1],[\"q\",\"public\",\"" + groupField.str() +
         "\",2]],"
         "[\"zkc.ring/0\"," +
         arenaInputs +
         ",[[\"input\",0],[\"input\",1],[\"input\",2],[\"mul\",0,2],[\"neg\",3]"
         ","
         "[\"add\",1,4],[\"input\",3],[\"neg\",6],[\"add\",0,7]],[5,8]],"
         "[[\"read\",1,\"0\",0],[\"read\",1,\"1\",0],[\"read\",0,\"0\",0],"
         "[\"read\",2,\"-1\",1]],"
         "[[0,[\"all\"]],[1,[\"interior\",1,0]]],[]]]]";
}
std::string chain(unsigned length, StringRef height) {
  std::string nodes = "[[\"input\",0]";
  for (unsigned i = 0; i < length; ++i)
    nodes += ",[\"add\"," + std::to_string(i) + ",0]";
  nodes += "]";
  return "[\"zkc.relation-bundle/0\",[],[],[[\"t\",\"required\"," +
         height.str() +
         ",\"finite\",[[\"w\",\"witness\",\"koala-bear\",8]],[\"zkc.ring/0\","
         "[\"koala-bear\"]," +
         nodes + ",[" + std::to_string(length) +
         "]],[[\"read\",0,\"0\",0]],[[0,[\"all\"]]],[]]]]";
}
} // namespace

int main(int argc, char **argv) {
  require(argc == 2, "usage: relation_table_view FIXTURE_DIRECTORY");
  fixtureDirectory = argv[1];
  zkc::test::Cases cases;

  cases.run("recurrence fixture facts, lengths and layout", [] {
    auto recurrence = bundle(read("bundle.json"));
    auto view = take(bundleTableView(recurrence, 0, KB));
    require(view.table == 0 && view.field == KB && !view.optional &&
                view.height.authority == BundleHeightAuthority::Fixed &&
                view.height.min == 8 && view.height.max == 8 &&
                view.readModel == BundleReadModel::Cyclic,
            "recurrence table policy");
    require(view.publicSlots == 3 && view.witnessWidth == 4 &&
                view.configWidth == 1 && view.publicWidth == 0 &&
                view.assertions == 9 && view.degree == 3 &&
                view.coordinates == 1,
            "recurrence derived widths, count and degree");
    auto lengths = take(bundleTableLengths(recurrence, view, 8));
    require(lengths.witness == 32 && lengths.configuration == 8 &&
                lengths.publicData == 3 && lengths.results == 72,
            "recurrence lengths at the fixed height");
    for (uint32_t height : {0u, 7u, 16u})
      refuses(bundleTableLengths(recurrence, view, height), "bundle-height");
    refuses(bundleTableView(recurrence, 1, KB), "relation-table-index");
    refuses(bundleTableView(recurrence, 0, EXT), "relation-table-carrier");
    refuses(bundleTableView(recurrence, 0, "bls12-381.fr"),
            "relation-table-carrier");
    refuses(bundleTableView(recurrence, 0, "bls12-381.g1"),
            "relation-table-carrier");
    auto config = take(readBundleConfiguration(
        recurrence, carrier(read("bundle-configuration.json"))));
    auto instance = take(
        readBundleInstance(recurrence, carrier(read("bundle-instance.json"))));
    auto witness = take(
        readBundleWitness(recurrence, carrier(read("bundle-witness.json"))));
    auto sliced =
        take(sliceBundleTableData(recurrence, view, config, instance, witness));
    require(sliced.height == 8 && sliced.witness.size() == 32 &&
                sliced.configuration.size() == 8 &&
                sliced.publicData.size() == 3,
            "sliced recurrence lengths");
    require(sliced.witness[0] == "2" && sliced.witness[1] == "5" &&
                sliced.witness[4] == "5" && sliced.witness[31] == "965489560" &&
                sliced.configuration[0] == "3" &&
                sliced.configuration[7] == "101" &&
                sliced.publicData == BundleColumns{"2", "5", "965489560"},
            "sliced recurrence layout is row-major in declaration order");
    auto changed = witness;
    changed.tables[0]->front()[0] = "3";
    require(
        take(sliceBundleTableData(recurrence, view, config, instance, changed))
                .witness[0] == "3",
        "a changed trace cell changes the sliced witness");
    changed.tables[0]->front().push_back("0");
    refuses(sliceBundleTableData(recurrence, view, config, instance, changed),
            "bundle-group-shape");
    auto identity = instance;
    identity.relation = std::string(64, '0');
    refuses(sliceBundleTableData(recurrence, view, config, identity, witness),
            "bundle-relation");
  });

  cases.run("finite scopes, lengths and windows before evaluation", [] {
    auto b = bundle(finite());
    auto view = take(bundleTableView(b, 0, KB));
    require(view.readModel == BundleReadModel::Finite &&
                view.height.authority == BundleHeightAuthority::Instance &&
                view.height.min == 1 && view.height.max == 8 &&
                !view.height.powerOfTwo,
            "finite table policy");
    require(view.publicSlots == 1 && view.witnessWidth == 2 &&
                view.configWidth == 0 && view.publicWidth == 0 &&
                view.assertions == 5 && view.degree == 2,
            "finite derived facts");
    auto lengths = take(bundleTableLengths(b, view, 4));
    require(lengths.witness == 8 && lengths.configuration == 0 &&
                lengths.publicData == 1 && lengths.results == 20,
            "finite lengths at height 4");
    require(take(bundleTableLengths(b, view, 3)).results == 15,
            "finite lengths at height 3");
    // The product with zero still reads the next row: height 2 leaves row 1
    // of interval [0,2) without a next row, and height 1 cannot hold the
    // interval at all.
    refuses(bundleTableLengths(b, view, 2), "bundle-window");
    refuses(bundleTableLengths(b, view, 1), "bundle-scope-height");
    refuses(bundleTableLengths(b, view, 9), "bundle-height");
    refuses(bundleTableLengths(b, view, 0), "bundle-height");
    BundleConfiguration config;
    BundleInstance instance;
    BundleWitness witness;
    config.relation = instance.relation = witness.relation = b.identity().str();
    config.tables.push_back({std::nullopt, {}});
    instance.publics = {{"1"}};
    instance.tables.push_back({true, 3u, {}});
    witness.tables.push_back(
        std::vector<BundleColumns>{{"1", "0", "1", "1", "1", "0"}});
    auto sliced =
        take(sliceBundleTableData(b, view, config, instance, witness));
    require(sliced.height == 3 &&
                sliced.witness == BundleColumns{"1", "0", "1", "1", "1", "0"} &&
                sliced.configuration.empty() &&
                sliced.publicData == BundleColumns{"1"},
            "finite slice keeps rows in order after the public slots");
    instance.tables[0].height = 2;
    witness.tables[0] = std::vector<BundleColumns>{{"1", "0", "1", "1"}};
    refuses(sliceBundleTableData(b, view, config, instance, witness),
            "bundle-window");
  });

  cases.run("cyclic table with every authority", [] {
    auto b = bundle(cyclic());
    auto view = take(bundleTableView(b, 0, KB));
    require(view.readModel == BundleReadModel::Cyclic &&
                view.height.authority == BundleHeightAuthority::Fixed &&
                view.publicSlots == 0 && view.witnessWidth == 1 &&
                view.configWidth == 1 && view.publicWidth == 2 &&
                view.assertions == 2 && view.degree == 2,
            "cyclic derived facts");
    auto lengths = take(bundleTableLengths(b, view, 4));
    require(lengths.witness == 4 && lengths.configuration == 4 &&
                lengths.publicData == 8 && lengths.results == 8,
            "cyclic lengths");
    refuses(bundleTableLengths(b, view, 3), "bundle-height");
    BundleConfiguration config;
    BundleInstance instance;
    BundleWitness witness;
    config.relation = instance.relation = witness.relation = b.identity().str();
    config.tables.push_back({std::nullopt, {{"2", "2", "2", "2"}}});
    instance.tables.push_back(
        {true, std::nullopt, {{"0", "1", "0", "2", "0", "4", "0", "8"}}});
    witness.tables.push_back(std::vector<BundleColumns>{{"1", "2", "4", "8"}});
    auto sliced =
        take(sliceBundleTableData(b, view, config, instance, witness));
    require(sliced.witness == BundleColumns{"1", "2", "4", "8"} &&
                sliced.configuration == BundleColumns{"2", "2", "2", "2"} &&
                sliced.publicData ==
                    BundleColumns{"0", "1", "0", "2", "0", "4", "0", "8"},
            "cyclic slice separates authorities");
    witness.tables[0] = std::vector<BundleColumns>{};
    refuses(sliceBundleTableData(b, view, config, instance, witness),
            "bundle-group-count");
  });

  cases.run("carrier homogeneity and explicit embeddings", [] {
    auto mixedSlot = bundle(cyclic(EXT));
    refuses(bundleTableView(mixedSlot, 0, KB), "relation-table-carrier");
    refuses(bundleTableView(mixedSlot, 0, EXT), "relation-table-carrier");
    auto extension = bundle(cyclic("", EXT));
    auto view = take(bundleTableView(extension, 0, EXT));
    require(view.coordinates == 8 && view.publicWidth == 2,
            "extension carrier facts");
    require(take(bundleTableLengths(extension, view, 4)).publicData == 8,
            "lengths count elements, not coordinates");
    refuses(bundleTableView(extension, 0, KB), "relation-table-carrier");
    // A base constant reaches an extension output only through an explicit
    // embedding; the embedded node is admitted under the extension carrier.
    auto embedded = bundle(R"(["zkc.relation-bundle/0",[],[],
      [["e","required",["fixed",2],"finite",
        [["w","witness","koala-bear.ext8-binomial3",1]],
        ["zkc.ring/0",["koala-bear.ext8-binomial3"],
         [["input",0],["constant","koala-bear","3"],
          ["embed","koala-bear.ext8-binomial3",1],["neg",2],["add",0,3]],[4]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]])");
    auto embeddedView = take(bundleTableView(embedded, 0, EXT));
    require(embeddedView.degree == 1 && embeddedView.coordinates == 8,
            "embedded constant view");
    refuses(bundleTableView(embedded, 0, KB), "relation-table-carrier");
  });

  cases.run("optional tables are views only when present", [] {
    auto b = bundle(R"(["zkc.relation-bundle/0",[],[],
      [["o","optional",["instance",1,4,true],"finite",
        [["w","witness","koala-bear",1]],
        ["zkc.ring/0",["koala-bear"],[["input",0]],[0]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]])");
    auto view = take(bundleTableView(b, 0, KB));
    require(view.optional && view.height.powerOfTwo, "optional view facts");
    refuses(bundleTableLengths(b, view, 3), "bundle-height");
    require(take(bundleTableLengths(b, view, 4)).results == 4,
            "power-of-two height admitted");
    BundleConfiguration config;
    BundleInstance instance;
    BundleWitness witness;
    config.relation = instance.relation = witness.relation = b.identity().str();
    config.tables.push_back({std::nullopt, {}});
    instance.tables.push_back({false, std::nullopt, {}});
    witness.tables.push_back(std::nullopt);
    refuses(sliceBundleTableData(b, view, config, instance, witness),
            "relation-table-absent");
    instance.tables[0] = {true, 2u, {}};
    witness.tables[0] = std::vector<BundleColumns>{{"5", "6"}};
    require(
        take(sliceBundleTableData(b, view, config, instance, witness)).height ==
            2,
        "present optional table slices");
  });

  cases.run("declared bounds refuse before any length is compared", [] {
    auto wide = bundle(chain(1, "[\"instance\",1,1048576,false]"));
    auto view = take(bundleTableView(wide, 0, KB));
    require(take(bundleTableLengths(wide, view, 1024)).witness == 8192,
            "wide table within the data bound");
    refuses(bundleTableLengths(wide, view, 1048576), "bundle-data-limit");
    auto deep = bundle(chain(70, "[\"instance\",1,1048576,false]"));
    auto deepView = take(bundleTableView(deep, 0, KB));
    require(take(bundleTableLengths(deep, deepView, 1024)).results == 1024,
            "deep arena within the work bound");
    std::string outputs, assertions;
    for (unsigned i = 0; i < 4096; ++i) {
      outputs += (i ? ",0" : "0");
      assertions +=
          (i ? "," : "") + std::string("[") + std::to_string(i) + ",[\"all\"]]";
    }
    auto many = bundle("[\"zkc.relation-bundle/0\",[],[],[[\"t\",\"required\","
                       "[\"fixed\",512],\"finite\",[],[\"zkc.ring/0\",[],"
                       "[[\"constant\",\"koala-bear\",\"0\"]],[" +
                       outputs + "]],[],[" + assertions + "],[]]]]");
    auto manyView = take(bundleTableView(many, 0, KB));
    require(manyView.assertions == 4096 && manyView.degree == 0 &&
                manyView.witnessWidth == 0,
            "assertion-only table facts");
    refuses(bundleTableLengths(many, manyView, 512), "bundle-result-limit");
  });

  cases.run("work bound uses the reference formula", [] {
    // 2^20 rows over 71 nodes, one input and one assertion exceed 2^26 while
    // the single-column data stays within its bound.
    auto single = bundle(R"(["zkc.relation-bundle/0",[],[],
      [["t","required",["instance",1,1048576,false],"finite",
        [["w","witness","koala-bear",1]],
        ["zkc.ring/0",["koala-bear"],[["input",0],["add",0,0],["add",1,1],
         ["add",2,2],["add",3,3],["add",4,4],["add",5,5],["add",6,6],
         ["add",7,7],["add",8,8],["add",9,9],["add",10,10],["add",11,11],
         ["add",12,12],["add",13,13],["add",14,14],["add",15,15],
         ["add",16,16],["add",17,17],["add",18,18],["add",19,19],
         ["add",20,20],["add",21,21],["add",22,22],["add",23,23],
         ["add",24,24],["add",25,25],["add",26,26],["add",27,27],
         ["add",28,28],["add",29,29],["add",30,30],["add",31,31],
         ["add",32,32],["add",33,33],["add",34,34],["add",35,35],
         ["add",36,36],["add",37,37],["add",38,38],["add",39,39],
         ["add",40,40],["add",41,41],["add",42,42],["add",43,43],
         ["add",44,44],["add",45,45],["add",46,46],["add",47,47],
         ["add",48,48],["add",49,49],["add",50,50],["add",51,51],
         ["add",52,52],["add",53,53],["add",54,54],["add",55,55],
         ["add",56,56],["add",57,57],["add",58,58],["add",59,59],
         ["add",60,60],["add",61,61],["add",62,62],["add",63,63],
         ["add",64,64],["add",65,65],["add",66,66],["add",67,67],
         ["add",68,68],["add",69,69]],[70]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]])");
    auto singleView = take(bundleTableView(single, 0, KB));
    require(take(bundleTableLengths(single, singleView, 65536)).results ==
                65536,
            "work within the bound at 2^16 rows");
    refuses(bundleTableLengths(single, singleView, 1048576),
            "bundle-work-limit");
  });
  cases.run(
      "polynomial premises lift base tables and keep extensions exact", [] {
        auto recurrence = bundle(read("bundle.json"));
        for (StringRef field : {StringRef(KB), StringRef(EXT)})
          take(accepted(checkBundlePolynomialTable(recurrence, 0, field)));
        refuses(accepted(checkBundlePolynomialTable(recurrence, 1, EXT)),
                "relation-table-index");
        refuses(
            accepted(checkBundlePolynomialTable(recurrence, 0, "bls12-381.g1")),
            "relation-table-carrier");
        refuses(
            accepted(checkBundlePolynomialTable(recurrence, 0, "bls12-381.fr")),
            "relation-table-carrier");
        // A base-field slot or group is substituted in its extension; an
        // extension slot, group or arena is never narrowed.
        auto mixedSlot = bundle(cyclic(EXT));
        take(accepted(checkBundlePolynomialTable(mixedSlot, 0, EXT)));
        refuses(accepted(checkBundlePolynomialTable(mixedSlot, 0, KB)),
                "relation-table-carrier");
        auto extension = bundle(cyclic("", EXT));
        take(accepted(checkBundlePolynomialTable(extension, 0, EXT)));
        refuses(accepted(checkBundlePolynomialTable(extension, 0, KB)),
                "relation-table-carrier");
        auto embedded = bundle(R"(["zkc.relation-bundle/0",[],[],
      [["e","required",["fixed",2],"finite",
        [["w","witness","koala-bear",1]],
        ["zkc.ring/0",["koala-bear"],
         [["input",0],["embed","koala-bear.ext8-binomial3",0]],[1]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]])");
        take(accepted(checkBundlePolynomialTable(embedded, 0, EXT)));
        refuses(accepted(checkBundlePolynomialTable(embedded, 0, KB)),
                "relation-table-carrier");
        // An extension output used only by an interaction is not evaluated.
        auto interaction = bundle(R"(["zkc.relation-bundle/0",[],
      [["c","field-balance",["koala-bear.ext8-binomial3"],"koala-bear"]],
      [["i","required",["fixed",4],"finite",
        [["w","witness","koala-bear",2]],
        ["zkc.ring/0",["koala-bear","koala-bear"],
         [["input",0],["input",1],["embed","koala-bear.ext8-binomial3",1],
          ["constant","koala-bear","1"]],[0,2,3]],
        [["read",0,"0",0],["read",0,"0",1]],[[0,["all"]]],
        [["field-balance",0,["global"],["all"],[1],2,null]]]]])");
        take(accepted(checkBundlePolynomialTable(interaction, 0, KB)));
        take(accepted(checkBundlePolynomialTable(interaction, 0, EXT)));
        // Some power of two of at least 2 must satisfy the height policy.
        for (StringRef height :
             {R"(["fixed",1])", R"(["fixed",3])", R"(["instance",1,1,false])",
              R"(["instance",5,7,false])"})
          refuses(accepted(checkBundlePolynomialTable(bundle(chain(1, height)),
                                                      0, KB)),
                  "bundle-polynomial-two-adic");
        for (StringRef height : {R"(["fixed",2])", R"(["instance",1,2,false])",
                                 R"(["instance",5,8,false])"})
          take(accepted(
              checkBundlePolynomialTable(bundle(chain(1, height)), 0, KB)));
        // Each installed kernel keeps its own reference rule.
        refuses(accepted(checkBundleTableReference(
                    recurrence, "relation.table_rows", 0, EXT)),
                "relation-table-carrier");
        for (StringRef contract :
             {"relation.table_shape", "relation.table_input",
              "relation.table_scope", "relation.table_point",
              "relation.table_points"}) {
          take(accepted(
              checkBundleTableReference(recurrence, contract, 0, EXT)));
          refuses(accepted(checkBundleTableReference(
                      bundle(chain(1, R"(["fixed",3])")), contract, 0, KB)),
                  "bundle-polynomial-two-adic");
        }
        refuses(accepted(
                    checkBundleTableReference(recurrence, "ring.point", 0, KB)),
                "relation-table-contract");
      });
  cases.run(
      "interaction premises visit every output and policies need no domain",
      [] {
        // An Ext8 tuple output over KoalaBear columns: the assertion-only
        // polynomial admission lifts the table into KoalaBear, but the
        // whole-table admission of the interaction kernels does not.
        auto interaction = bundle(R"(["zkc.relation-bundle/0",[],
      [["c","field-balance",["koala-bear.ext8-binomial3"],"koala-bear"]],
      [["i","required",["fixed",4],"finite",
        [["w","witness","koala-bear",2]],
        ["zkc.ring/0",["koala-bear","koala-bear"],
         [["input",0],["input",1],["embed","koala-bear.ext8-binomial3",1],
          ["constant","koala-bear","1"]],[0,2,3]],
        [["read",0,"0",0],["read",0,"0",1]],[[0,["all"]]],
        [["field-balance",0,["global"],["all"],[1],2,null]]]]])");
        const StringRef interactionKernels[] = {"relation.table_interactions",
                                                "relation.table_interaction",
                                                "relation.table_record_points"};
        take(accepted(checkBundleTableReference(
            interaction, "relation.table_points", 0, KB)));
        refuses(admitBundleTableCarrier(interaction, 0, KB),
                "relation-table-carrier");
        for (StringRef contract : interactionKernels)
          refuses(
              accepted(checkBundleTableReference(interaction, contract, 0, KB)),
              "relation-table-carrier");
        refuses(accepted(checkBundleTableReference(
                    interaction, "relation.table_policy", 0, KB)),
                "relation-table-carrier");
        require(take(admitBundleTableCarrier(interaction, 0, EXT)) == 8,
                "an Ext8 carrier has eight base coordinates");
        for (StringRef contract : interactionKernels)
          take(accepted(
              checkBundleTableReference(interaction, contract, 0, EXT)));
        refuses(accepted(checkBundleTableReference(
                    interaction, "relation.table_policy", 1, EXT)),
                "relation-table-index");
        // Interaction metadata and substitution need no polynomial domain.
        for (StringRef height : {R"(["fixed",1])", R"(["fixed",12])",
                                 R"(["instance",5,7,false])"}) {
          auto table = bundle(chain(1, height));
          take(accepted(checkBundleTableReference(
              table, "relation.table_policy", 0, KB)));
          for (StringRef contract : interactionKernels)
            take(accepted(checkBundleTableReference(table, contract, 0, KB)));
        }
        auto recurrence = bundle(read("bundle.json"));
        for (StringRef field : {StringRef(KB), StringRef(EXT)}) {
          take(accepted(checkBundleTableReference(
              recurrence, "relation.table_policy", 0, field)));
          for (StringRef contract : interactionKernels)
            take(accepted(
                checkBundleTableReference(recurrence, contract, 0, field)));
        }
      });
  return cases.result();
}
