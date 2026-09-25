#!/usr/bin/env python3
"""Check package pins, architectural imports and module naming.

Lean's separate declaration audit checks types, proof bodies and axioms.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path
import re

# The package directory, which is no longer this file's own now that the
# checks sit together: support/ is beside formal/, not beside this.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.lean_headers import HeaderParser  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
INTEGRATION = ROOT / "integrations/arklib"
BOUNDARIES = {
    "family_and_iteration_realization": {
        "roots": ["Zkc.Realization.Family", "Zkc.Realization.Iteration"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compiler", "Zkc.Protocols", "ZkcArkLib", "Tests", "Examples", "Tools"],
    },
    "participant_projection": {
        "roots": ["Zkc.Compiler.Participant.Execution", "Zkc.Compiler.Participant.Counts",
                  "Zkc.Compiler.Role.Counts"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Protocols", "ZkcArkLib", "Tests", "Examples", "Tools"],
    },
    "source_definitions": {
        "roots": ["Zkc.Source.DefinitionRenaming", "Zkc.Source.LocatedExecution",
                  "Zkc.Source.ControlAgreement", "Zkc.Source.Protocol.Execution",
                  "Zkc.Source.Family", "Zkc.Source.Protocol.Family"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compiler", "Zkc.Protocols", "ZkcArkLib", "Tests", "Examples", "Tools"],
    },
    "factor_semantic_contracts": {
        "roots": ["Zkc.Modules.Factor", "Zkc.Modules.FactorState",
                  "Zkc.Modules.FactorExecution", "Zkc.Modules.FactorBinding",
                  "Zkc.Modules.FreshAllocation", "Zkc.Modules.PolynomialPreparation",
                  "Zkc.Source.FactorQueries", "Zkc.Source.FactorInputs"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compiler", "Zkc.Protocols", "ZkcArkLib", "Tests", "Examples", "Tools"],
    },
    "json_arrays": {
        "roots": ["Zkc.Realization.JsonArrays"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "ZkcArkLib", "Tests", "TestsArkLib"],
    },
    "structural_readback": {
        "roots": ["Zkc.Compiler.Readback.Compilation"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "ZkcArkLib", "Tests", "TestsArkLib"],
    },
    "bytecode_endpoints": {
        "roots": ["Zkc.Protocols.ScalarBytecode.Endpoint.Frames", "Zkc.Protocols.ScalarBytecode.ReadPackets", "Zkc.Protocols.ScalarBytecode.Suppliers.Causality"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Protocols.ScalarBytecode.Schedules", "Zkc.Protocols.ScalarBytecode.Horner", "Zkc.Protocols.ScalarBytecode.StreamingFamily", "Tests", "TestsArkLib"],
    },
    "bytecode_execution": {
        "roots": ["Zkc.Protocols.ScalarBytecode.Execution", "Zkc.Protocols.ScalarBytecode.Frames", "Zkc.Protocols.ScalarBytecode.MessageEvaluation.Composition"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Tests", "TestsArkLib"],
    },
    "public_dimensions": {
        "roots": ["Zkc.Source.PublicDimensions", "Zkc.Protocols.AlgebraicRounds.ParameterFamily"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Protocols.ScalarBytecode", "Tests"],
    },
    "scalar_codec_and_prover": {
        "roots": ["Zkc.Protocols.ScalarBytecode.ProverCorrespondence", "Zkc.Protocols.ScalarBytecode.Certificates"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Tests", "TestsArkLib"],
    },
    "public_shape_and_local_code": {
        "roots": ["Zkc.Source.MessageSchema", "Zkc.Compiler.Arithmetic.Dag", "Zkc.Transformations.EncodingReuse"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Protocols", "Tests"],
    },
    "external_free_programs": {
        "roots": ["ZkcArkLib.PolyFun.Blocks", "ZkcArkLib.PolyFun.Failure"],
        "external": ["Init", "Lean", "Std", "Mathlib", "PolyFun"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "ZkcArkLib.Sumcheck", "Tests", "TestsArkLib"],
    },
    "table_preparation": {
        "roots": ["Zkc.Source.TablePreparation"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Protocols", "Zkc.Polynomial", "Tests"],
    },
    "bilinear_preparation": {
        "roots": ["Zkc.Polynomial.Bilinear.Compilation"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Protocols", "Tests"],
    },
    "commitment_sessions": {
        "roots": ["Zkc.Protocols.CommitmentSessions.Source"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Polynomial", "Tests"],
    },
    "execution_representations": {
        "roots": ["Zkc.Realization.InstructionSimulation", "Zkc.Realization.InstructionComposition", "Zkc.Realization.ByteEncoding", "Zkc.Semantics.OperationContract", "Zkc.Semantics.Locality"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "scalar_rounds": {
        "roots": ["Zkc.Protocols.AlgebraicRounds.EarlySource", "Zkc.Protocols.AlgebraicRounds.BlockTemplates", "Zkc.Protocols.Sumcheck.ProductFamily.Wire"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Examples", "Tests"],
    },
    "captured_programs": {
        "roots": ["Zkc.Protocols.CapturedPrograms.Probability", "Zkc.Protocols.CorrelatedSetup.Communication"],
        "external": ["Init", "Lean", "Std", "Mathlib", "Aesop"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Examples", "Tests"],
    },
    "local_prover": {
        "roots": ["Zkc.Protocols.Sumcheck.LocalProver.Admission", "Zkc.Source.Frontend"],
        "external": ["Init", "Lean", "Std", "Mathlib", "Aesop"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Examples", "Tests"],
    },
    "bounded_cache": {
        "roots": ["Zkc.Modules.BoundedCache"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "Zkc.Compiler", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "block_compiler": {
        "roots": ["Zkc.Compiler.Blocks.StateRefinement", "Zkc.Compiler.Blocks.BoundedCache"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "bound_inputs": {
        "roots": ["Zkc.Source.Elaboration"],
        "external": ["Init", "Lean", "Std", "Mathlib", "Aesop"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "factor_allocation": {
        "roots": ["Zkc.Modules.FreshAllocation", "Zkc.Polynomial.Factors"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "sumcheck": {
        "roots": ["Zkc.Protocols.Sumcheck.Security", "Zkc.Protocols.Sumcheck.Admission",
                  "Zkc.Protocols.Sumcheck.Optimization", "Zkc.Protocols.Sumcheck.Framed",
                  "Zkc.Protocols.Sumcheck.Endpoints.Composition"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Examples", "Tests"],
    },
    "probability": {
        "roots": ["Zkc.Probability.FramedMask", "Zkc.Probability.AdaptiveTape",
                  "Zkc.Probability.AffineMask", "Zkc.Probability.UniformTape",
                  "Zkc.Probability.FiniteKernel", "Zkc.Probability.ProductTape",
                  "Zkc.Probability.ConditionalTape", "Zkc.Probability.Concentration",
                  "Zkc.Probability.FiniteDomain", "Zkc.Probability.Disclosure"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Source", "Zkc.Compiler",
                      "Zkc.Examples", "Tests"],
    },
    "embedded_roots": {
        "roots": ["Zkc.Polynomial.EmbeddedRoots", "Zkc.Protocols.Sumcheck.ProductFamily.OneRound"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Zkc.Examples", "Tests"],
    },
    "correlated_preparation": {
        "roots": ["Zkc.Protocols.CorrelatedSetup.Preparation"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Examples", "Tests"],
    },
    "factor_compiler": {
        "roots": ["Zkc.Compiler.FactorOptimization",
                  "Zkc.Compiler.FactorOptimization.Size"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "polynomial_preparation": {
        "roots": ["Zkc.Modules.PolynomialPreparation"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "immutable_operations": {
        "roots": ["Zkc.Modules.ImmutableCache", "Zkc.Transformations.Memoization",
                  "Zkc.Modules.Preparation", "Zkc.Semantics.Preparation"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "foundation": {
        "roots": ["Zkc", "Tests.FoundationAudit"],
        "external": ["Init", "Lean", "Std"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples"],
    },
    "compiler": {
        "roots": ["Zkc.Compiler.ArtifactFormat", "Zkc.Compiler.Admission",
                  "Zkc.Compiler.Arithmetic.Horner"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Protocols", "Zkc.Examples", "Tests"],
    },
    "algebraic_rounds": {
        "roots": ["Zkc.Protocols.AlgebraicRounds.Framed",
                  "Zkc.Protocols.AlgebraicRounds.Endpoints"],
        "external": ["Init", "Lean", "Std", "Mathlib"],
        "forbidden": ["Zkc.Compat", "Zkc.Examples", "Tests"],
    },
}


def check_boundary(name, boundary, parser):
    pending = list(boundary["roots"])
    sources = {}
    external = set()
    while pending:
        module = pending.pop()
        if module in sources:
            continue
        if any(module == prefix or module.startswith(prefix + ".")
               for prefix in boundary["forbidden"]):
            raise ValueError(f"{name}: forbidden dependency {module}")
        family = module.split(".")[0]
        if family not in {"Zkc", "Tests", "ZkcArkLib", "TestsArkLib", "Examples", "Tools"}:
            if family not in boundary["external"]:
                raise ValueError(f"{name}: undeclared external dependency {module}")
            external.add(family)
            continue
        root = INTEGRATION if family in {"ZkcArkLib", "TestsArkLib"} else ROOT
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        data = path.read_bytes()
        source = data.decode()
        namespaces = re.findall(r"^namespace\s+(\S+)", source, re.M)
        if any(re.match(r"[A-Z]\d", part)
               for namespace in namespaces for part in namespace.split(".")):
            raise ValueError(f"{name}: numbered namespace in {module}")
        sources[module] = hashlib.sha256(data).hexdigest()
        pending.extend(parser.imports(source, path))
    return {"roots": boundary["roots"], "local_sources": sources,
            "direct_external_families": sorted(external)}


def package_pins(main_only):
    main = json.loads((ROOT / "lake-manifest.json").read_text())
    pins = {entry["name"]: entry["rev"] for entry in main["packages"]}
    if {"Arklib", "VCVio", "PolyFun"} & pins.keys():
        raise ValueError("optional dependencies entered the main package")
    if not main_only:
        optional = json.loads((INTEGRATION / "lake-manifest.json").read_text())
        other = {entry["name"]: entry["rev"] for entry in optional["packages"]
                 if entry["type"] == "git"}
        for name, rev in pins.items():
            if other.get(name) != rev:
                raise ValueError(f"incompatible shared dependency: {name}")
        if (ROOT / "lean-toolchain").read_bytes() != (INTEGRATION / "lean-toolchain").read_bytes():
            raise ValueError("incompatible main and integration Lean toolchains")
    return pins


def all_modules(root, family):
    return [".".join(path.relative_to(root).with_suffix("").parts)
            for path in sorted((root / family).rglob("*.lean"))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--main-only", action="store_true")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--lean", default="lean")
    selection.add_argument("--lake", help="select the header parser through Lake env lean")
    args = parser.parse_args()
    pins = package_pins(args.main_only)
    boundaries = {name: value for name, value in BOUNDARIES.items()
                  if not (args.main_only and name == "external_free_programs")}
    boundaries["source_and_module_contracts"] = {
        "roots": all_modules(ROOT, "Zkc/Source") + all_modules(ROOT, "Zkc/Modules"),
        "external": ["Init", "Lean", "Std", "Mathlib", "Aesop"],
        "forbidden": ["Zkc.Compiler", "Zkc.Protocols", "ZkcArkLib", "Tests", "Examples", "Tools"],
    }
    boundaries["complete_main_library"] = {
        "roots": ["Zkc"] + all_modules(ROOT, "Zkc"),
        "external": ["Init", "Lean", "Std", "Mathlib", "Aesop"],
        "forbidden": ["Zkc.Compat", "ZkcArkLib", "Tests", "TestsArkLib", "Examples", "Tools"],
    }
    if not args.main_only:
        boundaries["complete_optional_library"] = {
            "roots": all_modules(INTEGRATION, "ZkcArkLib"),
            "external": ["Init", "Lean", "Std", "Mathlib", "Aesop", "ArkLib", "VCVio", "PolyFun"],
            "forbidden": ["Zkc.Compat", "Tests", "TestsArkLib", "Examples", "Tools"],
        }
    with HeaderParser(args.lean, lake=args.lake) as headers:
        checked = {name: check_boundary(name, boundary, headers) for name, boundary in boundaries.items()}
    print(json.dumps({"format": "zkc.library-boundaries.v2", "status": "pass",
                      "main_package_pins": pins,
                      "boundaries": checked,
                      "scope": "complete owned library imports, selected narrower dependency boundaries, "
                               "module naming and compatible package pins; not a theorem or native proof"},
                     indent=2))


if __name__ == "__main__":
    main()
