#!/usr/bin/env python3
"""Static and log audit for round-15 seed R2.

This checks compilation evidence only.  It does not turn the conditional
physical dictionary or the fixed finite model into an area-seed proof.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
HERE = ROOT / "AHP/round15/seed/r2"
LOCAL = HERE / "Leading.lean"
SHARED = ROOT / "AHP/round15/shared/seed/R2_Leading.lean"
BASE_LOG = ROOT / "AHP/round15/seed/r1/Seed.lean.log"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MAIN = "AdalyFormal.Round15.Seed.cofinalUnitDominantAreaSeed_of_chargedVector"
NEW = {
    "AdalyFormal.Round14.Cancellation.chargedArea_smul",
    "AdalyFormal.Round15.Seed.chargedArea_real_smul",
    "AdalyFormal.Round15.Seed.chargedBilin",
    "AdalyFormal.Round15.Seed.chargedMixed",
    "AdalyFormal.Round15.Seed.chargedBilin_add_left",
    "AdalyFormal.Round15.Seed.chargedBilin_add_right",
    "AdalyFormal.Round15.Seed.chargedBilin_real_smul_left",
    "AdalyFormal.Round15.Seed.chargedBilin_real_smul_right",
    "AdalyFormal.Round15.Seed.chargedTwoLayerMode",
    "AdalyFormal.Round15.Seed.chargedArea_twoLayerMode",
    "AdalyFormal.Round15.Seed.radiusChargedTwoLayerObservable",
    "AdalyFormal.Round15.Seed.radiusLaurentData_of_chargedTwoLayer",
    "AdalyFormal.Round15.Seed.ChargedVectorLeading",
    "AdalyFormal.Round15.Seed.tendsto_chargedArea_vector",
    "AdalyFormal.Round15.Seed.radiusChargedVectorObservable",
    "AdalyFormal.Round15.Seed.radiusDominantData_of_chargedVectorLeading",
    "AdalyFormal.Round15.Seed.chargedVectorLeading_of_twoLayer",
    "AdalyFormal.Round15.Seed.ChargedVectorData",
    "AdalyFormal.Round15.Seed.CofinalChargedVectorCertificate",
    MAIN,
    "AdalyFormal.Round15.Seed.collarTestMatrix",
    "AdalyFormal.Round15.Seed.collarTestLeadingConstant",
    "AdalyFormal.Round15.Seed.collarTestLeadingConstant_ne_zero",
    "AdalyFormal.Round15.Seed.dictionary_mode0_ne_zero",
    "AdalyFormal.Round15.Seed.collarModelLeading",
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def record_list(path):
    return re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", path.read_text(), re.S)

def records(path):
    return {
        name: {x.strip() for x in body.replace("\n", " ").split(",") if x.strip()}
        for name, body in record_list(path)
    }

def clean_log(path):
    text = path.read_text()
    assert "error:" not in text, f"error in {path}"
    assert "warning:" not in text, f"warning in {path}"
    assert "sorryAx" not in text, f"sorryAx in {path}"

for path in (LOCAL, SHARED):
    assert path.with_suffix(path.suffix + ".exit").read_text().strip() == "0"
    clean_log(path.with_suffix(path.suffix + ".log"))
assert LOCAL.read_bytes() == SHARED.read_bytes(), "publication is not byte-identical"
assert LOCAL.with_suffix(".lean.log").read_bytes() == SHARED.with_suffix(".lean.log").read_bytes()

local_records = records(LOCAL.with_suffix(".lean.log"))
shared_records = records(SHARED.with_suffix(".lean.log"))
assert local_records == shared_records
assert len(record_list(LOCAL.with_suffix(".lean.log"))) == 419
assert len(local_records) == 417, len(local_records)
assert all(ax <= ALLOWED for ax in local_records.values())
base_records = records(BASE_LOG)
assert set(base_records) == set(local_records) - NEW
assert len(NEW) == 25
assert MAIN in local_records
assert local_records[MAIN] == ALLOWED

source = LOCAL.read_text()
fragment = (HERE / "R2Declarations.lean").read_text()
assert source == (ROOT / "AHP/round15/seed/r1/Seed.lean").read_text().rstrip() + "\n" + fragment
assert re.findall(r"^import\s+(\S+)", source, re.M) == ["DrEquiv", "ZXR2Flat6"]
for forbidden in ("sorry", "admit", "native_decide", "unsafe", "implemented_by", "extern", "opaque"):
    assert not re.search(rf"\b{forbidden}\b", fragment), forbidden
assert not re.search(r"^\s*axiom\b", fragment, re.M)
assert not re.search(r"\b(lake build|REPRODUCE\.sh)\b", fragment)

build = json.loads((HERE / "BUILD.json").read_text())
assert build["identical"] is True
assert build["sha256"] == sha(LOCAL)
assert build["lines"] == len(source.splitlines())

main_line = re.search(
    rf"'{re.escape(MAIN)}' depends on axioms: \[(.*?)\]",
    LOCAL.with_suffix(".lean.log").read_text(), re.S).group(0)
main_line = " ".join(main_line.split())
result = {
    "status": "pass",
    "local": str(LOCAL.relative_to(ROOT)),
    "shared": str(SHARED.relative_to(ROOT)),
    "source_sha256": sha(LOCAL),
    "log_sha256": sha(LOCAL.with_suffix(".lean.log")),
    "lines": len(source.splitlines()),
    "local_exit": 0,
    "shared_exit": 0,
    "byte_identical_source": True,
    "byte_identical_log": True,
    "imports": ["DrEquiv", "ZXR2Flat6"],
    "axiom_record_count": len(record_list(LOCAL.with_suffix(".lean.log"))),
    "unique_axiom_record_names": len(local_records),
    "new_axiom_record_count": len(NEW),
    "all_axioms_permitted": True,
    "mainDeclaration": MAIN,
    "axiomLine": main_line,
    "conditional_only": True,
    "physical_certificate_inhabited": False,
    "closedGoal": "none",
}
(HERE / "AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
