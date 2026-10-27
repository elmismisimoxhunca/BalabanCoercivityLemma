#!/usr/bin/env python3
"""Static audit of the local and published Round-14 transfer R2 artifacts."""
from pathlib import Path
import hashlib
import json
import re

H = Path(__file__).resolve().parent
LOCAL = H / "Collar.lean"
SHARED = H.parents[1] / "shared/transfer/R2_Collar.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NEW = [
    "twoLayerMode", "twoLayerDecay", "twoLayerMixed", "twoLayerGrow",
    "twoLayerQuadratic", "twoLayerQuadratic_eq_laurent",
    "twoLayerQuadratic_eventually_ne_zero", "eventually_ne_zero_of_normalized_limit",
    "RadiusDominantData", "radiusDominantData_of_laurent", "dominant_cofinal_index",
    "radius_cofinal_nonzero_of_dominant",
]
NEW_PHYSICAL = [
    "kernelLine_smul", "areaSum_smul", "areaSum_smul_ne_zero", "normalize",
    "normalize_norm", "normalize_kernelLine", "exists_unit_area_generator",
    "UnitAreaSeedRightStar", "unitAreaSeedRightStar_iff", "p3_of_unitAreaSeed",
    "CofinalUnitAreaSeedRightStar", "cofinalUnitAreaSeedRightStar_iff",
    "cofinalP3_of_unitAreaSeed", "CofinalDominantAreaSeed",
    "dominantAreaSeed_of_laurent", "cofinalP3_of_dominantAreaSeed",
    "CofinalUnitDominantAreaSeed", "cofinalP3_of_unitDominantAreaSeed",
]
NAMES = [f"AdalyFormal.Round14.Transfer.{n}" for n in NEW]
NAMES += [f"AdalyFormal.Round14.Transfer.Physical.{n}" for n in NEW_PHYSICAL]
assert len(NAMES) == 30


def audit_source(path):
    text = path.read_text()
    forbidden = re.findall(
        r"\b(?:sorry|admit|native_decide|unsafe|implemented_by|extern|opaque)\b|^\s*axiom\b",
        text,
        flags=re.MULTILINE,
    )
    return text, forbidden


def audit_log(path):
    text = path.read_text()
    records = {}
    for name in NAMES:
        hits = list(re.finditer(re.escape(name) + r"' depends on axioms: \[(.*?)\]", text, re.S))
        assert len(hits) == 1, (path, name, len(hits))
        axioms = {x.strip() for x in hits[0].group(1).replace("\n", " ").split(",")}
        assert axioms <= ALLOWED, (path, name, axioms)
        records[name] = sorted(axioms)
    total = len(re.findall(r"depends on axioms", text))
    return {
        "path": str(path),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "total_axiom_records": total,
        "new_records_checked": len(records),
        "all_new_records_permitted": True,
        "no_error_warning_or_sorryAx": not re.search(r"error:|warning:|sorryAx", text),
    }


local_text, local_forbidden = audit_source(LOCAL)
shared_text, shared_forbidden = audit_source(SHARED)
logs = [audit_log(LOCAL.with_suffix(LOCAL.suffix + ".log")),
        audit_log(SHARED.with_suffix(SHARED.suffix + ".log"))]
exits = {
    str(p): p.with_suffix(p.suffix + ".exit").read_text().strip()
    for p in (LOCAL, SHARED)
}
result = {
    "pass": (
        local_text == shared_text
        and not local_forbidden
        and not shared_forbidden
        and set(exits.values()) == {"0"}
        and all(x["no_error_warning_or_sorryAx"] and x["total_axiom_records"] == 347 for x in logs)
    ),
    "source_byte_identical": local_text == shared_text,
    "source_sha256": hashlib.sha256(LOCAL.read_bytes()).hexdigest(),
    "forbidden_proof_mechanisms": local_forbidden + shared_forbidden,
    "exits": exits,
    "new_declarations_checked": NAMES,
    "logs": logs,
    "qualification": (
        "Builder and separate-publication audit only. These are conditional transfer "
        "reductions, not a physical collar recurrence, an independent mathematical "
        "review, or a proof of P3/CofinalP3/GoalNeg2."
    ),
}
(H / "AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "new_declarations_checked"}, indent=2))
raise SystemExit(0 if result["pass"] else 1)
