#!/usr/bin/env python3
"""Static audit of the local and published round-2 assembly artifacts."""
from pathlib import Path
import hashlib
import json
import re

H = Path(__file__).resolve().parent
LOCAL = H / "AreaLine.lean"
SHARED = H.parents[1] / "shared/assembly/R2_AreaLine.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAMES = [
    "AdalyFormal.Round14.Assembly.AreaNonvanishing",
    "AdalyFormal.Round14.Assembly.areaNonvanishing_of_areaSeed",
    "AdalyFormal.Round14.Assembly.areaNonvanishing_of_unitAreaSeed",
    "AdalyFormal.Round14.Assembly.p3_of_areaNonvanishing",
    "AdalyFormal.Round14.Assembly.p3_of_areaSeed_via_area",
    "AdalyFormal.Round14.Assembly.p3_of_unitAreaSeed_via_area",
]


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
    all_groups = re.findall(r"depends on axioms: \[(.*?)\]", text, re.S)
    all_permitted = all(
        {x.strip() for x in group.replace("\n", " ").split(",")} <= ALLOWED
        for group in all_groups
    )
    return {
        "path": str(path),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "total_axiom_records": total,
        "new_records_checked": len(records),
        "all_new_records_permitted": True,
        "all_records_permitted": all_permitted,
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
        and all(x["no_error_warning_or_sorryAx"] and x["all_records_permitted"]
                and x["total_axiom_records"] == 367 for x in logs)
    ),
    "source_byte_identical": local_text == shared_text,
    "source_sha256": hashlib.sha256(LOCAL.read_bytes()).hexdigest(),
    "forbidden_proof_mechanisms": local_forbidden + shared_forbidden,
    "exits": exits,
    "new_declarations_checked": NAMES,
    "logs": logs,
    "qualification": (
        "Builder and separate-publication audit only. These are conditional area-line "
        "reductions, not a physical area seed, independent mathematical review, or a proof "
        "of P3/CofinalP3/GoalNeg2."
    ),
}
(H / "AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "new_declarations_checked"}, indent=2))
raise SystemExit(0 if result["pass"] else 1)
