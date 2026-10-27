#!/usr/bin/env python3
"""Independent artifact checks; no numerical model and no Lean invocation."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ITEM = HERE.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b")
DECL = re.compile(r"^(?:noncomputable )?(?:def|abbrev|theorem|lemma) ([^\s:({]+)")
RECORD = re.compile(r"^'(.+?)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.M)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def declarations(text):
    lines = text.splitlines()
    scopes = []
    result = {}
    for i, line in enumerate(lines):
        m = re.match(r"^(namespace|section)(?: (\S+))?$", line)
        if m:
            scopes.append((m[1], m[2] or ""))
        elif re.match(r"^end(?: |$)", line):
            assert scopes, (i + 1, line)
            scopes.pop()
        m = DECL.match(line)
        if m:
            name = ".".join([value for kind, value in scopes if kind == "namespace"] + [m[1]])
            stop = i + 1
            while stop < len(lines) and lines[stop] and lines[stop][0].isspace():
                stop += 1
            assert name not in result, name
            result[name] = {"line": i + 1, "text": "\n".join(lines[i:stop])}
    assert not scopes, scopes
    return result


def short_decl(text, name):
    found = [v for k, v in declarations(text).items() if k == name or k.endswith("." + name)]
    assert len(found) == 1, (name, len(found))
    return found[0]


pin = ITEM / "pin/Statement.lean"
pin_raw = pin.read_bytes()
old_pin = ROOT / "AHP/round2/guarded/pin/Statement.lean"
assert pin_raw.startswith(old_pin.read_bytes())
pin_text = pin_raw.decode()
for n in (1, 2):
    assert short_decl(pin_text, f"GoalNeg{n}")["text"] == f"def GoalNeg{n} : Prop := ¬ GoalPos{n}"

provenance = {
    "lean/src/D1Lit.lean": ["PlaqSel", "selIn", "selAll", "DeltaS", "DpiFullS", "DpiFullS_symm", "JfS", "dataS", "dataS_laws", "G1invS", "H1inS", "NmatS", "firstTermS", "genFormS", "InstIneqS"],
    "lean/src/D2Cons.lean": ["InstIneqSG", "CoercG8AtSG", "P428Target8SG"],
    "lean/src/GdR5a.lean": ["GuardResidualT"],
    "lean/src/DrEquiv.lean": ["GShape", "CPen", "GuardPencilT"],
    "AHP/round2/guarded/r2-prove/Attempt.lean": ["response", "boundaryShift", "localCorrected", "CBoundaryResponse", "CNoBoundaryReturn"],
}
copy_records = []
for path, names in provenance.items():
    source = (ROOT / path).read_text()
    for name in names:
        local, frozen = short_decl(pin_text, name), short_decl(source, name)
        assert local["text"] == frozen["text"], (path, name)
        copy_records.append({"name": name, "pinLine": local["line"], "source": path, "sourceLine": frozen["line"], "exact": True})

round2 = declarations((ROOT / "AHP/round2/guarded/r2-prove/Attempt.lean").read_text())
main_names = {
    "r1-prove": "AdalyFormal.Round3.Guarded.R1Prove.goalPos2_of_return_offSelectorShell",
    "r1-refute": "AdalyFormal.Round3.Guarded.RefuteR1.probe_not_negative_witness",
    "r2-prove": "AdalyFormal.Round3.Guarded.R2Prove.goalPos2_of_inverse_boundary_jetInputZero",
    "r2-refute": "AdalyFormal.Round3.Guarded.RefuteR2.wide_probe_geometry_and_competitor",
    "r3-prove": "AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero",
    "r3-refute": "AdalyFormal.Round3.Guarded.RefuteR3.wide_in_class_nonflat_competitor",
}
files = []
for name in ["pin"] + list(main_names):
    original = pin if name == "pin" else ITEM / name / "Attempt.lean"
    checked = HERE / (name + ".lean")
    raw = original.read_bytes()
    assert raw == checked.read_bytes(), name
    assert raw.startswith(pin_raw), name
    text = raw.decode()
    imports = re.findall(r"^import (\S+)\s*$", text, re.M)
    assert imports == ["DrEquiv"], (name, imports)
    assert (ROOT / "lean/src/DrEquiv.lean").is_file()
    assert not FORBIDDEN.findall(text), name
    decls = declarations(text)
    reused = []
    for decl_name, decl in decls.items():
        if decl_name in round2:
            assert decl["text"] == round2[decl_name]["text"], (name, decl_name)
            reused.append(decl_name)
    log_path, exit_path = Path(str(checked) + ".log"), Path(str(checked) + ".exit")
    exit_code = int(exit_path.read_text().strip())
    assert exit_code == 0, (name, exit_code)
    assert checked.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns, name
    log = log_path.read_text()
    diagnostics = re.findall(r"^.*\b(?:warning|error):.*$", log, re.M)
    assert not diagnostics, (name, diagnostics)
    assert "sorryAx" not in log
    records = [{"name": m[1], "axioms": [s.strip() for s in (m[2] or "").split(",") if s.strip()]} for m in RECORD.finditer(log)]
    assert records
    for record in records:
        assert set(record["axioms"]) <= ALLOWED, (name, record)
    names = {r["name"] for r in records}
    assert set(decls) <= names, (name, set(decls) - names)
    requested = re.findall(r"^#print axioms (\S+)\s*$", text, re.M)
    assert len(requested) == len(records), (name, len(requested), len(records))
    for request, record in zip(requested, records):
        assert record["name"] == request or record["name"].endswith("." + request), (name, request, record)
    builder_log = Path(str(original) + ".log").read_text()
    builder_records = [{"name": m[1], "axioms": [s.strip() for s in (m[2] or "").split(",") if s.strip()]} for m in RECORD.finditer(builder_log)]
    assert builder_records == records, (name, "dependency records changed")
    row = {"name": name, "original": str(original.relative_to(ROOT)), "checkedCopy": str(checked.relative_to(ROOT)), "sha256": sha(raw), "exactCopy": True, "completePinBytePrefix": True, "imports": imports, "forbiddenTokens": [], "exitCode": exit_code, "freshTimestampOrder": True, "diagnostics": diagnostics, "localDeclarationCount": len(decls), "allLocalDeclarationsPrinted": True, "recordCount": len(records), "distinctRecordCount": len(names), "axiomsStandard": True, "recordsMatchBuilderLog": True, "reusedRound2DeclarationsVerbatim": reused, "records": records}
    if name in main_names:
        main = main_names[name]
        row["mainDeclaration"] = main
        row["mainLine"] = decls[main]["line"]
        row["mainTypeSource"] = decls[main]["text"].split(":=", 1)[0].rstrip()
        row["mainAxioms"] = next(r["axioms"] for r in records if r["name"] == main)
        row["verdict"] = "does-not-close"
    files.append(row)

assert (ITEM / "r3-refute/Attempt.lean").read_bytes().startswith((ITEM / "r2-refute/Attempt.lean").read_bytes())
p2 = (ITEM / "r2-prove/Attempt.lean").read_text()
p3 = (ITEM / "r3-prove/Attempt.lean").read_text()
assert p2.split("/-! New positive attempt:", 1)[0] == p3.split("/-! Mixed second-jet cancellation", 1)[0]
assert int((HERE / "recheck.exit").read_text().strip()) == 0
result = {"checksPass": True, "round2PinExactBytePrefix": True, "round2PinSHA256": sha(old_pin.read_bytes()), "round3PinSHA256": sha(pin_raw), "negativeGoalsLiteralNegations": True, "verbatimPinCopies": copy_records, "files": files, "totalDependencyRecordsIncludingRepetitions": sum(r["recordCount"] for r in files), "allAxiomsStandard": True, "closedGoals": [], "status": "open", "limitations": "Artifact audit and independent Lean replay of partial results only. No numerical replay, source-image rereading, full build, or positive/negative headline proof."}
(HERE / "CHECKS.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({k: result[k] for k in ["checksPass", "status", "closedGoals", "totalDependencyRecordsIncludingRepetitions", "allAxiomsStandard"]}, indent=2))
for row in files:
    print(f'{row["name"]}: exit={row["exitCode"]}, local={row["localDeclarationCount"]}, records={row["recordCount"]}, distinct={row["distinctRecordCount"]}, sha256={row["sha256"]}')
