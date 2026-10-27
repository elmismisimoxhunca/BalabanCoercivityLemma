#!/usr/bin/env python3
"""Assemble the round-9.2 joint attempt:
  history/Attempt.r2a.lean  (= round-8 Attempt.lean + round-9.1 appendix + round-9.2 appendix, compiled)
+ snap/AnalyticR1_Appendix.lean, snap/AnalyticR2_Appendix.lean   (analytic route, verbatim snapshots)
+ scratch/P6_joint.lean + one `#print axioms` line per new declaration.
Usage: build2.py <out>   (out relative to the round directory; Appendix2.lean is rewritten too)"""
import sys, re, pathlib
here = pathlib.Path(__file__).resolve().parent
rd = here.parent
base = (rd / "history/Attempt.r2a.lean").read_text()
ar1 = (rd / "snap/AnalyticR1_Appendix.lean").read_text()
ar2 = (rd / "snap/AnalyticR2_Appendix.lean").read_text()
p6 = (here / "P6_joint.lean").read_text()
ns = "AdalyFormal.Round9.Guarded.QualitativeR2Joint."
decls = re.findall(r'^(?:theorem|def|lemma|noncomputable def|noncomputable abbrev|abbrev)\s+(\S+)', p6, re.M)
prints = "\n" + "".join("#print axioms " + ns + d + "\n" for d in decls)
app2 = p6 + prints
out = sys.argv[1] if len(sys.argv) > 1 else "scratch/Draft.lean"
(rd / "Appendix2.lean").write_text(app2)
full = base + ar1 + ar2 + app2
(rd / out).write_text(full)
print("wrote", rd / out, len(full), "bytes,", full.count("\n"), "lines,", len(decls), "new declarations")
