#!/usr/bin/env python3
"""Assemble the round-9.2 appendix and the full attempt (round-8 Attempt.lean verbatim,
then the round-9.1 appendix verbatim, then the round-9.2 appendix)."""
import sys, pathlib
here = pathlib.Path(__file__).resolve().parent
root = here.parents[3]
r8 = (root / "AHP/round8/guarded-idea/Attempt.lean").read_text()
r91 = (root / "AHP/round9/qualitative-r1/Appendix.lean").read_text()
parts = ["appendix_head.lean", "P1_abstract.lean", "P2_lattice.lean", "P3_concrete.lean", "P4_flip.lean", "P5_u1.lean"]
app = "".join((here / p).read_text() for p in parts)
out = sys.argv[1] if len(sys.argv) > 1 else "Draft.lean"
(here.parent / "Appendix.lean").write_text(app)
(here / out).write_text(r8 + r91 + app)
print("wrote", here / out, len(r8 + r91 + app), "bytes")
