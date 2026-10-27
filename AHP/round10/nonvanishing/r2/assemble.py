#!/usr/bin/env python3
"""Assemble only this round's short self-contained files; never compile or publish."""
from pathlib import Path
p=Path(__file__).resolve().parent
base=(p/'DirichletResponse.lean').read_text()
tri=base+(p/'TridiagonalPart.lean.txt').read_text()
full=tri+(p/'SourceFamilyPart.lean.txt').read_text()
for name,text in [('TridiagonalResponse.lean',tri),('SourceFamily.lean',full)]:
    dst=p/name
    if not dst.exists() or dst.read_text()!=text:
        dst.write_text(text)
    print(name, len(text.splitlines()), 'lines')
