#!/usr/bin/env python3
"""Verbatim frozen coordinate lemmas, without the unused ambient CfData parameter."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
src=REPO/'lean/src/NsPtB.lean'
s=src.read_text()
names=['mkS','mkS_val','mkS_val0','mkS_val1','mkS_val2','mkS_eta','shift_val_self','shift_val_ne','shift_mkS1','mkS_mem_block','sum_block_eq_cube']
parts=[]; records=[]
for name in names:
 start=re.search(r'^(?:def|theorem) '+name+r'\b',s,re.M).start()
 rest=s[start:]
 # all needed bodies terminate on a blank line (none contain an internal blank)
 stop=rest.index('\n\n')
 nxt=re.search(r'\n(?:def|theorem) ',rest)
 if nxt: stop=min(stop,nxt.start())
 body=rest[:stop]+'\n'
 parts.append(body)
 records.append(dict(name=name,source=str(src.relative_to(REPO)),sha256=hashlib.sha256(body.encode()).hexdigest()))
cube='def cube (g : ℕ → ℕ → ℕ → E) (n a b c : ℕ) : E :=\n  ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, g (a + i) (b + j) (c + k)\n'
assert cube in (REPO/'lean/src/NsPtA.lean').read_text()
records.append(dict(name='cube',source='lean/src/NsPtA.lean',sha256=hashlib.sha256(cube.encode()).hexdigest()))
header='''\nnamespace AdalyFormal.Round10.Nonvanishing.Coordinate
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
variable {L : PeriodicLatticeExtent}
section Cube
variable {E : Type*} [AddCommGroup E]
'''
(ROOT/'Coordinates.lean.txt').write_text(header+cube+'end Cube\n\n'+'\n'.join(parts)+'\n'+''.join('#print axioms '+n+'\n' for n in ['cube']+names)+'end AdalyFormal.Round10.Nonvanishing.Coordinate\n')
old=REPO/'AHP/round10/dictionary/r1/Actual.lean'
s=old.read_text()
gnames=['dilLu','dilTower','dil_unit_size','dil_fine_size']
gparts=[]
for name in gnames:
 start=re.search(r'^(?:def|theorem) '+name+r'\b',s,re.M).start()
 rest=s[start:]; stop=rest.index('\n\n')
 nxt=re.search(r'\n(?:def|theorem) ',rest)
 if nxt: stop=min(stop,nxt.start())
 body=rest[:stop]+'\n'; gparts.append(body)
 records.append(dict(name=name,source=str(old.relative_to(REPO)),sha256=hashlib.sha256(body.encode()).hexdigest()))
(ROOT/'Geometry.lean.txt').write_text('namespace AdalyFormal.Round4.Guarded.RefuteR1\nopen AdalyFormal.Target.ClayStatement\nopen AdalyFormal.StatementLane\n'+'\n'.join(gparts)+'\n'+''.join('#print axioms '+n+'\n' for n in gnames)+'end AdalyFormal.Round4.Guarded.RefuteR1\n')
(ROOT/'COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
